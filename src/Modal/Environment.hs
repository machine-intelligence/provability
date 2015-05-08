{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
module Modal.Environment
  ( Env
  , nobody
  , participants
  , rankedParticipants
  , missingSubagents
  , tryInsert
  , insert
  , forceInsert
  , (@<)
  , (@+)
  , (@!)
  , EnvError(..)
  , CompetitionError(..)
  , tryCompetitionMap
  , competitionMap
  , forceCompetitionMap
  , tryCompete
  , compete
  ) where
import Control.Applicative
import Control.Monad (when, unless)
import Data.Either (partitionEithers)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Modal.Formulas hiding (left)
import Modal.GameTools hiding (left)
import Modal.Utilities
import Modal.Code
import Text.Printf (printf)

die :: Show x => x -> IO a
die = printf "Error: %s" . show

--------------------------------------------------------------------------------

data VsVar a o
  = Vs1 Name Name a
  | Vs2 Name Name o
  deriving (Eq, Ord)
instance (Show a, Show o) => Show (VsVar a o) where
  show (Vs1 n1 n2 a) = printf "%s(%s)=%s" (Text.unpack n1) (Text.unpack n2) (show a)
  show (Vs2 n1 n2 o) = printf "%s(%s)=%s" (Text.unpack n1) (Text.unpack n2) (show o)

flipVs :: VsVar a o -> VsVar o a
flipVs (Vs1 x y z) = Vs2 x y z
flipVs (Vs2 x y z) = Vs1 x y z

is1 :: Name -> Name -> VsVar a o -> Bool
is1 n m (Vs1 x y _) = x == n && y == m
is1 _ _ _ = False

is2 :: Name -> Name -> VsVar a o -> Bool
is2 n m (Vs2 x y _) = x == n && y == m
is2 _ _ _ = False

expandNames ::
  (Name -> Name -> a -> v) -> (Name -> Name -> o -> v) ->
  Name -> Name -> ModalFormula (ModalVar a o) -> ModalFormula v
expandNames v1 v2 me them = mapVariable expandName where
  expandName (MeVsThemIs val) = v1 me them val
  expandName (ThemVsMeIs val) = v2 them me val
  expandName (ThemVsOtherIs other val) = v2 them other val

--------------------------------------------------------------------------------

type IsAct a = (Ord a, Enum a)

isModalized :: ModalFormula v -> Bool
isModalized = modalEval ModalEvaluator {
  handleVar = const False, handleVal = const True, handleNeg = id,
  handleAnd = (&&), handleOr = (&&), handleImp = (&&), handleIff = (&&),
  handleBox = const True, handleDia = const True }

isFullyModalized :: Enum a => Program a v -> Bool
isFullyModalized program = all (isModalized . program) enumerate

subagents :: Enum a => Program a o -> Set Name
subagents program = Set.unions [fSubagents $ program a | a <- enumerate] where
  fSubagents = Set.fromList . extractName . allVars
  extractName xs = [name | ThemVsOtherIs name _ <- xs]

--------------------------------------------------------------------------------

newtype Env a o = Env { _participants :: Map Name (Program a o, Int) }
instance Show (Env a o) where
	show (Env ps) = printf "(%s)" (Text.unpack $ Text.intercalate ", " $ Map.keys ps)

nobody :: Env a o
nobody = Env Map.empty

participants :: Env a o -> Set Name
participants = Set.fromList . Map.keys . _participants

rankedParticipants :: Env a o -> Map Name Int
rankedParticipants = Map.map snd . _participants

missingSubagents :: IsAct a => Env a o -> Program a o-> Set Name
missingSubagents env program = subagents program Set.\\ participants env

rankIn :: IsAct a => Env a o -> Name -> Program a o -> Either EnvError Int
rankIn env name program = if null missings then Right rank else Left err where
  err = MissingSubagents name (Set.fromList missings)
  rank = if null ranks then 0 else succ $ maximum ranks
  (missings, ranks) = partitionEithers $ Set.toList $ Set.map lookupRank $ subagents program
  lookupRank n = maybe (Left n) (Right . snd) $ Map.lookup n (_participants env)

-------------------------------------------------------------------------------

data EnvError
  = IsNotModalized Name
  | NameCollision Name
  | MissingSubagents Name (Set Name)
  deriving (Eq, Ord, Read)
instance Show EnvError where
  show (IsNotModalized n) = printf "%s is not fully modalized." $ Text.unpack n
  show (NameCollision n) = printf "%s is already in the environment!" $ Text.unpack n
  show (MissingSubagents n ns) = printf "Unknown agents referenced by %s: %s"
    (Text.unpack n) (Text.unpack $ Text.intercalate ", " $ Set.toList ns)

--------------------------------------------------------------------------------

tryInsert :: IsAct a => Env a o -> Name -> Program a o -> Either EnvError (Env a o)
tryInsert env name program = do
  (unless $ isFullyModalized program) (Left $ IsNotModalized name)
  (when $ Map.member name $ _participants env) (Left $ NameCollision name)
  rank <- rankIn env name program
  return $ Env $ Map.insert name (program, rank) (_participants env)

insert :: IsAct a => Env a o -> Name -> Program a o -> IO (Env a o)
insert = either die return .:: tryInsert

forceInsert :: IsAct a => Env a o -> Name -> Program a o -> Env a o
forceInsert = either (error . show) id .:: tryInsert

(@+) :: IsAct a =>
  Either EnvError (Env a o) -> (Name, Program a o) -> Either EnvError (Env a o)
e @+ nf = e >>= (@< nf)

(@<) :: IsAct a => Env a o -> (Name, Program a o) -> Either EnvError (Env a o)
(@<) e = uncurry (tryInsert e)

(@!) :: IsAct a => Env a o -> (Name, Program a o) -> (Env a o)
(@!) e = uncurry (forceInsert e)

--------------------------------------------------------------------------------

data CompetitionError = UnknownPlayer Name deriving (Eq, Ord, Read, Show)

type Competition a o = Map (VsVar a o) (ModalFormula (VsVar a o))

tryCompetitionMap2 :: (IsAct a, IsAct o) =>
  Env a o -> Env o a -> Name -> Name -> Either CompetitionError (Competition a o)
tryCompetitionMap2 env1 env2 name1 name2 = do
  let emap1 = _participants env1
  let emap2 = _participants env2
  program1 <- maybe (Left $ UnknownPlayer name1) (Right . fst) (Map.lookup name1 emap1)
  program2 <- maybe (Left $ UnknownPlayer name2) (Right . fst) (Map.lookup name2 emap2)
  let top1 = [(Vs1 name1 name2 a, expandNames Vs1 Vs2 name1 name2 (program1 a))
                      | a <- enumerate]
  let top2 = [(Vs2 name2 name1 o, expandNames Vs2 Vs1 name2 name1 (program2 o))
                      | o <- enumerate]
  lefts <- sequence [tryCompetitionMap2 env1 env2 x name2
                      | x <- Set.toList $ subagents program1]
  rights <- sequence [tryCompetitionMap2 env1 env2 name1 x
                      | x <- Set.toList $ subagents program2]
  return $ Map.unions $ (Map.fromList top1) : (Map.fromList top2) : lefts ++ rights

competitionMap2 :: (IsAct a, IsAct o) =>
  Env a o -> Env o a -> Name -> Name -> IO (Competition a o)
competitionMap2 = either die return .::: tryCompetitionMap2

forceCompetitionMap2 :: (IsAct a, IsAct o) =>
  Env a o -> Env o a -> Name -> Name -> (Competition a o)
forceCompetitionMap2 = either (error . show) id .::: tryCompetitionMap2

tryCompete2 :: (IsAct a, IsAct o) =>
  Env a o -> Env o a -> Name -> Name -> Either CompetitionError (a, o)
tryCompete2 env1 env2 name1 name2 = do
  fixpt <- findGeneralGLFixpoint <$> tryCompetitionMap2 env1 env2 name1 name2
  let Vs1 _ _ result1 = extractPMEEkey (is1 name1 name2) fixpt
  let Vs2 _ _ result2 = extractPMEEkey (is2 name2 name1) fixpt
  return (result1, result2)

compete2 :: (IsAct a, IsAct o) => Env a o -> Env o a -> Name -> Name -> IO (a, o)
compete2 = either die return .::: tryCompete2

--------------------------------------------------------------------------------

tryCompetitionMap :: IsAct a =>
  Env a a -> Name -> Name -> Either CompetitionError (Competition a a)
tryCompetitionMap env = tryCompetitionMap2 env env

competitionMap :: IsAct a => Env a a -> Name -> Name -> IO (Competition a a)
competitionMap env = competitionMap2 env env

forceCompetitionMap :: IsAct a => Env a a -> Name -> Name -> (Competition a a)
forceCompetitionMap env = forceCompetitionMap2 env env

tryCompete :: IsAct a => Env a a -> Name -> Name -> Either CompetitionError (a, a)
tryCompete env = tryCompete2 env env

compete :: IsAct a => Env a a -> Name -> Name -> IO (a, a)
compete env = compete2 env env
