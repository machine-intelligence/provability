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

-- TODO: Generalize so that players can have different action types.

die :: Show x => x -> IO a
die = printf "Error: %s" . show

type Action a = ModalVar a a
type IsAct a = (Ord a, Enum a)

data VsVar a = Vs { player :: Name, playedOn :: Name, plays :: a } deriving (Eq, Ord)
instance Show a => Show (VsVar a) where
  show (Vs n1 n2 a) = printf "%s(%s)=%s" (Text.unpack n1) (Text.unpack n2) (show a)

expandNames :: Name -> Name -> ModalFormula (Action a) -> ModalFormula (VsVar a)
expandNames me them = mapVariable expandName where
  expandName (MeVsThemIs val) = Vs me them val
  expandName (ThemVsMeIs val) = Vs them me val
  expandName (ThemVsOtherIs other val) = Vs them other val

subagents :: Enum a => Program a a -> Set Name
subagents program = Set.unions [fSubagents $ program a | a <- enumerate] where
  fSubagents = Set.fromList . extractName . allVars
  extractName xs = [name | ThemVsOtherIs name _ <- xs]

isModalized :: ModalFormula v -> Bool
isModalized = modalEval ModalEvaluator {
  handleVar = const False, handleVal = const True, handleNeg = id,
  handleAnd = (&&), handleOr = (&&), handleImp = (&&), handleIff = (&&),
  handleBox = const True, handleDia = const True }

isFullyModalized :: Enum a => Program a v -> Bool
isFullyModalized program = all (isModalized . program) enumerate

newtype Env a = Env { _participants :: Map Name (Program a a, Int) }
instance Show (Env a) where
	show (Env ps) = printf "(%s)" (Text.unpack $ Text.intercalate ", " $ Map.keys ps)

nobody :: Env a
nobody = Env Map.empty

participants :: Env a -> Set Name
participants = Set.fromList . Map.keys . _participants

rankedParticipants :: Env a -> Map Name Int
rankedParticipants = Map.map snd . _participants

missingSubagents :: IsAct a => Env a -> Program a a-> Set Name
missingSubagents env program = subagents program Set.\\ participants env

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

rankIn :: IsAct a => Env a -> Name -> Program a a -> Either EnvError Int
rankIn env name program = if null missings then Right rank else Left err where
  err = MissingSubagents name (Set.fromList missings)
  rank = if null ranks then 0 else succ $ maximum ranks
  (missings, ranks) = partitionEithers $ Set.toList $ Set.map lookupRank $ subagents program
  lookupRank n = maybe (Left n) (Right . snd) $ Map.lookup n (_participants env)

tryInsert :: IsAct a => Env a -> Name -> Program a a -> Either EnvError (Env a)
tryInsert env name program = do
  (unless $ isFullyModalized program) (Left $ IsNotModalized name)
  (when $ Map.member name $ _participants env) (Left $ NameCollision name)
  rank <- rankIn env name program
  return $ Env $ Map.insert name (program, rank) (_participants env)

insert :: IsAct a => Env a -> Name -> Program a a -> IO (Env a)
insert = either die return .:: tryInsert

forceInsert :: IsAct a => Env a -> Name -> Program a a -> Env a
forceInsert = either (error . show) id .:: tryInsert

(@+) :: IsAct a => Either EnvError (Env a) -> (Name, Program a a) -> Either EnvError (Env a)
e @+ nf = e >>= (@< nf)

(@<) :: IsAct a => Env a -> (Name, Program a a) -> Either EnvError (Env a)
(@<) e = uncurry (tryInsert e)

(@!) :: IsAct a => Env a -> (Name, Program a a) -> (Env a)
(@!) e = uncurry (forceInsert e)

data CompetitionError = UnknownPlayer Name deriving (Eq, Ord, Read, Show)

type Competition a = Map (VsVar a) (ModalFormula (VsVar a))

tryCompetitionMap :: IsAct a =>
  Env a -> Name -> Name -> Either CompetitionError (Competition a)
tryCompetitionMap env name1 name2 = do
  let emap = _participants env
  let getPlayer n = maybe (Left $ UnknownPlayer n) (Right . fst) (Map.lookup n emap)
  program1 <- getPlayer name1
  program2 <- getPlayer name2
  let top1 = [(Vs name1 name2 a, expandNames name1 name2 (program1 a)) | a <- enumerate]
  let top2 = [(Vs name2 name1 a, expandNames name2 name1 (program2 a)) | a <- enumerate]
  lefts <- sequence [tryCompetitionMap env name2 x | x <- Set.toList $ subagents program1]
  rights <- sequence [tryCompetitionMap env name1 x | x <- Set.toList $ subagents program2]
  return $ Map.unions $ (Map.fromList top1) : (Map.fromList top2) : lefts ++ rights

competitionMap :: IsAct a => Env a -> Name -> Name -> IO (Competition a)
competitionMap = either die return .:: tryCompetitionMap

forceCompetitionMap :: IsAct a => Env a -> Name -> Name -> (Competition a)
forceCompetitionMap = either (error . show) id .:: tryCompetitionMap

tryCompete :: IsAct a => Env a -> Name -> Name -> Either CompetitionError (a, a)
tryCompete env name1 name2 = do
  fixpt <- findGeneralGLFixpoint <$> tryCompetitionMap env name1 name2
  let is1 (Vs n1 n2 _) = n1 == name1 && n2 == name2
  let is2 (Vs n1 n2 _) = n1 == name2 && n2 == name1
  let Vs _ _ result1 = extractPMEEkey is1 fixpt
  let Vs _ _ result2 = extractPMEEkey is2 fixpt
  return (result1, result2)

compete :: IsAct a => Env a -> Name -> Name -> IO (a, a)
compete = either die return .:: tryCompete
