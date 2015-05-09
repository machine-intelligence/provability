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
  , unsafeInsert
  , (@<)
  , (@+)
  , (@!)
  , EnvError(..)
  , CompetitionError(..)
  , tryCompetitionMap
  , competitionMap
  , unsafeCompetitionMap
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

--------------------------------------------------------------------------------
-- The variable type in the modalized formulas.
-- Examples: "FairBot(PrudentBot)=C", "UDT(U)=a", "U(UDT)=o"
-- This is how the modal agents reference "possibilities".

data VsVar a o
  = Vs1 Name Name a
  | Vs2 Name Name o
  deriving (Eq, Ord)
instance (Show a, Show o) => Show (VsVar a o) where
  show (Vs1 n1 n2 a) = printf "%s(%s)=%s" (Text.unpack n1) (Text.unpack n2) (show a)
  show (Vs2 n1 n2 o) = printf "%s(%s)=%s" (Text.unpack n1) (Text.unpack n2) (show o)

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
-- Helper functions to verify that modal formulas and modal programs are fully
-- modalized (which is necessary in order to guarantee a fixpoint).

isModalized :: ModalFormula v -> Bool
isModalized = modalEval ModalEvaluator {
  handleVar = const False, handleVal = const True, handleNeg = id,
  handleAnd = (&&), handleOr = (&&), handleImp = (&&), handleIff = (&&),
  handleBox = const True, handleDia = const True }

isFullyModalized :: Enum a => Program a v -> Bool
isFullyModalized program = all (isModalized . program) enumerate

--------------------------------------------------------------------------------
-- The environment type. It holds all of the agents on a given side of combat.
-- Agents in an Env A O have action type A and consider opponents with option
-- type O. That is, these agents can return elements of A and face opponents
-- who can return elements of O.

newtype Env a o = Env { _participants :: Map Name (Program a o, Int) }
instance Show (Env a o) where
	show (Env ps) = printf "(%s)" (Text.unpack $ Text.intercalate ", " $ Map.keys ps)

nobody :: Env a o
nobody = Env Map.empty

subagents :: Enum a => Program a o -> Set Name
subagents program = Set.unions [fSubagents $ program a | a <- enumerate] where
  fSubagents = Set.fromList . extractName . allVars
  extractName xs = [name | ThemVsOtherIs name _ <- xs]

missingSubagents :: IsAct a => Env a o -> Program a o-> Set Name
missingSubagents env program = subagents program Set.\\ participants env

participants :: Env a o -> Set Name
participants = Set.fromList . Map.keys . _participants

-- The modal rank of each agent is tracked, but not yet used.
rankedParticipants :: Env a o -> Map Name Int
rankedParticipants = Map.map snd . _participants

rankIn :: IsAct a => Env a o -> Name -> Program a o -> Either EnvError Int
rankIn env name program = if null missings then Right rank else Left err where
  err = MissingSubagents name (Set.fromList missings)
  rank = if null ranks then 0 else succ $ maximum ranks
  (missings, ranks) = partitionEithers $ Set.toList $ Set.map lookupRank $ subagents program
  lookupRank n = maybe (Left n) (Right . snd) $ Map.lookup n (_participants env)

-------------------------------------------------------------------------------

-- Helper constraint kind capturing the constraints required on the action type
-- in order to insert an agent into an environment. (The constraint is fairly
-- small now, but may grow.)
type IsAct a = (Ord a, Enum a)

-- If you want to deal with environments in a safe way, you need to handle
-- errors of this type.
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

die :: Show x => x -> IO a
die = printf "Error: %s" . show

-------------------------------------------------------------------------------
-- Functions that insert agents into environments.

-- This is the safe way of inserting an agent into an environment.
tryInsert :: IsAct a => Env a o -> Name -> Program a o -> Either EnvError (Env a o)
tryInsert env name program = do
  (unless $ isFullyModalized program) (Left $ IsNotModalized name)
  (when $ Map.member name $ _participants env) (Left $ NameCollision name)
  rank <- rankIn env name program
  return $ Env $ Map.insert name (program, rank) (_participants env)

-- This is the way that complains nicely if there's a problem.
insert :: IsAct a => Env a o -> Name -> Program a o -> IO (Env a o)
insert = either die return .:: tryInsert

-- This is the unsafe way of inserting agents into environments.
unsafeInsert :: IsAct a => Env a o -> Name -> Program a o -> Env a o
unsafeInsert = either (error . show) id .:: tryInsert

-- A safe way to start building an environment.
-- Example: env = nobody @< cooperateBot @+ defectBot @+ fairBot
(@<) :: IsAct a => Env a o -> (Name, Program a o) -> Either EnvError (Env a o)
(@<) e = uncurry (tryInsert e)

-- A safe combinator for continuing to build an environment
-- Example: env = nobody @< cooperateBot @+ defectBot @+ fairBot
(@+) :: IsAct a =>
  Either EnvError (Env a o) -> (Name, Program a o) -> Either EnvError (Env a o)
e @+ nf = e >>= (@< nf)

-- The unsafe way of building environments
(@!) :: IsAct a => Env a o -> (Name, Program a o) -> (Env a o)
(@!) e = uncurry (unsafeInsert e)

--------------------------------------------------------------------------------
-- Competitions, by default, allow agents with different action types to play
-- against each other. This introduces a bit of extra complexity to the types;
-- some helper functions (without 2s in their names) exist below to handle this
-- simpler case.

type Competition a o = Map (VsVar a o) (ModalFormula (VsVar a o))
data CompetitionError = UnknownPlayer Name deriving (Eq, Ord, Read, Show)

-- Attempts to build a map of modal formulas describing the competition, given
-- two environments and two names.
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

-- Attempts to build the competition map, and complains nicely on failure.
competitionMap2 :: (IsAct a, IsAct o) =>
  Env a o -> Env o a -> Name -> Name -> IO (Competition a o)
competitionMap2 = either die return .::: tryCompetitionMap2

-- Unsafely builds the competition map.
unsafeCompetitionMap2 :: (IsAct a, IsAct o) =>
  Env a o -> Env o a -> Name -> Name -> (Competition a o)
unsafeCompetitionMap2 = either (error . show) id .::: tryCompetitionMap2

-- Attempts to figure out how the two named agents behave against each other.
-- WARNING: This function may error if the modal formulas in the competition
-- map are not P.M.E.E. (provably mutally exclusive and extensional).
tryCompete2 :: (IsAct a, IsAct o) =>
  Env a o -> Env o a -> Name -> Name -> Either CompetitionError (a, o)
tryCompete2 env1 env2 name1 name2 = do
  fixpt <- findGeneralGLFixpoint <$> tryCompetitionMap2 env1 env2 name1 name2
  let Vs1 _ _ result1 = extractPMEEkey (is1 name1 name2) fixpt
  let Vs2 _ _ result2 = extractPMEEkey (is2 name2 name1) fixpt
  return (result1, result2)

-- Attempts to figure out how the two named agents behave, complains nicely on
-- failure.
compete2 :: (IsAct a, IsAct o) => Env a o -> Env o a -> Name -> Name -> IO (a, o)
compete2 = either die return .::: tryCompete2

-- Unsafely figures out how the two agents behave.
unsafeCompete2 :: (IsAct a, IsAct o) => Env a o -> Env o a -> Name -> Name -> (a, o)
unsafeCompete2 = either (error . show) id .::: tryCompete2

--------------------------------------------------------------------------------
-- Simplified versions of the above functions for the scenario where both
-- agents have the same action type.

tryCompetitionMap :: IsAct a =>
  Env a a -> Name -> Name -> Either CompetitionError (Competition a a)
tryCompetitionMap env = tryCompetitionMap2 env env

competitionMap :: IsAct a => Env a a -> Name -> Name -> IO (Competition a a)
competitionMap env = competitionMap2 env env

unsafeCompetitionMap :: IsAct a => Env a a -> Name -> Name -> (Competition a a)
unsafeCompetitionMap env = unsafeCompetitionMap2 env env

tryCompete :: IsAct a => Env a a -> Name -> Name -> Either CompetitionError (a, a)
tryCompete env = tryCompete2 env env

unsafeCompete :: IsAct a => Env a a -> Name -> Name -> (a, a)
unsafeCompete env = unsafeCompete2 env env

compete :: IsAct a => Env a a -> Name -> Name -> IO (a, a)
compete env = compete2 env env
