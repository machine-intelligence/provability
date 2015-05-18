{-# LANGUAGE OverloadedStrings #-}
module Modal.Environment
  ( Env
  , ModalVar(..)
  , modalVarParser
  , nobody
  , actions
  , subagents
  , participants
  , rankedParticipants
  , missingSubagents
  , insert
  , insertAll
  , (@<)
  , (@+)
  , (@++)
  , (@!)
  , EnvError(..)
  ) where
import Control.Applicative
import Control.Monad (when, unless)
import Data.Either (partitionEithers)
import Data.Map (Map)
import Data.Set (Set)
import Data.Text (Text)
import Modal.Code
import Modal.Formulas hiding (left)
import Modal.Parser (Parsable, parser)
import Modal.Programming
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Printf (printf)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Modal.Parser as P

-- TODO: Rename, and perhaps move.
data ModalVar a o = MeVsThemIs a | ThemVsMeIs o | ThemVsOtherIs Name o deriving (Eq, Ord)

instance (Show a, Show o) => Show (ModalVar a o) where
  show (MeVsThemIs a) = "Me(Them)=" ++ show a
  show (ThemVsMeIs o) = "Them(Me)=" ++ show o
  show (ThemVsOtherIs n o) = "Them(" ++ Text.unpack n ++ ")=" ++ show o

instance (Parsable a, Parsable o) => Parsable (ModalVar a o) where
  parser = modalVarParser parser parser

instance ModalizableVar ModalVar where
  makeRelParser a o = modalVarParser (relationParser a) (relationParser o)

  relToFormula (MeVsThemIs rel) = evalRelation getA MeVsThemIs rel
  relToFormula (ThemVsMeIs rel) = evalRelation getO ThemVsMeIs rel
  relToFormula (ThemVsOtherIs n rel) = evalRelation getO (ThemVsOtherIs n) rel

  otherAgentsReferencedIn (ThemVsOtherIs n _) = [n]
  otherAgentsReferencedIn _ = []

  expandNames v1 v2 me them = fmap expandName where
    expandName (MeVsThemIs val) = v1 me them val
    expandName (ThemVsMeIs val) = v2 them me val
    expandName (ThemVsOtherIs other val) = v2 them other val

modalVarParser :: Parsec Text s a -> Parsec Text s o -> Parsec Text s (ModalVar a o)
modalVarParser a o = try mvt <|> try tvm <|> try tvo <?> "a modal variable" where
  mvt = choice [string "Me(Them)", string "Me()"] *> (MeVsThemIs <$> a)
  tvm = choice [string "Them(Me)", string "Them()"] *> (ThemVsMeIs <$> o)
  tvo = string "Them(" *> (ThemVsOtherIs <$> P.name) <*> (char ')' *> o)

--------------------------------------------------------------------------------
-- Helper functions to verify that modal formulas and modal programs are fully
-- modalized (which is necessary in order to guarantee a fixpoint).

isModalized :: ModalFormula v -> Bool
isModalized = modalEval ModalEvaluator {
  handleVar = const False, handleVal = const True, handleNeg = id,
  handleAnd = (&&), handleOr = (&&), handleImp = (&&), handleIff = (&&),
  handleBox = const True, handleDia = const True }

isFullyModalized :: [a] -> Program v a o -> Bool
isFullyModalized as (ModalProgram p) = all (isModalized . p) as

subagents :: ModalizableVar v => [a] -> Program v a o -> Set Name
subagents as program = Set.unions [fSubagents $ formulaFor program a | a <- as] where
  fSubagents = Set.fromList . extractName . allVars
  extractName = concatMap otherAgentsReferencedIn

--------------------------------------------------------------------------------
-- The environment type. It holds all of the agents on a given side of combat.
-- Agents in an Env A O have action type A and consider opponents with option
-- type O. That is, these agents can return elements of A and face opponents
-- who can return elements of O.

data Env v a o = Env
  { _participants :: Map Name (Program v a o, Int)
  , actions :: [a] }
instance Show (Env v a o) where
	show (Env ps _) = printf "{%s}" (Text.unpack $ Text.intercalate ", " $ Map.keys ps)

nobody :: [a] -> Env v a o
nobody = Env Map.empty

missingSubagents :: ModalizableVar v => Env v a o -> Program v a o-> Set Name
missingSubagents env program = subagents (actions env) program Set.\\ namesIn env where
  namesIn = Set.fromList . Map.keys . _participants

participants :: Env v a o -> Map Name (Program v a o)
participants = Map.map fst . _participants

-- The modal rank of each agent is tracked, but not yet used.
rankedParticipants :: Env v a o -> Map Name Int
rankedParticipants = Map.map snd . _participants

rankIn :: ModalizableVar v => Env v a o -> Name -> Program v a o -> Either EnvError Int
rankIn env name program = if null missings then Right rank else Left err where
  err = MissingSubagents name (Set.fromList missings)
  rank = if null ranks then 0 else succ $ maximum ranks
  (missings, ranks) = partitionEithers $ Set.toList $ Set.map lookupRank subs
  subs = subagents (actions env) program
  lookupRank n = maybe (Left n) (Right . snd) $ Map.lookup n (_participants env)

-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
-- Functions that insert agents into environments.

-- This is the safe way of inserting an agent into an environment.
insert :: ModalizableVar v => Env v a o -> Name -> Program v a o -> Either EnvError (Env v a o)
insert env name program = do
  (unless $ isFullyModalized (actions env) program) (Left $ IsNotModalized name)
  (when $ Map.member name $ _participants env) (Left $ NameCollision name)
  rank <- rankIn env name program
  return env{_participants=Map.insert name (program, rank) (_participants env)}

insertAll :: ModalizableVar v =>
  Env v a o -> [(Name, Program v a o)] -> Either EnvError (Env v a o)
insertAll env ((n, p):xs) = insert env n p >>= flip insertAll xs
insertAll env [] = Right env

-- A safe way to start building an environment.
-- Example: env = nobody @< cooperateBot @+ defectBot @+ fairBot
(@<) :: (ModalizableVar v, Enum a) =>
  Env v a o -> (Name, Program v a o) -> Either EnvError (Env v a o)
(@<) e = uncurry (insert e)

-- A safe combinator for continuing to build an environment
-- Example: env = nobody @< cooperateBot @+ defectBot @+ fairBot
(@+) :: (ModalizableVar v, Enum a) =>
  Either EnvError (Env v a o) -> (Name, Program v a o) -> Either EnvError (Env v a o)
e @+ nf = e >>= (@< nf)

-- An inline version of insertAll
(@++) :: (ModalizableVar v, Enum a) =>
  Either EnvError (Env v a o) -> [(Name, Program v a o)] -> Either EnvError (Env v a o)
e @++ nps = e >>= flip insertAll nps

-- The unsafe way of building environments
(@!) :: (ModalizableVar v, Enum a) => Env v a o -> (Name, Program v a o) -> Env v a o
(@!) e = uncurry (force .: insert e)
