{-# LANGUAGE OverloadedStrings #-}
module ModalEnvironment
  ( AgentVar(..)
  , Name
  , Env
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
import ModalFormulas hiding (left)
import Text.Printf (printf)

(.:) :: (c -> x) -> (a -> b -> c) -> (a -> b -> x)
(.:) = (.) . (.)

(.::) :: (d -> x) -> (a -> b -> c -> d) -> (a -> b -> c -> x)
(.::) = (.) . (.) . (.)

die :: Show x => x -> IO a
die = printf "Error: %s" . show

type Name = Text

vs :: Name -> Name -> Name
x `vs` y = x <> "(" <> y <> ")"

data AgentVar = MeVsThem | ThemVsMe | ThemVs Name deriving (Eq, Ord)
instance Show AgentVar where
  show MeVsThem = "Me(Them)"
  show ThemVsMe = "Them(Me)"
  show (ThemVs n) = "Them(" ++ Text.unpack n ++ ")"
instance Read AgentVar where
  readsPrec _ str = [(from name, rest) | not $ null name] where
      name = takeWhile (`elem` '_' : ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9']) str
      rest = dropWhile (`elem` '_' : ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9']) str
      from "a" = MeVsThem
      from "b" = ThemVsMe
      from  n  = ThemVs $ Text.pack n

expandNames :: Name -> Name -> ModalFormula AgentVar -> ModalFormula Name
expandNames me them = mapVariable expandName where
  expandName MeVsThem = me `vs` them
  expandName ThemVsMe = them `vs` me
  expandName (ThemVs x) = them `vs` x

subagents :: ModalFormula AgentVar -> Set Name
subagents = Set.fromList . extractName . Set.toList . allVars where
  extractName xs = [name | ThemVs name <- xs]

isModalized :: ModalFormula v -> Bool
isModalized = modalEval ModalEvaluator {
  handleVar = const False, handleVal = const True, handleNeg = id,
  handleAnd = (&&), handleOr = (&&), handleImp = (&&), handleIff = (&&),
  handleBox = const True, handleDia = const True }

newtype Env = Env { _participants :: Map Name (ModalFormula AgentVar, Int) }
instance Show Env where
	show (Env ps) = printf "(%s)" (Text.unpack $ Text.intercalate ", " $ Map.keys ps)

nobody :: Env
nobody = Env Map.empty

participants :: Env -> Set Name
participants = Set.fromList . Map.keys . _participants

rankedParticipants :: Env -> Map Name Int
rankedParticipants = Map.map snd . _participants

missingSubagents :: Env -> ModalFormula AgentVar -> Set Name
missingSubagents env formula = subagents formula Set.\\ participants env

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

rankIn :: Env -> Name -> ModalFormula AgentVar -> Either EnvError Int
rankIn env name formula = if null missings then Right rank else Left err where
  err = MissingSubagents name (Set.fromList missings)
  rank = if null ranks then 0 else succ $ maximum ranks
  (missings, ranks) = partitionEithers $ Set.toList $ Set.map lookupRank $ subagents formula
  lookupRank n = maybe (Left n) (Right . snd) $ Map.lookup n (_participants env)

tryInsert :: Env -> Name -> ModalFormula AgentVar -> Either EnvError Env
tryInsert env name formula = do
  (unless $ isModalized formula) (Left $ IsNotModalized name)
  (when $ Map.member name $ _participants env) (Left $ NameCollision name)
  rank <- rankIn env name formula
  return $ Env $ Map.insert name (formula, rank) (_participants env)

insert :: Env -> Name -> ModalFormula AgentVar -> IO Env
insert = either die return .:: tryInsert

forceInsert :: Env -> Name -> ModalFormula AgentVar -> Env
forceInsert = either (error . show) id .:: tryInsert

(@+) :: Either EnvError Env -> (Name, ModalFormula AgentVar) -> Either EnvError Env
e @+ nf = e >>= (@< nf)

(@<) :: Env -> (Name, ModalFormula AgentVar) -> Either EnvError Env
(@<) e = uncurry (tryInsert e)

(@!) :: Env -> (Name, ModalFormula AgentVar) -> Env
(@!) e = uncurry (forceInsert e)

data CompetitionError = UnknownPlayer Name deriving (Eq, Ord, Read, Show)

type Competition = Map Name (ModalFormula Name)

tryCompetitionMap :: Env -> Name -> Name -> Either CompetitionError Competition
tryCompetitionMap env name1 name2 = do
  let emap = _participants env
  let getPlayer n = maybe (Left $ UnknownPlayer n) (Right . fst) (Map.lookup n emap)
  formula1 <- getPlayer name1
  formula2 <- getPlayer name2
  let top = [(name1 `vs` name2, expandNames name1 name2 formula1),
             (name2 `vs` name1, expandNames name2 name1 formula2)]
  lefts <- sequence [tryCompetitionMap env name2 x | x <- Set.toList $ subagents formula1]
  rights <- sequence [tryCompetitionMap env name1 x | x <- Set.toList $ subagents formula2]
  return $ Map.unions $ Map.fromList top : lefts ++ rights

competitionMap :: Env -> Name -> Name -> IO Competition
competitionMap = either die return .:: tryCompetitionMap

forceCompetitionMap :: Env -> Name -> Name -> Competition
forceCompetitionMap = either (error . show) id .:: tryCompetitionMap

tryCompete :: Env -> Name -> Name -> Either CompetitionError (Bool, Bool)
tryCompete env name1 name2 = do
  fixpt <- findGeneralGLFixpoint <$> tryCompetitionMap env name1 name2
  return (fixpt Map.! (name1 `vs` name2), fixpt Map.! (name2 `vs` name1))

compete :: Env -> Name -> Name -> IO (Bool, Bool)
compete = either die return .:: tryCompete
