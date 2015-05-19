{-# LANGUAGE OverloadedStrings #-}
module Modal.Competition where
import Control.Applicative
import Control.Arrow ((***))
import Data.Map (Map)
import Modal.Code
import Modal.Environment
import Modal.Formulas hiding (left)
import Modal.Utilities
import Text.Printf (printf)
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Text as Text

extractPMEEkey :: (k -> Bool) -> Map k Bool -> k
extractPMEEkey p = extract . Map.keys . Map.filterWithKey matchKey where
  matchKey k v = p k && v
  extract [ ] = error "No true formula! Map was not P.M.E.E."
  extract [x] = x
  extract  _  = error "Multiple true formulas! Map was not P.M.E.E."

--------------------------------------------------------------------------------
-- The type of variables that actually makes it into the full competition map.
-- This can be thought as the type of "canonicalized names" of various
-- statements, such as "FairBot(PrudentBot)=C."

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

class AgentVar v => Canonicalizable2 v where
  canonicalize2 ::
    (Name -> Name -> a -> x) ->
    (Name -> Name -> o -> x) ->
    Name -> Name -> ModalFormula (v a o) ->
    ModalFormula x

--------------------------------------------------------------------------------
-- Competitions, by default, allow agents with different action types to play
-- against each other. This introduces a bit of extra complexity to the types;
-- some helper functions (without 2s in their names) exist below to handle this
-- simpler case.

type Competition a o = Map (VsVar a o) (ModalFormula (VsVar a o))
data CompetitionError = UnknownPlayer Name deriving (Eq, Ord, Read)
instance Show CompetitionError where
  show (UnknownPlayer n) = printf "unknown player %s" (Text.unpack n)

-- Attempts to build a map of modal formulas describing the competition, given
-- two environments and two names.
competitionMap2 :: (Ord a, Ord o, Canonicalizable2 v1, Canonicalizable2 v2) =>
  Env v1 a o -> Env v2 o a -> Name -> Name ->
  Either CompetitionError (Competition a o)
competitionMap2 env1 env2 name1 name2 = do
  let getAgent name = maybe (Left $ UnknownPlayer name) Right . Map.lookup name . participants
  agent1 <- getAgent name1 env1
  agent2 <- getAgent name2 env2
  let agent1map = Map.toList agent1
  let agent2map = Map.toList agent2
  let top1 = map (Vs1 name1 name2 *** canonicalize2 Vs1 Vs2 name1 name2) agent1map
  let top2 = map (Vs2 name2 name1 *** canonicalize2 Vs2 Vs1 name2 name1) agent2map
  let recurse = competitionMap2 env1 env2
  lefts <- sequence [recurse x name2 | x <- Set.toList $ subagents agent1]
  rights <- sequence [recurse name1 x | x <- Set.toList $ subagents agent2]
  return $ Map.unions $ Map.fromList top1 : Map.fromList top2 : lefts ++ rights

-- Attempts to figure out how the two named agents behave against each other.
-- WARNING: This function may error if the modal formulas in the competition
-- map are not P.M.E.E. (provably mutally exclusive and extensional).
compete2 :: (Ord a, Ord o, Canonicalizable2 v1, Canonicalizable2 v2) =>
  Env v1 a o -> Env v2 o a -> Name -> Name ->
  Either CompetitionError (a, o)
compete2 env1 env2 name1 name2 = do
  fixpt <- findGeneralGLFixpoint <$> competitionMap2 env1 env2 name1 name2
  let Vs1 _ _ result1 = extractPMEEkey (is1 name1 name2) fixpt
  let Vs2 _ _ result2 = extractPMEEkey (is2 name2 name1) fixpt
  return (result1, result2)

--------------------------------------------------------------------------------
-- Simplified versions of the above functions for the scenario where both
-- agents have the same action type.

competitionMap :: (Ord a, Enum a, Canonicalizable2 v) =>
  Env v a a -> Name -> Name ->
  Either CompetitionError (Competition a a)
competitionMap env = competitionMap2 env env

compete :: (Ord a, Enum a, Canonicalizable2 v) =>
  Env v a a -> Name -> Name ->
  Either CompetitionError (a, a)
compete env = compete2 env env

--------------------------------------------------------------------------------
-- Competitions, by default, allow agents with different action types to play
-- against each other. This introduces a bit of extra complexity to the types;
-- some helper functions (without 2s in their names) exist below to handle this
-- simpler case.

data MultiVar u a
  = UniversePlays [Name] u
  | PlayerPlays [Name] Int a
  deriving (Eq, Ord)

instance (Show u, Show a) => Show (MultiVar u a) where
  show (UniversePlays ns x) = printf "%U[%s]=%s" names (show x) where
    names = List.intercalate "," $ map Text.unpack ns
  show (PlayerPlays ns i x) = printf "%[s]#%d=%s" names i (show x) where
    names = List.intercalate "," $ map Text.unpack ns

isEntryFor :: [Name] -> Int -> MultiVar u a -> Bool
isEntryFor ns 0 (UniversePlays xs _) = xs == ns
isEntryFor ns n (PlayerPlays xs x _) = x == n && xs == ns
isEntryFor _ _ _ = False

class AgentVar v => IsMultiVarA v where
  promoteA :: [Name] -> Int -> v a u -> MultiVar u a

class IsMultiVarU v where
  promoteU :: [Name] -> v u a -> MultiVar u a

type MultiCompetition u a = Map (MultiVar u a) (ModalFormula (MultiVar u a))

multiCompetition :: (Ord a, Ord u, IsMultiVarA av, IsMultiVarU uv) =>
  (Name, Env uv u a) ->
  [(Name, Env av a u)] ->
  Either CompetitionError (MultiCompetition u a)
multiCompetition (uName, uEnv) pnes = combineMaps <$> uMap <*> pMaps where
  getAgent name = maybe (Left $ UnknownPlayer name) Right . Map.lookup name . participants
  uMap = Map.fromList . map createEntry . Map.toList <$> getAgent uName uEnv where
    createEntry = UniversePlays names *** fmap (promoteU names)
  pMaps = do
    numberedAgents <- zip [1..] <$> mapM (uncurry getAgent) pnes
    let createEntry n = PlayerPlays names n *** fmap (promoteA names n)
    let createTopMap n = Map.fromList . map (createEntry n) . Map.toList
    let createSubMap n = mapM (recurse . switch n) . Set.toList . subagents
    let tops = map (uncurry createTopMap) numberedAgents
    subs <- mapM (uncurry createSubMap) numberedAgents
    return $ tops ++ concat subs
  switch i o = alter pnes i (\(_, e) -> (o, e))
  recurse = multiCompetition (uName, uEnv)
  combineMaps xs ys = Map.unions (xs : ys)
  names = uName : map fst pnes

multiCompete :: (Ord a, Ord u, IsMultiVarA av, IsMultiVarU uv) =>
  (Name, Env uv u a) ->
  [(Name, Env av a u)] ->
  Either CompetitionError (u, [a])
multiCompete une pnes = do
  fixpt <- findGeneralGLFixpoint <$> multiCompetition une pnes
  let names = fst une : map fst pnes
  let UniversePlays _ u = extractPMEEkey (isEntryFor names 0) fixpt
  return (u, [let PlayerPlays _ _ x = extractPMEEkey (isEntryFor names n) fixpt
              in x | n <- [1 .. length pnes]])
