{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Modal.Competition where
import Control.Applicative
import Control.Arrow ((***))
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Modal.Statement
import Modal.Environment
import Modal.Formulas hiding (left)
import Modal.Utilities
import Text.Printf (printf)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

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
  show (Vs1 n1 n2 a) = printf "%s(%s)=%s" n1 n2 (show a)
  show (Vs2 n1 n2 o) = printf "%s(%s)=%s" n1 n2 (show o)

is1 :: Name -> Name -> VsVar a o -> Bool
is1 n m (Vs1 x y _) = x == n && y == m
is1 _ _ _ = False

is2 :: Name -> Name -> VsVar a o -> Bool
is2 n m (Vs2 x y _) = x == n && y == m
is2 _ _ _ = False

class AgentVar v => Canonicalizable2 v where
  canonicalize2 ::
    (a -> x) -> (Maybe Name -> o -> x) -> ModalFormula (v a o) -> ModalFormula x

--------------------------------------------------------------------------------
-- Competitions, by default, allow agents with different action types to play
-- against each other. This introduces a bit of extra complexity to the types;
-- some helper functions (without 2s in their names) exist below to handle this
-- simpler case.

type Competition a o = Map (VsVar a o) (ModalFormula (VsVar a o))

-- Attempts to build a map of modal formulas describing the competition, given
-- two environments and two names.
competitionMap2 :: (Ord x, Ord y, Canonicalizable2 v1, Canonicalizable2 v2) =>
  Env v1 x y -> Env v2 y x -> Name -> Name -> Either EnvError (Competition x y)
competitionMap2 env1 env2 name1 name2 = do
  let unknown = Left . UnknownPlayer
  let getAgent name = maybe (unknown name) Right . Map.lookup name . participants
  agent1 <- getAgent name1 env1
  agent2 <- getAgent name2 env2
  let agent1map = Map.toList agent1
  let agent2map = Map.toList agent2
  let expand1 = canonicalize2 (Vs1 name1 name2) (Vs2 name2 . fromMaybe name1)
  let expand2 = canonicalize2 (Vs2 name2 name1) (Vs1 name1 . fromMaybe name2)
  let top1 = map (Vs1 name1 name2 *** expand1) agent1map
  let top2 = map (Vs2 name2 name1 *** expand2) agent2map
  let recurse = competitionMap2 env1 env2
  lefts <- sequence [recurse x name2 | x <- Set.toList $ subagents agent1]
  rights <- sequence [recurse name1 x | x <- Set.toList $ subagents agent2]
  return $ Map.unions $ Map.fromList top1 : Map.fromList top2 : lefts ++ rights

-- TODO: Add error handling
resolve2 :: (Show x, Show y, Ord x, Ord y) => Name -> Name -> Competition x y -> (x, y)
resolve2 name1 name2 cmap = (result1, result2) where
  fixpt = findGeneralGLFixpoint cmap
  Vs1 _ _ result1 = extractPMEEkey (is1 name1 name2) fixpt
  Vs2 _ _ result2 = extractPMEEkey (is2 name2 name1) fixpt

-- Attempts to figure out how the two named agents behave against each other.
-- WARNING: This function may error if the modal formulas in the competition
-- map are not P.M.E.E. (provably mutally exclusive and extensional).
compete2 :: (Show x, Show y, Ord x, Ord y, Canonicalizable2 v1, Canonicalizable2 v2) =>
  Env v1 x y -> Env v2 y x -> Name -> Name -> Either EnvError (x, y)
compete2 env1 env2 name1 name2 = resolve2 name1 name2
  <$> competitionMap2 env1 env2 name1 name2

--------------------------------------------------------------------------------
-- Simplified versions of the above functions for the scenario where both
-- agents have the same action type.

competitionMap :: (Ord a, Canonicalizable2 v) =>
  Env v a a -> Name -> Name -> Either EnvError (Competition a a)
competitionMap env = competitionMap2 env env

compete :: (Show a, Ord a, Canonicalizable2 v) =>
  Env v a a -> Name -> Name -> Either EnvError (a, a)
compete env = compete2 env env

--------------------------------------------------------------------------------
-- Competitions, by default, allow agents with different action types to play
-- against each other. This introduces a bit of extra complexity to the types;
-- some helper functions (without 2s in their names) exist below to handle this
-- simpler case.

data MultiVsVar u a
  = UniversePlays [Name] u
  | PlayerNPlays [Name] Int a
  deriving (Eq, Ord)

instance (Show u, Show a) => Show (MultiVsVar u a) where
  show (UniversePlays ns x) = printf "%s(%s)=%s"
    (head ns) (List.intercalate "," $ tail ns) (show x)
  show (PlayerNPlays ns i x) = printf "%s(%s)=%s" (ns !! i) (head ns) (show x)

isEntryFor :: [Name] -> Int -> MultiVsVar u a -> Bool
isEntryFor ns 0 (UniversePlays xs _) = xs == ns
isEntryFor ns n (PlayerNPlays xs x _) = x == n && xs == ns
isEntryFor _ _ _ = False

class AgentVar v => IsMultiVarA v where
  promoteA :: [Name] -> Int -> v a u -> MultiVsVar u a

class AgentVar v => IsMultiVarU v where
  promoteU :: [Name] -> v u a -> MultiVsVar u a

type MultiCompetition u a = Map (MultiVsVar u a) (ModalFormula (MultiVsVar u a))

-- TODO: This uses NameCollision in a terrible hackish way.
-- You're going to need to refactor the error handling at some point.
multiCompetition :: (Ord u, Ord a, IsMultiVarU vu, IsMultiVarA va) =>
  (Name, Env vu u a) -> [(Name, Env va a u)] ->
  Either EnvError (MultiCompetition u a)
multiCompetition (uName, uEnv) pnes
  | length (List.nub names) < length names = Left $ NameCollision (List.intercalate "," names)
  | otherwise = combineMaps <$> uMap <*> pMaps
  where
    getAgent name = maybe (Left $ UnknownPlayer name) Right . Map.lookup name . participants
    uMap = Map.fromList . map createEntry . Map.toList <$> getAgent uName uEnv where
      createEntry = UniversePlays names *** fmap (promoteU names)
    pMaps = do
      numberedAgents <- zip [1..] <$> mapM (uncurry getAgent) pnes
      let createEntry n = PlayerNPlays names n *** fmap (promoteA names n)
      let createTopMap n = Map.fromList . map (createEntry n) . Map.toList
      let createSubMap n = mapM (recurse . switch n) . Set.toList . subagents
      let tops = map (uncurry createTopMap) numberedAgents
      subs <- mapM (uncurry createSubMap) numberedAgents
      return $ tops ++ concat subs
    switch i o = alter pnes i (\(_, e) -> (o, e))
    recurse = multiCompetition (uName, uEnv)
    combineMaps xs ys = Map.unions (xs : ys)
    names = uName : map fst pnes

multiResolve :: (Show a, Show u, Ord a, Ord u) => [Name] -> MultiCompetition u a -> (u, [a])
multiResolve names cmap = (u, as) where
  fixpt = findGeneralGLFixpoint cmap
  UniversePlays _ u = extractPMEEkey (isEntryFor names 0) fixpt
  as = [let PlayerNPlays _ _ a = extractPMEEkey (isEntryFor names n) fixpt in a
       | n <- [1 .. length names]]

multiCompete :: (Show a, Show u, Ord a, Ord u, IsMultiVarU vu, IsMultiVarA va) =>
  (Name, Env vu u a) -> [(Name, Env va a u)] -> Either EnvError (u, [a])
multiCompete une pnes = do
  cmap <- multiCompetition une pnes
  return $ multiResolve (fst une : map fst pnes) cmap

-- TODO: Make this be able to return an EnvError, and then throw an EnvError
-- instead of crashing the program if names are ambiguous.
simpleMultiCompetition :: (Ord u, Ord a, IsMultiVarU vu , IsMultiVarA va) =>
  (Name, Map u (ModalFormula (vu u a))) ->
  [(Name, Map a (ModalFormula (va a u)))] ->
  MultiCompetition u a
simpleMultiCompetition (uName, uAgent) aPairs
  | length (List.nub names) < length names = error "Ambiguous names."
  | otherwise = combineMaps uMap pMaps where
    uMap = Map.fromList $ map createEntry $ Map.toList uAgent where
      createEntry = UniversePlays names *** fmap (promoteU names)
    pMaps = map (uncurry createMap) numberedAgents where
      numberedAgents = zip [1..] (map snd aPairs)
      createEntry n = PlayerNPlays names n *** fmap (promoteA names n)
      createMap n = Map.fromList . map (createEntry n) . Map.toList
    combineMaps xs ys = Map.unions (xs : ys)
    names = uName : map fst aPairs

simpleMultiCompete :: (Show u, Show a, Ord u, Ord a, IsMultiVarU vu , IsMultiVarA va) =>
  (Name, Map u (ModalFormula (vu u a))) ->
  [(Name, Map a (ModalFormula (va a u)))] ->
  (u, [a])
simpleMultiCompete (uName, uAgent) aPairs = (u, as) where
  fixpt = findGeneralGLFixpoint $ simpleMultiCompetition (uName, uAgent) aPairs
  names = uName : map fst aPairs
  UniversePlays _ u = extractPMEEkey (isEntryFor names 0) fixpt
  as = [let PlayerNPlays _ _ x = extractPMEEkey (isEntryFor names n) fixpt
        in x | n <- [1 .. length aPairs]]
