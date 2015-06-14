{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Modal.Competition where
import Prelude hiding (mapM, sequence)
import Control.Applicative
import Control.Arrow ((***))
import Control.Monad.Except hiding (mapM, sequence)
import Data.Traversable (mapM, sequence, traverse)
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

class AgentVar v => ModalCombatVar v where
  makeModalVar ::
    (a -> x) -> (Maybe Name -> o -> x) -> ModalFormula (v a o) -> ModalFormula x

--------------------------------------------------------------------------------
-- Competitions, by default, allow agents with different action types to play
-- against each other. This introduces a bit of extra complexity to the types;
-- some helper functions (without 2s in their names) exist below to handle this
-- simpler case.

type Competition a o = Map (VsVar a o) (ModalFormula (VsVar a o))
type IsCompetition v1 v2 x y = (Ord x, Ord y, ModalCombatVar v1, ModalCombatVar v2)

-- Attempts to build a map of modal formulas describing the competition, given
-- two environments and two names.
modalCombatMap :: (IsCompetition v1 v2 x y, EnvErrorM m) =>
  Env v1 x y -> Env v2 y x -> Name -> Name -> m (Competition x y)
modalCombatMap env1 env2 name1 name2 = do
  agent1 <- getAgent name1 env1
  agent2 <- getAgent name2 env2
  let agent1map = Map.toList agent1
  let agent2map = Map.toList agent2
  let expand1 = makeModalVar (Vs1 name1 name2) (Vs2 name2 . fromMaybe name1)
  let expand2 = makeModalVar (Vs2 name2 name1) (Vs1 name1 . fromMaybe name2)
  let top1 = map (Vs1 name1 name2 *** expand1) agent1map
  let top2 = map (Vs2 name2 name1 *** expand2) agent2map
  let recurse = modalCombatMap env1 env2
  lefts <- sequence [recurse x name2 | x <- Set.toList $ subagents agent1]
  rights <- sequence [recurse name1 x | x <- Set.toList $ subagents agent2]
  return $ Map.unions $ Map.fromList top1 : Map.fromList top2 : lefts ++ rights
  where
    unknownErr :: EnvErrorM m => Name -> m x
    unknownErr = throwError . UnknownPlayer
    getAgent :: EnvErrorM m => Name -> Env v a o -> m (AgentMap v a o)
    getAgent name = maybe (unknownErr name) return . Map.lookup name . participants

-- TODO: Add error handling.
-- (Right now, the fixpoint evaluator just errors when bad things happen.)
modalCombatResolve :: (Show x, Show y, Ord x, Ord y) =>
  Name -> Name -> Competition x y -> (x, y)
modalCombatResolve name1 name2 cmap = (result1, result2) where
  fixpt = findGeneralGLFixpoint cmap
  Vs1 _ _ result1 = extractPMEEkey (is1 name1 name2) fixpt
  Vs2 _ _ result2 = extractPMEEkey (is2 name2 name1) fixpt

-- Attempts to figure out how the two named agents behave against each other.
-- WARNING: This function may error if the modal formulas in the competition
-- map are not P.M.E.E. (provably mutally exclusive and extensional).
modalCombat :: (Show x, Show y, IsCompetition v1 v2 x y, EnvErrorM m) =>
  Env v1 x y -> Env v2 y x -> Name -> Name -> m (x, y)
modalCombat env1 env2 name1 name2 =
  modalCombatResolve name1 name2 <$> modalCombatMap env1 env2 name1 name2

--------------------------------------------------------------------------------
-- Simplified versions of the above functions for the scenario where both
-- agents have the same action type.

modalCombatMap1 :: (Ord a, ModalCombatVar v) =>
  Env v a a -> Name -> Name -> Either EnvError (Competition a a)
modalCombatMap1 env = modalCombatMap env env

modalCombat1 :: (Show a, Ord a, ModalCombatVar v) =>
  Env v a a -> Name -> Name -> Either EnvError (a, a)
modalCombat1 env = modalCombat env env

--------------------------------------------------------------------------------
-- Competitions, by default, allow agents with different action types to play
-- against each other. This introduces a bit of extra complexity to the types;
-- some helper functions (without 2s in their names) exist below to handle this
-- simpler case.

type IsMultiCompetition vu va u a = (Ord u, Ord a, IsMultiVarU vu, IsMultiVarA va)
type MultiCompetition u a = Map (MultiVsVar u a) (ModalFormula (MultiVsVar u a))

class AgentVar v => IsMultiVarA v where
  promoteA :: Int -> v a u -> MultiVsVar u a

class AgentVar v => IsMultiVarU v where
  promoteU :: v u a -> MultiVsVar u a

data MultiVsVar u a = UniversePlays u | PlayerNPlays Int a deriving (Eq, Ord)

instance (Show u, Show a) => Show (MultiVsVar u a) where
  show (UniversePlays x) = printf "U()=%s" (show x)
  show (PlayerNPlays i x) = printf "A%d()=%s" i (show x)

isEntryFor :: Int -> MultiVsVar u a -> Bool
isEntryFor 0 (UniversePlays _) = True
isEntryFor n (PlayerNPlays i _) = n == i

multiCompetition :: IsMultiCompetition vu va u a =>
  Map u (ModalFormula (vu u a)) ->
  [Map a (ModalFormula (va a u))] ->
  MultiCompetition u a
multiCompetition univ agents = Map.unions (uMap : pMaps) where
  uMap = Map.fromList $ map (uncurry createUEntry) $ Map.toList univ
  createUEntry outcome uFormula = (UniversePlays outcome, promoteU <$> uFormula)
  pMaps = map (uncurry createMap) (zip [1..] agents) where
    createEntry n = PlayerNPlays n *** fmap (promoteA n)
    createMap n = Map.fromList . map (createEntry n) . Map.toList

multiResolve :: (Show a, Show u, Ord a, Ord u) =>
  Int -> MultiCompetition u a -> (u, [a])
multiResolve n cmap = (u, as) where
  fixpt = findGeneralGLFixpoint cmap
  UniversePlays u = extractPMEEkey (isEntryFor 0) fixpt
  as = [let PlayerNPlays _ a = extractPMEEkey (isEntryFor n) fixpt in a
       | n <- [1 .. n]]

multiCompete :: (Show a, Show u, IsMultiCompetition vu va u a) =>
  Map u (ModalFormula (vu u a)) ->
  [Map a (ModalFormula (va a u))] ->
  (u, [a])
multiCompete univ agents =
  multiResolve (length agents) (multiCompetition univ agents)
