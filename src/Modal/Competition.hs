{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module Modal.Competition where
import Prelude hiding (mapM, sequence)
import Control.Arrow ((***))
import Control.Monad.Except hiding (mapM, sequence)
import Data.Traversable (sequence)
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Modal.CompilerBase
import Modal.Formulas hiding (left)
import Text.Printf (printf)
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
  = Vs1 Call Call a
  | Vs2 Call Call o
  deriving (Eq, Ord)

instance (Show a, Show o) => Show (VsVar a o) where
  show (Vs1 call1 call2 a) = printf "%s(%s)=%s" (show call1) (show call2) (show a)
  show (Vs2 call1 call2 o) = printf "%s(%s)=%s" (show call1) (show call2) (show o)

is1 :: Call -> Call -> VsVar a o -> Bool
is1 n m (Vs1 x y _) = x == n && y == m
is1 _ _ _ = False

is2 :: Call -> Call -> VsVar a o -> Bool
is2 n m (Vs2 x y _) = x == n && y == m
is2 _ _ _ = False

class ModalCombatVar v where
  subagentsIn :: v a o -> Set Call
  makeModalVar :: (a-> x) -> (Maybe Call -> o-> x) -> v a o -> x

subagents :: ModalCombatVar v => ModalAgent v a o  -> Set Call
subagents = Set.unions . map fSubagents . Map.elems where
  fSubagents = Set.unions . map subagentsIn . allVars

--------------------------------------------------------------------------------
-- Competitions, by default, allow agents with different action types to play
-- against each other. This introduces a bit of extra complexity to the types;
-- some helper functions (without 2s in their names) exist below to handle this
-- simpler case.

type ModalAgent v a o = Map a (ModalFormula (v a o))
type Env m v a o = Call -> m (ModalAgent v a o)
type Competition a o = Map (VsVar a o) (ModalFormula (VsVar a o))
type IsCompetition v1 v2 a o =
  ( Ord a, Ord o, ModalCombatVar v1, ModalCombatVar v2 )

-- Attempts to build a map of modal formulas describing the competition, given
-- two environments and two names.
modalCombatMap :: (IsCompetition v1 v2 a o, MonadError RuntimeError m) =>
  Env m v1 a o -> Env m v2 o a -> Call -> Call -> m (Competition a o)
modalCombatMap env1 env2 call1 call2 = do
  agent1 <- env1 call1
  agent2 <- env2 call2
  let agent1map = Map.toList agent1
  let agent2map = Map.toList agent2
  let expand1 = fmap $ makeModalVar (Vs1 call1 call2) (Vs2 call2 . fromMaybe call1)
  let expand2 = fmap $ makeModalVar (Vs2 call2 call1) (Vs1 call1 . fromMaybe call2)
  let top1 = map (Vs1 call1 call2 *** expand1) agent1map
  let top2 = map (Vs2 call2 call1 *** expand2) agent2map
  let recurse = modalCombatMap env1 env2
  lefts <- sequence [recurse x call2 | x <- Set.toList $ subagents agent1]
  rights <- sequence [recurse call1 x | x <- Set.toList $ subagents agent2]
  return $ Map.unions $ Map.fromList top1 : Map.fromList top2 : lefts ++ rights

-- TODO: Add error handling.
-- (Right now, the fixpoint evaluator just errors when bad things happen.)
modalCombatResolve :: (Show x, Show y, Ord x, Ord y) =>
  Call -> Call -> Competition x y -> (x, y)
modalCombatResolve call1 call2 cmap = (result1, result2) where
  fixpt = findGeneralGLFixpoint cmap
  Vs1 _ _ result1 = extractPMEEkey (is1 call1 call2) fixpt
  Vs2 _ _ result2 = extractPMEEkey (is2 call2 call1) fixpt

-- Attempts to figure out how the two named agents behave against each other.
-- WARNING: This function may error if the modal formulas in the competition
-- map are not P.M.E.E. (provably mutally exclusive and extensional).
modalCombat :: (Show x, Show y, IsCompetition v1 v2 x y, MonadError RuntimeError m) =>
  Env m v1 x y -> Env m v2 y x -> Call -> Call -> m (x, y)
modalCombat env1 env2 call1 call2 =
  modalCombatResolve call1 call2 <$> modalCombatMap env1 env2 call1 call2

--------------------------------------------------------------------------------
-- Simplified versions of the above functions for the scenario where both
-- agents have the same action type.

modalCombatMap1 :: (Ord a, ModalCombatVar v, MonadError RuntimeError m) =>
  Env m v a a -> Call -> Call -> m (Competition a a)
modalCombatMap1 env = modalCombatMap env env

modalCombat1 :: (Show a, Ord a, ModalCombatVar v, MonadError RuntimeError m) =>
  Env m v a a -> Call -> Call -> m (a, a)
modalCombat1 env = modalCombat env env

--------------------------------------------------------------------------------
-- Competitions, by default, allow agents with different action types to play
-- against each other. This introduces a bit of extra complexity to the types;
-- some helper functions (without 2s in their names) exist below to handle this
-- simpler case.

type IsMultiCompetition vu va u a = (Ord u, Ord a, MultiVarU vu, MultiVarA va)
type MultiCompetition u a = Map (MultiVsVar u a) (ModalFormula (MultiVsVar u a))

class MultiVarA v where
  promoteA :: Int -> v a u -> MultiVsVar u a

class MultiVarU v where
  promoteU :: v u a -> MultiVsVar u a

data MultiVsVar u a = UniversePlays u | PlayerNPlays Int a deriving (Eq, Ord)

instance (Show u, Show a) => Show (MultiVsVar u a) where
  show (UniversePlays x) = printf "U()=%s" (show x)
  show (PlayerNPlays i x) = printf "A%d()=%s" i (show x)

isEntryFor :: Int -> MultiVsVar u a -> Bool
isEntryFor 0 (UniversePlays _) = True
isEntryFor _ (UniversePlays _) = False
isEntryFor n (PlayerNPlays i _) = n == i

multiCompetition :: IsMultiCompetition vu va u a =>
  Map u (ModalFormula (vu u a)) ->
  [Map a (ModalFormula (va a u))] ->
  MultiCompetition u a
multiCompetition univ agents = Map.unions (uMap : pMaps) where
  uMap = Map.fromList $ map (uncurry createUEntry) $ Map.toList univ
  createUEntry outcome uFormula = (UniversePlays outcome, promoteU <$> uFormula)
  pMaps = zipWith createMap [1..] agents where
    createEntry n = PlayerNPlays n *** fmap (promoteA n)
    createMap n = Map.fromList . map (createEntry n) . Map.toList

-- TODO: Add error handling.
-- (Right now, the fixpoint evaluator just errors when bad things happen.)
multiResolve :: (Show a, Show u, Ord a, Ord u) =>
  Int -> MultiCompetition u a -> (u, [a])
multiResolve n cmap = (u, as) where
  fixpt = findGeneralGLFixpoint cmap
  UniversePlays u = extractPMEEkey (isEntryFor 0) fixpt
  as = [let PlayerNPlays _ a = extractPMEEkey (isEntryFor i) fixpt
        in a | i <- [1 .. n]]

multiCompete :: (Show a, Show u, IsMultiCompetition vu va u a) =>
  Map u (ModalFormula (vu u a)) ->
  [Map a (ModalFormula (va a u))] ->
  (u, [a])
multiCompete univ agents =
  multiResolve (length agents) (multiCompetition univ agents)
