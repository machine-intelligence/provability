{-# LANGUAGE OverloadedStrings #-}
module Modal.Competition where
import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Modal.Code
import Modal.Formulas hiding (left)
import Modal.Programming
import Modal.Environment
import Modal.Utilities
import Text.Printf (printf)

extractPMEEkey :: (k -> Bool) -> Map k Bool -> k
extractPMEEkey p = extract . Map.keys . Map.filterWithKey matchKey where
  matchKey k v = p k && v
  extract [ ] = error "No true formula! Map was not P.M.E.E."
  extract [x] = x
  extract  _  = error "Multiple true formulas! Map was not P.M.E.E."

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
expandNames v1 v2 me them = fmap expandName where
  expandName (MeVsThemIs val) = v1 me them val
  expandName (ThemVsMeIs val) = v2 them me val
  expandName (ThemVsOtherIs other val) = v2 them other val

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
competitionMap2 :: (Ord a, Ord o) =>
  Env a o -> Env o a -> Name -> Name ->
  Either CompetitionError (Competition a o)
competitionMap2 env1 env2 name1 name2 = do
  let emap1 = participants env1
  let emap2 = participants env2
  program1 <- maybe (Left $ UnknownPlayer name1) Right (Map.lookup name1 emap1)
  program2 <- maybe (Left $ UnknownPlayer name2) Right (Map.lookup name2 emap2)
  let top1 = [(Vs1 name1 name2 a, expandNames Vs1 Vs2 name1 name2 (formulaFor program1 a))
                      | a <- actions env1]
  let top2 = [(Vs2 name2 name1 o, expandNames Vs2 Vs1 name2 name1 (formulaFor program2 o))
                      | o <- actions env2]
  lefts <- sequence [competitionMap2 env1 env2 x name2
                      | x <- Set.toList $ subagents (actions env1) program1]
  rights <- sequence [competitionMap2 env1 env2 name1 x
                      | x <- Set.toList $ subagents (actions env2) program2]
  return $ Map.unions $ Map.fromList top1 : Map.fromList top2 : lefts ++ rights

-- Attempts to figure out how the two named agents behave against each other.
-- WARNING: This function may error if the modal formulas in the competition
-- map are not P.M.E.E. (provably mutally exclusive and extensional).
compete2 :: (Ord a, Ord o) =>
  Env a o -> Env o a -> Name -> Name -> Either CompetitionError (a, o)
compete2 env1 env2 name1 name2 = do
  fixpt <- findGeneralGLFixpoint <$> competitionMap2 env1 env2 name1 name2
  let Vs1 _ _ result1 = extractPMEEkey (is1 name1 name2) fixpt
  let Vs2 _ _ result2 = extractPMEEkey (is2 name2 name1) fixpt
  return (result1, result2)

--------------------------------------------------------------------------------
-- Simplified versions of the above functions for the scenario where both
-- agents have the same action type.

competitionMap :: (Ord a, Enum a) =>
  Env a a -> Name -> Name -> Either CompetitionError (Competition a a)
competitionMap env = competitionMap2 env env

compete :: (Ord a, Enum a) => Env a a -> Name -> Name -> Either CompetitionError (a, a)
compete env = compete2 env env


--------------------------------------------------------------------------------
-- Competitions, by default, allow agents with different action types to play
-- against each other. This introduces a bit of extra complexity to the types;
-- some helper functions (without 2s in their names) exist below to handle this
-- simpler case.

type MultiCompetition = Map MultiVar (ModalFormula MultiVar)
data MultiVar = Universe Name | Player Int Name deriving (Eq, Ord, Read)
instance Show MultiVar where
  show (Universe n) = Text.unpack n
  show (Player i n) = case i of
    1 -> Text.unpack n ++ "₁"
    2 -> Text.unpack n ++ "₂"
    3 -> Text.unpack n ++ "₃"
    _ -> printf "%s_%d" (Text.unpack n) i

isUniverse :: MultiVar -> Bool
isUniverse (Universe _) = True
isUniverse _ = False

isPlayer :: Int -> MultiVar -> Bool
isPlayer n (Player x _) = x == n
isPlayer _ _ = False

multiCompetition :: ([Name], ModalProgram Name (Int, Name)) -> [([Name], ModalProgram Name Name)] -> MultiCompetition
multiCompetition (uActs, uProg) = Map.fromList . (us ++) . concatMap promote . zip [1..] where
  us = [(Universe u, uncurry Player <$> formulaFor uProg u) | u <- uActs]
  promote (n, (pActs, pProg)) = [(Player n a, Universe <$> formulaFor pProg a) | a <- pActs]

competeN :: ([Name], ModalProgram Name (Int, Name)) -> [([Name], ModalProgram Name Name)] -> [Name]
competeN us ps = uresult : presults where
  fixpt = findGeneralGLFixpoint $ multiCompetition us ps
  Universe uresult = extractPMEEkey isUniverse fixpt
  presults = [let Player _ presult = extractPMEEkey (isPlayer n) fixpt in presult | n <- [1 .. length ps]]

