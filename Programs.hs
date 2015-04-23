module Programs where
import Modal
import Data.Map hiding (map)
import qualified Data.Map as Map

-- The enum list associated with an enum type.
-- Assumes toEnum 0 is the least element in the enum.
enumerate :: Enum a => [a]
enumerate = enumFrom (toEnum 0)

-- Intuitively, a modal program is a series of modal formulas, one for each
-- action, saying whether or not the program executes that action.
type ModalProgram v a = a -> ModalFormula v

-- Turns a modal program into the associated list of modal formulas.
progToList :: Enum a => ModalProgram v a -> [ModalFormula v]
progToList f = map f enumerate

progToMap :: (Ord a, Enum a) => ModalProgram v a -> Map a (ModalFormula v)
progToMap f = fromList [(a, f a) | a <- enumerate]

-- Used to construct partial programs, which essentially do some but not all of
-- the program. (You must tell them "what to do next" in order to generate the
-- completed ModalProgram.)
data ProgFrag v a = ProgFrag (ModalProgram v a -> ModalProgram v a)

-- Given a default action and a program fragment, completes the program
-- fragment with "return the default"
modalProgram :: Eq a => a -> ProgFrag v a -> ModalProgram v a
modalProgram dflt (ProgFrag f) = f $ \a -> Val (a == dflt)

-- Program fragment that ignores "what to do next" and returns a.
mReturn :: Eq a => a -> ProgFrag v a
mReturn a = ProgFrag $ const $ \a' -> Val (a == a')

mPass :: ProgFrag v a
mPass = ProgFrag id

mIf' :: ModalFormula v -> ProgFrag v a -> ProgFrag v a -> ProgFrag v a
mIf' cond (ProgFrag t) (ProgFrag e) = ProgFrag $ \prog a ->
  And (Imp cond       (t prog a))
      (Imp (Neg cond) (e prog a))

mIf :: ModalFormula v -> ProgFrag v a -> ProgFrag v a
mIf cond t = mIf' cond t mPass

-- Composition of program fragments.
(>->) :: ProgFrag v a -> ProgFrag v a -> ProgFrag v a
ProgFrag f >-> ProgFrag g = ProgFrag (f . g)

mFor' :: [c] -> (c -> ProgFrag v a) -> ProgFrag v a
mFor' []     _ = mPass
mFor' (c:cs) f = f c >-> mFor' cs f

mFor :: Enum c => (c -> ProgFrag v a) -> ProgFrag v a
mFor = mFor' enumerate

-- A map from actions to whether or not the agent takes that action.
programBehavior :: (Ord a, Enum a) => ModalProgram a a -> Map a Bool
programBehavior = findGeneralGLFixpoint . progToMap

-- A map of actions for which the action equation is true.
-- (Only one of these should be the case, if the program is p.m.e.e.)
trueEquations :: (Ord a, Enum a) => ModalProgram a a -> Map a (ModalFormula a)
trueEquations prog = filterWithKey (\k _ -> programBehavior prog ! k) (progToMap prog)

-- The action/formula pair for the equation that is true.
-- (Errors if the program is not p.m.e.e.)
trueEquation :: (Ord a, Enum a) => ModalProgram a a -> (a, ModalFormula a)
trueEquation prog = case toList $ trueEquations prog of
  [ ] -> error "No action taken! Program was not p.m.e.e."
  [x] -> x
  _   -> error "Multiple actions taken! Program was not p.m.e.e."

-- The modal formula which is true for this program.
trueFormula :: (Ord a, Enum a) => ModalProgram a a -> ModalFormula a
trueFormula = snd . trueEquation

-- The action that this program takes.
evalProgram :: (Ord a, Enum a) => ModalProgram a a -> a
evalProgram = fst . trueEquation

-- Takes a question about the true formula (as a function from formulas to
-- formulas) and answers it (by evaluating it given how all the action formulas
-- are actually valued).
query :: (Ord a, Enum a) => ModalProgram a a -> (ModalFormula a -> ModalFormula a) -> Bool
query prog q = evalWithSoundnessAndAnswers answers (q f) where
  answers = programBehavior prog
  f = trueFormula prog

-- Lets you ask a number of additional questions about the true formula.
-- You give a map from a qurey type onto a way to transform the true formula
-- into a query formula, and this gives you back the map with answers to all
-- queries (along with the full program map, for convenience.)
query' :: (Ord a, Ord q, Enum a) =>
  ModalProgram a a -> Map q (ModalFormula a -> ModalFormula a) -> Map (Either q a) Bool
query' prog queries = findGeneralGLFixpoint $ union qmap pmap where
  f = trueFormula prog
  qmap = mapKeysMonotonic Left $ Map.map (mapVariable Right . ($ f)) queries
  pmap = mapKeysMonotonic Right $ Map.map (mapVariable Right) $ progToMap prog

-- Gives you a boolean answer to a single query about the true formula.
-- Example:
-- let q = (\f -> boxk 100 f)
-- query (escalatingUDT 0 (strangeverse 100) Beta) q
query :: (Ord a, Enum a) => ModalProgram a a -> (ModalFormula a -> ModalFormula a) -> Bool
query prog f = query' prog (insert () f empty) ! Left () where

udt :: (Enum u, Ord a, Enum a) => Int -> ModalProgram a u -> a -> ModalProgram a a
udt level univ dflt = modalProgram dflt $
  mFor $ \u ->
    mFor $ \a ->
      mIf (boxk level (Var a %> univ u)) (mReturn a)

escalatingUDT :: (Enum u, Ord a, Enum a) => Int -> ModalProgram a u -> a -> ModalProgram a a
escalatingUDT level univ dflt = modalProgram dflt mainLoop where
  mainLoop = mFor' (zip outcomeActionPairs [0..]) checkOutcomeAction
  outcomeActionPairs = [(u, a) | u <- enumerate, a <- enumerate]
  checkOutcomeAction ((u, a), n) =
    mIf (boxk (level + n) (Var a %> univ u)) (mReturn a)
