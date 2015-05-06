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
  Or (cond %^ t prog a) (Neg cond %^ e prog a)
--  And (Imp cond       (t prog a))
--      (Imp (Neg cond) (e prog a))

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

gameMap :: (Ord a, Enum a, Ord u, Enum u) =>
  ModalProgram (UA u a) a ->
  ModalProgram a u ->
  Map (UA u a) (ModalFormula (UA u a))
gameMap agent univ = Map.fromList $ acts ++ outs where
  acts = [(A a, agent a) | a <- enumerate]
  outs = [(U u, mapVariable A $ univ u) | u <- enumerate]

playGame :: (Ord a, Enum a, Ord u, Enum u) =>
  ModalProgram (UA u a) a ->
  ModalProgram a u ->
  (a, u)
playGame agent univ = (action, outcome) where
  behavior = findGeneralGLFixpoint $ gameMap agent univ
  U outcome = fst $ extractPair $ filterWithKey (\k v -> isU k && v) behavior
  A action = fst $ extractPair $ filterWithKey (\k v -> isA k && v) behavior
  extractPair m = case Map.toList m of
    [ ] -> error "No action taken! Program was not p.m.e.e."
    [x] -> x
    _   -> error "Multiple actions taken! Program was not p.m.e.e."

queryMap :: (Ord a, Enum a, Ord u, Enum u) =>
  String -> ModalFormula (UA u a) ->
  ModalProgram (UA u a) a -> ModalProgram a u ->
  Map (UA u a) (ModalFormula (UA u a))
queryMap name query agent univ = Map.insert (Query name) query $ gameMap agent univ

data UA u a = U u | A a | Query String deriving (Eq, Ord, Read)
instance (Show a, Show u) => Show (UA u a) where
  show (U u) = show u
  show (A a) = show a
  show (Query q) = q ++ "?"
instance Functor (UA u) where
  fmap f (A a) = A (f a)
  fmap _ (U u) = U u
  fmap _ (Query s) = Query s

isU :: UA a b -> Bool
isU (U _) = True
isU _ = False

isA :: UA a b -> Bool
isA (A _) = True
isA _ = False

-- UDT that does all its proofs in the same proof system.
udt' :: (Ord a, Enum a) => [u] -> Int -> a -> ModalProgram (UA u a) a
udt' ordering level dflt = modalProgram dflt $
  mFor' ordering $ \u ->
    mFor $ \a ->
      mIf (boxk level (Var (A a) %> Var (U u))) (mReturn a)

udt :: (Enum u, Ord a, Enum a) => Int -> a -> ModalProgram (UA u a) a
udt = udt' enumerate

-- UDT that escalates its proof system by +1 for each action/outcome pair it reasons about.
escalatingUDT' :: (Enum u, Ord a, Enum a) => [u] -> [Int] -> a -> ModalProgram (UA u a) a
escalatingUDT' ordering levels dflt = modalProgram dflt mainLoop where
  mainLoop = mFor' (zip outcomeActionPairs levels) checkOutcomeAction
  outcomeActionPairs = [(u, a) | u <- ordering, a <- enumerate]
  checkOutcomeAction ((u, a), n) =
    mIf (boxk n (Var (A a) %> Var (U u))) (mReturn a)

escalatingUDT :: (Enum u, Ord a, Enum a) => [Int] -> a -> ModalProgram (UA u a) a
escalatingUDT = escalatingUDT' enumerate

displayAgent :: (Show a, Show v, Enum a) => ModalProgram v a -> IO ()
displayAgent agent = mapM_ putStrLn [show a ++ ": " ++ show (agent a) | a <- enumerate]
