module Programs where
import Modal
import Data.Map hiding (map)
import qualified Data.Map as Map
import Text.Printf (printf)


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


extractPMEEkey :: (k -> Bool) -> Map k Bool -> k
extractPMEEkey pred = extract . Map.keys . filterWithKey matchKey where
  matchKey k v = pred k && v
  extract [ ] = error "No true formula! Map was not P.M.E.E."
  extract [x] = x
  extract  _  = error "Multiple true formulas! Map was not P.M.E.E."


data U1 u a = U1 u | U1A a | Q1 String deriving (Eq, Ord, Read)
instance (Show a, Show u) => Show (U1 u a) where
  show (U1 u) = show u ++ "ₒ"
  show (U1A a) = show a ++ "ₐ"
  show (Q1 q) = q ++ "?"
instance Functor (U1 u) where
  fmap f (U1A a) = U1A (f a)
  fmap _ (U1 u) = U1 u
  fmap _ (Q1 s) = Q1 s

u1IsU :: U1 u a -> Bool
u1IsU (U1 _) = True
u1IsU _ = False

u1IsA :: U1 u a -> Bool
u1IsA (U1A _) = True
u1IsA _ = False

u1ExtractU :: Map (U1 u a) Bool -> u
u1ExtractU m = let U1 u = extractPMEEkey u1IsU m in u

u1ExtractA :: Map (U1 u a) Bool -> a
u1ExtractA m = let U1A a = extractPMEEkey u1IsA m in a

u1GameMap :: (Ord u, Enum u, Ord a, Enum a) =>
  ModalProgram a u ->
  ModalProgram (U1 u a) a ->
  Map (U1 u a) (ModalFormula (U1 u a))
u1GameMap universe agent = Map.fromList $ us ++ as where
  us = [(U1 u, mapVariable U1A $ universe u) | u <- enumerate]
  as = [(U1A a, agent a) | a <- enumerate]

u1Resolve :: (Ord u, Enum u, Ord a, Enum a) =>
  Map (U1 u a) (ModalFormula (U1 u a)) ->
  (u, a)
u1Resolve game = (u1ExtractU fixpt, u1ExtractA fixpt) where
  fixpt = findGeneralGLFixpoint game

u1Play :: (Ord u, Enum u, Ord a, Enum a) =>
  ModalProgram a u ->
  ModalProgram (U1 u a) a ->
  (u, a)
u1Play universe agent = u1Resolve $ u1GameMap universe agent

u1Display :: (Show u, Show a) => (u, a) -> IO ()
u1Display (u, a) =
  printf "U=%s, A=%s\n" (show u) (show a)

displayU1 :: (Ord u, Enum u, Show u, Ord a, Enum a, Show a) =>
  ModalProgram a u ->
  ModalProgram (U1 u a) a ->
  IO ()
displayU1 universe agent = u1Display $ u1Play universe agent




data U2 u a1 a2 = U2 u | U2A1 a1 | U2A2 a2 | Q2 String deriving (Eq, Ord, Read)
instance (Show u, Show a1, Show a2) => Show (U2 u a1 a2) where
  show (U2 u) = show u ++ "ₒ"
  show (U2A1 a) = show a ++ "₁"
  show (U2A2 a) = show a ++ "₂"
  show (Q2 q) = q ++ "?"

u2IsU :: U2 u a1 a2 -> Bool
u2IsU (U2 _) = True
u2IsU _ = False

u2IsA1 :: U2 u a1 a2 -> Bool
u2IsA1 (U2A1 _) = True
u2IsA1 _ = False

u2IsA2 :: U2 u a1 a2 -> Bool
u2IsA2 (U2A2 _) = True
u2IsA2 _ = False

u2ExtractU :: Map (U2 u a1 a2) Bool -> u
u2ExtractU m = let U2 u = extractPMEEkey u2IsU m in u

u2ExtractA1 :: Map (U2 u a1 a2) Bool -> a1
u2ExtractA1 m = let U2A1 a = extractPMEEkey u2IsA1 m in a

u2ExtractA2 :: Map (U2 u a1 a2) Bool -> a2
u2ExtractA2 m = let U2A2 a = extractPMEEkey u2IsA2 m in a

u2GameMap :: (Ord u, Enum u, Ord a1, Enum a1, Ord a2, Enum a2) =>
  ModalProgram (Either a1 a2) u ->
  ModalProgram (U1 u a1) a1 ->
  ModalProgram (U1 u a2) a2 ->
  Map (U2 u a1 a2) (ModalFormula (U2 u a1 a2))
u2GameMap universe agent1 agent2 = Map.fromList $ us ++ a1s ++ a2s where
  us = [(U2 u, mapVariable promoteToA $ universe u) | u <- enumerate]
  a1s = [(U2A1 a1, mapVariable promoteTo1 $ agent1 a1) | a1 <- enumerate]
  a2s = [(U2A2 a2, mapVariable promoteTo2 $ agent2 a2) | a2 <- enumerate]
  promoteToA (Left a) = U2A1 a
  promoteToA (Right a) = U2A2 a
  promoteTo1 (U1A a) = U2A1 a
  promoteTo1 (U1 u) = U2 u
  promoteTo1 (Q1 s) = Q2 s
  promoteTo2 (U1A a) = U2A2 a
  promoteTo2 (U1 u) = U2 u
  promoteTo2 (Q1 s) = Q2 s

u2Resolve :: (Ord u, Enum u, Ord a1, Enum a1, Ord a2, Enum a2) =>
  Map (U2 u a1 a2) (ModalFormula (U2 u a1 a2)) ->
  (u, a1, a2)
u2Resolve game = (u2ExtractU fixpt, u2ExtractA1 fixpt, u2ExtractA2 fixpt) where
  fixpt = findGeneralGLFixpoint game

u2Play :: (Ord u, Enum u, Ord a1, Enum a1, Ord a2, Enum a2) =>
  ModalProgram (Either a1 a2) u ->
  ModalProgram (U1 u a1) a1 ->
  ModalProgram (U1 u a2) a2 ->
  (u, a1, a2)
u2Play u a1 a2 = u2Resolve $ u2GameMap u a1 a2

u2Display :: (Show u, Show a1, Show a2) => (u, a1, a2) -> IO ()
u2Display (u, a1, a2) =
  printf "U=%s, A₁=%s, A₂=%s\n" (show u) (show a1) (show a2)

displayU2 ::
  (Ord u, Enum u, Show u,
   Ord a1, Enum a1, Show a1,
   Ord a2, Enum a2, Show a2) =>
  ModalProgram (Either a1 a2) u ->
  ModalProgram (U1 u a1) a1 ->
  ModalProgram (U1 u a2) a2 ->
  IO ()
displayU2 universe agent1 agent2 = u2Display $ u2Play universe agent1 agent2


displayAgent :: (Show a, Show v, Enum a) => ModalProgram v a -> IO ()
displayAgent agent = mapM_ putStrLn formulaLines where
  formulaLines = [show a ++ ": " ++ show (agent a) | a <- enumerate]


generalUDT :: Eq a => [Int] -> [u] -> [a] -> a -> ModalProgram (U1 u a) a
generalUDT levels uorder aorder dflt = modalProgram dflt mainLoop where
  mainLoop = mFor' (zip levels uaPairs) (uncurry checkUApair)
  uaPairs = [(u, a) | u <- uorder, a <- aorder]
  checkUApair n (u, a) = mIf (boxk n (Var (U1A a) %> Var (U1 u))) (mReturn a)

escalatingUDT :: (Eq a, Enum a, Enum u) => [Int] -> a -> ModalProgram (U1 u a) a
escalatingUDT levels = generalUDT levels enumerate enumerate

flatUDT :: Eq a => Int -> [u] -> [a] -> a -> ModalProgram (U1 u a) a
flatUDT level = generalUDT (repeat level)

udtN :: (Eq a, Enum a, Enum u) => Int -> a -> ModalProgram (U1 u a) a
udtN level = flatUDT level enumerate enumerate

udt' :: Eq a => [u] -> [a] -> a -> ModalProgram (U1 u a) a
udt' = flatUDT 0

udt :: (Eq a, Enum a, Enum u) => a -> ModalProgram (U1 u a) a
udt = udtN 0
