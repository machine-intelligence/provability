module Modal.GameTools where
import Modal.Formulas
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

displayAgent :: (Show a, Show v, Enum a) => ModalProgram v a -> IO ()
displayAgent agent = mapM_ putStrLn formulaLines where
  formulaLines = [show a ++ ": " ++ show (agent a) | a <- enumerate]

extractPMEEkey :: (k -> Bool) -> Map k Bool -> k
extractPMEEkey p = extract . Map.keys . filterWithKey matchKey where
  matchKey k v = p k && v
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

gameMap :: (Ord u, Enum u, Ord a, Enum a) =>
  ModalProgram a u ->
  ModalProgram (U1 u a) a ->
  Map (U1 u a) (ModalFormula (U1 u a))
gameMap universe agent = Map.fromList $ us ++ as where
  us = [(U1 u, mapVariable U1A $ universe u) | u <- enumerate]
  as = [(U1A a, agent a) | a <- enumerate]

resolveGame :: (Ord u, Enum u, Ord a, Enum a) =>
  Map (U1 u a) (ModalFormula (U1 u a)) ->
  (u, a)
resolveGame game = (u1ExtractU fixpt, u1ExtractA fixpt) where
  fixpt = findGeneralGLFixpoint game

playGame :: (Ord u, Enum u, Ord a, Enum a) =>
  ModalProgram a u ->
  ModalProgram (U1 u a) a ->
  (u, a)
playGame universe agent = resolveGame $ gameMap universe agent

showGame :: (Show u, Show a) => (u, a) -> IO ()
showGame (u, a) =
  printf "U=%s, A=%s\n" (show u) (show a)

displayGame :: (Ord u, Enum u, Show u, Ord a, Enum a, Show a) =>
  ModalProgram a u ->
  ModalProgram (U1 u a) a ->
  IO ()
displayGame universe agent = showGame $ playGame universe agent


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

gameMap2 :: (Ord u, Enum u, Ord a1, Enum a1, Ord a2, Enum a2) =>
  ModalProgram (Either a1 a2) u ->
  ModalProgram (U1 u a1) a1 ->
  ModalProgram (U1 u a2) a2 ->
  Map (U2 u a1 a2) (ModalFormula (U2 u a1 a2))
gameMap2 universe agent1 agent2 = Map.fromList $ us ++ a1s ++ a2s where
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

resolveGame2 :: (Ord u, Enum u, Ord a1, Enum a1, Ord a2, Enum a2) =>
  Map (U2 u a1 a2) (ModalFormula (U2 u a1 a2)) ->
  (u, a1, a2)
resolveGame2 game = (u2ExtractU fp, u2ExtractA1 fp, u2ExtractA2 fp) where
  fp = findGeneralGLFixpoint game

playGame2 :: (Ord u, Enum u, Ord a1, Enum a1, Ord a2, Enum a2) =>
  ModalProgram (Either a1 a2) u ->
  ModalProgram (U1 u a1) a1 ->
  ModalProgram (U1 u a2) a2 ->
  (u, a1, a2)
playGame2 u a1 a2 = resolveGame2 $ gameMap2 u a1 a2

showGame2 :: (Show u, Show a1, Show a2) => (u, a1, a2) -> IO ()
showGame2 (u, a1, a2) =
  printf "U=%s, A₁=%s, A₂=%s\n" (show u) (show a1) (show a2)

displayGame2 ::
  (Ord u, Enum u, Show u,
   Ord a1, Enum a1, Show a1,
   Ord a2, Enum a2, Show a2) =>
  ModalProgram (Either a1 a2) u ->
  ModalProgram (U1 u a1) a1 ->
  ModalProgram (U1 u a2) a2 ->
  IO ()
displayGame2 u a1 a2= showGame2 $ playGame2 u a1 a2
