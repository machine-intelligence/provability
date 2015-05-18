module Modal.Programs where
import Modal.Formulas
import Modal.GameTools
import Modal.Programming
import Modal.Utilities

generalUDT :: Eq a => [Int] -> [u] -> [a] -> a -> ModalProgram a (U1 u a)
generalUDT levels uorder aorder dflt = completeProgram dflt mainLoop where
  mainLoop = mFor (zip levels uaPairs) (uncurry checkUApair)
  uaPairs = [(u, a) | u <- uorder, a <- aorder]
  checkUApair n (u, a) = mIf (boxk n (Var (U1A a) %> Var (U1 u))) (mReturn a)

escalatingUDT :: (Eq a, Enum a, Enum u) => [Int] -> a -> ModalProgram a (U1 u a)
escalatingUDT levels = generalUDT levels enumerate enumerate

udtN :: (Eq a, Enum a, Enum u) => Int -> a -> ModalProgram a (U1 u a)
udtN level = generalUDT (repeat level) enumerate enumerate

udt' :: Eq a => [u] -> [a] -> a -> ModalProgram a (U1 u a)
udt' = generalUDT (repeat 0)

udt :: (Eq a, Enum a, Enum u) => a -> ModalProgram a (U1 u a)
udt = udtN 0
