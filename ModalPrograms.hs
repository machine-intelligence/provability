module ModalPrograms where
import ModalFormulas
import ModalGameTools
import ModalProgramming

generalUDT :: Eq a => [Int] -> [u] -> [a] -> a -> ModalProgram (U1 u a) a
generalUDT levels uorder aorder dflt = modalProgram dflt mainLoop where
  mainLoop = mFor' (zip levels uaPairs) (uncurry checkUApair)
  uaPairs = [(u, a) | u <- uorder, a <- aorder]
  checkUApair n (u, a) = mIf (boxk n (Var (U1A a) %> Var (U1 u))) (mReturn a)

escalatingUDT :: (Eq a, Enum a, Enum u) => [Int] -> a -> ModalProgram (U1 u a) a
escalatingUDT levels = generalUDT levels enumerate enumerate

udtN :: (Eq a, Enum a, Enum u) => Int -> a -> ModalProgram (U1 u a) a
udtN level = generalUDT (repeat level) enumerate enumerate

udt' :: Eq a => [u] -> [a] -> a -> ModalProgram (U1 u a) a
udt' = generalUDT (repeat 0)

udt :: (Eq a, Enum a, Enum u) => a -> ModalProgram (U1 u a) a
udt = udtN 0
