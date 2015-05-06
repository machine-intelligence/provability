module ModalProgramming where
import ModalFormulas
import ModalGameTools
import Data.Map hiding (map)
import qualified Data.Map as Map
import Text.Printf (printf)

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
