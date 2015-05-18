module Modal.Programming where
import Prelude hiding ((.), id)
import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Monad
import Data.Maybe
import qualified Data.List as List
import Data.Text (Text)
import Modal.Display
import Modal.Formulas
import Modal.Parser
import Modal.Utilities
import Text.Parsec (Parsec, sepEndBy)

newtype ModalProgram a v = ModalProgram { formulaFor :: a -> ModalFormula v }

instance Functor (ModalProgram a) where
  fmap f (ModalProgram p) = ModalProgram (fmap f . p)

instance Arrow ModalProgram where
  arr a2v = ModalProgram (Var . a2v)
  first (ModalProgram f) = ModalProgram (\(a, x) -> (\v -> (v, x)) <$> f a)
  second (ModalProgram f) = ModalProgram (\(x, a) -> (\v -> (x, v)) <$> f a)

instance Category ModalProgram where
  id = arr id
  (ModalProgram f) . (ModalProgram g) = ModalProgram (g >=> f)

instance (Show v, Show a, Enum a) => Show (ModalProgram a v) where
  show = showProgram enumerate

instance (Eq a, Parsable a, Read v) => Parsable (ModalProgram a v) where
  parser = programParser parser

showProgram :: (Show a, Show v) => [a] -> ModalProgram a v -> String
showProgram as (ModalProgram p) = renderTable $ tuplesToTable [(a, p a) | a <- as]

programParser :: (Eq a, Read v) => Parsec Text s a -> Parsec Text s (ModalProgram a v)
programParser p = makeProgram <$> (line `sepEndBy` w) where
  line = (,) <$> (p <* symbol ":") <*> parser
  makeProgram kvs = ModalProgram (fromJust . flip List.lookup kvs)

affectFormula :: (ModalFormula v -> ModalFormula w) -> ModalProgram a v -> ModalProgram a w
affectFormula f (ModalProgram p) = ModalProgram (f . p)

-------------------------------------------------------------------------------

-- The type of partial programs. You must tell them "what to do next" in order
-- to generate the completed ModalProgram.
type PartialProgram a v = ModalProgram a v -> ModalProgram a v

-- Completes a program by adding a default action.
completeProgram :: Eq a => a -> PartialProgram a v -> ModalProgram a v
completeProgram dflt f = f $ ModalProgram $ Val . (dflt ==)

-- Partial program that ignores the continuation and returns a.
mReturn :: Eq a => a -> PartialProgram a v
mReturn a _ = ModalProgram $ Val . (a ==)

-- Partial program that either does t or e before the continuation.
mIfElse :: ModalFormula v -> PartialProgram a v -> PartialProgram a v -> PartialProgram a v
mIfElse cond t e next = ModalProgram $ \a -> Or (cond %^ tnext a) (Neg cond %^ enext a) where
  ModalProgram tnext = t next
  ModalProgram enext = e next
-- Alternatively: And (Imp cond (tnext a)) (Imp (Neg cond) (enext a))

-- Partial program that may or may not do t.
mIf :: ModalFormula v -> PartialProgram a v-> PartialProgram a v
mIf cond t = mIfElse cond t id

-- Partial program that iterates over the list of cs.
mFor :: [c] -> (c -> PartialProgram a v) -> PartialProgram a v
mFor []     _ = id
mFor (c:cs) f = f c <<< mFor cs f
