module Modal.Programming where
import Prelude hiding ((.), id)
import Control.Arrow
import Control.Category
import Data.Maybe
import qualified Data.List as List
import Modal.Display
import Modal.Formulas
import Modal.Parser
import Text.Parsec (sepEndBy)
import Text.Parsec.Text

type ModalProgram a v = a -> ModalFormula v

showProgram :: (Show a, Show v) => [a] -> ModalProgram a v -> String
showProgram as p = renderTable $ tuplesToTable [(a, p a) | a <- as]

programParser :: (Eq a, Read v) => Parser a -> Parser (ModalProgram a v)
programParser p = makeProgram <$> (line `sepEndBy` w) where
  line = (,) <$> (p <* symbol ":") <*> parser
  makeProgram kvs = fromJust . flip List.lookup kvs

-------------------------------------------------------------------------------

-- The type of partial programs. You must tell them "what to do next" in order
-- to generate the completed ModalProgram.
type PartialProgram a v = ModalProgram a v -> ModalProgram a v

-- Completes a program by adding a default action.
completeProgram :: Eq a => a -> PartialProgram a v -> ModalProgram a v
completeProgram dflt f = f $ Val . (dflt ==)

-- Partial program that ignores the continuation and returns a.
mReturn :: Eq a => a -> PartialProgram a v
mReturn a _ = Val . (a ==)

-- Partial program that either does t or e before the continuation.
mIfElse :: ModalFormula v -> PartialProgram a v -> PartialProgram a v -> PartialProgram a v
mIfElse cond t e next a = Or (cond %^ t next a) (Neg cond %^ e next a) where
-- Alternatively: And (Imp cond (tnext a)) (Imp (Neg cond) (enext a))

-- Partial program that may or may not do t.
mIf :: ModalFormula v -> PartialProgram a v-> PartialProgram a v
mIf cond t = mIfElse cond t id

-- Partial program that iterates over the list of cs.
mFor :: [c] -> (c -> PartialProgram a v) -> PartialProgram a v
mFor []     _ = id
mFor (c:cs) f = f c <<< mFor cs f
