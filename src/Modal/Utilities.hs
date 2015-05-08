module Modal.Utilities
  ( (.:)
  , (.::)
  , ($>)
  , (<$$>)
  , Name
  , enumerate
  ) where
import Data.Text (Text)
import Control.Applicative

(.:) :: (c -> x) -> (a -> b -> c) -> a -> b -> x
(.:) = (.) . (.)

(.::) :: (d -> x) -> (a -> b -> c -> d) -> a -> b -> c -> x
(.::) = (.) . (.) . (.)

infixl 4 $>, <$$>

($>) :: Applicative f => f a -> b -> f b
x $> y = x *> pure y

(<$$>) :: Functor f => f a -> (a -> b) -> f b
(<$$>) = flip (<$>)

type Name = Text

enumerate :: Enum a => [a]
enumerate = enumFrom (toEnum 0)
