module Modal.Utilities
  ( (.:)
  , (.::)
  , (.:::)
  , ($>)
  , (<$$>)
  , Name
  , die
  , enumerate
  , force
  , run
  ) where
import Control.Applicative
import Control.Monad.Except
import Data.Text (Text)
import Text.Printf (printf)

(.:) :: (c -> x) -> (a -> b -> c) -> a -> b -> x
(.:) = (.) . (.)

(.::) :: (d -> x) -> (a -> b -> c -> d) -> a -> b -> c -> x
(.::) = (.) . (.) . (.)

(.:::) :: (e -> x) -> (a -> b -> c -> d -> e) -> a -> b -> c -> d -> x
(.:::) = (.) . (.) . (.) . (.)

infixl 4 $>, <$$>

($>) :: Applicative f => f a -> b -> f b
x $> y = x *> pure y

(<$$>) :: Functor f => f a -> (a -> b) -> f b
(<$$>) = flip (<$>)

type Name = Text

enumerate :: Enum a => [a]
enumerate = enumFrom (toEnum 0)

die :: Show a => a -> IO b
die = printf "Error: %s" . show

force :: Show l => Either l r -> r
force = either (error . printf "Forcing failed: %s" . show) id

run :: Show x => Either x a -> IO a
run = either die return
