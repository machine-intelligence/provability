module Modal.Utilities
  ( (.:)
  , (.::)
  , (.:::)
  , ($>)
  , (<$$>)
  , Name
  , Void
  , die
  , enumerate
  , force
  , run
  , runFile
  ) where
import Prelude hiding (readFile)
import Control.Applicative
import Data.Text (Text)
import Data.Text.IO (readFile)
import System.IO (stderr, hPutStrLn)
import System.Exit
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

data Void
instance Eq Void
instance Ord Void
instance Read Void
instance Show Void

enumerate :: Enum a => [a]
enumerate = enumFrom (toEnum 0)

die :: Show a => a -> IO b
die x = hPutStrLn stderr ("Error: " ++ show x) >> exitFailure

force :: Show l => Either l r -> r
force = either (error . printf "Forcing failed: %s" . show) id

run :: Show x => Either x a -> IO a
run = either die return

runFile :: Show x => (Text -> Either x a) -> FilePath -> IO a
runFile f path = run . f =<< readFile path
