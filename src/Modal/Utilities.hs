module Modal.Utilities
  ( (.:)
  , (.::)
  , (.:::)
  , ($>)
  , (<$$>)
  , Name
  , Void
  , enumerate
  , alter
  , every
  , die
  , force
  , run
  , runFile
  ) where
import Prelude hiding (readFile)
import Control.Applicative
import Data.Text (Text)
import Data.Text.IO (readFile)
import System.IO (stderr, hPutStrLn)
import System.Exit hiding (die)
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

type Name = String

data Void
instance Eq Void
instance Ord Void
instance Read Void
instance Show Void

enumerate :: Enum a => [a]
enumerate = enumFrom (toEnum 0)

alter :: [a] -> Int -> (a -> a) -> [a]
alter [] _ _ = error "empty list"
alter (x:xs) 0 f = f x : xs
alter (x:xs) n f = x : alter xs (pred n) f

every :: Int -> [a] -> [a]
every n (x : xs) = x : every n (drop (pred n) xs)
every _ [] = []

die :: Show a => a -> IO b
die x = hPutStrLn stderr ("Error: " ++ show x) >> exitFailure

force :: Show l => Either l r -> r
force = either (error . printf "Forcing failed: %s" . show) id

run :: Show x => Either x a -> IO a
run = either die return

runFile :: Show x => (Text -> Either x a) -> FilePath -> IO a
runFile f path = run . f =<< readFile path
