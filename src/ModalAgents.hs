module Main where
import Prelude hiding (foldr)
import Data.Monoid
import Data.Foldable
import Options.Applicative
import System.Environment (getProgName)
import Modal.Universes
import Modal.Environment
import Modal.Utilities

programDescription :: String
programDescription =
  "Modal agent checker. Figures out how modal agents will behave " <>
  "in various modal universes."

data Options = Options { optFile :: FilePath } deriving Show

optionParser :: Parser Options
optionParser = Options <$> argument str (metavar "FILE")

options :: String -> ParserInfo Options
options name = info (helper <*> optionParser)
  (  fullDesc
  <> progDesc programDescription
  <> header (name ++ " - Modal agent checker" ) )

main :: IO ()
main = do
  name <- getProgName
  opts <- execParser $ options name
  playFile (optFile opts)
