module Main where
import Prelude hiding (foldr)
import Data.Monoid
import Data.Foldable
import Options.Applicative
import System.Environment (getProgName)
import Modal.Combat
import Modal.Environment
import Modal.Utilities

programDescription :: String
programDescription =
  "Modal combat checker. Figures out how modal agents will behave " <>
  "in the prisoner's dilemma with shared source code."

data Options = Options
  { optEnvs :: [FilePath]
  , optFile :: FilePath
  } deriving Show

optionParser :: Parser Options
optionParser = Options
  <$> many (option str
    (  long "env"
    <> short 'e'
    <> metavar "FILE"
    <> help "An environment file defining other agents." ))
  <*> argument str
    ( metavar "FILE" )

options :: String -> ParserInfo Options
options name = info (helper <*> optionParser)
  (  fullDesc
  <> progDesc programDescription
  <> header (name ++ " - Modal Combat!" ) )

main :: IO ()
main = do
  name <- getProgName
  opts <- execParser $ options name
  bases <- mapM compileFile (optEnvs opts)
  env <- run (foldlM insertAll (nobody enumerate) $ map players bases)
  playFile (optFile opts) env
