module Main where
import Control.Monad (foldM)
import Data.Monoid
import Options.Applicative
import System.Environment (getProgName)
import Modal.Combat
import Modal.Utilities

programDescription :: String
programDescription =
  "Modal combat checker. Figures out how modal agents will behave " <>
  "when pitted against each other."

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
  <> header (name ++ " - MODAL COMBAT!" ) )

main :: IO ()
main = do
  name <- getProgName
  opts <- execParser $ options name
  settings <- mapM compileFile (optEnvs opts)
  case settings of
    [] -> playFile (optFile opts)
    (x:xs) -> foldM (run .: mergeSettingsR) x xs >>= playFile' (optFile opts)
