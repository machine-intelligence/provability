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
  , optUtf8 :: Bool
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
  <*> switch
    (  long "utf8"
    <> short 'u'
    <> help "Interpret input files in UTF-8." )

options :: String -> ParserInfo Options
options name = info (helper <*> optionParser)
  (  fullDesc
  <> progDesc programDescription
  <> header (name ++ " - MODAL COMBAT!" ) )

main :: IO ()
main = do
  name <- getProgName
  opts <- execParser $ options name
  let useUtf8 = optUtf8 opts
      file = optFile opts
  settings <- mapM (compileFile useUtf8) (optEnvs opts)
  case settings of
    [] -> playFile useUtf8 file
    (x:xs) -> foldM (run .: mergeSettingsR) x xs >>= playFile' useUtf8 file
