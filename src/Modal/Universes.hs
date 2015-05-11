{-# LANGUAGE DeriveFunctor #-}
module Modal.Universes where
import Prelude hiding (mapM, mapM_, foldr)
import Control.Applicative
import Control.Monad (void)
import Data.Monoid
import Data.Map (Map)
import qualified Data.List as L
import Modal.Code
import Modal.Display
import Modal.Formulas
import Modal.Environment
import Modal.Parser
import Modal.Programming
import Modal.Utilities
import Data.Foldable
import qualified Data.Map as M
import Data.Text (Text)
import qualified Data.Text as T
import Data.Traversable
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Printf (printf)

extractPMEEkey :: (k -> Bool) -> Map k Bool -> k
extractPMEEkey p = extract . M.keys . M.filterWithKey matchKey where
  matchKey k v = p k && v
  extract [ ] = error "No true formula! Map was not P.M.E.E."
  extract [x] = x
  extract  _  = error "Multiple true formulas! Map was not P.M.E.E."

data GameObject a
  = ActionsAre [Name]
  | OutcomesAre [Name]
  | Player a
  | Universe a
  | Play Name Name
  | Describe Name Name
  deriving (Eq, Functor)

instance Show a => Show (GameObject a) where
  show (ActionsAre as) = printf "Actions: %s" (L.intercalate "," $ map T.unpack as)
  show (OutcomesAre os) = printf "Outcomes: %s" (L.intercalate "," $ map T.unpack os)
  show (Player a) = show a
  show (Universe u) = show u
  show (Play n1 n2) = printf "play %s vs %s" (T.unpack n1) (T.unpack n2)
  show (Describe n1 n2) = printf "describe %s vs %s" (T.unpack n1) (T.unpack n2)

data ParserState = PS { getAs :: Maybe [Name], getOs :: Maybe [Name] }

freshState :: ParserState
freshState = PS Nothing Nothing

setAs :: [Name] -> ParserState -> Maybe ParserState
setAs as (PS Nothing os) = Just $ PS (Just as) os
setAs _ _ = Nothing

setOs :: [Name] -> ParserState -> Maybe ParserState
setOs os (PS as Nothing) = Just $ PS as (Just os)
setOs _ _ = Nothing

gameObjectParser :: Parsec Text ParserState (GameObject (Agent Text Text))
gameObjectParser
  = try acts
  <|> try outs
  <|> try agent
  <|> try universe
  <|> try pPlay
  <|> try pDescribe
  <?> "a game object"
  where
   acts = do
     keyword "actions"
     acts <- name `sepBy` w1
     state <- getState
     case setAs acts state of
       Nothing -> fail "Actions set twice."
       Just newstate -> putState newstate $> ActionsAre acts
   outs = do
     keyword "outcomes"
     outs <- name `sepBy` w1
     state <- getState
     case setOs outs state of
       Nothing -> fail "Outcomes set twice."
       Just newstate -> putState newstate $> OutcomesAre outs
   agent = do
     state <- getState
     case state of
       PS Nothing Nothing -> fail "Actions and outcomes not set."
       PS Nothing _ -> fail "Actions not set."
       PS _ Nothing -> fail "Outcomes not set."
       PS (Just as) (Just os) -> Player <$> agentParser (pick as) (pick os)
   universe = do
     state <- getState
     case state of
       PS Nothing Nothing -> fail "Actions and outcomes not set."
       PS Nothing _ -> fail "Actions not set."
       PS _ Nothing -> fail "Outcomes not set."
       PS (Just as) (Just os) -> Universe <$> agentParser (pick os) (pick as)
   pick xs = choice [T.pack <$> string (T.unpack x) | x <- xs]
   pPlay = Play <$> (keyword "play" *> name) <*> (keyword "vs" *> name)
   pDescribe = Describe <$> (keyword "describe" *> name) <*> (keyword "vs" *> name)


newtype Game a = Game { objects :: [GameObject a] } deriving (Eq, Show, Functor)
instance Foldable Game where
  foldMap _ (Game []) = mempty
  foldMap f (Game (Player x : xs)) = f x <> foldMap f (Game xs)
  foldMap f (Game (Universe x : xs)) = f x <> foldMap f (Game xs)
  foldMap f (Game (_ : xs)) = foldMap f (Game xs)
instance Traversable Game where
  traverse _ (Game []) = pure $ Game []
  traverse f (Game (Player x : xs)) = rejoin <$> f x <*> traverse f (Game xs) where
    rejoin x' (Game ys) = Game (Player x' : ys)
  traverse f (Game (Universe x : xs)) = rejoin <$> f x <*> traverse f (Game xs) where
    rejoin x' (Game ys) = Game (Universe x' : ys)
  traverse f (Game (Play n1 n2 : xs))
    = (Game . (Play n1 n2 :) . objects) <$> traverse f (Game xs)
  traverse f (Game (Describe n1 n2 : xs))
    = (Game . (Describe n1 n2 :) . objects) <$> traverse f (Game xs)

gameParser :: Parsec Text ParserState (Game (Agent Text Text))
gameParser = Game <$> (gameObjectParser `sepEndBy` w) <* eof

parseAndCompileGame :: SourceName -> Text -> Either CompileError (Game (Name, Program Text Text))
parseAndCompileGame = parseAndCompile' getAs getOs freshState gameParser

compileGameFile :: FilePath -> IO (Game (Name, Program Text Text))
compileGameFile = compileFile' getAs getOs freshState gameParser

players :: Game (Name, Program Text Text) -> [(Name, Program Text Text)]
players (Game []) = []
players (Game (Player x : xs)) = x : players (Game xs)
players (Game (_ : xs)) = players (Game xs)

universes :: Game (Name, Program Text Text) -> [(Name, Program Text Text)]
universes (Game []) = []
universes (Game (Universe x : xs)) = x : universes (Game xs)
universes (Game (_ : xs)) = universes (Game xs)

doAction :: Env Text Text -> Env Text Text -> GameObject (Name, Program Text Text) -> IO ()
doAction env1 env2 (Play n1 n2) = do
  void $ printf "%s vs %s:\n" (T.unpack n1) (T.unpack n2)
  (r1, r2) <- run (compete2 env1 env2 n1 n2)
  void $ printf "  %s=%s, %s=%s\n\n" (T.unpack n1) (show r1) (T.unpack n2) (show r2)
doAction env1 env2 (Describe n1 n2) = do
  void $ printf "%s vs %s:\n\n" (T.unpack n1) (T.unpack n2)
  cmap <- run (competitionMap2 env1 env2 n1 n2)
  displayTable $ indentTable "  " $ tuplesToTable $ M.toAscList cmap
  displayTable $ indentTable "  " $ kripkeTable cmap
  (r1, r2) <- run (compete2 env1 env2 n1 n2)
  printf "  Result: %s=%s, %s=%s\n\n" (T.unpack n1) (show r1) (T.unpack n2) (show r2)
doAction _ _ _ = return ()

playGame :: Game (Name, Program Text Text) -> Env Text Text -> Env Text Text -> IO ()
playGame game base1 base2 = do
  env1 <- run (insertAll base1 $ players game)
  env2 <- run (insertAll base2 $ universes game)
  putStr "Agents loaded: "
  print env1
  putStr "Universes loaded: "
  print env2
  putStrLn ""
  mapM_ (doAction env1 env2) (objects game)

playFile :: FilePath -> Env Text Text -> Env Text Text -> IO ()
playFile fp env1 env2 = compileGameFile fp >>= (\g -> playGame g env1 env2)
