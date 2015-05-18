module Modal.Universes where
import Prelude hiding (mapM, mapM_, sequence, foldr)
import Control.Applicative
import Control.Monad (void)
import Data.Map (Map)
import qualified Data.List as L
import Modal.Code
import Modal.Agent
import Modal.Display
import Modal.Formulas
import Modal.Environment
import Modal.Competition (competitionMap2, compete2)
import Modal.Parser
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

data GameObject
  = ActionsAre [Name]
  | OutcomesAre [Name]
  | Agent (ModalizedAgent Text Text)
  | Universe (FreeAgent Text Text)
  | Play Name Name
  | Describe Name Name
  deriving Eq

instance Show GameObject where
  show (ActionsAre as) = printf "Actions: %s" (L.intercalate "," $ map T.unpack as)
  show (OutcomesAre os) = printf "Outcomes: %s" (L.intercalate "," $ map T.unpack os)
  show (Agent a) = show a
  show (Universe u) = show u
  show (Play n1 n2) = printf "play %s %s" (T.unpack n1) (T.unpack n2)
  show (Describe n1 n2) = printf "describe %s %s" (T.unpack n1) (T.unpack n2)

data ParserState = PS { getAs :: Maybe [Name], getOs :: Maybe [Name] }

freshState :: ParserState
freshState = PS Nothing Nothing

setAs :: [Name] -> ParserState -> Maybe ParserState
setAs as (PS Nothing os) = Just $ PS (Just as) os
setAs _ _ = Nothing

setOs :: [Name] -> ParserState -> Maybe ParserState
setOs os (PS as Nothing) = Just $ PS as (Just os)
setOs _ _ = Nothing

gameObjectParser :: Parsec Text ParserState GameObject
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
     a <- name `sepBy` w1
     state <- getState
     case setAs a state of
       Nothing -> fail "Actions set twice."
       Just newstate -> putState newstate $> ActionsAre a
   outs = do
     keyword "outcomes"
     o <- name `sepBy` w1
     state <- getState
     case setOs o state of
       Nothing -> fail "Outcomes set twice."
       Just newstate -> putState newstate $> OutcomesAre o
   agent = do
     state <- getState
     case state of
       PS Nothing Nothing -> fail "Actions and outcomes not set."
       PS Nothing _ -> fail "Actions not set."
       PS _ Nothing -> fail "Outcomes not set."
       PS (Just as) (Just os) -> Agent <$> modalizedAgentParser
        (pick as) (pick os) "actions" "outcomes" "agent"
   universe = do
     state <- getState
     case state of
       PS Nothing Nothing -> fail "Actions and outcomes not set."
       PS Nothing _ -> fail "Actions not set."
       PS _ Nothing -> fail "Outcomes not set."
       PS (Just as) (Just os) -> Universe <$> freeAgentParser
        (pick os) (pick as) "outcomes" "actions" "universe"
   pick xs = choice [T.pack <$> string (T.unpack x) | x <- xs]
   pPlay = Play <$> (keyword "play" *> name) <*> (keyword "vs" *> name)
   pDescribe = Describe <$> (keyword "describe" *> name) <*> (keyword "vs" *> name)

gameParser :: Parsec Text ParserState [GameObject]
gameParser = (gameObjectParser `sepEndBy` w) <* eof

mapAgents :: (ModalizedAgent Text Text -> a) -> [GameObject] -> [a]
mapAgents _ [] = []
mapAgents f (Agent x : xs) = f x : mapAgents f xs
mapAgents f (_ : xs) = mapAgents f xs

mapUniverses :: (FreeAgent Text Text -> a) -> [GameObject] -> [a]
mapUniverses _ [] = []
mapUniverses f (Universe x : xs) = f x : mapUniverses f xs
mapUniverses f (_ : xs) = mapUniverses f xs

parseFile :: FilePath -> IO ([GameObject], ParserState)
parseFile path = runFile (runParser getGameAndState freshState path) path where
  getGameAndState = (,) <$> gameParser <*> getState

compileGame :: ([GameObject], ParserState) ->
  IO ([(Name, Program Text Text)], [(Name, Program Text Text)])
compileGame (objects, state) = do
  as <- maybe (fail "No actions given.") return (getAs state)
  os <- maybe (fail "No outcomes given.") return (getOs state)
  universes <- run $ sequence (mapUniverses (compileFreeAgent $ emptyContext os as) objects)
  agents <- run $ sequence (mapAgents (compileModalizedAgent $ emptyContext as os) objects)
  return (universes, agents)

doAction :: Env Text Text -> Env Text Text -> GameObject -> IO ()
doAction uEnv aEnv (Play n1 n2) = do
  void $ printf "%s vs %s:\n" (T.unpack n1) (T.unpack n2)
  (r1, r2) <- run (compete2 uEnv aEnv n1 n2)
  void $ printf "  %s=%s, %s=%s\n\n" (T.unpack n1) (show r1) (T.unpack n2) (show r2)
doAction uEnv aEnv (Describe n1 n2) = do
  void $ printf "%s vs %s:\n\n" (T.unpack n1) (T.unpack n2)
  cmap <- run (competitionMap2 uEnv aEnv n1 n2)
  displayTable $ indentTable "  " $ tuplesToTable $ M.toAscList cmap
  displayTable $ indentTable "  " $ kripkeTable cmap
  (r1, r2) <- run (compete2 uEnv aEnv n1 n2)
  printf "  Result: %s=%s, %s=%s\n\n" (T.unpack n1) (show r1) (T.unpack n2) (show r2)
doAction _ _ _ = return ()

playGame ::
  Env Text Text ->
  Env Text Text ->
  ([GameObject], ParserState) ->
  IO ()
playGame uBase aBase (objects, state) = do
  (universes, agents) <- compileGame (objects, state)
  uEnv <- run $ insertAll uBase universes
  aEnv <- run $ insertAll aBase agents
  putStr "Universes loaded: "
  print uEnv
  putStr "Agents loaded: "
  print aEnv
  putStrLn ""
  mapM_ (doAction uEnv aEnv) objects

playFile :: Env Text Text -> Env Text Text -> FilePath -> IO ()
playFile uEnv aEnv path = parseFile path >>= playGame uEnv aEnv
