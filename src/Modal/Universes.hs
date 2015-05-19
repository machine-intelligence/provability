module Modal.Universes where
import Prelude hiding (mapM, mapM_, sequence, foldr)
import Control.Applicative
import Control.Monad.Identity hiding (mapM, mapM_, sequence)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.Text (Text)
import Data.Traversable
import Modal.Code
import Modal.Combat (MeVsThem(..))
import Modal.Competition
import Modal.Display
import Modal.Environment
import Modal.Formulas
import Modal.Parser
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Printf (printf)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified Modal.Parser as P

data UniverseVar u p
  = PlayerNvsMe Int p
  | PlayerNvsU Int Name p
  | IPlay u
  deriving (Eq, Ord)

instance (Show u, Show p) => Show (UniverseVar u p) where
  show (PlayerNvsMe i p) = printf "A%d()=%s" i (show p)
  show (PlayerNvsU i other p) = printf "A%d(%s)=%s" i (Text.unpack other) (show p)
  show (IPlay u) = printf "U()=%s" (show u)

instance Bifunctor UniverseVar where
  bimap f g = runIdentity . bitraverse (Identity . f) (Identity . g)

instance Bifoldable UniverseVar where
  bifoldMap _ addP (PlayerNvsMe _ p) = addP p
  bifoldMap _ addP (PlayerNvsU _ _ p) = addP p
  bifoldMap addU _ (IPlay u) = addU u

instance Bitraversable UniverseVar where
  bitraverse _ g (PlayerNvsMe i p) = PlayerNvsMe i <$> g p
  bitraverse _ g (PlayerNvsU i other p) = PlayerNvsU i other <$> g p
  bitraverse f _ (IPlay u) = IPlay <$> f u

instance AgentVar UniverseVar where
  otherAgentsReferencedBy (PlayerNvsU _ other _) = [other]
  otherAgentsReferencedBy _ = []
  makeVParser u p = try pvm <|> try pvo <|> try ip <?> "a universe variable" where
    anum = string "A" *> option 1 parser
    pvm = PlayerNvsMe <$> choice [anum <* string "()", anum <* string "(U)"] <*> p
    pvo = PlayerNvsU <$> anum <*> P.parens P.name <*> p
    ip = IPlay <$> (string "U()" *> u)

instance Canonicalizable2 UniverseVar where
  canonicalize2 v1 v2 me them = fmap expandName where
    expandName (IPlay val) = v1 me them val
    expandName (PlayerNvsMe _ val) = v2 them me val
    expandName (PlayerNvsU _ other val) = v2 them other val

instance (Parsable a, Parsable o) => Parsable (UniverseVar a o) where
  parser = makeVParser parser parser

instance IsMultiVarU UniverseVar where
  promoteU names (PlayerNvsMe i x) = PlayerPlays names i x
  promoteU names (PlayerNvsU i univ x) = PlayerPlays (alter names 0 $ const univ) i x
  promoteU names (IPlay x) = UniversePlays names x

data GameObject
  = ActionsAre [Name]
  | OutcomesAre [Name]
  | Agent (ModalizedDef MeVsThem Text Text)
  | Universe (UnrestrictedDef UniverseVar Text Text)
  | Play Name Name
  | Describe Name Name
  deriving Eq

instance Show GameObject where
  show (ActionsAre as) = printf "Actions: %s" (List.intercalate "," $ map Text.unpack as)
  show (OutcomesAre os) = printf "Outcomes: %s" (List.intercalate "," $ map Text.unpack os)
  show (Agent a) = show a
  show (Universe u) = show u
  show (Play n1 n2) = printf "play %s %s" (Text.unpack n1) (Text.unpack n2)
  show (Describe n1 n2) = printf "describe %s %s" (Text.unpack n1) (Text.unpack n2)

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
       PS (Just as) (Just os) -> Agent <$> modalizedDefParser
        (pick as) (pick os) "actions" "outcomes" "agent"
   universe = do
     state <- getState
     case state of
       PS Nothing Nothing -> fail "Actions and outcomes not set."
       PS Nothing _ -> fail "Actions not set."
       PS _ Nothing -> fail "Outcomes not set."
       PS (Just as) (Just os) -> Universe <$> unrestrictedDefParser
        (pick os) (pick as) "outcomes" "actions" "universe"
   pick xs = choice [Text.pack <$> string (Text.unpack x) | x <- xs]
   pPlay = Play <$> (keyword "play" *> name) <*> (keyword "vs" *> name)
   pDescribe = Describe <$> (keyword "describe" *> name) <*> (keyword "vs" *> name)

gameParser :: Parsec Text ParserState [GameObject]
gameParser = (gameObjectParser `sepEndBy` w) <* eof

mapAgents :: (ModalizedDef MeVsThem Text Text -> a) -> [GameObject] -> [a]
mapAgents _ [] = []
mapAgents f (Agent x : xs) = f x : mapAgents f xs
mapAgents f (_ : xs) = mapAgents f xs

mapUniverses :: (UnrestrictedDef UniverseVar Text Text -> a) -> [GameObject] -> [a]
mapUniverses _ [] = []
mapUniverses f (Universe x : xs) = f x : mapUniverses f xs
mapUniverses f (_ : xs) = mapUniverses f xs

parseFile :: FilePath -> IO ([GameObject], ParserState)
parseFile path = runFile (runParser getGameAndState freshState path) path where
  getGameAndState = (,) <$> gameParser <*> getState

compileGame :: ([GameObject], ParserState) ->
  IO ([(Name, AgentMap UniverseVar Text Text)], [(Name, AgentMap MeVsThem Text Text)])
compileGame (objects, state) = do
  as <- maybe (fail "No actions given.") return (getAs state)
  os <- maybe (fail "No outcomes given.") return (getOs state)
  universes <- run $ sequence (mapUniverses (compileUnrestrictedAgent $ emptyContext os as) objects)
  agents <- run $ sequence (mapAgents (compileModalizedAgent $ emptyContext as os) objects)
  return (universes, agents)

doAction :: Env UniverseVar Text Text -> Env MeVsThem Text Text -> GameObject -> IO ()
doAction uEnv aEnv (Play n1 n2) = do
  void $ printf "%s vs %s:\n" (Text.unpack n1) (Text.unpack n2)
  (r1, r2) <- run (compete2 uEnv aEnv n1 n2)
  void $ printf "  %s=%s, %s=%s\n\n" (Text.unpack n1) (show r1) (Text.unpack n2) (show r2)
doAction uEnv aEnv (Describe n1 n2) = do
  void $ printf "%s vs %s:\n\n" (Text.unpack n1) (Text.unpack n2)
  cmap <- run (competitionMap2 uEnv aEnv n1 n2)
  displayTable $ indentTable "  " $ tuplesToTable $ Map.toAscList cmap
  displayTable $ indentTable "  " $ kripkeTable cmap
  (r1, r2) <- run (compete2 uEnv aEnv n1 n2)
  printf "  Result: %s=%s, %s=%s\n\n" (Text.unpack n1) (show r1) (Text.unpack n2) (show r2)
doAction _ _ _ = return ()

playGame ::
  Env UniverseVar Text Text ->
  Env MeVsThem Text Text ->
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

playFile :: Env UniverseVar Text Text -> Env MeVsThem Text Text -> FilePath -> IO ()
playFile uEnv aEnv path = parseFile path >>= playGame uEnv aEnv
