module Modal.Universes where
import Prelude hiding (mapM, mapM_, sequence, foldr)
import Control.Applicative
import Control.Monad.Identity hiding (mapM, mapM_, sequence)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.Map (Map)
import Data.Text (Text)
import Data.Traversable
import Modal.Code
import Modal.Combat (MeVsThem(..))
import Modal.Competition
import Modal.Display
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

data AgentConfig = AgentConfig
  { acArgs :: Map Name (Val Text Text)
  , acActs :: [Text]
  , acOuts :: [Text]
  } deriving (Eq, Ord, Show)

data GameObject
  = Agent (ModalizedDef MeVsThem Text Text)
  | Universe (UnrestrictedDef UniverseVar Text Text)
  | Play (Name, Parameters Text Text) [(Name, Parameters Text Text)]
  | Describe (Name, Parameters Text Text) [(Name, Parameters Text Text)]
  deriving (Eq, Show)

atParser, dollarParser :: Parsec Text s Name
atParser = char '@' *> name
dollarParser = char '$' *> name


instance Parsable GameObject where
  parser = try a <|> try u <|> try (play Play "play") <|> play Describe "describe" where
    a = Agent <$> modalizedDefParser
      atParser dollarParser "actions" "outcomes" "agent"
    u = Universe <$> unrestrictedDefParser
      dollarParser atParser "outcomes" "actions" "universe"
    play make word = keyword word *> (make <$> callU <*> many1 callA)
    callU = (,) <$> name <*> paramsParser dollarParser atParser
    callA = (,) <$> name <*> paramsParser atParser dollarParser

gameParser :: Parsec Text s [GameObject]
gameParser = (parser `sepEndBy` w) <* eof

mapAgents :: (Agent -> a) -> [GameObject] -> [a]
mapAgents f (Agent x : xs) = f x : mapAgents f xs
mapAgents f (_ : xs) = mapAgents f xs
mapAgents _ [] = []

mapUniverses :: (Universe -> a) -> [GameObject] -> [a]
mapUniverses f (Universe x : xs) = f x : mapUniverses f xs
mapUniverses f (_ : xs) = mapUniverses f xs
mapUniverses _ [] = []

agentList :: [GameObject] -> [Agent]
agentList (Agent x : xs) = x : agentList xs
agentList (_ : xs) = agentList xs
agentList [] = []

universeList :: [GameObject] -> [Universe]
universeList (Universe x : xs) = x : universeList xs
universeList (_ : xs) = universeList xs
universeList [] = []

parseFile :: FilePath -> IO [GameObject]
parseFile path = runFile (runParser gameParser () path) path where

type Agent = ModalizedDef MeVsThem Text Text
type Agents = Map Name Agent
getAgent :: Agents -> Name -> Either CompileError Agent
getAgent as n = maybe (Left $ UnknownName n) Right (Map.lookup n as)

type Universe = UnrestrictedDef UniverseVar Text Text
type Universes = Map Name Universe
getUniv :: Universes -> Name -> Either CompileError Universe
getUniv as n = maybe (Left $ UnknownName n) Right (Map.lookup n as)

joinVars :: (Eq a, Eq u) =>
  UnrestrictedDef UniverseVar u a ->
  ModalizedDef MeVsThem a u ->
  Either CompileError (ModalizedDef MeVsThem a u)
joinVars u a = do
  acts <- check "actions" (agentOutcomes u) (agentActions a)
  outs <- check "outcomes" (agentActions u) (agentOutcomes a)
  return a{agentActions=acts, agentOutcomes=outs}
  where check str x y = case (x, y) of
                         (Nothing, Nothing) -> return Nothing
                         (Just xs, Nothing) -> return $ Just xs
                         (Nothing, Just ys) -> return $ Just ys
                         (Just xs, Just ys)
                           | xs == ys  -> return (Just xs)
                           | otherwise -> Left (Mismatch (agentName a) str)

_buildPairs ::
  Name -> Parameters Text Text -> [(Name, Parameters Text Text)] ->
  Agents -> Universes ->
  IO ((Name, AgentMap UniverseVar Text Text), [(Name, AgentMap MeVsThem Text Text)])
_buildPairs uname uparams anps as us = do
  udef <- run $ getUniv us uname
  adefs <- run $ mapM (getAgent as . fst) anps
  adefs' <- run $ mapM (joinVars udef) adefs
  upair <- run $ compileUnrestrictedAgent uparams udef
  apairs <- run $ mapM (\(d, p) -> compileModalizedAgent p d) (zip adefs' (map snd anps))
  return (upair, apairs)

doAction :: Agents -> Universes -> GameObject -> IO ()
doAction as us (Play (uname, uparams) anps) = do
  void $ printf "%s(%s)\n" (Text.unpack uname)
    (List.intercalate ("," :: String) (map (Text.unpack . fst) anps))
  (upair, apairs) <- _buildPairs uname uparams anps as us
  (ur, ars) <- run $ simpleMultiCompete upair apairs
  void $ printf "  %s(%s)\n" (Text.unpack ur) (List.intercalate "," $ map Text.unpack ars)
doAction as us (Describe (uname, uparams) anps) = do
  void $ printf "%s(%s)\n" (Text.unpack uname)
    (List.intercalate ("," :: String) (map (Text.unpack . fst) anps))
  (upair, apairs) <- _buildPairs uname uparams anps as us
  cmap <- run $ simpleMultiCompetition upair apairs
  displayTable $ indentTable "  " $ tuplesToTable $ Map.toAscList cmap
  displayTable $ indentTable "  " $ kripkeTable cmap
  (ur, ars) <- run $ simpleMultiCompete upair apairs
  void $ printf "  %s(%s)\n" (Text.unpack ur) (List.intercalate "," $ map Text.unpack ars)
doAction _ _ _ = return ()

playGame :: [GameObject] -> IO ()
playGame objects = do
  let agentDefs = agentList objects
  let universeDefs = universeList objects
  putStr "Universes loaded: "
  print (map agentName agentDefs)
  putStr "Agents loaded: "
  print (map agentName universeDefs)
  putStrLn ""
  let agents = Map.fromList [(agentName a, a) | a <- agentDefs]
  let universes = Map.fromList [(agentName u, u) | u <- universeDefs]
  mapM_ (doAction agents universes) objects

playFile :: FilePath -> IO ()
playFile path = parseFile path >>= playGame
