{-# LANGUAGE TypeFamilies #-}
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
import Modal.Competition
import Modal.Display
import Modal.Formulas
import Modal.Parser (Parsable, parser)
import Modal.Statement
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Printf (printf)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified Modal.Parser as P

newtype A = A Text deriving (Eq, Ord)
instance Show A where show (A a) = '@' : Text.unpack a
instance Parsable A where parser = char '@' *> P.name <$$> A

newtype U = U Text deriving (Eq, Ord)
instance Show U where show (U u) = '$' : Text.unpack u
instance Parsable U where parser = char '$' *> P.name <$$> U

data BiVar m t = Me m | Them t deriving (Eq, Ord)
instance (Show a, Show o) => Show (BiVar a o) where
  show (Me m) = printf "Me(Them)=%s" (show m)
  show (Them t) = printf "Them(Me)=%s" (show t)
instance Bifunctor BiVar where
  bimap f g = runIdentity . bitraverse (Identity . f) (Identity . g)
instance Bifoldable BiVar where
  bifoldMap f _ (Me m) = f m
  bifoldMap _ g (Them t) = g t
instance Bitraversable BiVar where
  bitraverse f _ (Me m) = Me <$> f m
  bitraverse _ g (Them t) = Them <$> g t
instance AgentVar BiVar where
  makeAgentVarParser m t = try mvt <|> try tvm <?> "a modal variable" where
    mvt = choice [string "Me(Them)", string "Me()"] *> (Me <$> m)
    tvm = choice [string "Them(Me)", string "Them()"] *> (Them <$> t)
instance Canonicalizable2 BiVar where
  canonicalize2 v1 v2 = fmap expandName where
    expandName (Me val) = v1 val
    expandName (Them val) = v2 Nothing val
instance (Parsable m, Parsable t) => Parsable (BiVar m t) where
  parser = makeAgentVarParser parser parser
instance IsMultiVarA BiVar where
  promoteA names i (Me x) = PlayerNPlays names i x
  promoteA names _ (Them x) = UniversePlays names x

data MultiVar u a = UPlays u | ANPlays Int a deriving (Eq, Ord)
instance (Show a, Show o) => Show (MultiVar a o) where
  show (UPlays u) = printf "U(...)=%s" (show u)
  show (ANPlays i a) = printf "A%d(U)=%s" i (show a)
instance Bifunctor MultiVar where
  bimap f g = runIdentity . bitraverse (Identity . f) (Identity . g)
instance Bifoldable MultiVar where
  bifoldMap f _ (UPlays u) = f u
  bifoldMap _ g (ANPlays _ a) = g a
instance Bitraversable MultiVar where
  bitraverse f _ (UPlays u) = UPlays <$> f u
  bitraverse _ g (ANPlays i a) = ANPlays i <$> g a
instance AgentVar MultiVar where
  makeAgentVarParser u a = try aPlays <|> try uPlays <?> "a universe variable" where
    anum = string "A" *> option 1 parser
    aPlays = ANPlays <$> choice [anum <* string "()", anum <* string "(U)"] <*> a
    uPlays = UPlays <$> (string "U()" *> u)
instance Canonicalizable2 MultiVar where
  canonicalize2 v1 v2 = fmap expandName where
    expandName (UPlays val) = v1 val
    expandName (ANPlays _ val) = v2 Nothing val
instance (Parsable u, Parsable a) => Parsable (MultiVar u a) where
  parser = makeAgentVarParser parser parser
instance IsMultiVarU MultiVar where
  promoteU names (UPlays x) = UniversePlays names x
  promoteU names (ANPlays i x) = PlayerNPlays names i x

newtype AStatement = AStatement { getAStatement :: ModalizedStatement BiVar A U }
  deriving Show
instance IsStatement AStatement where
  type Var AStatement = BiVar
  type Act AStatement = A
  type Out AStatement = U
  makeStatementParser = fmap AStatement .: modalizedStatementParser
  evalStatement = evalModalizedStatement . getAStatement

newtype UStatement = UStatement { getUStatement :: UnrestrictedStatement MultiVar U A }
  deriving Show
instance IsStatement UStatement where
  type Var UStatement = MultiVar
  type Act UStatement = U
  type Out UStatement = A
  makeStatementParser = fmap UStatement .: unrestrictedStatementParser
  evalStatement = evalUnrestrictedStatement . getUStatement

type Agent = Def AStatement
type Agents = Map Name Agent

type Universe = Def UStatement
type Universes = Map Name Universe

data GameObject
  = Agent (Def AStatement)
  | Universe (Def UStatement)
  | Play (Name, Parameters U A) [(Name, Parameters A U)]
  | Describe (Name, Parameters U A) [(Name, Parameters A U)]
  deriving Show

instance Parsable GameObject where
  parser = try a <|> try u <|> try (play Play "play") <|> play Describe "describe" where
    a = Agent <$> defParser parser parser "actions" "outcomes" "agent"
    u = Universe <$> defParser parser parser "outcomes" "actions" "universe"
    play make word = P.keyword word *> (make <$> callU <*> many1 callA)
    callU = (,) <$> P.name <*> paramsParser parser parser
    callA = (,) <$> P.name <*> paramsParser parser parser

getAgent :: Agents -> Name -> Either CompileError Agent
getAgent as n = maybe (Left $ UnknownName n) Right (Map.lookup n as)

getUniv :: Universes -> Name -> Either CompileError Universe
getUniv as n = maybe (Left $ UnknownName n) Right (Map.lookup n as)

gameParser :: Parsec Text s [GameObject]
gameParser = (parser `sepEndBy` P.w) <* eof

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

joinVars :: Universe -> Agent -> Either CompileError Agent
joinVars u a = do
  acts <- ensureCompatible (agentName a) "actions" (agentOutcomes u) (agentActions a)
  outs <- ensureCompatible (agentName a) "outcomes" (agentActions u) (agentOutcomes a)
  return a{agentActions=acts, agentOutcomes=outs}

ensureCompatible :: Eq x =>
  Name -> String -> Maybe x -> Maybe x -> Either CompileError (Maybe x)
ensureCompatible name str x y = case (x, y) of
  (Nothing, Nothing) -> return Nothing
  (Just xs, Nothing) -> return $ Just xs
  (Nothing, Just ys) -> return $ Just ys
  (Just xs, Just ys)
    | xs == ys  -> return (Just xs)
    | otherwise -> Left (Mismatch name str)

buildCompetition ::
  Name -> Parameters U A -> [(Name, Parameters A U)] -> Agents -> Universes ->
  IO ((Name, AgentMap UStatement), [(Name, AgentMap AStatement)])
buildCompetition uname uparams anps as us = do
  udef <- run $ getUniv us uname
  adefs <- run $ mapM (getAgent as . fst) anps
  adefs' <- run $ mapM (joinVars udef) adefs
  upair <- run $ compile uparams udef
  apairs <- run $ mapM (\(d, p) -> compile p d) (zip adefs' (map snd anps))
  return (upair, apairs)

doAction :: Agents -> Universes -> GameObject -> IO ()
doAction as us (Play (uname, uparams) anps) = do
  void $ printf "%s(%s)\n" (Text.unpack uname)
    (List.intercalate ("," :: String) (map (Text.unpack . fst) anps))
  (upair, apairs) <- buildCompetition uname uparams anps as us
  let (ur, ars) = simpleMultiCompete upair apairs
  void $ printf "  %s(%s)\n" (show ur) (List.intercalate "," $ map show ars)
doAction as us (Describe (uname, uparams) anps) = do
  void $ printf "%s(%s)\n" (Text.unpack uname)
    (List.intercalate ("," :: String) (map (Text.unpack . fst) anps))
  (upair, apairs) <- buildCompetition uname uparams anps as us
  let cmap = simpleMultiCompetition upair apairs
  displayTable $ indentTable "  " $ tuplesToTable $ Map.toAscList cmap
  displayTable $ indentTable "  " $ kripkeTable cmap
  let (ur, ars) = simpleMultiCompete upair apairs
  void $ printf "  %s(%s)\n" (show ur) (List.intercalate "," $ map show ars)
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
