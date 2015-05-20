{-# LANGUAGE TypeFamilies #-}
module Modal.Universes where
import Prelude hiding (mapM, mapM_, sequence, foldr)
import Control.Applicative
import Control.Monad.Identity hiding (mapM, mapM_, sequence)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.Maybe (fromMaybe)
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

newtype A = A String deriving (Eq, Ord)
instance Show A where show (A a) = '@' : a
instance Parsable A where parser = char '@' *> P.anyname <$$> A
instance Read A where
  readsPrec _ ('@':xs) = [(A x, rest) | not $ null x] where
    (x, rest) = (takeWhile P.isNameChar xs, dropWhile P.isNameChar xs)
  readsPrec _ _ = []

newtype U = U String deriving (Eq, Ord)
instance Show U where show (U u) = '$' : u
instance Parsable U where parser = char '$' *> P.anyname <$$> U
instance Read U where
  readsPrec _ ('$':xs) = [(U x, rest) | not $ null x] where
    (x, rest) = (takeWhile P.isNameChar xs, dropWhile P.isNameChar xs)
  readsPrec _ _ = []

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
  makeAgentVarParser m t = try mvt <|> try tvm <?> "a variable" where
    mvt = choice [string "A()", string "Me()"] *> (Me <$> m)
    tvm = choice [string "U()", string "Them()"] *> (Them <$> t)
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
instance (Parsable u, Parsable a) => Read (MultiVar u a) where
  readsPrec _ s = case parse (parser <* eof) "reading multivar" (Text.pack s) of
    Right result -> [(result,"")]
    Left err -> error $ show err

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

data Call x y = Call
  { callName :: Name
  , callParams :: Parameters x y
  , callAlias :: Maybe Name
  } deriving (Eq, Ord, Show)

callSign :: (Show x, Show y) => Call x y -> Name
callSign call = fromMaybe (callHeader call) (callAlias call)

callHeader :: (Show x, Show y) => Call x y -> String
callHeader (Call name params _) = name ++ renderParams params

instance (Parsable x, Parsable y) => Parsable (Call x y) where
  parser = Call <$> P.name <*> paramsParser parser parser <*> alias where
    alias = optional (P.keyword "as" *> P.name)

data GameObject
  = Agent (Def AStatement)
  | Universe (Def UStatement)
  | Play (Call U A) [Call A U]
  | Describe (Call U A) [Call A U]
  deriving Show

-- TODO: This needs refactoring. It should probably go into Code.hs somehow.
-- Also, the syntax is quite bad; consider removing the need for a "where" and
-- for the semicolons.
universeMapParser :: Parsec Text u (Def UStatement)
universeMapParser = do
  n <- P.keyword "umap" *> P.name
  ps <- option [] (try $ defargsParser parser parser)
  (as, os) <- defordersParser "outcomes" "actions" parser parser
  P.keyword "where"
  c <- FullMap <$> codeMapParser parser parser
  P.keyword "end"
  return $ Def ps as os n c

instance Parsable GameObject where
  parser = try a <|> try u <|> try umap <|> try p <|> d where
    a = Agent <$> defParser parser parser "actions" "outcomes" "agent"
    u = Universe <$> defParser parser parser "outcomes" "actions" "universe"
    p = play Play "play"
    d = play Describe "describe"
    play make word = P.keyword word *> P.parens maker where
      maker = (make <$> (parser <* P.comma) <*> parser `sepEndBy1` P.comma)
    umap = Universe <$> universeMapParser

getAgent :: Agents -> Call A U -> Either CompileError Agent
getAgent amap (Call aname _ _) = maybe (Left $ UnknownName aname) Right (Map.lookup aname amap)

getUniv :: Universes -> Call U A -> Either CompileError Universe
getUniv umap (Call uname _ _) = maybe (Left $ UnknownName uname) Right (Map.lookup uname umap)

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

-- TODO: I'm not sure excatly what should happen when there are incompatible
-- actions/outcomes. Right now I just let things beak.  (Remember that it *is*
-- ok for the agents to have different orderings on the same action/outcome
-- set.)
joinVars :: Universe -> Agent -> Either CompileError Agent
joinVars u a = do
  acts <- rightBiased (defOutcomes u) (defActions a)
  outs <- rightBiased (defActions u) (defOutcomes a)
  return a{defActions=acts, defOutcomes=outs}

rightBiased :: Maybe x -> Maybe x -> Either CompileError (Maybe x)
rightBiased x y = case (x, y) of
  (Nothing, Nothing) -> return Nothing
  (Just xs, Nothing) -> return $ Just xs
  (Nothing, Just ys) -> return $ Just ys
  (Just _ , Just ys) -> return $ Just ys

buildCompetition ::
  Call U A -> [Call A U] -> Agents -> Universes ->
  IO ((Name, CompiledAgent UStatement), [(Name, CompiledAgent AStatement)])
buildCompetition ucall acalls amap umap = do
  udef <- run $ getUniv umap ucall
  adefs <- run $ mapM (getAgent amap) acalls
  adefs' <- run $ mapM (joinVars udef) adefs
  uprog <- run $ compile (callParams ucall) udef
  aprogs <- run $ mapM (\(d, p) -> compile p d) (zip adefs' $ map callParams acalls)
  let uname = callSign ucall
  let anames = map callSign acalls
  return ((uname, uprog), zip anames aprogs)

showHeader :: Call U A -> [Call A U] -> IO ()
showHeader ucall acalls = void $ printf "%s, %s:\n" un ans where
  un = callHeader ucall
  ans = List.intercalate (", " :: String) (map callHeader acalls)

showResults :: (Name, CompiledAgent UStatement) -> [(Name, CompiledAgent AStatement)] -> IO ()
showResults upair apairs = void $ printf "%s=%s, %s\n\n" un (show u) alist where
  un = fst upair
  (u, as) = simpleMultiCompete upair apairs
  showA n a = printf "%s=%s" n (show a) :: String
  alist = List.intercalate (", " :: String) (zipWith showA (map fst apairs) as)

doAction :: Agents -> Universes -> GameObject -> IO ()
doAction amap umap (Play ucall acalls) = do
  showHeader ucall acalls
  (upair, apairs) <- buildCompetition ucall acalls amap umap
  putStr "  "
  showResults upair apairs
doAction amap umap (Describe ucall acalls) = do
  showHeader ucall acalls
  (upair, apairs) <- buildCompetition ucall acalls amap umap
  let cmap = simpleMultiCompetition upair apairs
  displayTable $ indentTable "  " $ tuplesToTable $ Map.toAscList cmap
  displayTable $ indentTable "  " $ kripkeTable cmap
  putStr "  "
  showResults upair apairs
doAction _ _ _ = return ()

playGame :: [GameObject] -> IO ()
playGame objects = do
  let agentDefs = agentList objects
  let universeDefs = universeList objects
  putStr "Universes loaded: "
  void $ printf "{ %s }\n" $ List.intercalate ", " (map defName universeDefs)
  putStr "Agents loaded: "
  void $ printf "{ %s }\n" $ List.intercalate ", " (map defName agentDefs)
  putStrLn ""
  let agents = Map.fromList [(defName a, a) | a <- agentDefs]
  let universes = Map.fromList [(defName u, u) | u <- universeDefs]
  mapM_ (doAction agents universes) objects

playFile :: FilePath -> IO ()
playFile path = parseFile path >>= playGame
