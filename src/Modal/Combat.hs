{-# LANGUAGE DeriveFunctor #-}
module Modal.Combat where
import Prelude hiding (mapM, mapM_, foldr)
import Control.Applicative
import Control.Monad (void)
import Data.Monoid
import Modal.Code
import Modal.Display
import Modal.Formulas
import Modal.Environment
import Modal.Competition (compete, competitionMap, VsVar(..))
import Modal.Parser
import Modal.Programming
import Modal.Utilities
import Data.Foldable
import qualified Data.Map as M
import qualified Data.Text as T
import Data.Traversable
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Text (Parser)
import Text.Printf (printf)

data CD = C | D deriving (Eq, Ord, Enum, Read, Show)
instance Parsable CD where parser = read . return <$> oneOf "CD"

type ModalAgent = ModalizedAgent ModalVar CD CD

data RawVar = MeVsThem | ThemVsMe | ThemVs Name deriving (Eq, Ord, Show)
instance Read RawVar where
  readsPrec _ str = [(from n, rest) | not $ null n] where
    (n, rest) = case str of
      [] -> ("", [])
      (x:xs) -> if isNameFirstChar x
        then (x : takeWhile isNameChar xs, dropWhile isNameChar xs)
        else ("", [])
    from "a" = MeVsThem
    from "b" = ThemVsMe
    from o = ThemVs $ T.pack o

rawToMV :: RawVar -> ModalVar CD CD
rawToMV MeVsThem = MeVsThemIs C
rawToMV ThemVsMe = ThemVsMeIs C
rawToMV (ThemVs n) = ThemVsOtherIs n C

data GameObject a
  = Player a
  | Raw Name (ModalFormula RawVar)
  | Play Name Name
  | Describe Name Name
  deriving (Eq, Functor)

instance Show a => Show (GameObject a) where
  show (Player a) = show a
  show (Raw n f) = printf "raw %s %s" (T.unpack n) (show f)
  show (Play n1 n2) = printf "play %s %s" (T.unpack n1) (T.unpack n2)
  show (Describe n1 n2) = printf "describe %s %s" (T.unpack n1) (T.unpack n2)


newtype Game a = Game { objects :: [GameObject a] } deriving (Eq, Show, Functor)

instance Foldable Game where
  foldMap _ (Game []) = mempty
  foldMap f (Game (Player x : xs)) = f x <> foldMap f (Game xs)
  foldMap f (Game (_ : xs)) = foldMap f (Game xs)

instance Traversable Game where
  traverse _ (Game []) = pure $ Game []
  traverse f (Game (Player x : xs)) = rejoin <$> f x <*> traverse f (Game xs) where
    rejoin x' (Game ys) = Game (Player x' : ys)
  traverse f (Game (Raw n x : xs))
    = (Game . (Raw n x :) . objects) <$> traverse f (Game xs)
  traverse f (Game (Play n1 n2 : xs))
    = (Game . (Play n1 n2 :) . objects) <$> traverse f (Game xs)
  traverse f (Game (Describe n1 n2 : xs))
    = (Game . (Describe n1 n2 :) . objects) <$> traverse f (Game xs)

gameObjectParser :: Parser (GameObject ModalAgent)
gameObjectParser = try pY <|> try pR <|> try pP <|> try pD <?> "a game object" where
  pY = Player <$> agentParser
  pR = Raw <$> (keyword "raw" *> name <* w1) <*> parser
  pP = Play <$> (keyword "play" *> name <* w1) <*> name
  pD = Describe <$> (keyword "describe" *> name <* w1) <*> name
  agentParser = modalizedAgentParser parser parser "mine" "theirs" "def"

gameParser :: Parser (Game ModalAgent)
gameParser = Game <$> (gameObjectParser `sepEndBy` w) <* eof

players :: Game (Name, Program ModalVar CD CD) -> [(Name, Program ModalVar CD CD)]
players g = rawPlayers g ++ foldr (:) [] g where
  rawPlayers (Game []) = []
  rawPlayers (Game (Raw n f : xs)) = (n, ModalProgram $ f2p f) : rawPlayers (Game xs)
  rawPlayers (Game (_ : xs)) = rawPlayers (Game xs)
  f2p f a = let f' = rawToMV <$> f in if a == C then f' else Neg f'

doAction :: Env ModalVar CD CD -> GameObject (Name, Program ModalVar CD CD) -> IO ()
doAction env (Play n1 n2) = do
  void $ printf "%s vs %s:\n" (T.unpack n1) (T.unpack n2)
  (r1, r2) <- run (compete env n1 n2)
  void $ printf "  %s=%s, %s=%s\n\n" (T.unpack n1) (show r1) (T.unpack n2) (show r2)
doAction env (Describe n1 n2) = do
  void $ printf "%s vs %s:\n\n" (T.unpack n1) (T.unpack n2)
  fullCmap <- run (competitionMap env n1 n2)
  let isCvar v = case v of
                  Vs1 _ _ C -> True
                  Vs2 _ _ C -> True
                  _ -> False
  let toC m = m >>= \v -> case v of
                            Vs1 x1 x2 D -> Neg (Var $ Vs1 x1 x2 C)
                            Vs2 x1 x2 D -> Neg (Var $ Vs2 x1 x2 C)
                            x -> Var x
  let cmap = M.filterWithKey (const . isCvar) (M.map toC fullCmap)
  displayTable $ indentTable "  " $ tuplesToTable $ M.toAscList cmap
  displayTable $ indentTable "  " $ kripkeTable cmap
  (r1, r2) <- run (compete env n1 n2)
  printf "  Result: %s=%s, %s=%s\n\n" (T.unpack n1) (show r1) (T.unpack n2) (show r2)
doAction _ _ = return ()

playGame :: Game (Name, Program ModalVar CD CD) -> Env ModalVar CD CD -> IO ()
playGame game base = do
  env <- run (insertAll base $ players game)
  putStr "Agents loaded: "
  print env
  putStrLn ""
  mapM_ (doAction env) (objects game)

compileFile :: FilePath -> IO (Game (Name, Program ModalVar CD CD))
compileFile path = do
  game <- runFile (parse gameParser path) path
  run $ mapM (compileModalizedAgent defaultContext) game

playFile :: FilePath -> Env ModalVar CD CD -> IO ()
playFile path env = compileFile path >>= flip playGame env where
