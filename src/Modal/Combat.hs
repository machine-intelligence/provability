{-# LANGUAGE DeriveFunctor #-}
module Modal.Combat where
import Prelude hiding (mapM, mapM_, foldr)
import Control.Applicative
import Data.Monoid
import Modal.Code hiding (Statement(..))
import Modal.Display
import Modal.Formulas
import Modal.Environment
import Modal.Parser
import Modal.Utilities
import Data.Foldable
import qualified Data.Map as M
import Data.Text (Text)
import qualified Data.Text as T
import Data.Traversable
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Printf (printf)

data CD = C | D deriving (Eq, Ord, Enum, Read, Show)
instance Parsable CD where parser = read . return <$> oneOf "CD"

data RawVar = MeVsThem | ThemVsMe | ThemVs Name deriving (Eq, Ord, Show)
instance Read RawVar where
  readsPrec _ str = [(from name, rest) | not $ null name] where
    (name, rest) = case str of
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
  show (Raw name f) = printf "raw %s = %s" (T.unpack name) (show f)
  show (Play n1 n2) = printf "play %s vs %s" (T.unpack n1) (T.unpack n2)
  show (Describe n1 n2) = printf "describe %s vs %s" (T.unpack n1) (T.unpack n2)

instance Parsable a => Parsable (GameObject a) where
  parser = try pPlayer <|> try pRaw <|> try pPlay <|> try pDescribe <?> "a game object" where
    pPlayer = Player <$> parser
    pRaw = Raw <$> (keyword "raw" *> name) <*> (symbol "=" *> parser)
    pPlay = Play <$> (keyword "play" *> name) <*> (keyword "vs" *> name)
    pDescribe = Describe <$> (keyword "describe" *> name) <*> (keyword "vs" *> name)

newtype Game a = Game { objects :: [GameObject a] } deriving (Eq, Show, Functor)
instance Foldable Game where
  foldMap f (Game []) = mempty
  foldMap f (Game ((Player x):xs)) = f x <> foldMap f (Game xs)
  foldMap f (Game (x:xs)) = foldMap f (Game xs)
instance Traversable Game where
  traverse f (Game []) = pure $ Game []
  traverse f (Game ((Player x):xs)) = rejoin <$> f x <*> traverse f (Game xs) where
    rejoin x' (Game ys) = Game ((Player x'):ys)
  traverse f (Game ((Raw n x):xs))
    = (Game . (Raw n x :) . objects) <$> traverse f (Game xs)
  traverse f (Game ((Play n1 n2):xs))
    = (Game . (Play n1 n2 :) . objects) <$> traverse f (Game xs)
  traverse f (Game ((Describe n1 n2):xs))
    = (Game . (Describe n1 n2 :) . objects) <$> traverse f (Game xs)
instance Parsable a => Parsable (Game a) where
  parser = Game <$> (parser `sepEndBy` w) <* eof

parseAndCompileGame :: SourceName -> Text -> Either CompileError (Game (Name, Program CD CD))
parseAndCompileGame = parseAndCompile' parser

compileGameFile :: FilePath -> IO (Game (Name, Program CD CD))
compileGameFile = compileFile' parser

players :: Game (Name, Program CD CD) -> [(Name, Program CD CD)]
players g = (rawPlayers g) ++ (foldr (:) [] g) where
  rawPlayers (Game []) = []
  rawPlayers (Game ((Raw n f):xs)) = (n, f2p f) : rawPlayers (Game xs)
  rawPlayers (Game (x:xs)) = rawPlayers (Game xs)
  f2p f a = let f' = mapVariable rawToMV f in if a == C then f' else Neg f'

doAction :: Env CD CD -> GameObject (Name, Program CD CD) -> IO ()
doAction env (Player _) = return ()
doAction env (Raw _ _) = return ()
doAction env (Play n1 n2) = do
  printf "%s vs %s:\n" (T.unpack n1) (T.unpack n2)
  (r1, r2) <- run (compete env n1 n2)
  printf "  %s=%s, %s=%s\n\n" (T.unpack n1) (show r1) (T.unpack n2) (show r2)
doAction env (Describe n1 n2) = do
  printf "%s vs %s:\n\n" (T.unpack n1) (T.unpack n2)
  fullCmap <- run (competitionMap env n1 n2)
  let isCvar v = case v of
                  Vs1 _ _ C -> True
                  Vs2 _ _ C -> True
                  _ -> False
  let toC = joinVariable $ \v -> case v of
                                Vs1 n1 n2 D -> Neg (Var $ Vs1 n1 n2 C)
                                Vs2 n1 n2 D -> Neg (Var $ Vs2 n1 n2 C)
                                x -> Var x
  let cmap = M.filterWithKey (const . isCvar) (M.map toC fullCmap)
  displayTable $ indentTable "  " $ mapToTable cmap
  putStrLn ""
  displayTable $ indentTable "  " $ kripkeTable cmap
  (r1, r2) <- run (compete env n1 n2)
  printf "  Result: %s=%s, %s=%s\n\n" (T.unpack n1) (show r1) (T.unpack n2) (show r2)

playGame :: Game (Name, Program CD CD) -> Env CD CD -> IO ()
playGame game base = do
  env <- run (insertAll base $ players game)
  putStr "Agents loaded: "
  print env
  putStrLn ""
  mapM_ (doAction env) (objects game)

playFile :: FilePath -> Env CD CD -> IO ()
playFile fp env = compileGameFile fp >>= flip playGame env
