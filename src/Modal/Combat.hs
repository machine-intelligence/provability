{-# LANGUAGE DeriveFunctor #-}
module Modal.Combat where
import Prelude hiding (mapM, mapM_, sequence, foldr)
import Control.Applicative
import Control.Monad.Identity hiding (mapM, mapM_, sequence)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.Monoid
import Data.Traversable
import Modal.Code
import Modal.Competition
import Modal.Display
import Modal.Environment
import Modal.Formulas hiding (left)
import Modal.Parser
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Text (Parser)
import Text.Printf (printf)
import qualified Data.Map as Map
import qualified Data.Text as Text

-------------------------------------------------------------------------------
-- The type of actions.

data CD = C | D deriving (Eq, Ord, Enum, Read, Show)

instance Parsable CD where
  parser = read . return <$> oneOf "CD"

-------------------------------------------------------------------------------
-- The type of variables as referred to by the code: each agent can refer to
-- itself (in the actual case), the opponent (in the actual case) or the
-- opponent as played against another opponent.

data MeVsThem a o = MeVsThemIs a | ThemVsMeIs o | ThemVsOtherIs Name o deriving (Eq, Ord)

instance (Show a, Show o) => Show (MeVsThem a o) where
  show (MeVsThemIs a) = "Me(Them)=" ++ show a
  show (ThemVsMeIs o) = "Them(Me)=" ++ show o
  show (ThemVsOtherIs n o) = "Them(" ++ Text.unpack n ++ ")=" ++ show o

instance Bifunctor MeVsThem where
  bimap f g = runIdentity . bitraverse (Identity . f) (Identity . g)

instance Bifoldable MeVsThem where
  bifoldMap addA _ (MeVsThemIs a) = addA a
  bifoldMap _ addO (ThemVsMeIs o) = addO o
  bifoldMap _ addO (ThemVsOtherIs _ o) = addO o

instance Bitraversable MeVsThem where
  bitraverse f _ (MeVsThemIs a) = MeVsThemIs <$> f a
  bitraverse _ g (ThemVsMeIs b) = ThemVsMeIs <$> g b
  bitraverse _ g (ThemVsOtherIs other b) = ThemVsOtherIs other <$> g b

instance AgentVar MeVsThem where
  otherAgentsReferencedBy (ThemVsOtherIs n _) = [n]
  otherAgentsReferencedBy _ = []
  makeVParser a o = try mvt <|> try tvm <|> try tvo <?> "a modal variable" where
    mvt = choice [string "Me(Them)", string "Me()"] *> (MeVsThemIs <$> a)
    tvm = choice [string "Them(Me)", string "Them()"] *> (ThemVsMeIs <$> o)
    tvo = string "Them(" *> (ThemVsOtherIs <$> name) <*> (char ')' *> o)

instance Canonicalizable2 MeVsThem where
  canonicalize2 v1 v2 me them = fmap expandName where
    expandName (MeVsThemIs val) = v1 me them val
    expandName (ThemVsMeIs val) = v2 them me val
    expandName (ThemVsOtherIs other val) = v2 them other val

instance IsMultiVarA MeVsThem where
  promoteA names i (MeVsThemIs x) = PlayerPlays names i x
  promoteA names _ (ThemVsMeIs x) = UniversePlays names x
  promoteA names i (ThemVsOtherIs other x) = UniversePlays (alter names i $ const other) x

instance (Parsable a, Parsable o) => Parsable (MeVsThem a o) where
  parser = makeVParser parser parser

-------------------------------------------------------------------------------
-- The type of variables in the "old-style" single-formula format, where "a"
-- stands for "Me vs Them", "b" stands for "Them vs Me", and "xxx" stands for
-- "Them vs xxx" for fairly arbitrary values of xxx.

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
    from o = ThemVs $ Text.pack o

rawToMV :: RawVar -> MeVsThem CD CD
rawToMV MeVsThem = MeVsThemIs C
rawToMV ThemVsMe = ThemVsMeIs C
rawToMV (ThemVs n) = ThemVsOtherIs n C

-------------------------------------------------------------------------------

type ModalDef = ModalizedDef MeVsThem CD CD
type ModalAgent = AgentMap MeVsThem CD CD

data GameObject a
  = Player a
  | Raw Name (ModalFormula RawVar)
  | Play Name Name
  | Describe Name Name
  deriving (Eq, Functor)

instance Show a => Show (GameObject a) where
  show (Player a) = show a
  show (Raw n f) = printf "raw %s %s" (Text.unpack n) (show f)
  show (Play n1 n2) = printf "play %s %s" (Text.unpack n1) (Text.unpack n2)
  show (Describe n1 n2) = printf "describe %s %s" (Text.unpack n1) (Text.unpack n2)

newtype Game a = Game { objects :: [GameObject a] }
  deriving (Eq, Show, Functor)

instance Foldable Game where
  foldMap f = foldMap g . objects where
    g (Player x) = f x
    g _ = mempty

instance Traversable Game where
  traverse f = fmap Game . traverse g . objects where
    g (Player x) = Player <$> f x
    g (Raw a b) = pure $ Raw a b
    g (Play a b) = pure $ Play a b
    g (Describe a b) = pure $ Describe a b

gameObjectParser :: Parser (GameObject ModalDef)
gameObjectParser = try pY <|> try pR <|> try pP <|> try pD where
  pY = Player <$> defParser
  pR = Raw <$> (keyword "raw" *> name <* w1) <*> parser
  pP = Play <$> (keyword "play" *> name <* w1) <*> name
  pD = Describe <$> (keyword "describe" *> name <* w1) <*> name
  defParser = modalizedDefParser parser parser "mine" "theirs" "def"

gameParser :: Parser (Game ModalDef)
gameParser = Game <$> (gameObjectParser `sepEndBy` w) <* eof

players :: Game (Name, ModalAgent) -> [(Name, ModalAgent)]
players g = rawPlayers g ++ foldr (:) [] g where
  rawPlayers (Game []) = []
  rawPlayers (Game (Raw n f : xs)) = (n, f2p f) : rawPlayers (Game xs)
  rawPlayers (Game (_ : xs)) = rawPlayers (Game xs)
  f2p f = Map.fromList [(C, rawToMV <$> f), (D, Neg $ rawToMV <$> f)]

varIsC :: VsVar CD CD -> Bool
varIsC (Vs1 _ _ C) = True
varIsC (Vs2 _ _ C) = True
varIsC _ = False

toCformula :: ModalFormula (VsVar CD CD) -> ModalFormula (VsVar CD CD)
toCformula m = m >>= cify where
  cify (Vs1 x1 x2 D) = Neg (Var $ Vs1 x1 x2 C)
  cify (Vs2 x1 x2 D) = Neg (Var $ Vs2 x1 x2 C)
  cify x = Var x

doAction :: Env MeVsThem CD CD -> GameObject (Name, ModalAgent) -> IO ()
doAction env (Play n1 n2) = do
  void $ printf "%s vs %s:\n" (Text.unpack n1) (Text.unpack n2)
  (r1, r2) <- run (compete env n1 n2)
  void $ printf "  %s=%s, %s=%s\n\n" (Text.unpack n1) (show r1) (Text.unpack n2) (show r2)
doAction env (Describe n1 n2) = do
  void $ printf "%s vs %s:\n\n" (Text.unpack n1) (Text.unpack n2)
  fullCmap <- run (competitionMap env n1 n2)
  let cmap = Map.filterWithKey (const . varIsC) (Map.map toCformula fullCmap)
  displayTable $ indentTable "  " $ tuplesToTable $ Map.toAscList cmap
  displayTable $ indentTable "  " $ kripkeTable cmap
  (r1, r2) <- run (compete env n1 n2)
  printf "  Result: %s=%s, %s=%s\n\n" (Text.unpack n1) (show r1) (Text.unpack n2) (show r2)
doAction _ _ = return ()

playGame :: Game (Name, ModalAgent) -> Env MeVsThem CD CD -> IO ()
playGame game base = do
  env <- run (insertAll base $ players game)
  putStr "Agents loaded: "
  print env
  putStrLn ""
  mapM_ (doAction env) (objects game)

compileFile :: FilePath -> IO (Game (Name, ModalAgent))
compileFile path = do
  game <- runFile (parse gameParser path) path
  run $ mapM (compileModalizedAgent defaultContext) game

playFile :: FilePath -> Env MeVsThem CD CD -> IO ()
playFile path env = compileFile path >>= flip playGame env
