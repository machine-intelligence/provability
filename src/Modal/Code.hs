{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Modal.Code
  ( Program
  , CompileError
  , Agent(..)
  , compile
  , parseAndCompile
  , compileFile
  , Void(..)
  , ContextError(..)
  , ParseError(..)
  , ModalVar(..)
  , V(..)
  , vParser
  , Relation(..)
  , relationParser
  , Expr(..)
  , Range(..)
  , rangeParser
  , elemsIn
  , CodeFragment(..)
  , codeFragmentParser
  , evalCodeFragment
  , Code(..)
  , codeParser
  , evalCode
  , codeToFormula
  ) where
import Prelude hiding (readFile, sequence, mapM)
import Control.Applicative
import Control.Arrow (second)
import Control.Monad (void)
import Control.Monad.Except hiding (mapM, sequence)
import Control.Monad.State hiding (mapM, sequence)
import Data.Map (Map)
import Data.Functor.Identity
import Data.Traversable (Traversable, sequence, mapM)
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Maybe (isJust)
import Data.Monoid ((<>))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.IO (readFile)
import Modal.Formulas (ModalFormula, (%^), (%|))
import qualified Modal.Formulas as L
import Modal.Programming hiding (modalProgram)
import Modal.GameTools (ModalProgram)
import Modal.Display
import Modal.Parser
import Modal.Utilities
import System.Exit (exitFailure)
import System.IO (stderr, hPutStrLn)
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Expr
import Text.Parsec.Text (Parser)
import Text.Printf (printf)

-- GOAL:
--
-- def UDT(U):
--   let $level = 0
--   for $o in theirActions
--     for $a in myActions
--        if □⌜UDT(U)=$a → U(UDT)=$o⌝
--          return $a
--        let $level = $level + 1

-------------------------------------------------------------------------------

data Void
instance Eq Void
instance Ord Void
instance Read Void
instance Show Void
instance Parsable Void where parser = fail "Cannot instantiate the Void."

-------------------------------------------------------------------------------

type Program a o = ModalProgram (ModalVar a o) a
type CompileError = Either ParseError ContextError

data Agent a o = Agent { agentName :: Name, sourceCode :: Code a o } deriving Eq
instance (Show a, Show o) => Blockable (Agent a o) where
  blockLines (Agent n c) =
    (0, T.pack $ printf "def %s" (T.unpack n)) : increaseIndent (blockLines c)
instance (Show a, Show o) => Show (Agent a o) where
  show = T.unpack . renderBlock
instance (Ord a, Parsable a, Ord o, Parsable o) => Parsable (Agent a o) where
  parser = Agent <$> (keyword "def" *> name) <*> parser

compile :: (Eq a, Eq o) => [a] -> [o] -> Agent a o -> Either ContextError (Name, Program a o)
compile as os (Agent n c) = second (L.simplify .) . (n,) <$> codeToFormula as os c

parseAndCompile :: (Eq a, Eq o, Traversable t) =>
  [a] -> [o] -> Parser (t (Agent a o)) -> SourceName -> Text ->
  Either CompileError (t (Name, Program a o))
parseAndCompile as os p = either pErr (either cErr Right . compileAll) .: parse p where
  compileAll = mapM $ compile as os
  pErr = Left . Left
  cErr = Left . Right

compileFile :: (Eq a, Eq o, Traversable t) =>
  [a] -> [o] -> Parser (t (Agent a o)) -> FilePath ->
  IO (t (Name, Program a o))
compileFile as os p fname = do
  txt <- readFile fname
  let showErr = either show (printf "Error: %s" . show)
  let handleErr = (>> exitFailure) . hPutStrLn stderr . showErr
  either handleErr return $ parseAndCompile as os p fname txt

-------------------------------------------------------------------------------

data Context a o = C
  { avars :: Map Name a
  , ovars :: Map Name o
  , nvars :: Map Name Int
  , alist :: [a]
  , olist :: [o]
  } deriving (Eq, Show)

data ContextError
  = UnknownAVar Name
  | UnknownOVar Name
  | UnknownNVar Name
  deriving (Eq, Ord)

instance Show ContextError where
  show (UnknownAVar n) = printf "action variable %s is undefined" (show n)
  show (UnknownOVar n) = printf "outcome variable %s is undefined" (show n)
  show (UnknownNVar n) = printf "number variable %s is undefined" (show n)

type Contextual a o m = (Applicative m, MonadState (Context a o) m, MonadError ContextError m)
type Evalable a o m = (Eq a, Eq o, Contextual a o m)

emptyContext :: [a] -> [o] -> Context a o
emptyContext = C Map.empty Map.empty Map.empty

withA :: Name -> a -> Context a o -> Context a o
withA n a c = c{avars=Map.insert n a $ avars c}

withO :: Name -> o -> Context a o -> Context a o
withO n o c = c{ovars=Map.insert n o $ ovars c}

withN :: Name -> Int -> Context a o -> Context a o
withN n i c = c{nvars=Map.insert n i $ nvars c}

getA :: Contextual a o m => V a -> m a
getA (Ref n) = maybe (throwError $ UnknownAVar n) return . Map.lookup n . avars =<< get
getA (Lit a) = return a

getO :: Contextual a o m => V o -> m o
getO (Ref n) = maybe (throwError $ UnknownOVar n) return . Map.lookup n . ovars =<< get
getO (Lit o) = return o

getN :: Contextual a o m => V Int -> m Int
getN (Ref n) = maybe (throwError $ UnknownNVar n) return . Map.lookup n . nvars =<< get
getN (Lit i) = return i

getAs :: Contextual a o m => m [a]
getAs = alist <$> get

getOs :: Contextual a o m => m [o]
getOs = olist <$> get

defaultAction :: Contextual a o m => m a
defaultAction = head <$> getAs

-------------------------------------------------------------------------------

data ModalVar a o = MeVsThemIs a | ThemVsMeIs o | ThemVsOtherIs Name o deriving (Eq, Ord)
instance (Show a, Show o) => Show (ModalVar a o) where
  show (MeVsThemIs a) = "Me(Them)=" ++ show a
  show (ThemVsMeIs o) = "Them(Me)=" ++ show o
  show (ThemVsOtherIs n o) = "Them(" ++ T.unpack n ++ ")=" ++ show o

evalVar :: Contextual a o m =>
  ModalVar (Relation a) (Relation o) -> m (ModalFormula (ModalVar a o))
evalVar (MeVsThemIs rel) = evalRelation getA MeVsThemIs rel
evalVar (ThemVsMeIs rel) = evalRelation getO ThemVsMeIs rel
evalVar (ThemVsOtherIs name rel) = evalRelation getO (ThemVsOtherIs name) rel

-------------------------------------------------------------------------------

data V a = Ref Name | Lit a deriving (Eq, Ord, Read)
instance Show a => Show (V a) where
  show (Ref name) = '$' : T.unpack name
  show (Lit x) = show x
instance Parsable a => Parsable (V a) where
  parser = vParser parser

vParser :: Parser x -> Parser (V x)
vParser p =   try (Lit <$> p)
          <|> try (Ref <$> (char '$' *> name))
          <?> "a variable"

-------------------------------------------------------------------------------

data Relation a
  = Equals (V a)
  | NotEquals (V a)
  | In (Set (V a))
  | NotIn (Set (V a))
  deriving (Eq, Ord)
instance Show a => Show (Relation a) where
  show (Equals v) = "=" ++ show v
  show (NotEquals v) = "≠" ++ show v
  show (In v) = "∈{" ++ List.intercalate "," (map show $ Set.toList v) ++ "}"
  show (NotIn v) = "∉{" ++ List.intercalate "," (map show $ Set.toList v) ++ "}"
instance (Ord a, Parsable a) => Parsable (Relation a) where
  parser = relationParser parser

relationParser :: Ord x => Parser x -> Parser (Relation x)
relationParser p =   try (Equals <$> (sEquals *> vParser p))
                 <|> try (NotEquals <$> (sNotEquals *> vParser p))
                 <|> try (In <$> (sIn *> setParser (vParser p)))
                 <|> try (NotIn <$> (sNotIn *> setParser (vParser p)))
                 <?> "a relation"

evalRelation :: Contextual a o m =>
  (V x -> m x) -> (x -> v) -> Relation x -> m (ModalFormula v)
evalRelation extract make (Equals var) = L.Var . make <$> extract var
evalRelation extract make (NotEquals var) = L.Neg <$> evalRelation extract make (Equals var)
evalRelation extract make (In vs)
  | Set.null vs = return $ L.Val False
  | otherwise = foldr1 L.Or <$> mapM (evalRelation extract make . Equals) (Set.toList vs)
evalRelation extract make (NotIn vs)
  | Set.null vs = return $ L.Val True
  | otherwise = foldr1 L.And <$> mapM (evalRelation extract make . NotEquals) (Set.toList vs)

-------------------------------------------------------------------------------

data Expr
  = Num (V Int)
  | Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr
  | Exp Expr Expr
  deriving Eq
instance Show Expr where
  show (Num v) = show v
  show (Add x y) = show x ++ "+" ++ show y
  show (Sub x y) = show x ++ "-" ++ show y
  show (Mul x y) = show x ++ "*" ++ show y
  show (Exp x y) = show x ++ "^" ++ show y
instance Parsable Expr where
  parser = buildExpressionParser lTable term where
    lTable =
      [ [Infix (try $ symbol "+" $> Add) AssocRight]
      , [Infix (try $ symbol "-" $> Sub) AssocRight]
      , [Infix (try $ symbol "*" $> Mul) AssocRight]
      , [Infix (try $ symbol "^" $> Exp) AssocRight] ]
    term
      =   parens parser
      <|> try (Num <$> (parser :: Parser (V Int)))
      <?> "a math expression"

evalExpr :: Contextual a o m => Expr -> m Int
evalExpr (Num v) = getN v
evalExpr (Add x y) = (+) <$> evalExpr x <*> evalExpr y
evalExpr (Sub x y) = (-) <$> evalExpr x <*> evalExpr y
evalExpr (Mul x y) = (*) <$> evalExpr x <*> evalExpr y
evalExpr (Exp x y) = (^) <$> evalExpr x <*> evalExpr y

-------------------------------------------------------------------------------

data Range m x
  = EnumRange (m x) (Maybe (m x)) (Maybe (m Int))
  | ListRange [m x]
  | TotalRange
instance (Eq (m x), Eq (m Int)) => Eq (Range m x) where
  (EnumRange sta sto ste) == (EnumRange sta' sto' ste') =
    (sta, sto, ste) == (sta', sto', ste')
  (ListRange xs) == (ListRange ys) = xs == ys
  TotalRange == TotalRange = True
  _ == _ = False
instance (Show (m x), Show (m Int)) => Show (Range m x) where
  show (EnumRange sta msto mste) = printf "%s..%s%s" (show sta) x y where
    x = maybe ("" :: String) show msto
    y = maybe ("" :: String) (printf " by %s" . show) mste
  show (ListRange xs) = printf "[%s]" (List.intercalate ", " $ map show xs)
  show TotalRange = "..."
instance (Parsable (m x), Parsable (m Int)) => Parsable (Range m x) where
  parser = rangeParser parser parser

rangeParser :: Parser (m Int) -> Parser (m x) -> Parser (Range m x)
rangeParser n x = try rEnum <|> try rList <|> try rAll <?> "a range" where
    rEnum = EnumRange <$> (x <* symbol "..") <*> optional x <*> pEnumBy
    pEnumBy = optional (try $ keyword "by" *> n)
    rList = ListRange <$> listParser x
    rAll = symbol "..." $> TotalRange

boundedRange :: (Parsable (m x), Parsable (m Int)) => Parser (Range m x)
boundedRange = try rBoundedEnum <|> try rList <?> "a bounded range" where
  rBoundedEnum = EnumRange <$> (parser <* symbol "..") <*> (Just <$> parser) <*> pEnumBy
  pEnumBy = optional (try $ keyword "by" *> parser)
  rList = ListRange <$> parser

elemsIn :: (Enum x, Applicative m, Monad m) =>
  (v Int -> m Int) -> (v x -> m x) -> Range v x -> m [x]
elemsIn getNum getX rng = case rng of
  TotalRange -> pure enumerate
  EnumRange sta Nothing Nothing -> enumFrom <$> getX sta
  EnumRange sta (Just sto) Nothing -> enumFromTo <$> getX sta <*> getX sto
  EnumRange sta Nothing (Just ste) ->
    getX sta >>= \s -> enumFromThen s . toThen s <$> getNum ste
  EnumRange sta (Just sto) (Just ste) ->
    getX sta >>= \s -> enumFromThenTo s . toThen s <$> getNum ste <*> getX sto
  ListRange xs -> mapM getX xs
  where toThen sta ste = toEnum $ fromEnum sta + ste

elemsInContext :: (Eq x, Evalable a o m) => (m [x]) -> (V x -> m x) -> Range V x -> m [x]
elemsInContext getXs _    TotalRange = getXs
elemsInContext _     getX (ListRange xs) = mapM getX xs
elemsInContext getXs getX (EnumRange sta msto mste) = renum msto mste where
  renum Nothing    Nothing    = dropWhile . (/=) <$> getX sta <*> getXs
  renum (Just sto) Nothing    = takeWhile . (/=) <$> getX sto <*> renum Nothing Nothing
  renum _          (Just ste) = every <$> getN ste <*> renum msto Nothing
  every n xs = case drop (pred n) xs of
                 (y:ys) -> y : every n ys
                 [] -> []

-------------------------------------------------------------------------------

data Statement oa oo a o
  = Val Bool
  | Var (ModalVar (Relation oa) (Relation oo))
  | Neg (Statement oa oo a o)
  | And (Statement oa oo a o) (Statement oa oo a o)
  | Or (Statement oa oo a o) (Statement oa oo a o)
  | Imp (Statement oa oo a o) (Statement oa oo a o)
  | Iff (Statement oa oo a o) (Statement oa oo a o)
  | Consistent (V Int)
  | Provable (V Int) (Statement a o a o)
  | Possible (V Int) (Statement a o a o)
  deriving Eq

data ShowStatement = ShowStatement {
  topSymbol :: String,
  botSymbol :: String,
  notSymbol :: String,
  andSymbol :: String,
  orSymbol  :: String,
  impSymbol :: String,
  iffSymbol :: String,
  conSign :: String -> String,
  boxSign :: String-> String,
  diaSign :: String -> String,
  quotes :: (String, String) }

showFormula :: (Show oa, Show oo, Show a, Show o) =>
  ShowStatement -> Statement oa oo a o -> String
showFormula sf f = showsFormula show 0 f "" where
  showsFormula :: (Show oa, Show oo, Show o, Show a) =>
    (ModalVar (Relation oa) (Relation oo) -> String) -> Int -> Statement oa oo a o -> ShowS
  showsFormula svar p f = case f of
    Val l -> showString $ if l then topSymbol sf else botSymbol sf
    Var v -> showString $ svar v
    Neg x -> showParen (p > 8) $ showString (notSymbol sf) . showsFormula svar 8 x
    And x y -> showParen (p > 7) $ showBinary svar (andSymbol sf) 7 x 8 y
    Or  x y -> showParen (p > 6) $ showBinary svar (orSymbol sf) 6 x 7 y
    Imp x y -> showParen (p > 5) $ showBinary svar (impSymbol sf) 6 x 5 y
    Iff x y -> showParen (p > 4) $ showBinary svar (iffSymbol sf) 5 x 4 y
    Consistent v -> showString $ conSign sf (show v)
    Provable v x -> showParen (p > 8) $ showInner boxSign sf v 8 x
    Possible v x -> showParen (p > 8) $ showInner diaSign sf v 8 x
  padded o = showString " " . showString o . showString " "
  showBinary svar o l x r y = showsFormula svar l x . padded o . showsFormula svar r y
  showInner sig sf v i x = showString (sig sf $ show v) . quote sf (showsFormula srelv i x)
  quote sf s = let (l, r) = quotes sf in showString l . s . showString r
  srelv (MeVsThemIs v) = "Me(Them)" ++ show v
  srelv (ThemVsMeIs v) = "Them(Me)" ++ show v
  srelv (ThemVsOtherIs n v) = "Them(" ++ show n ++ ")" ++ show v

showUnicode :: (Show oa, Show oo, Show a, Show o) => Statement oa oo a o -> String
showUnicode = showFormula $ ShowStatement "⊤" "⊥" "¬" "∧" "∨" "→" "↔"
  (printf "Con(%s)")
  (\var -> if var == "0" then "□" else printf "[%s]" var)
  (\var -> if var == "0" then "◇" else printf "<%s>" var)
  ("⌜", "⌝")

showAscii :: (Show oa, Show oo, Show a, Show o) => Statement oa oo a o -> String
showAscii = showFormula $ ShowStatement "T" "F" "~" "&&" "||" "->" "<->"
  (printf "Con(%s)")
  (\var -> if var == "0" then "[]" else printf "[%s]" var)
  (\var -> if var == "0" then "<>" else printf "<%s>" var)
  ("[", "]")

instance (Show oa, Show oo, Show a, Show o) => Show (Statement oa oo a o) where
  show = showUnicode

instance (
  Ord oa, Parsable oa,
  Ord oo, Parsable oo,
  Ord a, Parsable a,
  Ord o, Parsable o ) => Parsable (Statement oa oo a o) where
  parser = statementParser parser parser parser parser

statementParser :: (Ord oa, Ord oo, Ord a, Ord o) =>
  Parser oa -> Parser oo -> Parser a -> Parser o -> Parser (Statement oa oo a o)
statementParser oa oo a o = buildExpressionParser lTable term where
    lTable =
      [ [Prefix lNeg]
      , [Infix lAnd AssocRight]
      , [Infix lOr AssocRight]
      , [Infix lImp AssocRight]
      , [Infix lIff AssocRight] ]
    term
      =   parens (statementParser oa oo a o)
      <|> try (constant cCon)
      <|> try (fProvable <*> quoted (statementParser a o a o))
      <|> try (fPossible <*> quoted (statementParser a o a o))
      <|> try (Var <$> relVar oa oo)
      <|> try (Val <$> val)
      <?> "a statement"

type ModalizedStatement a o = Statement Void Void a o

mstatementParser :: (Ord a, Ord o) => Parser a -> Parser o -> Parser (ModalizedStatement a o)
mstatementParser = statementParser parser parser

evalStatement :: Contextual a o m => ModalizedStatement a o -> m (ModalFormula (ModalVar a o))
evalStatement = evalStatement' (\v -> fail "Where did you even get this element of the Void?")

evalStatement' :: Contextual a o m =>
  (ModalVar (Relation oa) (Relation oo) -> m (ModalFormula (ModalVar a o))) ->
  Statement oa oo a o ->
  m (ModalFormula (ModalVar a o))
evalStatement' evar stm = case stm of
  Val v -> return $ L.Val v
  Var v -> evar v
  Neg x -> L.Neg <$> rec x
  And x y -> L.And <$> rec x <*> rec y
  Or x y -> L.Or <$> rec x <*> rec y
  Imp x y -> L.Imp <$> rec x <*> rec y
  Iff x y -> L.Iff <$> rec x <*> rec y
  Consistent v -> L.incon <$> getN v
  Provable v x -> L.boxk <$> getN v <*> evalStatement' evalVar x
  Possible v x -> L.diak <$> getN v <*> evalStatement' evalVar x
  where rec = evalStatement' evar

-------------------------------------------------------------------------------

data CodeFragment a o
  = ForMe Name (Range V a) [CodeFragment a o]
  | ForThem Name (Range V o) [CodeFragment a o]
  | ForN Name (Range V Int) [CodeFragment a o]
  | LetN Name Expr
  | If (ModalizedStatement a o) [CodeFragment a o]
  | EarlyReturn (Maybe (V a))
  | Pass
  deriving Eq

instance (Show a, Show o) => Blockable (CodeFragment a o) where
  blockLines (ForMe n r cs) =
    [(0, T.pack $ printf "for action %s in %s" (T.unpack n) (show r))] <>
    increaseIndent (concatMap blockLines cs)
  blockLines (ForThem n r cs) =
    [(0, T.pack $ printf "for outcome %s in %s" (T.unpack n) (show r))] <>
    increaseIndent (concatMap blockLines cs)
  blockLines (ForN n r cs) =
    [(0, T.pack $ printf "for number %s in %s" (T.unpack n) (show r))] <>
    increaseIndent (concatMap blockLines cs)
  blockLines (LetN n x) =
    [(0, T.pack $ printf "let %s = %s" (T.unpack n) (show x))]
  blockLines (If s xs) =
    [ (0, T.pack $ printf "if %s" $ show s) ] <>
    increaseIndent (concatMap blockLines xs)
  blockLines (EarlyReturn Nothing) = [(0, "return")]
  blockLines (EarlyReturn (Just x)) = [(0, T.pack $ printf "return %s" (show x))]
  blockLines (Pass) = [(0, "pass")]

instance (Show a, Show o) => Show (CodeFragment a o) where
  show = T.unpack . renderBlock

instance (Ord a, Parsable a, Ord o, Parsable o ) => Parsable (CodeFragment a o) where
  parser = codeFragmentParser parser parser

codeFragmentParser :: (Ord a, Ord o) => Parser a -> Parser o -> Parser (CodeFragment a o)
codeFragmentParser a o = pFrag where
  pFrag =   try fForMe
        <|> try fForThem
        <|> try fForN
        <|> try fLetN
        <|> try fIf
        <|> try (EarlyReturn <$> fReturn (vParser a))
        <|> try fPass
        <?> "a code fragment"
  fLetN = LetN <$> (keyword "let" *> varname <* symbol "=") <*> parser
  fIf = If <$> (keyword "if" *> mstatementParser a o) <*> fBlock
  fForMe = ForMe <$> (keyword "for" *> keyword "action" *> varname) <*>
    (keyword "in" *> rangeParser parser (vParser a)) <*> fBlock
  fForThem = ForThem <$> (keyword "for" *> keyword "outcome" *> varname) <*>
    (keyword "in" *> rangeParser parser (vParser o)) <*> fBlock
  fForN = ForN <$> (keyword "for" *> keyword "number" *> varname) <*>
    (keyword "in" *> boundedRange) <*> fBlock
  fBlock =   try (keyword "end" $> [])
         <|> ((:) <$> codeFragmentParser a o <*> fBlock) <?> "a code block"
  fPass = symbol "pass" $> Pass

evalCodeFragment :: Evalable a o m => CodeFragment a o -> m (ProgFrag (ModalVar a o) a)
evalCodeFragment code = case code of
  ForMe n r code -> loop (withA n) code =<< elemsInContext getAs getA r
  ForThem n r code -> loop (withO n) code =<< elemsInContext getOs getO r
  ForN n r code -> loop (withN n) code =<< elemsInContext (return [0..]) getN r
  LetN n x -> evalExpr x >>= modify . withN n >> return mPass
  If s block -> do
    cond <- evalStatement s
    thens <- mapM evalCodeFragment block
    let ProgFrag _then = foldr1 (>->) thens
    return $ ProgFrag $ \cont a ->
      (cond %^ _then cont a) %| (L.Neg cond %^ cont a)
  EarlyReturn x -> ProgFrag . const <$> evalCode (Return x)
  Pass -> return mPass
  where loop update block xs
          | null xs = return mPass
          | otherwise = foldr1 (>->) . concat <$> sequence fragments
          where fragments = [modify (update x) >> mapM evalCodeFragment block | x <- xs]

-------------------------------------------------------------------------------

data Code a o
  = Fragment (CodeFragment a o) (Code a o)
  | Return (Maybe (V a))
  deriving Eq

instance (Show a, Show o) => Blockable (Code a o) where
  blockLines (Fragment f c) = blockLines f ++ blockLines c
  blockLines (Return Nothing) = [(0, "return")]
  blockLines (Return (Just x)) = [(0, T.pack $ printf "return %s" (show x))]

instance (Show a, Show o) => Show (Code a o) where
  show = T.unpack . renderBlock

instance (Ord a, Parsable a, Ord o, Parsable o) => Parsable (Code a o) where
  parser = codeParser parser parser

codeParser :: (Ord a, Ord o) => Parser a -> Parser o -> Parser (Code a o)
codeParser a o =   try (Fragment <$> codeFragmentParser a o <*> codeParser a o)
               <|> try (Return <$> fReturn (vParser a))
               <?> "some code"

evalCode :: Evalable a o m => Code a o -> m (Program a o)
evalCode (Fragment f cont) = evalCodeFragment f >>= \(ProgFrag p) -> p <$> evalCode cont
evalCode (Return Nothing) = evalCode . Return . Just . Lit =<< defaultAction
evalCode (Return (Just v)) = (\a b -> L.Val (a == b)) <$> getA v

codeToFormula :: (Eq a, Eq o) => [a] -> [o] -> Code a o -> Either ContextError (Program a o)
codeToFormula as os code = runExcept $ fst <$> runStateT (evalCode code) (emptyContext as os)

-------------------------------------------------------------------------------

type VeryParsable a o = (Ord a, Parsable a, Ord o, Parsable o)

sEquals :: Parser ()
sEquals = void sym where
  sym =   try (symbol "=")
      <|> try (symbol "==")
      <|> try (keyword "is")
      <?> "an equality"

sNotEquals :: Parser ()
sNotEquals = void sym where
  sym =   try (symbol "≠")
      <|> try (symbol "!=")
      <|> try (symbol "/=")
      <|> try (keyword "isnt")
      <?> "a disequality"
sIn :: Parser ()
sIn = void sym where
  sym =   try (symbol "∈")
      <|> try (keyword "in")
      <?> "a membership test"
sNotIn :: Parser ()
sNotIn = void sym where
  sym =   try (symbol "∉")
      <|> try (keyword "notin")
      <?> "an absence test"

val :: Parser Bool
val = try sTop <|> try sBot <?> "a boolean value" where
  sTop = sym $> True where
    sym =   try (symbol "⊤")
        <|> try (keyword "top")
        <|> try (keyword "true")
        <|> try (keyword "True")
        <?> "truth"
  sBot = sym $> False where
    sym =   try (symbol "⊥")
        <|> try (keyword "bot")
        <|> try (keyword "bottom")
        <|> try (keyword "false")
        <|> try (keyword "False")
        <?> "falsehood"

lNeg :: Parser (Statement a b c d -> Statement a b c d)
lNeg = sym $> Neg where
  sym =   try (symbol "¬")
      <|> try (keyword "not")
      <?> "a negation"

lAnd :: Parser (Statement a b c d -> Statement a b c d -> Statement a b c d)
lAnd = sym $> And where
  sym =   try (symbol "∧")
      <|> try (symbol "/\\")
      <|> try (symbol "&")
      <|> try (symbol "&&")
      <|> try (keyword "and")
      <?> "an and"

lOr :: Parser (Statement a b c d -> Statement a b c d -> Statement a b c d)
lOr = sym $> Or where
  sym =   try (symbol "∨")
      <|> try (symbol "\\/")
      <|> try (symbol "|")
      <|> try (symbol "||")
      <|> try (keyword "and")
      <?> "an or"

lImp :: Parser (Statement a b c d -> Statement a b c d -> Statement a b c d)
lImp = sym $> Imp where
  sym =   try (symbol "→")
      <|> try (symbol "->")
      <|> try (keyword "implies")
      <?> "an implication"

lIff :: Parser (Statement a b c d -> Statement a b c d -> Statement a b c d)
lIff = sym $> Iff where
  sym =   try (symbol "↔")
      <|> try (symbol "<->")
      <|> try (keyword "iff")
      <?> "a biconditional"

constant :: Parser (V Int -> Statement a b c d) -> Parser (Statement a b c d)
constant x = x <*> option (Lit 0) parser

quoted :: Parser a -> Parser a
quoted x
  =   try (between (symbol "⌜") (symbol "⌝") x)
  <|> try (between (symbol "[") (symbol "]") x)
  <?> "something quoted"

cCon :: Parser (V Int -> Statement a b c d)
cCon = symbol "Con" $> Consistent

fProvable :: Parser (Statement c d c d -> Statement a b c d)
fProvable = try inSym <|> choice [try $ afterSym s | s <- syms] <?> "a box" where
  inSym = Provable <$> (char '[' *> option (Lit 0) parser <* char ']')
  afterSym s = Provable <$> (symbol s  *> option (Lit 0) parser)
  syms = ["□", "Provable", "Box"]

fPossible :: Parser (Statement c d c d -> Statement a b c d)
fPossible = try inSym <|> choice [try $ afterSym s | s <- syms] <?> "a diamond" where
  inSym = Provable <$> (char '<' *> option (Lit 0) parser <* char '>')
  afterSym s = Provable <$> (symbol s  *> option (Lit 0) parser)
  syms = ["◇", "Possible", "Dia", "Diamond"]

relVar :: (Ord a, Ord o) => Parser a -> Parser o -> Parser (ModalVar (Relation a) (Relation o))
relVar a o = try meVsThem <|> try themVsMe <|> try themVsOther <?> "a modal variable" where
  meVsThem = string "Me(Them)" *> (MeVsThemIs <$> relationParser a)
  themVsMe = string "Them(Me)" *> (ThemVsMeIs <$> relationParser o)
  themVsOther = string "Them(" *> (ThemVsOtherIs <$> name) <*> (char ')' *> relationParser o)

fReturn :: Parser a -> Parser (Maybe a)
fReturn p = try returnThing <|> returnNothing <?> "a return statement" where
  returnThing = Just <$> (symbol "return" *> p)
  returnNothing = symbol "return" $> Nothing

varname :: Parser Name
varname = char '$' *> name
