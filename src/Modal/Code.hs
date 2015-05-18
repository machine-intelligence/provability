{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Modal.Code
  ( Program
  , Val(..)
  , Context(..)
  , emptyContext
  , defaultContext
  , ContextError(..)
  , ModalVar(..)
  , Var(..)
  , varParser
  , Relation(..)
  , relationParser
  , Expr(..)
  , Range(..)
  , rangeParser
  , elemsIn
  , FreeStatement
  , freeStatementParser
  , evalFreeStatement
  , ModalizedStatement
  , modalizedStatementParser
  , evalModalizedStatement
  , OuterToInner
  , o2iImpossible
  , o2iTrivial
  , Code
  , evalCode
  , codeParser
  , codeToProgram
  , ModalizedCode
  , evalModalizedCode
  , modalizedCodeParser
  , modalizedCodeToProgram
  , FreeCode
  , evalFreeCode
  , freeCodeParser
  , freeCodeToProgram
  ) where
import Prelude hiding (readFile, sequence, mapM)
import Control.Applicative
import Control.Monad.Except hiding (mapM, sequence)
import Control.Monad.State hiding (mapM, sequence)
import Control.Monad.Identity hiding (mapM, sequence)
import Data.Map (Map)
import Data.Traversable (Traversable, sequence, mapM)
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Monoid ((<>))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Modal.Formulas (ModalFormula, (%^), (%|))
import qualified Modal.Formulas as L
import Modal.Display
import Modal.Parser
import Modal.Programming
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Expr
import Text.Printf (printf)

type Program a o = ModalProgram a (ModalVar a o)

-------------------------------------------------------------------------------

data Val a o = Number Int | Action a | Outcome o deriving (Eq, Ord, Read, Show)

data Context a o = Context
  { variables :: Map Name (Val a o)
  , actionList :: [a]
  , outcomeList :: [o]
  } deriving (Eq, Show)

data ContextError
  = UnknownVar Name String
  | WrongType Name String String
  deriving (Eq, Ord)

instance Show ContextError where
  show (UnknownVar n t) = printf "%s variable %s is undefined" t (show n)
  show (WrongType n x y) = printf "%s variable %s is not a %s" x (show n) y

type Contextual a o m = (Applicative m, MonadState (Context a o) m, MonadError ContextError m)
type Evalable a o m = (Eq a, Eq o, Contextual a o m)

emptyContext :: [a] -> [o] -> Context a o
emptyContext = Context Map.empty

defaultContext :: (Enum a, Enum o) => Context a o
defaultContext = emptyContext enumerate enumerate

withA :: Name -> a -> Context a o -> Context a o
withA n a c = c{variables=Map.insert n (Action a) $ variables c}

withO :: Name -> o -> Context a o -> Context a o
withO n o c = c{variables=Map.insert n (Outcome o) $ variables c}

withN :: Name -> Int -> Context a o -> Context a o
withN n i c = c{variables=Map.insert n (Number i) $ variables c}

getA :: Contextual a o m => Var a -> m a
getA (Ref n) = variables <$> get >>= \vs -> case Map.lookup n vs of
  (Just (Action a)) -> return a
  (Just (Outcome _)) -> throwError $ WrongType n "action" "outcome"
  (Just (Number _)) -> throwError $ WrongType n "action" "number"
  Nothing -> throwError $ UnknownVar n "action"
getA (Lit a) = return a

getO :: Contextual a o m => Var o -> m o
getO (Ref n) = variables <$> get >>= \vs -> case Map.lookup n vs of
  (Just (Outcome o)) -> return o
  (Just (Action _)) -> throwError $ WrongType n "outcome" "action"
  (Just (Number _)) -> throwError $ WrongType n "outcome" "number"
  Nothing -> throwError $ UnknownVar n "outcome"
getO (Lit o) = return o

getN :: Contextual a o m => Var Int -> m Int
getN (Ref n) = variables <$> get >>= \vs -> case Map.lookup n vs of
  (Just (Number i)) -> return i
  (Just (Outcome _)) -> throwError $ WrongType n "action" "outcome"
  (Just (Action _)) -> throwError $ WrongType n "outcome" "action"
  Nothing -> throwError $ UnknownVar n "number"
getN (Lit i) = return i

getAs :: Contextual a o m => m [a]
getAs = actionList <$> get

getOs :: Contextual a o m => m [o]
getOs = outcomeList <$> get

defaultAction :: Contextual a o m => m a
defaultAction = head <$> getAs

-------------------------------------------------------------------------------

data Var a = Ref Name | Lit a deriving (Eq, Ord, Read)

instance Show a => Show (Var a) where
  show (Ref n) = '$' : T.unpack n
  show (Lit x) = show x

instance Parsable a => Parsable (Var a) where
  parser = varParser parser

varParser :: Parsec Text s x -> Parsec Text s (Var x)
varParser p =   try (Lit <$> p)
          <|> try (Ref <$> (char '$' *> name))
          <?> "a variable"

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
evalVar (ThemVsOtherIs n rel) = evalRelation getO (ThemVsOtherIs n) rel

-------------------------------------------------------------------------------

data Relation a
  = Equals (Var a)
  | NotEquals (Var a)
  | In (Set (Var a))
  | NotIn (Set (Var a))
  deriving (Eq, Ord)
instance Show a => Show (Relation a) where
  show (Equals v) = "=" ++ show v
  show (NotEquals v) = "≠" ++ show v
  show (In v) = "∈{" ++ List.intercalate "," (map show $ Set.toList v) ++ "}"
  show (NotIn v) = "∉{" ++ List.intercalate "," (map show $ Set.toList v) ++ "}"
instance (Ord a, Parsable a) => Parsable (Relation a) where
  parser = relationParser parser

relationParser :: Ord x => Parsec Text s x -> Parsec Text s (Relation x)
relationParser p =   try (Equals <$> (sEquals *> varParser p))
                 <|> try (NotEquals <$> (sNotEquals *> varParser p))
                 <|> try (In <$> (sIn *> setParser (varParser p)))
                 <|> try (NotIn <$> (sNotIn *> setParser (varParser p)))
                 <?> "a relation"

evalRelation :: Contextual a o m =>
  (Var x -> m x) -> (x -> v) -> Relation x -> m (ModalFormula v)
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
  = Num (Var Int)
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
      <|> try (Num <$> (parser :: Parsec Text s (Var Int)))
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

rangeParser :: Parsec Text s (m Int) -> Parsec Text s (m x) -> Parsec Text s (Range m x)
rangeParser n x = try rEnum <|> try rList <|> try rAll <?> "a range" where
    rEnum = EnumRange <$> (x <* symbol "..") <*> optional x <*> pEnumBy
    pEnumBy = optional (try $ keyword "by" *> n)
    rList = ListRange <$> listParser x
    rAll = symbol "..." $> TotalRange

boundedRange :: (Parsable (m x), Parsable (m Int)) => Parsec Text s (Range m x)
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

elemsInContext :: (Eq x, Evalable a o m) => m [x] -> (Var x -> m x) -> Range Var x -> m [x]
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
  | Consistent (Var Int)
  | Provable (Var Int) (Statement a o a o)
  | Possible (Var Int) (Statement a o a o)
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

showStatement :: (Show oa, Show oo, Show a, Show o) =>
  ShowStatement -> Statement oa oo a o -> String
showStatement sf = flip (showsFormula show 0) "" where
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
    Provable v x -> showParen (p > 8) $ showInner boxSign v 8 x
    Possible v x -> showParen (p > 8) $ showInner diaSign v 8 x
  padded o = showString " " . showString o . showString " "
  showBinary svar o l x r y = showsFormula svar l x . padded o . showsFormula svar r y
  showInner sig v i x = showString (sig sf $ show v) . quote (showsFormula srelv i x)
  quote s = let (l, r) = quotes sf in showString l . s . showString r
  srelv (MeVsThemIs v) = "Me(Them)" ++ show v
  srelv (ThemVsMeIs v) = "Them(Me)" ++ show v
  srelv (ThemVsOtherIs n v) = "Them(" ++ show n ++ ")" ++ show v

showStatementUnicode :: (Show oa, Show oo, Show a, Show o) => Statement oa oo a o -> String
showStatementUnicode = showStatement $ ShowStatement "⊤" "⊥" "¬" "∧" "∨" "→" "↔"
  (printf "Con(%s)")
  (\var -> if var == "0" then "□" else printf "[%s]" var)
  (\var -> if var == "0" then "◇" else printf "<%s>" var)
  ("⌜", "⌝")

instance (Show oa, Show oo, Show a, Show o) => Show (Statement oa oo a o) where
  show = showStatementUnicode

instance (
  Ord oa, Parsable oa,
  Ord oo, Parsable oo,
  Ord a, Parsable a,
  Ord o, Parsable o ) => Parsable (Statement oa oo a o) where
  parser = statementParser parser parser parser parser

statementParser :: (Ord oa, Ord oo, Ord a, Ord o) =>
  Parsec Text s oa -> Parsec Text s oo -> Parsec Text s a -> Parsec Text s o -> Parsec Text s (Statement oa oo a o)
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

evalStatement :: Contextual a o m =>
  O2I oa oo a o m ->
  Statement oa oo a o ->
  m (ModalFormula (ModalVar a o))
evalStatement evar stm = case stm of
  Val v -> return $ L.Val v
  Var v -> evar v
  Neg x -> L.Neg <$> rec x
  And x y -> L.And <$> rec x <*> rec y
  Or x y -> L.Or <$> rec x <*> rec y
  Imp x y -> L.Imp <$> rec x <*> rec y
  Iff x y -> L.Iff <$> rec x <*> rec y
  Consistent v -> L.incon <$> getN v
  Provable v x -> L.boxk <$> getN v <*> evalStatement o2iTrivial x
  Possible v x -> L.diak <$> getN v <*> evalStatement o2iTrivial x
  where rec = evalStatement evar

-------------------------------------------------------------------------------

type ModalizedStatement a o = Statement Void Void a o

modalizedStatementParser :: (Ord a, Ord o) =>
  Parsec Text s a -> Parsec Text s o -> Parsec Text s (ModalizedStatement a o)
modalizedStatementParser = statementParser parser parser

evalModalizedStatement :: Contextual a o m =>
  ModalizedStatement a o -> m (ModalFormula (ModalVar a o))
evalModalizedStatement = evalStatement o2iImpossible

-------------------------------------------------------------------------------

type FreeStatement a o = Statement a o a o

freeStatementParser :: (Ord a, Ord o) =>
  Parsec Text s a -> Parsec Text s o -> Parsec Text s (FreeStatement a o)
freeStatementParser a o = statementParser a o a o

evalFreeStatement :: Contextual a o m => FreeStatement a o -> m (ModalFormula (ModalVar a o))
evalFreeStatement = evalStatement o2iTrivial

-------------------------------------------------------------------------------

data CodeFragment oa oo a o
  = ForMe Name (Range Var a) [CodeFragment oa oo a o]
  | ForThem Name (Range Var o) [CodeFragment oa oo a o]
  | ForN Name (Range Var Int) [CodeFragment oa oo a o]
  | LetN Name Expr
  | If (Statement oa oo a o) [CodeFragment oa oo a o]
  | EarlyReturn (Maybe (Var a))
  | Pass
  deriving Eq

instance (Show oa, Show oo, Show a, Show o) => Blockable (CodeFragment oa oo a o) where
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

instance (Show oa, Show oo, Show a, Show o) => Show (CodeFragment oa oo a o) where
  show = T.unpack . renderBlock

instance
  ( Ord ao
  , Parsable ao
  , Ord oo
  , Parsable oo
  , Ord a
  , Parsable a
  , Ord o
  , Parsable o
  ) => Parsable (CodeFragment ao oo a o) where
  parser = codeFragmentParser parser parser parser parser

codeFragmentParser :: (Ord ao, Ord oo, Ord a, Ord o) =>
  Parsec Text s ao -> Parsec Text s oo -> Parsec Text s a -> Parsec Text s o ->
  Parsec Text s (CodeFragment ao oo a o)
codeFragmentParser ao oo a o = pFrag where
  pFrag =   try fForMe
        <|> try fForThem
        <|> try fForN
        <|> try fLetN
        <|> try fIf
        <|> try (EarlyReturn <$> fReturn (varParser a))
        <|> try fPass
        <?> "a code fragment"
  fLetN = LetN <$> (keyword "let" *> varname <* symbol "=") <*> parser
  fIf = If <$> (keyword "if" *> statementParser ao oo a o) <*> fBlock
  fForMe = ForMe <$> (keyword "for" *> keyword "action" *> varname) <*>
    (keyword "in" *> rangeParser parser (varParser a)) <*> fBlock
  fForThem = ForThem <$> (keyword "for" *> keyword "outcome" *> varname) <*>
    (keyword "in" *> rangeParser parser (varParser o)) <*> fBlock
  fForN = ForN <$> (keyword "for" *> keyword "number" *> varname) <*>
    (keyword "in" *> boundedRange) <*> fBlock
  fBlock =   try (keyword "end" $> [])
         <|> ((:) <$> codeFragmentParser ao oo a o <*> fBlock) <?> "a code block"
  fPass = symbol "pass" $> Pass
  varname = char '$' *> name

type OuterToInner oa oo a o
  = O2I oa oo a o (StateT (Context a o) (ExceptT ContextError Identity))
type O2I oa oo a o m
  = ModalVar (Relation oa) (Relation oo) -> m (ModalFormula (ModalVar a o))

o2iImpossible :: Monad m => O2I Void Void a o m
o2iImpossible _ = fail "Where did you even get this element of the Void?"

o2iTrivial :: Contextual a o m => O2I a o a o m
o2iTrivial = evalVar

evalCodeFragment :: Evalable a o m =>
  O2I oa oo a o m -> CodeFragment oa oo a o -> m (Program a o -> Program a o)
evalCodeFragment o2i code = case code of
  ForMe n r inner -> loop (withA n) inner =<< elemsInContext getAs getA r
  ForThem n r inner -> loop (withO n) inner =<< elemsInContext getOs getO r
  ForN n r inner -> loop (withN n) inner =<< elemsInContext (return [0..]) getN r
  LetN n x -> evalExpr x >>= modify . withN n >> return id
  If s block -> do
    cond <- evalStatement o2i s
    thens <- mapM (evalCodeFragment o2i) block
    let yes = foldr1 (.) thens
    return (\continue -> ModalProgram $ \act ->
      (cond %^ formulaFor (yes continue) act) %| (L.Neg cond %^ formulaFor continue act))
  EarlyReturn x -> const <$> evalCode o2i (Return x)
  Pass -> return id
  where loop update block xs
          | null xs = return id
          | otherwise = foldr1 (.) . concat <$> sequence fragments
          where fragments = [modify (update x) >> mapM (evalCodeFragment o2i) block | x <- xs]

-------------------------------------------------------------------------------

data Code ao oo a o
  = Fragment (CodeFragment ao oo a o) (Code ao oo a o)
  | Return (Maybe (Var a))
  deriving Eq

instance (Show ao, Show oo, Show a, Show o) => Blockable (Code ao oo a o) where
  blockLines (Fragment f c) = blockLines f ++ blockLines c
  blockLines (Return Nothing) = [(0, "return")]
  blockLines (Return (Just x)) = [(0, T.pack $ printf "return %s" (show x))]

instance (Show ao, Show oo, Show a, Show o) => Show (Code ao oo a o) where
  show = T.unpack . renderBlock

instance
  ( Ord ao
  , Parsable ao
  , Ord oo
  , Parsable oo
  , Ord a
  , Parsable a
  , Ord o
  , Parsable o) => Parsable (Code ao oo a o) where
  parser = codeParser parser parser parser parser

codeParser :: (Ord ao, Ord oo, Ord a, Ord o) =>
  Parsec Text s ao -> Parsec Text s oo -> Parsec Text s a -> Parsec Text s o ->
  Parsec Text s (Code ao oo a o)
codeParser ao oo a o
  =   try (Fragment <$> codeFragmentParser ao oo a o <*> codeParser ao oo a o)
  <|> try (Return <$> fReturn (varParser a))
  <?> "some code"

evalCode :: Evalable a o m => O2I oa oo a o m -> Code oa oo a o -> m (Program a o)
evalCode o2i (Fragment f cont) = evalCodeFragment o2i f >>= (<$> evalCode o2i cont)
evalCode o2i (Return Nothing) = defaultAction >>= evalCode o2i . Return . Just . Lit
evalCode _ (Return (Just v)) = ModalProgram . (L.Val .) . (==) <$> getA v

codeToProgram :: (Eq a, Eq o) =>
  O2I oa oo a o (StateT (Context a o) (ExceptT ContextError Identity)) ->
  Context a o ->
  Code oa oo a o ->
  Either ContextError (Program a o)
codeToProgram o2i context code = runExcept $ fst <$> runStateT (evalCode o2i code) context

-------------------------------------------------------------------------------

type ModalizedCode a o = Code Void Void a o

evalModalizedCode :: Evalable a o m => ModalizedCode a o -> m (Program a o)
evalModalizedCode = evalCode o2iImpossible

modalizedCodeParser :: (Ord a, Ord o) =>
  Parsec Text s a -> Parsec Text s o -> Parsec Text s (ModalizedCode a o)
modalizedCodeParser = codeParser parser parser

modalizedCodeToProgram :: (Eq a, Eq o) =>
  Context a o -> ModalizedCode a o -> Either ContextError (Program a o)
modalizedCodeToProgram = codeToProgram o2iImpossible

-------------------------------------------------------------------------------

type FreeCode a o = Code a o a o

evalFreeCode :: Evalable a o m => FreeCode a o -> m (Program a o)
evalFreeCode = evalCode o2iTrivial

freeCodeParser :: (Ord a, Ord o) =>
  Parsec Text s a -> Parsec Text s o -> Parsec Text s (FreeCode a o)
freeCodeParser a o = codeParser a o a o

freeCodeToProgram :: (Eq a, Eq o) =>
  Context a o -> FreeCode a o -> Either ContextError (Program a o)
freeCodeToProgram = codeToProgram o2iTrivial

-------------------------------------------------------------------------------

sEquals :: Parsec Text s ()
sEquals = void sym where
  sym =   try (symbol "=")
      <|> try (symbol "==")
      <|> try (keyword "is")
      <?> "an equality"

sNotEquals :: Parsec Text s ()
sNotEquals = void sym where
  sym =   try (symbol "≠")
      <|> try (symbol "!=")
      <|> try (symbol "/=")
      <|> try (keyword "isnt")
      <?> "a disequality"
sIn :: Parsec Text s ()
sIn = void sym where
  sym =   try (symbol "∈")
      <|> try (keyword "in")
      <?> "a membership test"
sNotIn :: Parsec Text s ()
sNotIn = void sym where
  sym =   try (symbol "∉")
      <|> try (keyword "notin")
      <?> "an absence test"

val :: Parsec Text s Bool
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

lNeg :: Parsec Text s (Statement a b c d -> Statement a b c d)
lNeg = sym $> Neg where
  sym =   try (symbol "¬")
      <|> try (keyword "not")
      <?> "a negation"

lAnd :: Parsec Text s (Statement a b c d -> Statement a b c d -> Statement a b c d)
lAnd = sym $> And where
  sym =   try (symbol "∧")
      <|> try (symbol "/\\")
      <|> try (symbol "&")
      <|> try (symbol "&&")
      <|> try (keyword "and")
      <?> "an and"

lOr :: Parsec Text s (Statement a b c d -> Statement a b c d -> Statement a b c d)
lOr = sym $> Or where
  sym =   try (symbol "∨")
      <|> try (symbol "\\/")
      <|> try (symbol "|")
      <|> try (symbol "||")
      <|> try (keyword "and")
      <?> "an or"

lImp :: Parsec Text s (Statement a b c d -> Statement a b c d -> Statement a b c d)
lImp = sym $> Imp where
  sym =   try (symbol "→")
      <|> try (symbol "->")
      <|> try (keyword "implies")
      <?> "an implication"

lIff :: Parsec Text s (Statement a b c d -> Statement a b c d -> Statement a b c d)
lIff = sym $> Iff where
  sym =   try (symbol "↔")
      <|> try (symbol "<->")
      <|> try (keyword "iff")
      <?> "a biconditional"

constant :: Parsec Text s (Var Int -> Statement a b c d) -> Parsec Text s (Statement a b c d)
constant x = x <*> option (Lit 0) parser

quoted :: Parsec Text s a -> Parsec Text s a
quoted x
  =   try (between (symbol "⌜") (symbol "⌝") x)
  <|> try (between (symbol "[") (symbol "]") x)
  <?> "something quoted"

cCon :: Parsec Text s (Var Int -> Statement a b c d)
cCon = symbol "Con" $> Consistent

fProvable :: Parsec Text s (Statement c d c d -> Statement a b c d)
fProvable = try inSym <|> choice [try $ afterSym s | s <- syms] <?> "a box" where
  inSym = Provable <$> (char '[' *> option (Lit 0) parser <* char ']')
  afterSym s = Provable <$> (symbol s  *> option (Lit 0) parser)
  syms = ["□", "Provable", "Box"]

fPossible :: Parsec Text s (Statement c d c d -> Statement a b c d)
fPossible = try inSym <|> choice [try $ afterSym s | s <- syms] <?> "a diamond" where
  inSym = Provable <$> (char '<' *> option (Lit 0) parser <* char '>')
  afterSym s = Provable <$> (symbol s  *> option (Lit 0) parser)
  syms = ["◇", "Possible", "Dia", "Diamond"]

relVar :: (Ord a, Ord o) => Parsec Text s a -> Parsec Text s o -> Parsec Text s (ModalVar (Relation a) (Relation o))
relVar a o = try meVsThem <|> try themVsMe <|> try themVsOther <?> "a modal variable" where
  meVsThem = choice [string "Me(Them)", string "Me()"] *> (MeVsThemIs <$> relationParser a)
  themVsMe = choice [string "Them(Me)", string "Them()"] *> (ThemVsMeIs <$> relationParser o)
  themVsOther = string "Them(" *> (ThemVsOtherIs <$> name) <*> (char ')' *> relationParser o)

fReturn :: Parsec Text s a -> Parsec Text s (Maybe a)
fReturn p = try returnThing <|> returnNothing <?> "a return statement" where
  returnThing = Just <$> (symbol "return" *> p)
  returnNothing = symbol "return" $> Nothing
