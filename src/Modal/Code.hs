{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
module Modal.Code
  ( agentName
  , agentDefaults
  , agentActions
  , agentOutcomes
  , agentCode
  ---
  , ModalizedAgent
  , modalizedAgentParser
  , makeModalizedAgent
  , compileModalizedAgent
  ---
  , FreeAgent
  , freeAgentParser
  , makeFreeAgent
  , compileFreeAgent
  ---
  , ModalizableVar(..)
  ---

  ---
  , Program
  ---
  , Val(..)
  , Var(..)
  , varParser
  ---
  , Context(..)
  , getA
  , getO
  , getN
  , emptyContext
  , defaultContext
  , ContextError(..)
  ---
  , Relation(..)
  , relationParser
  , evalRelation
  ---
  , SimpleExpr(..)
  ---
  , Range(..)
  , rangeParser
  , elemsIn
  ---

  ---
  , ModalizedCode
  , evalModalizedCode
  , modalizedCodeParser
  , modalizedCodeToProgram
  ---
  , FreeCode
  , evalFreeCode
  , freeCodeParser
  , freeCodeToProgram
  ---
  , ModalizedStatement
  , modalizedStatementParser
  , evalModalizedStatement
  ---
  , FreeStatement
  , freeStatementParser
  , evalFreeStatement
  ) where
-- TODO: Rename "Free", "ModalizedVar", etc.
import Prelude hiding (readFile, sequence, mapM)
import Control.Applicative
import Control.Monad.Except hiding (mapM, sequence)
import Control.Monad.Identity hiding (mapM, sequence)
import Control.Monad.State hiding (mapM, sequence)
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Set (Set)
import Data.Text (Text)
import Data.Traversable (Traversable, sequence, mapM)
import Modal.Display
import Modal.Formulas (ModalFormula, (%^), (%|))
import Modal.Parser
import Modal.Programming
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Expr
import Text.Printf (printf)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Modal.Formulas as L

type Program v a o = ModalProgram a (v a o)

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

-- TODO: Rename and move to a new home.
class ModalizableVar v where
  otherAgentsReferencedIn :: v a o -> [Name]
  relToFormula :: Contextual a o m => v (Relation a) (Relation o) -> m (ModalFormula (v a o))
  makeRelParser :: (Ord a, Ord o) =>
    Parsec Text s a -> Parsec Text s o -> Parsec Text s (v (Relation a) (Relation o))
  expandNames ::
    (Name -> Name -> a -> x) -> (Name -> Name -> o -> x) ->
    Name -> Name -> ModalFormula (v a o) -> ModalFormula x

trivialParser :: ModalizableVar v => Parsec Text s (v (Relation Void) (Relation Void))
trivialParser = fail "You cannot instantiate the Void."

voidToFormula :: (ModalizableVar v, Monad m) =>
  v (Relation Void) (Relation Void) -> m (ModalFormula (v a o))
voidToFormula _ = fail "Where did you even get this element of the Void?"


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
                 where
                   sEquals = void sym where
                     sym =   try (symbol "=")
                         <|> try (symbol "==")
                         <|> try (keyword "is")
                         <?> "an equality"
                   sNotEquals = void sym where
                     sym =   try (symbol "≠")
                         <|> try (symbol "!=")
                         <|> try (symbol "/=")
                         <|> try (keyword "isnt")
                         <?> "a disequality"
                   sIn = void sym where
                     sym =   try (symbol "∈")
                         <|> try (keyword "in")
                         <?> "a membership test"
                   sNotIn = void sym where
                     sym =   try (symbol "∉")
                         <|> try (keyword "notin")
                         <?> "an absence test"

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

data SimpleExpr
  = Num (Var Int)
  | Add SimpleExpr SimpleExpr
  | Sub SimpleExpr SimpleExpr
  | Mul SimpleExpr SimpleExpr
  | Exp SimpleExpr SimpleExpr
  deriving Eq

instance Show SimpleExpr where
  show (Num v) = show v
  show (Add x y) = show x ++ "+" ++ show y
  show (Sub x y) = show x ++ "-" ++ show y
  show (Mul x y) = show x ++ "*" ++ show y
  show (Exp x y) = show x ++ "^" ++ show y

instance Parsable SimpleExpr where
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

evalExpr :: Contextual a o m => SimpleExpr -> m Int
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

data Statement v oa oo a o
  = Val Bool
  | Var (v (Relation oa) (Relation oo))
  | Neg (Statement v oa oo a o)
  | And (Statement v oa oo a o) (Statement v oa oo a o)
  | Or (Statement v oa oo a o) (Statement v oa oo a o)
  | Imp (Statement v oa oo a o) (Statement v oa oo a o)
  | Iff (Statement v oa oo a o) (Statement v oa oo a o)
  | Consistent (Var Int)
  | Provable (Var Int) (Statement v a o a o)
  | Possible (Var Int) (Statement v a o a o)

instance
  ( Eq (v (Relation oa) (Relation oo))
  , Eq (v (Relation a) (Relation o))
  ) => Eq (Statement v oa oo a o) where
  Val x == Val y = x == y
  Var x == Var y = x == y
  Neg x == Neg y = x == y
  And x y == And a b = (x == a) && (y == b)
  Or x y == Or a b = (x == a) && (y == b)
  Imp x y == Imp a b = (x == a) && (y == b)
  Iff x y == Iff a b = (x == a) && (y == b)
  Consistent x == Consistent y = x == y
  Provable x y == Provable a b = (x == a) && (y == b)
  Possible x y == Possible a b = (x == a) && (y == b)
  _ == _ = False

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

showStatement ::
  ShowStatement ->
  (v (Relation oa) (Relation oo) -> String) ->
  (v (Relation a) (Relation o) -> String) ->
  Statement v oa oo a o ->
  String
showStatement sf showO showI statement = showsStatement sf showO showI 0 statement ""

showsStatement ::
  ShowStatement ->
  (v (Relation oa) (Relation oo) -> String) ->
  (v (Relation a) (Relation o) -> String) ->
  Int -> Statement v oa oo a o -> ShowS
showsStatement sf showO showI p statement = case statement of
  Val l -> showString $ if l then topSymbol sf else botSymbol sf
  Var v -> showString $ showO v
  Neg x -> showParen (p > 8) $ showString (notSymbol sf) . recO 8 x
  And x y -> showParen (p > 7) $ showBinary (andSymbol sf) 7 x 8 y
  Or  x y -> showParen (p > 6) $ showBinary (orSymbol sf) 6 x 7 y
  Imp x y -> showParen (p > 5) $ showBinary (impSymbol sf) 6 x 5 y
  Iff x y -> showParen (p > 4) $ showBinary (iffSymbol sf) 5 x 4 y
  Consistent v -> showString $ conSign sf (show v)
  Provable v x -> showParen (p > 8) $ showInner boxSign v 8 x
  Possible v x -> showParen (p > 8) $ showInner diaSign v 8 x
  where
    recO = showsStatement sf showO showI
    recI = showsStatement sf showI showI
    padded o = showString " " . showString o . showString " "
    showBinary o l x r y = recO l x . padded o . recO r y
    showInner sig v i x = showString (sig sf $ show v) . quote (recI i x)
    quote s = let (l, r) = quotes sf in showString l . s . showString r

instance
  ( Show (v (Relation oa) (Relation oo))
  , Show (v (Relation a) (Relation o))
  ) => Show (Statement v oa oo a o) where
  show = showStatement (ShowStatement "⊤" "⊥" "¬" "∧" "∨" "→" "↔"
    (printf "Con(%s)")
    (\var -> if var == "0" then "□" else printf "[%s]" var)
    (\var -> if var == "0" then "◇" else printf "<%s>" var)
    ("⌜", "⌝")) show show


instance
  ( Parsable (v (Relation oa) (Relation oo))
  , Parsable (v (Relation a) (Relation o))
  ) => Parsable (Statement v oa oo a o) where
  parser = statementParser parser parser

statementParser ::
  Parsec Text s (v (Relation oa) (Relation oo)) ->
  Parsec Text s (v (Relation a) (Relation o)) ->
  Parsec Text s (Statement v oa oo a o)
statementParser rvo rvi = buildExpressionParser lTable term where
  lTable =
    [ [Prefix lNeg]
    , [Infix lAnd AssocRight]
    , [Infix lOr AssocRight]
    , [Infix lImp AssocRight]
    , [Infix lIff AssocRight] ]
  term
    =   parens (statementParser rvo rvi)
    <|> try (constant cCon)
    <|> try (fProvable <*> quoted (statementParser rvi rvi))
    <|> try (fPossible <*> quoted (statementParser rvi rvi))
    <|> try (Var <$> rvo)
    <|> try (Val <$> val)
    <?> "a statement"
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
  lNeg = sym $> Neg where
    sym =   try (symbol "¬")
        <|> try (keyword "not")
        <?> "a negation"
  lAnd = sym $> And where
    sym =   try (symbol "∧")
        <|> try (symbol "/\\")
        <|> try (symbol "&")
        <|> try (symbol "&&")
        <|> try (keyword "and")
        <?> "an and"
  lOr = sym $> Or where
    sym =   try (symbol "∨")
        <|> try (symbol "\\/")
        <|> try (symbol "|")
        <|> try (symbol "||")
        <|> try (keyword "and")
        <?> "an or"
  lImp = sym $> Imp where
    sym =   try (symbol "→")
        <|> try (symbol "->")
        <|> try (keyword "implies")
        <?> "an implication"
  lIff = sym $> Iff where
    sym =   try (symbol "↔")
        <|> try (symbol "<->")
        <|> try (keyword "iff")
        <?> "a biconditional"

constant :: Parsec Text s (Var Int -> Statement v a b c d) ->
  Parsec Text s (Statement v a b c d)
constant x = x <*> option (Lit 0) parser

quoted :: Parsec Text s a -> Parsec Text s a
quoted x
  =   try (between (symbol "⌜") (symbol "⌝") x)
  <|> try (between (symbol "[") (symbol "]") x)
  <?> "something quoted"

cCon :: Parsec Text s (Var Int -> Statement v a b c d)
cCon = symbol "Con" $> Consistent

fProvable :: Parsec Text s (Statement v c d c d -> Statement v a b c d)
fProvable = try inSym <|> choice [try $ afterSym s | s <- syms] <?> "a box" where
  inSym = Provable <$> (char '[' *> option (Lit 0) parser <* char ']')
  afterSym s = Provable <$> (symbol s  *> option (Lit 0) parser)
  syms = ["□", "Provable", "Box"]

fPossible :: Parsec Text s (Statement v c d c d -> Statement v a b c d)
fPossible = try inSym <|> choice [try $ afterSym s | s <- syms] <?> "a diamond" where
  inSym = Provable <$> (char '<' *> option (Lit 0) parser <* char '>')
  afterSym s = Provable <$> (symbol s  *> option (Lit 0) parser)
  syms = ["◇", "Possible", "Dia", "Diamond"]

evalStatement :: (ModalizableVar v, Contextual a o m) =>
  O2I v oa oo a o m ->
  Statement v oa oo a o ->
  m (ModalFormula (v a o))
evalStatement evar stm = case stm of
  Val v -> return $ L.Val v
  Var v -> evar v
  Neg x -> L.Neg <$> rec x
  And x y -> L.And <$> rec x <*> rec y
  Or x y -> L.Or <$> rec x <*> rec y
  Imp x y -> L.Imp <$> rec x <*> rec y
  Iff x y -> L.Iff <$> rec x <*> rec y
  Consistent v -> L.incon <$> getN v
  Provable v x -> L.boxk <$> getN v <*> evalStatement relToFormula x
  Possible v x -> L.diak <$> getN v <*> evalStatement relToFormula x
  where rec = evalStatement evar

-------------------------------------------------------------------------------

type ModalizedStatement v a o = Statement v Void Void a o

modalizedStatementParser :: ModalizableVar v =>
  Parsec Text s (v (Relation a) (Relation o)) ->
  Parsec Text s (ModalizedStatement v a o)
modalizedStatementParser = statementParser trivialParser

evalModalizedStatement :: (ModalizableVar v, Contextual a o m) =>
  ModalizedStatement v a o -> m (ModalFormula (v a o))
evalModalizedStatement = evalStatement voidToFormula

-------------------------------------------------------------------------------

type FreeStatement v a o = Statement v a o a o

freeStatementParser ::
  Parsec Text s (v (Relation a) (Relation o)) ->
  Parsec Text s (FreeStatement v a o)
freeStatementParser p = statementParser p p

evalFreeStatement :: (ModalizableVar v, Contextual a o m) =>
  FreeStatement v a o -> m (ModalFormula (v a o))
evalFreeStatement = evalStatement relToFormula

-------------------------------------------------------------------------------

data CodeFragment v oa oo a o
  = ForMe Name (Range Var a) [CodeFragment v oa oo a o]
  | ForThem Name (Range Var o) [CodeFragment v oa oo a o]
  | ForN Name (Range Var Int) [CodeFragment v oa oo a o]
  | LetN Name SimpleExpr
  | If (Statement v oa oo a o) [CodeFragment v oa oo a o]
  | EarlyReturn (Maybe (Var a))
  | Pass

instance
  ( Eq (v (Relation oa) (Relation oo))
  , Eq (v (Relation a) (Relation o))
  , Eq a, Eq o
  ) => Eq (CodeFragment v oa oo a o) where
  ForMe a b c == ForMe x y z = (a == x) && (b == y) && (c == z)
  ForThem a b c == ForThem x y z = (a == x) && (b == y) && (c == z)
  ForN a b c == ForN x y z = (a == x) && (b == y) && (c == z)
  LetN x y == LetN a b = (x == a) && (y == b)
  If x y == If a b = (x == a) && (y == b)
  EarlyReturn x == EarlyReturn y = x == y
  Pass == Pass = True
  _ == _ = False

instance
  ( Show (v (Relation oa) (Relation oo))
  , Show (v (Relation a) (Relation o))
  , Show a, Show o
  ) => Blockable (CodeFragment v oa oo a o) where
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

instance
  ( Show (v (Relation oa) (Relation oo))
  , Show (v (Relation a) (Relation o))
  , Show a, Show o
  ) => Show (CodeFragment v oa oo a o) where
  show = T.unpack . renderBlock

instance
  ( Parsable (v (Relation oa) (Relation oo))
  , Parsable (v (Relation a) (Relation o))
  , Parsable a, Parsable o
  ) => Parsable (CodeFragment v oa oo a o) where
  parser = codeFragmentParser parser parser parser parser

codeFragmentParser ::
  Parsec Text s (v (Relation oa) (Relation oo)) ->
  Parsec Text s (v (Relation a) (Relation o)) ->
  Parsec Text s a -> Parsec Text s o ->
  Parsec Text s (CodeFragment v oa oo a o)
codeFragmentParser rvo rvi a o = pFrag where
  pFrag =   try fForMe
        <|> try fForThem
        <|> try fForN
        <|> try fLetN
        <|> try fIf
        <|> try fReturn
        <|> try fPass
        <?> "a code fragment"
  fLetN = LetN <$> (keyword "let" *> varname <* symbol "=") <*> parser
  fIf = If <$> (keyword "if" *> statementParser rvo rvi) <*> fBlock
  fForMe = ForMe <$> (keyword "for" *> keyword "action" *> varname) <*>
    (keyword "in" *> rangeParser parser (varParser a)) <*> fBlock
  fForThem = ForThem <$> (keyword "for" *> keyword "outcome" *> varname) <*>
    (keyword "in" *> rangeParser parser (varParser o)) <*> fBlock
  fForN = ForN <$> (keyword "for" *> keyword "number" *> varname) <*>
    (keyword "in" *> boundedRange) <*> fBlock
  fBlock =   try (keyword "end" $> [])
         <|> ((:) <$> codeFragmentParser rvo rvi a o <*> fBlock) <?> "a code block"
  fPass = symbol "pass" $> Pass
  fReturn = try returnThing <|> returnNothing <?> "a return statement"
  returnThing = EarlyReturn . Just <$> (symbol "return" *> varParser a)
  returnNothing = symbol "return" $> EarlyReturn Nothing
  varname = char '$' *> name

type OuterToInner v oa oo a o
  = O2I v oa oo a o (StateT (Context a o) (ExceptT ContextError Identity))
type O2I v oa oo a o m
  = v (Relation oa) (Relation oo) -> m (ModalFormula (v a o))

evalCodeFragment :: (ModalizableVar v, Evalable a o m) =>
  O2I v oa oo a o m -> CodeFragment v oa oo a o -> m (Program v a o -> Program v a o)
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

data Code v oa oo a o
  = Fragment (CodeFragment v oa oo a o) (Code v oa oo a o)
  | Return (Maybe (Var a))

instance
  ( Eq (v (Relation oa) (Relation oo))
  , Eq (v (Relation a) (Relation o))
  , Eq a, Eq o
  ) => Eq (Code v oa oo a o) where
  Fragment x y == Fragment a b = (x == a) && (y == b)
  Return x == Return y = x == y
  _ == _ = False

instance
  ( Show (v (Relation oa) (Relation oo))
  , Show (v (Relation a) (Relation o))
  , Show a, Show o
  ) => Blockable (Code v oa oo a o) where
  blockLines (Fragment f c) = blockLines f ++ blockLines c
  blockLines (Return Nothing) = [(0, "return")]
  blockLines (Return (Just x)) = [(0, T.pack $ printf "return %s" (show x))]

instance
  ( Show (v (Relation oa) (Relation oo))
  , Show (v (Relation a) (Relation o))
  , Show a, Show o
  ) => Show (Code v oa oo a o) where
  show = T.unpack . renderBlock

instance
  ( Parsable (v (Relation oa) (Relation oo))
  , Parsable (v (Relation a) (Relation o))
  , Parsable a, Parsable o
  ) => Parsable (Code v oa oo a o) where
  parser = codeParser parser parser parser parser

codeParser ::
  Parsec Text s (v (Relation oa) (Relation oo)) ->
  Parsec Text s (v (Relation a) (Relation o)) ->
  Parsec Text s a -> Parsec Text s o ->
  Parsec Text s (Code v oa oo a o)
codeParser rvo rvi a o = try frag <|> try ret <?> "some code" where
  frag = Fragment <$> codeFragmentParser rvo rvi a o <*> codeParser rvo rvi a o
  ret = Return <$> (try retThing <|> retNothing <?> "a concluding return statement")
  retThing = Just <$> (symbol "return" *> varParser a)
  retNothing = symbol "return" $> Nothing

evalCode :: (ModalizableVar v, Evalable a o m) =>
  O2I v oa oo a o m -> Code v oa oo a o -> m (Program v a o)
evalCode o2i (Fragment f cont) = evalCodeFragment o2i f >>= (<$> evalCode o2i cont)
evalCode o2i (Return Nothing) = defaultAction >>= evalCode o2i . Return . Just . Lit
evalCode _ (Return (Just v)) = ModalProgram . (L.Val .) . (==) <$> getA v

codeToProgram :: (Eq a, Eq o, ModalizableVar v) =>
  O2I v oa oo a o (StateT (Context a o) (ExceptT ContextError Identity)) ->
  Context a o ->
  Code v oa oo a o ->
  Either ContextError (Program v a o)
codeToProgram o2i context code = runExcept $ fst <$> runStateT (evalCode o2i code) context

-------------------------------------------------------------------------------

type ModalizedCode v a o = Code v Void Void a o

evalModalizedCode :: (ModalizableVar v, Evalable a o m) =>
  ModalizedCode v a o -> m (Program v a o)
evalModalizedCode = evalCode voidToFormula

modalizedCodeParser :: (Ord a, Ord o, ModalizableVar v) =>
  Parsec Text s a -> Parsec Text s o ->
  Parsec Text s (ModalizedCode v a o)
modalizedCodeParser a o = codeParser trivialParser (makeRelParser a o) a o

modalizedCodeToProgram :: (Eq a, Eq o, ModalizableVar v) =>
  Context a o -> ModalizedCode v a o -> Either ContextError (Program v a o)
modalizedCodeToProgram = codeToProgram voidToFormula

-------------------------------------------------------------------------------

type FreeCode v a o = Code v a o a o

evalFreeCode :: (ModalizableVar v, Evalable a o m) => FreeCode v a o -> m (Program v a o)
evalFreeCode = evalCode relToFormula

freeCodeParser ::
  Parsec Text s (v (Relation a) (Relation o)) ->
  Parsec Text s a -> Parsec Text s o ->
  Parsec Text s (FreeCode v a o)
freeCodeParser p = codeParser p p

freeCodeToProgram :: (Eq a, Eq o, ModalizableVar v) =>
  Context a o -> FreeCode v a o -> Either ContextError (Program v a o)
freeCodeToProgram = codeToProgram relToFormula

-------------------------------------------------------------------------------

data Agent v oa oo a o = Agent
  { agentDefaults :: Map Name (Val a o)
  , agentActions :: Maybe [a]
  , agentOutcomes :: Maybe [o]
  , agentName :: Name
  , agentCode :: Code v oa oo a o }

instance
  ( Eq (v (Relation oa) (Relation oo))
  , Eq (v (Relation a) (Relation o))
  , Eq a, Eq o
  ) => Eq (Agent v oa oo a o) where
  Agent p1 as1 os1 n1 c1 == Agent p2 as2 os2 n2 c2 =
    n1 == n2 && p1 == p2 && as1 == as2 && os1 == os2 && c1 == c2

instance
  ( Show (v (Relation oa) (Relation oo))
  , Show (v (Relation a) (Relation o))
  , Show a, Show o
  ) => Blockable (Agent v oa oo a o) where
  blockLines (Agent ps oa oo n c) =
    (0, header) : increaseIndent (blockLines c) where
      header = T.pack $ printf "def %s%s%s%s" (T.unpack n) x y z
      x, y, z :: String
      x = if Map.null ps
        then ""
        else printf "(%s)" $ List.intercalate ("," :: String) $ map showP $ Map.toList ps
      showP (var, Number i) = printf "number %s=%d" (T.unpack var) i
      showP (var, Action a) = printf "action %s=%s" (T.unpack var) (show a)
      showP (var, Outcome o) = printf "outcome %s=%s" (T.unpack var) (show o)
      y = maybe "" (printf "actions=[%s]" . List.intercalate "," . map show) oa
      z = maybe "" (printf "outcomes=[%s]" . List.intercalate "," . map show) oo

instance
  ( Show (v (Relation oa) (Relation oo))
  , Show (v (Relation a) (Relation o))
  , Show a, Show o
  ) => Show (Agent v oa oo a o) where
  show = T.unpack . renderBlock

agentParser ::
  Parsec Text s (v (Relation oa) (Relation oo)) ->
  Parsec Text s (v (Relation a) (Relation o)) ->
  Parsec Text s a -> Parsec Text s o ->
  String -> String -> String ->
  Parsec Text s (Agent v oa oo a o)
agentParser rvo rvi a o kwa kwo kw = makeAgent <$>
  (keyword kw *> name) <*>
  option Map.empty (try $ argsParser a o) <*>
  orderParser kwa a <*>
  orderParser kwo o <*>
  codeParser rvo rvi a o
  where makeAgent n ps as os = Agent ps as os n

compile :: (Eq a, Eq o, ModalizableVar v) =>
  OuterToInner v oa oo a o ->
  Context a o -> Agent v oa oo a o ->
  Either ContextError (Name, Program v a o)
compile o2i x agent = (agentName agent,) . simplified <$> getProgram where
  getProgram = codeToProgram o2i context (agentCode agent)
  simplified = affectFormula L.simplify
  context = x{
    variables=Map.union (variables x) (agentDefaults agent),
    actionList=fromMaybe (actionList x) (agentActions agent),
    outcomeList=fromMaybe (outcomeList x) (agentOutcomes agent) }

argsParser :: Parsec Text s a -> Parsec Text s o -> Parsec Text s (Map Name (Val a o))
argsParser a o = Map.fromList <$> parens (arg `sepBy` comma) where
  arg = try num <|> try act <|> try out <?> "an argument"
  num = keyword "number" *> ((,) <$> name <*> (symbol "=" *> (Number <$> parser)))
  act = keyword "actions" *> ((,) <$> name <*> (symbol "=" *> (Action <$> a)))
  out = keyword "outcomes" *> ((,) <$> name <*> (symbol "=" *> (Outcome <$> o)))

orderParser :: String -> Parsec Text s a -> Parsec Text s (Maybe [a])
orderParser kw p = try acts <|> try dunno <|> pure Nothing where
  acts = Just <$> (keyword kw *> symbol "=" *> brackets (p `sepEndBy` comma))
  dunno = brackets (string "...") $> Nothing

-------------------------------------------------------------------------------

type ModalizedAgent v a o = Agent v Void Void a o

makeModalizedAgent :: Name -> ModalizedCode v a o -> ModalizedAgent v a o
makeModalizedAgent = Agent Map.empty Nothing Nothing

compileModalizedAgent :: (Eq a, Eq o, ModalizableVar v) =>
  Context a o -> ModalizedAgent v a o -> Either ContextError (Name, Program v a o)
compileModalizedAgent = compile voidToFormula

modalizedAgentParser :: (Ord a, Ord o, ModalizableVar v) =>
  Parsec Text s a -> Parsec Text s o -> String -> String -> String ->
  Parsec Text s (ModalizedAgent v a o)
modalizedAgentParser a o = agentParser trivialParser (makeRelParser a o) a o

-------------------------------------------------------------------------------

type FreeAgent v a o = Agent v a o a o

makeFreeAgent :: Name -> FreeCode v a o -> FreeAgent v a o
makeFreeAgent = Agent Map.empty Nothing Nothing

compileFreeAgent :: (Eq a, Eq o, ModalizableVar v) =>
  Context a o -> FreeAgent v a o -> Either ContextError (Name, Program v a o)
compileFreeAgent = compile relToFormula

freeAgentParser :: (Ord a, Ord o, ModalizableVar v) =>
  Parsec Text s a -> Parsec Text s o -> String -> String -> String ->
  Parsec Text s (FreeAgent v a o)
freeAgentParser a o = agentParser (makeRelParser a o) (makeRelParser a o) a o
