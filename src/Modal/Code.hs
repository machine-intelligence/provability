{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Modal.Code
  ( AgentMap
  ---
  , ModalizedDef
  , modalizedDefParser
  , makeModalizedDef
  , compileModalizedAgent
  ---
  , UnrestrictedDef
  , unrestrictedDefParser
  , makeUnrestrictedDef
  , compileUnrestrictedAgent
  ---

  ---
  , agentName
  , agentDefaults
  , agentActions
  , agentOutcomes
  , agentCode
  ---

  ---
  , Var(..)
  , varParser
  , Relation(..)
  , relationParser
  , AgentVar(..)
  ---
  , Val(..)
  , Context(..)
  , getA
  , getO
  , getN
  , emptyContext
  , defaultContext
  , ContextError(..)
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
  , UnrestrictedCode
  , evalUnrestrictedCode
  , unrestrictedCodeParser
  , unrestrictedCodeToProgram
  ---
  , ModalizedStatement
  , modalizedStatementParser
  , evalModalizedStatement
  ---
  , UnrestrictedStatement
  , unrestrictedStatementParser
  , evalUnrestrictedStatement
  ) where
import Prelude hiding (readFile, sequence, mapM, foldr1, concat, concatMap)
import Control.Applicative
import Control.Monad.Except hiding (mapM, sequence)
import Control.Monad.Identity hiding (mapM, sequence)
import Control.Monad.State hiding (mapM, sequence, state)
import Data.Bifunctor
import Data.Bitraversable
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Text (Text)
import Data.Foldable
import Data.Traversable
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
import qualified Data.Text as T
import qualified Modal.Formulas as L

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

data Relation a
  = Equals a
  | In [a]
  | NotEquals a
  | NotIn [a]
  deriving (Eq, Ord, Functor)

instance Show a => Show (Relation a) where
  show (Equals v) = "=" ++ show v
  show (In v) = "∈{" ++ List.intercalate "," (map show v) ++ "}"
  show (NotEquals v) = "≠" ++ show v
  show (NotIn v) = "∉{" ++ List.intercalate "," (map show v) ++ "}"

instance Foldable Relation where
  foldMap addM (Equals a) = addM a
  foldMap addM (In as) = foldMap addM as
  foldMap addM (NotEquals a) = addM a
  foldMap addM (NotIn as) = foldMap addM as

instance Traversable Relation where
  traverse f (Equals a) = Equals <$> f a
  traverse f (In as) = In <$> sequenceA (map f as)
  traverse f (NotEquals a) = NotEquals <$> f a
  traverse f (NotIn as) = NotIn <$> sequenceA (map f as)

instance (Ord a, Parsable a) => Parsable (Relation a) where
  parser = relationParser parser

relationParser :: Parsec Text s x -> Parsec Text s (Relation x)
relationParser p = go <?> "a relation" where
  go =   try (Equals <$> (sEquals *> p))
     <|> try (NotEquals <$> (sNotEquals *> p))
     <|> try (In <$> (sIn *> set))
     <|> try (NotIn <$> (sNotIn *> set))
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
  set = braces $ sepEndBy p comma

relToFormula :: AgentVar v => v (Relation a) (Relation o) -> ModalFormula (v a o)
relToFormula = bisequence . bimap toF toF where
  toF (Equals a) = L.Var a
  toF (In []) = L.Val False
  toF (In as) = foldr1 L.Or $ map L.Var as
  toF (NotEquals a) = L.Neg $ toF (Equals a)
  toF (NotIn []) = L.Val True
  toF (NotIn as) = L.Neg $ toF (In as)

evalVar :: (AgentVar v, Contextual a o m) =>
  v (Relation (Var a)) (Relation (Var o)) -> m (ModalFormula (v a o))
evalVar v = relToFormula <$> bitraverse (mapM getA) (mapM getO) v

-------------------------------------------------------------------------------

class Bitraversable v => AgentVar v where
  otherAgentsReferencedBy :: v a o -> [Name]
  otherAgentsReferencedBy = const []
  makeVParser :: Parsec Text s a -> Parsec Text s o -> Parsec Text s (v a o)

vParser :: AgentVar v =>
  Parsec Text s a -> Parsec Text s o -> Parsec Text s (v (Relation (Var a)) (Relation (Var o)))
vParser a o = makeVParser (relationParser $ varParser a) (relationParser $ varParser o)

trivialParser :: AgentVar v =>
  Parsec Text s (v (Relation (Var Void)) (Relation (Var Void)))
trivialParser = fail "You cannot instantiate the Void."

voidToFormula :: (AgentVar v, Monad m) =>
  v (Relation (Var Void)) (Relation (Var Void)) -> m (ModalFormula (v a o))
voidToFormula _ = fail "Where did you even get this element of the Void?"

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

-------------------------------------------------------------------------------

data Statement v oa oo a o
  = Val Bool
  | Var (v (Relation (Var oa)) (Relation (Var oo)))
  | Neg (Statement v oa oo a o)
  | And (Statement v oa oo a o) (Statement v oa oo a o)
  | Or (Statement v oa oo a o) (Statement v oa oo a o)
  | Imp (Statement v oa oo a o) (Statement v oa oo a o)
  | Iff (Statement v oa oo a o) (Statement v oa oo a o)
  | Consistent (Var Int)
  | Provable (Var Int) (Statement v a o a o)
  | Possible (Var Int) (Statement v a o a o)

type HandleVar v oa oo a o m =
  v (Relation (Var oa)) (Relation (Var oo)) -> m (ModalFormula (v a o))

instance
  ( Eq (v (Relation (Var oa)) (Relation (Var oo)))
  , Eq (v (Relation (Var a)) (Relation (Var o)))
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
  (v (Relation (Var oa)) (Relation (Var oo)) -> String) ->
  (v (Relation (Var a)) (Relation (Var o)) -> String) ->
  Statement v oa oo a o ->
  String
showStatement sf showO showI statement = showsStatement sf showO showI 0 statement ""

showsStatement ::
  ShowStatement ->
  (v (Relation (Var oa)) (Relation (Var oo)) -> String) ->
  (v (Relation (Var a)) (Relation (Var o)) -> String) ->
  Int -> Statement v oa oo a o -> ShowS
showsStatement sf showO showI p statement = result where
  result = case statement of
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
  recO = showsStatement sf showO showI
  recI = showsStatement sf showI showI
  padded o = showString " " . showString o . showString " "
  showBinary o l x r y = recO l x . padded o . recO r y
  showInner sig v i x = showString (sig sf $ show v) . quote (recI i x)
  quote s = let (l, r) = quotes sf in showString l . s . showString r

instance
  ( Show (v (Relation (Var oa)) (Relation (Var oo)))
  , Show (v (Relation (Var a)) (Relation (Var o)))
  ) => Show (Statement v oa oo a o) where
  show = showStatement (ShowStatement "⊤" "⊥" "¬" "∧" "∨" "→" "↔"
    (printf "Con(%s)")
    (\var -> if var == "0" then "□" else printf "[%s]" var)
    (\var -> if var == "0" then "◇" else printf "<%s>" var)
    ("⌜", "⌝")) show show

instance
  ( Parsable (v (Relation (Var oa)) (Relation (Var oo)))
  , Parsable (v (Relation (Var a)) (Relation (Var o)))
  ) => Parsable (Statement v oa oo a o) where
  parser = statementParser parser parser

statementParser ::
  Parsec Text s (v (Relation (Var oa)) (Relation (Var oo))) ->
  Parsec Text s (v (Relation (Var a)) (Relation (Var o))) ->
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
    <|> try cConsistent
    <|> try (fProvable <*> quoted (statementParser rvi rvi))
    <|> try (fPossible <*> quoted (statementParser rvi rvi))
    <|> try (Var <$> rvo)
    <|> try (Val <$> val)
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
  cConsistent = (symbol "Con" $> Consistent) <*> option (Lit 0) parser
  quoted x
    =   try (between (symbol "⌜") (symbol "⌝") x)
    <|> try (between (symbol "[") (symbol "]") x)
  fProvable = try inSym <|> choice [try $ afterSym s | s <- syms] <?> "a box" where
    inSym = Provable <$> (char '[' *> option (Lit 0) parser <* char ']')
    afterSym s = Provable <$> (symbol s  *> option (Lit 0) parser)
    syms = ["□", "Provable", "Box"]
  fPossible = try inSym <|> choice [try $ afterSym s | s <- syms] <?> "a diamond" where
    inSym = Provable <$> (char '<' *> option (Lit 0) parser <* char '>')
    afterSym s = Provable <$> (symbol s  *> option (Lit 0) parser)
    syms = ["◇", "Possible", "Dia", "Diamond"]

evalStatement :: (AgentVar v, Contextual a o m) =>
  HandleVar v oa oo a o m ->
  Statement v oa oo a o ->
  m (ModalFormula (v a o))
evalStatement handleVar stm = case stm of
  Val v -> return $ L.Val v
  Var v -> handleVar v
  Neg x -> L.Neg <$> rec x
  And x y -> L.And <$> rec x <*> rec y
  Or x y -> L.Or <$> rec x <*> rec y
  Imp x y -> L.Imp <$> rec x <*> rec y
  Iff x y -> L.Iff <$> rec x <*> rec y
  Consistent v -> L.incon <$> getN v
  Provable v x -> L.boxk <$> getN v <*> evalStatement evalVar x
  Possible v x -> L.diak <$> getN v <*> evalStatement evalVar x
  where rec = evalStatement handleVar

-------------------------------------------------------------------------------

type ModalizedStatement v a o = Statement v Void Void a o

modalizedStatementParser :: AgentVar v =>
  Parsec Text s (v (Relation (Var a)) (Relation (Var o))) ->
  Parsec Text s (ModalizedStatement v a o)
modalizedStatementParser = statementParser trivialParser

evalModalizedStatement :: (AgentVar v, Contextual a o m) =>
  ModalizedStatement v a o -> m (ModalFormula (v a o))
evalModalizedStatement = evalStatement voidToFormula

-------------------------------------------------------------------------------

type UnrestrictedStatement v a o = Statement v a o a o

unrestrictedStatementParser ::
  Parsec Text s (v (Relation (Var a)) (Relation (Var o))) ->
  Parsec Text s (UnrestrictedStatement v a o)
unrestrictedStatementParser p = statementParser p p

evalUnrestrictedStatement :: (AgentVar v, Contextual a o m) =>
  UnrestrictedStatement v a o -> m (ModalFormula (v a o))
evalUnrestrictedStatement = evalStatement evalVar

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
  ( Eq (v (Relation (Var oa)) (Relation (Var oo)))
  , Eq (v (Relation (Var a)) (Relation (Var o)))
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
  ( Show (v (Relation (Var oa)) (Relation (Var oo)))
  , Show (v (Relation (Var a)) (Relation (Var o)))
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
  ( Show (v (Relation (Var oa)) (Relation (Var oo)))
  , Show (v (Relation (Var a)) (Relation (Var o)))
  , Show a, Show o
  ) => Show (CodeFragment v oa oo a o) where
  show = T.unpack . renderBlock

instance
  ( Parsable (v (Relation (Var oa)) (Relation (Var oo)))
  , Parsable (v (Relation (Var a)) (Relation (Var o)))
  , Parsable a, Parsable o
  ) => Parsable (CodeFragment v oa oo a o) where
  parser = codeFragmentParser parser parser parser parser

codeFragmentParser ::
  Parsec Text s (v (Relation (Var oa)) (Relation (Var oo))) ->
  Parsec Text s (v (Relation (Var a)) (Relation (Var o))) ->
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
  fLetN = LetN <$> (keyword "let" *> varname <* symbol "=") <*> parser
  fIf = If <$> (keyword "if" *> statementParser rvo rvi) <*> fBlock
  fForMe = ForMe <$> (keyword "for" *> keyword "action" *> varname) <*>
    (keyword "in" *> rangeParser parser (varParser a)) <*> fBlock
  fForThem = ForThem <$> (keyword "for" *> keyword "outcome" *> varname) <*>
    (keyword "in" *> rangeParser parser (varParser o)) <*> fBlock
  fForN = ForN <$> (keyword "for" *> keyword "number" *> varname) <*>
    (keyword "in" *> boundedRange) <*> fBlock
  fBlock =   try (keyword "end" $> [])
         <|> ((:) <$> codeFragmentParser rvo rvi a o <*> fBlock)
  fPass = symbol "pass" $> Pass
  fReturn = try returnThing <|> returnNothing <?> "a return statement"
  returnThing = EarlyReturn . Just <$> (symbol "return" *> varParser a)
  returnNothing = symbol "return" $> EarlyReturn Nothing
  varname = char '$' *> name

evalCodeFragment :: (AgentVar v, Evalable a o m) =>
  HandleVar v oa oo a o m -> CodeFragment v oa oo a o -> m (PartialProgram a (v a o))
evalCodeFragment handleVar code = case code of
  ForMe n r inner -> loop (withA n) inner =<< elemsInContext getAs getA r
  ForThem n r inner -> loop (withO n) inner =<< elemsInContext getOs getO r
  ForN n r inner -> loop (withN n) inner =<< elemsInContext (return [0..]) getN r
  LetN n x -> evalExpr x >>= modify . withN n >> return id
  If s block -> do
    cond <- evalStatement handleVar s
    thens <- mapM (evalCodeFragment handleVar) block
    let yes = foldr1 (.) thens
    return (\continue act ->
      (cond %^ yes continue act) %| (L.Neg cond %^ continue act))
  EarlyReturn x -> const <$> evalCode handleVar (Return x)
  Pass -> return id
  where loop update block xs
          | null xs = return id
          | otherwise = foldr1 (.) . concat <$> mapM doFragment xs
          where doFragment x = modify (update x) >> mapM (evalCodeFragment handleVar) block

-------------------------------------------------------------------------------

data Code v oa oo a o
  = Fragment (CodeFragment v oa oo a o) (Code v oa oo a o)
  | Return (Maybe (Var a))

instance
  ( Eq (v (Relation (Var oa)) (Relation (Var oo)))
  , Eq (v (Relation (Var a)) (Relation (Var o)))
  , Eq a, Eq o
  ) => Eq (Code v oa oo a o) where
  Fragment x y == Fragment a b = (x == a) && (y == b)
  Return x == Return y = x == y
  _ == _ = False

instance
  ( Show (v (Relation (Var oa)) (Relation (Var oo)))
  , Show (v (Relation (Var a)) (Relation (Var o)))
  , Show a, Show o
  ) => Blockable (Code v oa oo a o) where
  blockLines (Fragment f c) = blockLines f ++ blockLines c
  blockLines (Return Nothing) = [(0, "return")]
  blockLines (Return (Just x)) = [(0, T.pack $ printf "return %s" (show x))]

instance
  ( Show (v (Relation (Var oa)) (Relation (Var oo)))
  , Show (v (Relation (Var a)) (Relation (Var o)))
  , Show a, Show o
  ) => Show (Code v oa oo a o) where
  show = T.unpack . renderBlock

instance
  ( Parsable (v (Relation (Var oa)) (Relation (Var oo)))
  , Parsable (v (Relation (Var a)) (Relation (Var o)))
  , Parsable a, Parsable o
  ) => Parsable (Code v oa oo a o) where
  parser = codeParser parser parser parser parser

codeParser ::
  Parsec Text s (v (Relation (Var oa)) (Relation (Var oo))) ->
  Parsec Text s (v (Relation (Var a)) (Relation (Var o))) ->
  Parsec Text s a -> Parsec Text s o ->
  Parsec Text s (Code v oa oo a o)
codeParser rvo rvi a o = try frag <|> try ret where
  frag = Fragment <$> codeFragmentParser rvo rvi a o <*> codeParser rvo rvi a o
  ret = Return <$> ((try retThing <|> retNothing <?> "a return statement") <* end)
  end = try (keyword "end") <?> "an 'end'"
  retThing = Just <$> (symbol "return" *> varParser a)
  retNothing = symbol "return" $> Nothing

evalCode :: (AgentVar v, Evalable a o m) =>
  HandleVar v oa oo a o m -> Code v oa oo a o -> m (ModalProgram a (v a o))
evalCode o2i (Fragment f cont) = evalCodeFragment o2i f >>= (<$> evalCode o2i cont)
evalCode o2i (Return Nothing) = defaultAction >>= evalCode o2i . Return . Just . Lit
evalCode _ (Return (Just v)) = (L.Val .) . (==) <$> getA v

codeToProgram :: (Eq a, Ord a, Eq o, AgentVar v) =>
  HandleVar v oa oo a o (StateT (Context a o) (ExceptT ContextError Identity)) ->
  Context a o ->
  Code v oa oo a o ->
  Either ContextError (AgentMap v a o)
codeToProgram handleVar context code = runExcept $ do
  (prog, state) <- runStateT (evalCode handleVar code) context
  return $ Map.fromList [(a, prog a) | a <- actionList state]

-------------------------------------------------------------------------------

type ModalizedCode v a o = Code v Void Void a o

evalModalizedCode :: (AgentVar v, Evalable a o m) =>
  ModalizedCode v a o -> m (ModalProgram a (v a o))
evalModalizedCode = evalCode voidToFormula

modalizedCodeParser :: (Ord a, Ord o, AgentVar v) =>
  Parsec Text s a -> Parsec Text s o ->
  Parsec Text s (ModalizedCode v a o)
modalizedCodeParser a o = codeParser trivialParser (vParser a o) a o

modalizedCodeToProgram :: (Eq a, Ord a, Eq o, AgentVar v) =>
  Context a o -> ModalizedCode v a o -> Either ContextError (AgentMap v a o)
modalizedCodeToProgram = codeToProgram voidToFormula

-------------------------------------------------------------------------------

type UnrestrictedCode v a o = Code v a o a o

evalUnrestrictedCode :: (AgentVar v, Evalable a o m) =>
  UnrestrictedCode v a o -> m (ModalProgram a (v a o))
evalUnrestrictedCode = evalCode evalVar

unrestrictedCodeParser ::
  Parsec Text s (v (Relation (Var a)) (Relation (Var o))) ->
  Parsec Text s a -> Parsec Text s o ->
  Parsec Text s (UnrestrictedCode v a o)
unrestrictedCodeParser p = codeParser p p

unrestrictedCodeToProgram :: (Eq a, Ord a, Eq o, AgentVar v) =>
  Context a o -> UnrestrictedCode v a o -> Either ContextError (AgentMap v a o)
unrestrictedCodeToProgram = codeToProgram evalVar

-------------------------------------------------------------------------------

data Def v oa oo a o = Def
  { agentDefaults :: Map Name (Val a o)
  , agentActions :: Maybe [a]
  , agentOutcomes :: Maybe [o]
  , agentName :: Name
  , agentCode :: Code v oa oo a o }

type AgentMap v a o = Map a (ModalFormula (v a o))

instance
  ( Eq (v (Relation (Var oa)) (Relation (Var oo)))
  , Eq (v (Relation (Var a)) (Relation (Var o)))
  , Eq a, Eq o
  ) => Eq (Def v oa oo a o) where
  Def p1 as1 os1 n1 c1 == Def p2 as2 os2 n2 c2 =
    n1 == n2 && p1 == p2 && as1 == as2 && os1 == os2 && c1 == c2

instance
  ( Show (v (Relation (Var oa)) (Relation (Var oo)))
  , Show (v (Relation (Var a)) (Relation (Var o)))
  , Show a, Show o
  ) => Blockable (Def v oa oo a o) where
  blockLines (Def ps oa oo n c) =
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
  ( Show (v (Relation (Var oa)) (Relation (Var oo)))
  , Show (v (Relation (Var a)) (Relation (Var o)))
  , Show a, Show o
  ) => Show (Def v oa oo a o) where
  show = T.unpack . renderBlock

defParser ::
  Parsec Text s (v (Relation (Var oa)) (Relation (Var oo))) ->
  Parsec Text s (v (Relation (Var a)) (Relation (Var o))) ->
  Parsec Text s a -> Parsec Text s o ->
  String -> String -> String ->
  Parsec Text s (Def v oa oo a o)
defParser rvo rvi a o kwa kwo kw = makeDef <$>
  (keyword kw *> name) <*>
  option Map.empty (try $ argsParser a o) <*>
  orderParser kwa a <*>
  orderParser kwo o <*>
  codeParser rvo rvi a o
  where makeDef n ps as os = Def ps as os n

compile :: (Eq a, Ord a, Eq o, AgentVar v) =>
  HandleVar v oa oo a o (StateT (Context a o) (ExceptT ContextError Identity)) ->
  Context a o -> Def v oa oo a o ->
  Either ContextError (Name, AgentMap v a o)
compile o2i x agent = (agentName agent,) . Map.map L.simplify <$> getProgram where
  getProgram = codeToProgram o2i context (agentCode agent)
  context = x{
    variables=Map.union (variables x) (agentDefaults agent),
    actionList=fromMaybe (actionList x) (agentActions agent),
    outcomeList=fromMaybe (outcomeList x) (agentOutcomes agent) }

argsParser :: Parsec Text s a -> Parsec Text s o -> Parsec Text s (Map Name (Val a o))
argsParser a o = Map.fromList <$> parens (arg `sepBy` comma) where
  arg = try num <|> try act <|> try out
  num = keyword "number" *> ((,) <$> name <*> (symbol "=" *> (Number <$> parser)))
  act = keyword "actions" *> ((,) <$> name <*> (symbol "=" *> (Action <$> a)))
  out = keyword "outcomes" *> ((,) <$> name <*> (symbol "=" *> (Outcome <$> o)))

orderParser :: String -> Parsec Text s a -> Parsec Text s (Maybe [a])
orderParser kw p = try acts <|> try dunno <|> pure Nothing where
  acts = Just <$> (keyword kw *> symbol "=" *> brackets (p `sepEndBy` comma))
  dunno = brackets (string "...") $> Nothing

-------------------------------------------------------------------------------

type ModalizedDef v a o = Def v Void Void a o

makeModalizedDef :: Name -> ModalizedCode v a o -> ModalizedDef v a o
makeModalizedDef = Def Map.empty Nothing Nothing

modalizedDefParser :: (Ord a, Ord o, AgentVar v) =>
  Parsec Text s a -> Parsec Text s o -> String -> String -> String ->
  Parsec Text s (ModalizedDef v a o)
modalizedDefParser a o = defParser trivialParser (vParser a o) a o

compileModalizedAgent :: (Eq a, Ord a, Eq o, AgentVar v) =>
  Context a o -> ModalizedDef v a o -> Either ContextError (Name, AgentMap v a o)
compileModalizedAgent = compile voidToFormula

-------------------------------------------------------------------------------

type UnrestrictedDef v a o = Def v a o a o

makeUnrestrictedDef :: Name -> UnrestrictedCode v a o -> UnrestrictedDef v a o
makeUnrestrictedDef = Def Map.empty Nothing Nothing

unrestrictedDefParser :: (Ord a, Ord o, AgentVar v) =>
  Parsec Text s a -> Parsec Text s o -> String -> String -> String ->
  Parsec Text s (UnrestrictedDef v a o)
unrestrictedDefParser a o = defParser (vParser a o) (vParser a o) a o

compileUnrestrictedAgent :: (Eq a, Ord a, Eq o, AgentVar v) =>
  Context a o -> UnrestrictedDef v a o -> Either ContextError (Name, AgentMap v a o)
compileUnrestrictedAgent = compile evalVar
