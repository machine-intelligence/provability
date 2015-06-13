{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Modal.Statement where
import Prelude hiding (readFile, sequence, mapM, foldr1, concat, concatMap)
import Control.Applicative
import Control.Arrow ((***))
import Control.Monad.Except hiding (mapM, sequence)
import Control.Monad.State hiding (mapM, sequence, state)
import Data.Bifunctor
import Data.Bitraversable
import Data.Map (Map)
import Data.Set (Set)
import Data.Foldable
import Data.Traversable
import Modal.Formulas (ModalFormula)
import Modal.Parser
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Expr
import Text.Parsec.Text
import Text.Printf (printf)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Modal.Formulas as F

-------------------------------------------------------------------------------

data EvalError
  = UnknownVar Name ValType
  | WrongType Name ValType ValType
  deriving (Eq, Ord)

instance Show EvalError where
  show (UnknownVar n t) = printf "%s variable %s is undefined" (show t) (show n)
  show (WrongType n x y) = printf "%s variable %s is not a %s" (show x) (show n) (show y)

type EvalErrorM m = (Applicative m, MonadError EvalError m)

-------------------------------------------------------------------------------

data Val a o = Number Int | Action a | Outcome o deriving (Eq, Ord, Read, Show)

renderVal :: (Show a, Show o) => Val a o -> String
renderVal (Number i) = show i
renderVal (Action a) = show a
renderVal (Outcome o) = show o

data ValType = NumberT | ActionT | OutcomeT deriving (Eq, Ord, Enum)

instance Show ValType where
  show NumberT = "number"
  show ActionT = "action"
  show OutcomeT = "outcome"

typeOf :: Val a o -> ValType
typeOf (Number _) = NumberT
typeOf (Action _) = ActionT
typeOf (Outcome _) = OutcomeT

typesMatch :: Val a o -> Val a o -> Bool
typesMatch x y = typeOf x == typeOf y

-------------------------------------------------------------------------------

data PConf a o = PConf
  { actSym :: String
  , outSym :: String
  , parseA :: Parser a
  , parseO :: Parser o }

numSym :: PConf a o -> String
numSym = const "#"

parseAref :: PConf a o -> Parser (Ref a)
parseAref = refParser . parseA

parseOref :: PConf a o -> Parser (Ref o)
parseOref = refParser . parseO

-------------------------------------------------------------------------------

data Context a o = Context
  { variables :: Map Name (Val a o)
  , actionList :: [a]
  , outcomeList :: [o]
  } deriving (Eq, Show)
type Contextual a o m = (EvalErrorM m, MonadState (Context a o) m)
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

getA :: Contextual a o m => Ref a -> m a
getA (Ref n) = variables <$> get >>= \vs -> case Map.lookup n vs of
  (Just (Action a)) -> return a
  (Just (Outcome _)) -> throwError $ WrongType n ActionT OutcomeT
  (Just (Number _)) -> throwError $ WrongType n ActionT NumberT
  Nothing -> throwError $ UnknownVar n ActionT
getA (Lit a) = return a

getO :: Contextual a o m => Ref o -> m o
getO (Ref n) = variables <$> get >>= \vs -> case Map.lookup n vs of
  (Just (Outcome o)) -> return o
  (Just (Action _)) -> throwError $ WrongType n OutcomeT ActionT
  (Just (Number _)) -> throwError $ WrongType n OutcomeT NumberT
  Nothing -> throwError $ UnknownVar n OutcomeT
getO (Lit o) = return o

getN :: Contextual a o m => Ref Int -> m Int
getN (Ref n) = variables <$> get >>= \vs -> case Map.lookup n vs of
  (Just (Number i)) -> return i
  (Just (Outcome _)) -> throwError $ WrongType n ActionT OutcomeT
  (Just (Action _)) -> throwError $ WrongType n OutcomeT ActionT
  Nothing -> throwError $ UnknownVar n NumberT
getN (Lit i) = return i

getAs :: Contextual a o m => m [a]
getAs = actionList <$> get

getOs :: Contextual a o m => m [o]
getOs = outcomeList <$> get

defaultAction :: Contextual a o m => m a
defaultAction = head <$> getAs

-------------------------------------------------------------------------------

data Ref a = Ref Name | Lit a deriving (Eq, Ord, Read)

instance Show a => Show (Ref a) where
  show (Ref n) = '&' : n
  show (Lit x) = show x

instance Parsable a => Parsable (Ref a) where
  parser = refParser parser

lit :: Ref a -> Maybe a
lit (Lit a) = Just a
lit (Ref _) = Nothing

refParser :: Parser x -> Parser (Ref x)
refParser p =   try (Lit <$> p)
            <|> try (Ref <$> (char '&' *> name))
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

relationParser :: Parser x -> Parser (Relation x)
relationParser p = go where
  go =   try (Equals <$> (sEquals *> p))
     <|> try (NotEquals <$> (sNotEquals *> p))
     <|> try (In <$> (sIn *> set))
     <|> NotIn <$> (sNotIn *> set)
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

relToMentions :: Relation a -> [a]
relToMentions (Equals a) = [a]
relToMentions (In as) = as
relToMentions (NotEquals a) = [a]
relToMentions (NotIn as) = as

relToFormula :: AgentVar v => v (Relation a) (Relation o) -> ModalFormula (v a o)
relToFormula = bisequence . bimap toF toF where
  toF (Equals a) = F.Var a
  toF (In []) = F.Val False
  toF (In as) = foldr1 F.Or $ map F.Var as
  toF (NotEquals a) = F.Neg $ toF (Equals a)
  toF (NotIn []) = F.Val True
  toF (NotIn as) = F.Neg $ toF (In as)

evalVar :: (AgentVar v, Contextual a o m) =>
  v (Relation (Ref a)) (Relation (Ref o)) -> m (ModalFormula (v a o))
evalVar v = relToFormula <$> bitraverse (mapM getA) (mapM getO) v

-------------------------------------------------------------------------------

class Bitraversable v => AgentVar v where
  subagentsIn :: v a o -> Set Name
  subagentsIn = const Set.empty
  makeAgentVarParser :: Parser a -> Parser o -> Parser (v a o)

subagents :: AgentVar v => Map a (ModalFormula (v a o)) -> Set Name
subagents = Set.unions . map fSubagents . Map.elems where
  fSubagents = Set.unions . map subagentsIn . F.allVars

hasNoSubagents :: AgentVar v => Map a (ModalFormula (v a o)) -> Bool
hasNoSubagents = Set.null . subagents

varParser :: AgentVar v => PConf a o -> Parser (v (Relation (Ref a)) (Relation (Ref o)))
varParser pconf = makeAgentVarParser
  (relationParser $ refParser $ symbol (actSym pconf) *> parseA pconf)
  (relationParser $ refParser $ symbol (outSym pconf) *> parseO pconf)

voidToFormula :: (AgentVar v, Monad m) =>
  v (Relation (Ref Void)) (Relation (Ref Void)) -> m (ModalFormula (v a o))
voidToFormula _ = fail "Where did you even get this element of the Void?"

-------------------------------------------------------------------------------

-- TODO: Seriously consider removing all the type dickery here,
-- and just using isModalized at the compile step.
-- Parse-time safety probably isn't worth the code complexity!
-- (But right now, removing it isn't worth the time.)
data Statement v oa oo a o
  = Val Bool
  | Var (v (Relation (Ref oa)) (Relation (Ref oo)))
  | Neg (Statement v oa oo a o)
  | And (Statement v oa oo a o) (Statement v oa oo a o)
  | Or (Statement v oa oo a o) (Statement v oa oo a o)
  | Imp (Statement v oa oo a o) (Statement v oa oo a o)
  | Iff (Statement v oa oo a o) (Statement v oa oo a o)
  | Consistent (Ref Int)
  | Provable (Ref Int) (Statement v a o a o)
  | Possible (Ref Int) (Statement v a o a o)

type HandleVar v oa oo a o m =
  v (Relation (Ref oa)) (Relation (Ref oo)) -> m (ModalFormula (v a o))

instance
  ( Eq (v (Relation (Ref oa)) (Relation (Ref oo)))
  , Eq (v (Relation (Ref a)) (Relation (Ref o)))
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

-- TODO: Add something like getAs and getOs to statement.
-- It will have to be parameterized on a function (oa -> a).
getVars ::
  Statement v oa oo a o ->
  ([v (Relation (Ref oa)) (Relation (Ref oo))], [v (Relation (Ref a)) (Relation (Ref o))])
getVars (Var v) = ([v], [])
getVars (Neg s) = getVars s
getVars (And x y) = let (a, b) = getVars x in ((a ++) *** (b ++)) (getVars y)
getVars (Or x y) = let (a, b) = getVars x in ((a ++) *** (b ++)) (getVars y)
getVars (Imp x y) = let (a, b) = getVars x in ((a ++) *** (b ++)) (getVars y)
getVars (Iff x y) = let (a, b) = getVars x in ((a ++) *** (b ++)) (getVars y)
getVars (Provable _ s) = let (xs, ys) = getVars s in ([], xs ++ ys)
getVars (Possible _ s) = let (xs, ys) = getVars s in ([], xs ++ ys)
getVars _ = ([], [])

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
  (v (Relation (Ref oa)) (Relation (Ref oo)) -> String) ->
  (v (Relation (Ref a)) (Relation (Ref o)) -> String) ->
  Statement v oa oo a o ->
  String
showStatement sf showO showI statement = showsStatement sf showO showI 0 statement ""

showsStatement ::
  ShowStatement ->
  (v (Relation (Ref oa)) (Relation (Ref oo)) -> String) ->
  (v (Relation (Ref a)) (Relation (Ref o)) -> String) ->
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
  ( Show (v (Relation (Ref oa)) (Relation (Ref oo)))
  , Show (v (Relation (Ref a)) (Relation (Ref o)))
  ) => Show (Statement v oa oo a o) where
  show = showStatement (ShowStatement "⊤" "⊥" "¬" "∧" "∨" "→" "↔"
    (printf "Con(%s)")
    (\var -> if var == "0" then "□" else printf "[%s]" var)
    (\var -> if var == "0" then "◇" else printf "<%s>" var)
    ("⌜", "⌝")) show show

statementParser :: forall v oa oo a o. AgentVar v =>
  Parser oa -> Parser oo -> PConf a o -> Parser (Statement v oa oo a o)
statementParser oa oo pconf = buildExpressionParser lTable term where
  pconf' = pconf{parseA=oa, parseO=oo}
  rvo = varParser pconf' :: Parser (v (Relation (Ref oa)) (Relation (Ref oo)))
  descend = statementParser (parseA pconf) (parseO pconf) pconf
  lTable =
    [ [Prefix lNeg]
    , [Infix lAnd AssocRight]
    , [Infix lOr AssocRight]
    , [Infix lImp AssocRight]
    , [Infix lIff AssocRight] ]
  term
    =   parens (statementParser oa oo pconf)
    <|> try cConsistent
    <|> try (fProvable <*> quoted descend)
    <|> try (fPossible <*> quoted descend)
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

_evalStatement :: (AgentVar v, Contextual a o m) =>
  HandleVar v oa oo a o m ->
  Statement v oa oo a o ->
  m (ModalFormula (v a o))
_evalStatement handleVar stm = case stm of
  Val v -> return $ F.Val v
  Var v -> handleVar v
  Neg x -> F.Neg <$> rec x
  And x y -> F.And <$> rec x <*> rec y
  Or x y -> F.Or <$> rec x <*> rec y
  Imp x y -> F.Imp <$> rec x <*> rec y
  Iff x y -> F.Iff <$> rec x <*> rec y
  Consistent v -> F.incon <$> getN v
  Provable v x -> F.boxk <$> getN v <*> _evalStatement evalVar x
  Possible v x -> F.diak <$> getN v <*> _evalStatement evalVar x
  where rec = _evalStatement handleVar

-------------------------------------------------------------------------------

type ModalizedStatement v a o = Statement v Void Void a o

modalizedStatementParser :: AgentVar v => PConf a o -> Parser (ModalizedStatement v a o)
modalizedStatementParser = statementParser parser parser

evalModalizedStatement :: (AgentVar v, Contextual a o m) =>
  ModalizedStatement v a o -> m (ModalFormula (v a o))
evalModalizedStatement = _evalStatement voidToFormula

-------------------------------------------------------------------------------

type UnrestrictedStatement v a o = Statement v a o a o

unrestrictedStatementParser :: AgentVar v => PConf a o -> Parser (UnrestrictedStatement v a o)
unrestrictedStatementParser pconf = statementParser (parseA pconf) (parseO pconf) pconf

evalUnrestrictedStatement :: (AgentVar v, Contextual a o m) =>
  UnrestrictedStatement v a o -> m (ModalFormula (v a o))
evalUnrestrictedStatement = _evalStatement evalVar

class
  ( Eq (Act s)
  , Ord (Act s)
  , Show (Act s)
  , Eq (Out s)
  , Ord (Out s)
  , Show (Out s)
  , AgentVar (Var s)
  ) => IsStatement s where
  type Var s :: * -> * -> *
  type Act s :: *
  type Out s :: *
  makeStatementParser :: PConf (Act s) (Out s) -> Parser s
  evalStatement :: Contextual (Act s) (Out s) m =>
    s -> m (ModalFormula ((Var s) (Act s) (Out s)))
