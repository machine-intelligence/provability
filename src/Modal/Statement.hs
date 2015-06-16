{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Modal.Statement where
import Prelude hiding (readFile, sequence, mapM, foldr1, concat, concatMap)
import Control.Applicative
import Control.Monad.Except hiding (mapM, sequence)
import Data.Bifunctor
import Data.Bitraversable
import Data.Maybe (fromMaybe)
import Data.Foldable
import Modal.CompileContext
import Modal.Formulas (ModalFormula)
import Modal.Parser
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Expr
import Text.Parsec.Text
import Text.Printf (printf)
import qualified Data.List as List
import qualified Modal.Formulas as F

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

relToFormula :: Bitraversable v => v (Relation a) (Relation o) -> ModalFormula (v a o)
relToFormula = bisequence . bimap toF toF where
  toF (Equals a) = F.Var a
  toF (In []) = F.Val False
  toF (In as) = foldr1 F.Or $ map F.Var as
  toF (NotEquals a) = F.Neg $ toF (Equals a)
  toF (NotIn []) = F.Val True
  toF (NotIn as) = F.Neg $ toF (In as)

-------------------------------------------------------------------------------

data ActionClaim = ActionClaim Name (Maybe Name) (Relation (Ref Value))
  deriving (Eq, Ord)

instance Show ActionClaim where
  show (ActionClaim n o r) = printf "%s(%s)%s" n (fromMaybe "" o) (show r)

instance Parsable ActionClaim where
  parser = ActionClaim <$>
             name <*>
             optional (parens name) <*>
             relationParser (refParser value)

-------------------------------------------------------------------------------

data Statement
  = Val Bool
  | Var ActionClaim
  | Neg Statement
  | And Statement Statement
  | Or Statement Statement
  | Imp Statement Statement
  | Iff Statement Statement
  | Consistent (Ref Int)
  | Provable (Ref Int) Statement
  | Possible (Ref Int) Statement
  deriving Eq

type HandleVar v m = ActionClaim -> m (ModalFormula v)

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

showsStatement :: ShowStatement -> Int -> Statement -> ShowS
showsStatement sf p statement = result where
  result = case statement of
    Val l -> showString $ if l then topSymbol sf else botSymbol sf
    Var v -> showString $ show v
    Neg x -> showParen (p > 8) $ showString (notSymbol sf) . showsStatement sf 8 x
    And x y -> showParen (p > 7) $ showBinary (andSymbol sf) 7 x 8 y
    Or  x y -> showParen (p > 6) $ showBinary (orSymbol sf) 6 x 7 y
    Imp x y -> showParen (p > 5) $ showBinary (impSymbol sf) 6 x 5 y
    Iff x y -> showParen (p > 4) $ showBinary (iffSymbol sf) 5 x 4 y
    Consistent v -> showString $ conSign sf (show v)
    Provable v x -> showParen (p > 8) $ showInner boxSign v 8 x
    Possible v x -> showParen (p > 8) $ showInner diaSign v 8 x
  padded o = showString " " . showString o . showString " "
  showBinary o l x r y = showsStatement sf l x . padded o . showsStatement sf r y
  showInner sig v i x = showString (sig sf $ show v) . quote (showsStatement sf i x)
  quote s = let (l, r) = quotes sf in showString l . s . showString r

instance Show Statement where
  showsPrec = showsStatement (ShowStatement "⊤" "⊥" "¬" "∧" "∨" "→" "↔"
    (printf "Con(%s)")
    (\var -> if var == "0" then "□" else printf "[%s]" var)
    (\var -> if var == "0" then "◇" else printf "<%s>" var)
    ("⌜", "⌝"))

instance Parsable Statement where
  parser = buildExpressionParser lTable term where
    lTable =
      [ [Prefix lNeg]
      , [Infix lAnd AssocRight]
      , [Infix lOr AssocRight]
      , [Infix lImp AssocRight]
      , [Infix lIff AssocRight] ]
    term
      =   parens parser
      <|> try cConsistent
      <|> try (fProvable <*> quoted parser)
      <|> try (fPossible <*> quoted parser)
      <|> try (Var <$> parser)
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
    fProvable = try inSym <|> choice (map (try . afterSym) syms) <?> "a box" where
      inSym = Provable <$> (char '[' *> option (Lit 0) parser <* char ']')
      afterSym s = Provable <$> (symbol s  *> option (Lit 0) parser)
      syms = ["□", "Provable", "Box"]
    fPossible = try inSym <|> choice (map (try . afterSym) syms) <?> "a diamond" where
      inSym = Possible <$> (char '<' *> option (Lit 0) parser <* char '>')
      afterSym s = Possible <$> (symbol s  *> option (Lit 0) parser)
      syms = ["◇", "Possible", "Dia", "Diamond"]

evalStatement :: MonadCompile m => HandleVar v m -> Statement -> m (ModalFormula v)
evalStatement handleVar stm = case stm of
  Val v -> return $ F.Val v
  Var v -> handleVar v
  Neg x -> F.Neg <$> rec x
  And x y -> F.And <$> rec x <*> rec y
  Or x y -> F.Or <$> rec x <*> rec y
  Imp x y -> F.Imp <$> rec x <*> rec y
  Iff x y -> F.Iff <$> rec x <*> rec y
  Consistent v -> F.incon <$> lookupN v
  Provable r x -> F.boxk <$> lookupN r <*> rec x
  Possible r x -> F.diak <$> lookupN r <*> rec x
  where rec = evalStatement handleVar
