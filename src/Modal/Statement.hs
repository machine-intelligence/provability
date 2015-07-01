{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Modal.Statement where
import Prelude hiding (readFile, sequence, mapM, foldr1, concat, concatMap)
import Control.Applicative
import Modal.CompilerBase hiding (main)
import Modal.Formulas (ModalFormula)
import Modal.Parser hiding (main)
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Expr
import Text.Parsec.Text (Parser)
import Text.Printf (printf)
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Modal.Formulas as F

-------------------------------------------------------------------------------

data Statement
  = Val Bool
  | Var ParsedClaim
  | Neg Statement
  | And Statement Statement
  | Or Statement Statement
  | Imp Statement Statement
  | Iff Statement Statement
  | Consistent (Ref Int)
  | Provable (Ref Int) Statement
  | Possible (Ref Int) Statement
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
      , [ Infix lAnd AssocRight ]
      , [ Infix lOr AssocRight ]
      , [ Infix lImp AssocRight ]
      , [ Infix lIff AssocRight ] ]
    term
      =   parens parser
      <|> try cConsistent
      <|> try (fProvable <*> quoted parser)
      <|> try (fPossible <*> quoted parser)
      <|> try (Var <$> parser)
      <|> try (Val <$> val)
      <?> "a statement term"
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
          <|> try (symbol "~")
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
    cConsistent = (symbol "Con" $> Consistent) <*> option (Lit 0) (parens parser)
    quoted x
      =   try (between (symbol "⌜") (symbol "⌝") x)
      <|> try (between (symbol "[") (symbol "]") x)
    fProvable = try inSym <|> choice (map (try . afterSym) syms) <?> "a box" where
      inSym = Provable <$> (char '[' *> option (Lit 0) parser <* char ']')
      afterSym s = Provable <$> (symbol s *> option (Lit 0) (parens parser))
      syms = ["□", "Provable", "Box"]
    fPossible = try inSym <|> choice (map (try . afterSym) syms) <?> "a diamond" where
      inSym = Possible <$> (char '<' *> option (Lit 0) parser <* char '>')
      afterSym s = Possible <$> (symbol s  *> option (Lit 0) (parens parser))
      syms = ["◇", "Possible", "Dia", "Diamond"]

claimsParsed :: Statement -> [ParsedClaim]
claimsParsed statement = case statement of
  Val _ -> []
  Var a -> [a]
  Neg s -> claimsParsed s
  And x y -> claimsParsed x ++ claimsParsed y
  Or x y -> claimsParsed x ++ claimsParsed y
  Imp x y -> claimsParsed x ++ claimsParsed y
  Iff x y -> claimsParsed x ++ claimsParsed y
  Consistent _ -> []
  Provable _ s -> claimsParsed s
  Possible _ s -> claimsParsed s

type HandleVar v m = ParsedClaim -> m (ModalFormula v)

compileStatement :: MonadCompile m => HandleVar v m -> Statement -> m (ModalFormula v)
compileStatement handleVar stm = case stm of
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
  where rec = compileStatement handleVar

-------------------------------------------------------------------------------
-- Testing

main :: IO ()
main = do
  let fails = verifyParserFails (parser :: Parser Statement)
  let simpleClaim = ParsedClaim "A" Nothing (Equals $ Lit "a")
  verifyParsable "⊤" (Val True)
  verifyParsable "⊥" (Val False)
  fails          "a"
  verifyParsable "A()=a" (Var simpleClaim)
  verifyParsable "¬A()=a" (Neg $ Var simpleClaim)
  verifyParsable "A()=a ∧ A()=a" (And (Var simpleClaim) (Var simpleClaim))
  verifyParsable "A()=a∨A()=a" (Or (Var simpleClaim) (Var simpleClaim))
  verifyParsable "A()=a  →  A()=a" (Imp (Var simpleClaim) (Var simpleClaim))
  verifyParsable "(⊤ ∨ ⊥) ∧ (⊤ ∨ ⊥)" (And
    (Or (Val True) (Val False)) (Or (Val True) (Val False)))
  verifyParsable "⊤ ∧ ⊤ ∨ ⊥ ∧ ⊥" (Or
    (And (Val True) (Val True)) (And (Val False) (Val False)))
  verifyParsable "⊤ → ⊥ ∧ ⊥" (Imp (Val True) (And (Val False) (Val False)))
  verifyParsable "⊤↔⊥" (Iff (Val True) (Val False))
  fails          "x ∧ ∨ y"
  verifyParsable "Con(1)" (Consistent (Lit 1))
  verifyParsable "Con(&n)" (Consistent (Ref "n"))
  fails          "Con 1"
  verifyParsable "□⌜⊤⌝" (Provable (Lit 0) (Val True))
  verifyParsable "[][top]" (Provable (Lit 0) (Val True))
  verifyParsable "[1][top]" (Provable (Lit 1) (Val True))
  verifyParsable "Provable[top]" (Provable (Lit 0) (Val True))
  verifyParsable "Provable(1)[top]" (Provable (Lit 1) (Val True))
  verifyParsable "◇⌜⊤⌝" (Possible (Lit 0) (Val True))
  verifyParsable "<>[top]" (Possible (Lit 0) (Val True))
  verifyParsable "<1>[top]" (Possible (Lit 1) (Val True))
  verifyParsable "Possible[top]" (Possible (Lit 0) (Val True))
  verifyParsable "Possible(1)[top]" (Possible (Lit 1) (Val True))
  verifyParsable "Con(1) implies ¬□⌜⊥⌝" (Imp
    (Consistent (Lit 1)) (Neg (Provable (Lit 0) (Val False))))
  verifyParsable "Con(1) implies ~[][bottom]" (Imp
    (Consistent (Lit 1)) (Neg (Provable (Lit 0) (Val False))))
  putStrLn ""
