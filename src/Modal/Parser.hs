{-# LANGUAGE OverloadedStrings #-}
module Modal.Parser where
import Control.Applicative
import Control.Monad (void)
import Data.Char
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many)
import Text.Parsec.Text (Parser)

class Parsable a where
  parser :: Parser a

instance Parsable Int where
  parser = read <$> many1 digit
instance Parsable x => Parsable [x] where
  parser = brackets $ sepEndBy parser comma
instance (Ord x, Parsable x) => Parsable (Set x) where
  parser = Set.fromList <$> braces (sepEndBy parser comma)

keyword :: String -> Parser ()
keyword s = void $ w *> string s <* lookAhead ok <* w where
  ok = try eof <|> void (satisfy isOk)
  isOk c = not (isLetter c) && not (isNumber c) && c `notElem` "-_"

symbol :: String -> Parser ()
symbol s = void $ w *> string s <* w

w :: Parser ()
w = void $ many $ satisfy isSpace

w1 :: Parser ()
w1 = try (void $ many1 $ satisfy isSpace) <|> eof

identifier :: Parser Char -> Parser Char -> Parser Name
identifier h t = Text.pack <$> ((:) <$> h <*> many t)

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

comma :: Parser ()
comma = symbol ","

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

name :: Parser Name
name = identifier (satisfy isFirst) (satisfy isRest) where
  isFirst = (||) <$> isLetter <*> (`elem` "-_'")
  isRest = (||) <$> isFirst <*> isNumber
