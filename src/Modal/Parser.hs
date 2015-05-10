{-# LANGUAGE OverloadedStrings #-}
module Modal.Parser where
import Control.Applicative
import Control.Monad (void)
import Data.Char
import Data.Functor.Identity
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
  parser = listParser parser
instance (Ord x, Parsable x) => Parsable (Set x) where
  parser = setParser parser
instance Parsable a => Parsable (Identity a) where
  parser = Identity <$> parser

listParser :: Parser x -> Parser [x]
listParser p = brackets $ sepEndBy p comma

setParser :: Ord x => Parser x -> Parser (Set x)
setParser p = Set.fromList <$> braces (sepEndBy p comma)

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
name = identifier (satisfy isNameFirstChar) (satisfy isNameChar)

isNameFirstChar, isNameChar :: Char -> Bool
isNameFirstChar = (||) <$> isLetter <*> (`elem` "-_'")
isNameChar = (||) <$> isNameFirstChar <*> isNumber
