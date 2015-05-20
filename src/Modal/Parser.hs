{-# LANGUAGE OverloadedStrings #-}
module Modal.Parser where
import Control.Applicative
import Control.Monad (void)
import Data.Char
import Data.Functor.Identity
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Text (Text)
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many)

class Parsable a where
  parser :: Parsec Text s a

instance Parsable Int where
  parser = read <$> many1 digit
instance Parsable x => Parsable [x] where
  parser = listParser parser
instance (Ord x, Parsable x) => Parsable (Set x) where
  parser = setParser parser
instance Parsable a => Parsable (Identity a) where
  parser = Identity <$> parser
instance Parsable Void where
  parser = fail "Cannot instantiate the Void."

listParser :: Parsec Text s x -> Parsec Text s [x]
listParser p = brackets $ sepEndBy p comma

setParser :: Ord x => Parsec Text s x -> Parsec Text s (Set x)
setParser p = Set.fromList <$> braces (sepEndBy p comma)

keyword :: String -> Parsec Text s ()
keyword s = void $ w *> string s <* lookAhead ok <* w where
  ok = try eof <|> void (satisfy isOk)
  isOk c = not (isLetter c) && not (isNumber c) && c `notElem` "-_"

symbol :: String -> Parsec Text s ()
symbol s = void $ w *> string s <* w

w :: Parsec Text s ()
w = void $ many $ satisfy isSpace

w1 :: Parsec Text s ()
w1 = try (void $ many1 $ satisfy isSpace) <|> eof

identifier :: Parsec Text s Char -> Parsec Text s Char -> Parsec Text s Name
identifier h t = Text.pack <$> ((:) <$> h <*> many t)

parens :: Parsec Text s a -> Parsec Text s a
parens = between (symbol "(") (symbol ")")

comma :: Parsec Text s ()
comma = symbol ","

brackets :: Parsec Text s a -> Parsec Text s a
brackets = between (symbol "[") (symbol "]")

braces :: Parsec Text s a -> Parsec Text s a
braces = between (symbol "{") (symbol "}")

name :: Parsec Text s Name
name = identifier (satisfy isNameFirstChar) (satisfy isNameChar)

text :: Parsec Text s Name
text = identifier (satisfy isNameChar) (satisfy isNameChar)

isNameFirstChar, isNameChar :: Char -> Bool
isNameFirstChar = (||) <$> isLetter <*> (`elem` "-_'")
isNameChar = (||) <$> isNameFirstChar <*> isNumber
