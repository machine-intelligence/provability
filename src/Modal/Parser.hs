{-# LANGUAGE OverloadedStrings #-}
module Modal.Parser where
import Control.Applicative
import Control.Monad (void)
import Data.Char
import Data.Functor.Identity
import Data.Set (Set)
import Data.Text (Text)
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many)
import Text.Parsec.Text (Parser)
import Text.Printf (printf)
import qualified Data.Set as Set
import qualified Data.Text as Text

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
keyword s = void $ try w *> try (string s) <* lookAhead ok <* w where
  ok = try eof <|> void (satisfy isOk)
  isOk c = not (isLetter c) && not (isNumber c) && c `notElem` ("-_" :: String)

symbol :: String -> Parser ()
symbol s = void $ w *> string s <* w

eol :: Parser ()
eol = try (void newline) <|> try eof <?> "a line ending"

eols :: Parser ()
eols = void $ many1 (w *> newline)

ignoredToken :: Parser ()
ignoredToken
  = try _blockComment
  <|> try _lineComment
  <|> void (char ' ')
  <?> "whitespace"

_blockComment :: Parser ()
_blockComment = void (o *> many innards *> c) <?> "a block comment" where
  o = string "{-"
  c = string "-}"
  safeMark = char '-' *> notFollowedBy (char '}')
  innards = _blockComment <|> void (noneOf "-") <|> try safeMark

_lineComment :: Parser ()
_lineComment = void ((string "--" *> many (noneOf "\n")) <?> "a line comment")

ignoredLine :: Parser ()
ignoredLine = many (void (char '\t') <|> ignoredToken) *> void newline

w :: Parser ()
w = void $ many ignoredToken

w1 :: Parser ()
w1 = void $ many1 ignoredToken

identifier :: Parser Char -> Parser Char -> Parser Name
identifier h t = (:) <$> h <*> many t

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

comma :: Parser ()
comma = symbol ","

powerComma :: Parser () -- can span newlines and eat tabs etc. Ugh.
powerComma = void $ wN *> string "," <* wN where
  wN = void $ many (ignoredToken <|> void (char '\t') <|> void newline)

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

name :: Parser Name
name = identifier (satisfy isNameFirstChar) (satisfy isNameChar)

value :: Parser Value
value = many1 (satisfy isValueChar)

isNameFirstChar, isNameChar, isValueChar :: Char -> Bool
isNameFirstChar = (||) <$> isLetter <*> (`elem` ("-_'" :: String))
isNameChar = (||) <$> isNameFirstChar <*> isNumber
-- TODO: we may safely relax this, but it's not clear how far.
isValueChar c = c `elem` ("$@" :: String) || isNameChar c

anyComboOf :: Parser x -> Parser y -> Parser (Maybe x, Maybe y)
anyComboOf x y = try xThenMaybeY <|> try yThenMaybeX <|> pure (Nothing, Nothing) where
  xThenMaybeY = (,) <$> (Just <$> x) <*> optional y
  yThenMaybeX = flip (,) <$> (Just <$> y) <*> optional x

-------------------------------------------------------------------------------
-- Testing
verifyParseResult :: Show a => (a -> Maybe String) -> Parser a -> Text -> IO ()
verifyParseResult check p input = either parseErr doCheck parsed where
  parsed = parse (p <* eof) "verifying parser" input
  doCheck result = maybe (putStr ".") checkErr (check result)
  parseErr = printf "\nError parsing \"%s\" in %s\n" (Text.unpack input) . show
  checkErr = printf "\nFailure parsing \"%s\"!\n%s\n" (Text.unpack input)

verifyParser :: (Show a, Eq a) => Parser a -> Text -> a -> IO ()
verifyParser p input target = verifyParseResult isTarget p input where
  isTarget result = if result == target
    then Nothing
    else Just $ printf "Expected %s, got %s" (show target) (show result)

verifyParserFails :: Show a => Parser a -> Text -> IO ()
verifyParserFails p input = either succeed err parsed where
  parsed = parse (p <* eof) "verifying parser failure" input
  succeed _ = putStr "."
  err result = printf "\nError! Expected a failure parsing \"%s\", but parsed %s.\n"
    (Text.unpack input) (show result)

verifyParsable :: (Show a, Eq a, Parsable a) => Text -> a -> IO ()
verifyParsable = verifyParser parser

main :: IO ()
main = do
  verifyParser w "  {- IGNORE THIS COMMENT -}  {- this one too. -}" ()
  verifyParser w "  {- {- nested -} woo -} " ()
  verifyParser w "  -- anything goes now! \t \t" ()
  verifyParserFails w "  {- {- nested woo -} "
