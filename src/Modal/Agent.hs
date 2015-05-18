{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Modal.Agent
  ( ModalizedAgent
  , compileModalizedAgent
  , modalizedAgentParser
  , FreeAgent
  , compileFreeAgent
  , freeAgentParser
  , argsParser
  , orderParser
  ) where
import Prelude hiding (readFile, sequence, mapM)
import Control.Applicative
import Data.Map (Map)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Text (Text)
import qualified Data.Text as T
import qualified Modal.Formulas as L
import Modal.Code
import Modal.Display
import Modal.Parser
import Modal.Programming
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Printf (printf)

data Agent oa oo a o = Agent
  { agentName :: Name
  , parameters :: Map Name (Val a o)
  , actionOrder :: Maybe [a]
  , outcomeOrder :: Maybe [o]
  , sourceCode :: Code oa oo a o
  } deriving Eq

instance (Show ao, Show oo, Show a, Show o) => Blockable (Agent ao oo a o) where
  blockLines (Agent n ps ao oo c) =
    (0, header) : increaseIndent (blockLines c) where
      header = T.pack $ printf "def %s%s%s%s" (T.unpack n) x y z
      x, y, z :: String
      x = if Map.null ps
        then ""
        else printf "(%s)" $ List.intercalate ("," :: String) $ map showP $ Map.toList ps
      showP (var, Number i) = printf "number %s=%d" (T.unpack var) i
      showP (var, Action a) = printf "action %s=%s" (T.unpack var) (show a)
      showP (var, Outcome o) = printf "outcome %s=%s" (T.unpack var) (show o)
      y = maybe "" (printf "actions=[%s]" . List.intercalate "," . map show) ao
      z = maybe "" (printf "outcomes=[%s]" . List.intercalate "," . map show) oo

instance (Show ao, Show oo, Show a, Show o) => Show (Agent ao oo a o) where
  show = T.unpack . renderBlock

agentParser :: (Ord ao, Ord oo, Ord a, Ord o) =>
  Parsec Text s ao -> Parsec Text s oo -> Parsec Text s a -> Parsec Text s o ->
  String -> String -> String ->
  Parsec Text s (Agent ao oo a o)
agentParser ao oo a o kwa kwo kw = Agent <$>
  (keyword kw *> name) <*>
  option Map.empty (try $ argsParser a o) <*>
  orderParser kwa a <*>
  orderParser kwo o <*>
  codeParser ao oo a o

compile :: (Eq a, Eq o) =>
  OuterToInner oa oo a o ->
  Context a o -> Agent oa oo a o ->
  Either ContextError (Name, Program a o)
compile o2i x agent = (agentName agent,) . simplified <$> getProgram where
  getProgram = codeToProgram o2i context (sourceCode agent)
  simplified = affectFormula L.simplify
  context = x{
    variables=Map.union (variables x) (parameters agent),
    actionList=fromMaybe (actionList x) (actionOrder agent),
    outcomeList=fromMaybe (outcomeList x) (outcomeOrder agent) }

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

type ModalizedAgent a o = Agent Void Void a o

compileModalizedAgent :: (Eq a, Eq o) =>
  Context a o -> ModalizedAgent a o -> Either ContextError (Name, Program a o)
compileModalizedAgent = compile o2iImpossible

modalizedAgentParser :: (Ord a, Ord o) =>
  Parsec Text s a -> Parsec Text s o -> String -> String -> String ->
  Parsec Text s (ModalizedAgent a o)
modalizedAgentParser = agentParser parser parser

-------------------------------------------------------------------------------

type FreeAgent a o = Agent a o a o

compileFreeAgent :: (Eq a, Eq o) =>
  Context a o -> FreeAgent a o -> Either ContextError (Name, Program a o)
compileFreeAgent = compile o2iTrivial

freeAgentParser :: (Ord a, Ord o) =>
  Parsec Text s a -> Parsec Text s o -> String -> String -> String ->
  Parsec Text s (FreeAgent a o)
freeAgentParser a o = agentParser a o a o
