{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Modal.CompilerBase where
import Prelude hiding (readFile, sequence, mapM, foldr1, concat, concatMap)
import Control.Arrow (first)
import Control.Applicative
import Control.Monad.Except hiding (mapM, sequence)
import Control.Monad.State hiding (mapM, sequence, state)
import Data.Either (partitionEithers)
import Data.Foldable
import Data.Map (Map)
import Data.Set (Set)
import Data.String
import Data.Traversable
import Modal.Display (renderArgs)
import Modal.Formulas (ModalFormula)
import Modal.Parser hiding (main)
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Text (Parser)
import Text.Printf (printf)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Modal.Formulas as F

-------------------------------------------------------------------------------

newtype Value = V String deriving (Eq, Ord)

instance Read Value where
  readsPrec _ s = case parse (parser <* eof) "reading value" (Text.pack s) of
    Right result -> [(result, "")]
    Left err -> []

instance IsString Value where
  fromString = V

instance Show Value where
  show (V val) = val

instance Parsable Value where
  parser = V <$> valueStr

-------------------------------------------------------------------------------

data VarVal = Number Int | Action Value | Outcome Value deriving (Eq, Ord, Read)

instance Show VarVal where
    show (Number n) = '#' : show n
    show (Action v) = '@' : show v
    show (Outcome v) = '$' : show v

asN :: MonadCompile m =>  Name -> VarVal -> m Int
asN _ (Number i) = return i
asN n (Action _) = refError $ ExpectingNum n ActionT
asN n (Outcome _) = refError $ ExpectingNum n OutcomeT

asClaim :: MonadCompile m => Name -> VarVal -> m (ClaimType, Value)
asClaim _ (Action v) = return (ActionT, v)
asClaim _ (Outcome v) = return (OutcomeT, v)
asClaim n _ = refError $ ExpectingClaim n

-------------------------------------------------------------------------------

data ClaimType = ActionT | OutcomeT deriving (Eq, Ord, Read, Enum)

-- TODO: naming schema kinda sucks.
-- This is especially evident when the universe has an universe-output
-- enumeration that excludes values seen in the code, in which case the error
-- message refers to this as an "action enumeration." (This is confusing
-- because we think of the universe as outputing outcomes rather than actions,
-- but vise versa for agents.)
instance Show ClaimType where
    show ActionT = "action"
    show OutcomeT = "outcome"

-------------------------------------------------------------------------------

data VarType = NumberT | ClaimT ClaimType deriving (Eq, Read)

instance Show VarType where
  show NumberT = "number"
  show (ClaimT t) = show t

-------------------------------------------------------------------------------

data DefType = AgentT | TheoryT | ProblemT deriving (Eq, Ord, Read, Enum)

instance Show DefType where
  show AgentT = "agent"
  show TheoryT = "theory"
  show ProblemT = "problem"

-------------------------------------------------------------------------------

data Ref a = Ref Name | Lit a deriving (Eq, Ord, Read)

instance Show a => Show (Ref a) where
  show (Ref n) = '&' : n
  show (Lit x) = show x

instance Parsable a => Parsable (Ref a) where
  parser = refParser parser

_testRefParser :: IO ()
_testRefParser = do
  let succeeds = verifyParser (parser :: Parser (Ref Int))
  let fails = verifyParserFails (parser :: Parser (Ref Int))
  succeeds "&reference" (Ref "reference")
  fails    "&123"
  succeeds "&_123" (Ref "_123")
  succeeds "3" (Lit 3)
  fails    "hello"
  fails    "3four5"

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
  deriving (Eq, Ord, Read, Functor)

instance Show a => Show (Relation a) where
  show (Equals v) = printf "=%s" (show v)
  show (In vs) = printf "∈{%s}" (renderArgs show vs)
  show (NotEquals v) = printf "≠%s" (show v)
  show (NotIn vs) = printf "∉{%s}" (renderArgs show vs)

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

_testRelationParser :: IO ()
_testRelationParser = do
  let succeeds = verifyParser (parser :: Parser (Relation Int))
  let fails = verifyParserFails (parser :: Parser (Relation Int))
  succeeds "=3" (Equals 3)
  fails    "=A"
  succeeds "≠0" (NotEquals 0)
  succeeds "in {1, 2, 3}" (In [1, 2, 3])
  fails    "in {1,"
  succeeds "not in {1, 2, 3}" (NotIn [1, 2, 3])
  succeeds " ∈ {1,}" (In [1])

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
        <|> try (keyword "not" *> keyword "in")
        <?> "an absence test"
  set = braces $ sepEndBy p comma

relToMentions :: Relation a -> [a]
relToMentions (Equals a) = [a]
relToMentions (In as) = as
relToMentions (NotEquals a) = [a]
relToMentions (NotIn as) = as

-------------------------------------------------------------------------------

data Call = Call
  { callName :: Name
  , callArgs :: [Value]
  , callKwargs :: Map Name Value
  , callActions :: [Value]
  , callOutcomes :: [Value]
  } deriving (Eq, Ord)

instance Show Call where
  show (Call n args kwargs as os) = n ++ controlstr where
    controlstr = printf "%s%s%s" paramstr actsstr outsstr
    paramstr = if null args && Map.null kwargs then ("" :: String)
      else printf "(%s%s%s)" argstr mid kwargstr
    argstr = renderArgs show args
    mid = if List.null args || Map.null kwargs then "" else "," :: String
    kwargstr = renderArgs (\(k, v) -> printf "%s=%s" k (show v)) (Map.toAscList kwargs)
    actsstr = case (as, os) of
      ([], []) -> "" :: String
      ([], _) -> "[...]"
      (_, _) -> printf "[%s]" (renderArgs show as)
    outsstr = if null os then "" :: String else printf "[%s]" (renderArgs show os)

instance Parsable Call where
  parser = do
    n <- valueStr
    (args, kwargs) <- option ([], Map.empty) (try argsParser)
    as <- option [] (try valuesParser)
    os <- option [] (try valuesParser)
    return $ Call n args kwargs as os
    where
      valuesParser = try (brackets (string "...") $> []) <|> listParser parser
      argsParser = parens argsAndKwargs where
        argOrKwarg = try (Right <$> kwarg) <|> (Left <$> parser)
        kwarg = (,) <$> name <*> (symbol "=" *> parser)
        argsAndKwargs = do
          (args, kwargs) <- partitionEithers <$> (argOrKwarg `sepEndBy` comma)
          return (args, Map.fromList kwargs)

_testCallParser :: IO ()
_testCallParser = do
  let succeeds = verifyParser (parser :: Parser Call)
  let fails = verifyParserFails (parser :: Parser Call)
  succeeds "Name" (Call "Name" [] Map.empty [] [])
  succeeds "A-B()" (Call "A-B" [] Map.empty [] [])
  fails    "Name!#-"
  succeeds "A(x, y, z)" (Call "A" ["x", "y", "z"] Map.empty [] [])
  succeeds "A(arg, kwarg=1)" (Call "A" ["arg"] (Map.fromList [("kwarg", "1")]) [] [])
  succeeds "A(x=1, a, y=2, b,)" (Call "A" ["a", "b"] (Map.fromList
    [("x", "1"), ("y", "2")]) [] [])
  fails    "A(a a a )"
  succeeds "A()[x, y]" (Call "A" [] Map.empty ["x", "y"] [])
  succeeds "A()[x, y][a, b]" (Call "A" [] Map.empty ["x", "y"] ["a", "b"])
  succeeds "A()[][a, b]" (Call "A" [] Map.empty [] ["a", "b"])
  succeeds "A()[...][a, b]" (Call "A" [] Map.empty [] ["a", "b"])
  succeeds "A()[...][...]" (Call "A" [] Map.empty [] [])
  succeeds "A()[x, y][...]" (Call "A" [] Map.empty ["x", "y"] [])
  fails    "A()[][][]"

instance Read Call where
  readsPrec _ s = case parse (parser <* eof) "reading call" (Text.pack s) of
    Right result -> [(result,"")]
    Left err -> error $ show err

simpleCall :: Name -> Call
simpleCall n = Call n [] Map.empty [] []

-------------------------------------------------------------------------------

data ParsedClaim = ParsedClaim Name (Maybe Call) (Relation (Ref Value))
  deriving (Eq, Ord, Read)

instance Show ParsedClaim where
  show (ParsedClaim n o r) = printf "%s(%s)%s" n (maybe "" show o) (show r)

instance Parsable ParsedClaim where
  parser = try pclaim <?> "a claim about an agent" where
    pclaim = ParsedClaim <$>
      name <*>
      maybeCall <*>
      relationParser (refParser parser)
    maybeCall =   try (symbol "()" $> Nothing)
              <|> try (Just <$> parens parser)
              <|> pure Nothing

_testParsedClaimParser :: IO ()
_testParsedClaimParser = do
  let succeeds = verifyParser (parser :: Parser ParsedClaim)
  let fails = verifyParserFails (parser :: Parser ParsedClaim)
  succeeds "A=val" (ParsedClaim "A" Nothing (Equals $ Lit $ "val"))
  fails    "X=y=z"
  succeeds "A=&a" (ParsedClaim "A" Nothing (Equals $ Ref "a"))
  succeeds "A()=&a" (ParsedClaim "A" Nothing (Equals $ Ref "a"))
  succeeds "A(B(a))=&a" (ParsedClaim "A"
    (Just (Call "B" ["a"] Map.empty [] [])) (Equals $ Ref "a"))
  succeeds "Xxx(B(a)[...][x]) in {&a, b, &c}" (ParsedClaim "Xxx"
    (Just (Call "B" ["a"] Map.empty [] ["x"])) (In [Ref "a", Lit $ "b", Ref "c"]))
  fails    "X(f(g(h(x))))=value"

-------------------------------------------------------------------------------

data CompiledClaim = CompiledClaim
  { claimNameIs :: Name
  , claimPlayedVs :: Maybe Call
  , claimType :: Maybe ClaimType
  , claimAgentPlays :: Value
  } deriving (Eq, Ord, Read)

instance Show CompiledClaim where
  show (CompiledClaim n o t v) = printf "%s(%s)=%s%s" n showo showt (show v) where
    showo = maybe "" show o
    showt = maybe ("" :: String) (printf "%c" . tSymbol) t
    tSymbol ActionT = '@'
    tSymbol OutcomeT = '$'

compileClaim :: MonadCompile m => ParsedClaim -> m (ModalFormula CompiledClaim)
compileClaim (ParsedClaim n o rel) = mapM makeClaim (toF rel) where
  makeClaim :: MonadCompile m => Ref Value -> m CompiledClaim
  makeClaim ref = uncurry (CompiledClaim n o) <$> lookupClaim ref
  toF (Equals a) = F.Var a
  toF (In []) = F.Val False
  toF (In as) = foldr1 F.Or $ map F.Var as
  toF (NotEquals a) = F.Neg $ toF (Equals a)
  toF (NotIn []) = F.Val True
  toF (NotIn as) = F.Neg $ toF (In as)

-------------------------------------------------------------------------------

data CompileContext = CompileContext
  { variables :: Map Name VarVal
  , actionList :: [Value]
  , outcomeList :: [Value]
  , agentName :: Name
  } deriving (Eq, Show)

withN :: Name -> Int -> CompileContext -> CompileContext
withN n i c = c{variables=Map.insert n (Number i) $ variables c}

withA :: Name -> Value -> CompileContext -> CompileContext
withA n a c = c{variables=Map.insert n (Action a) $ variables c}

withO :: Name -> Value -> CompileContext -> CompileContext
withO n o c = c{variables=Map.insert n (Outcome o) $ variables c}

lookupN :: MonadCompile m => Ref Int -> m Int
lookupN (Ref n) = gets variables >>= toN where
  toN = maybe unknown (asN n) . Map.lookup n
  unknown = refError $ UnknownNumVar n
lookupN (Lit i) = return i

lookupClaim :: MonadCompile m => Ref Value -> m (Maybe ClaimType, Value)
lookupClaim (Ref n) = gets variables >>= toClaim where
  toClaim = maybe unknown (fmap (first Just) . asClaim n) . Map.lookup n
  unknown = refError $ UnknownClaimVar n
lookupClaim (Lit v) = return (Nothing, v)

lookupA :: MonadCompile m => Ref Value -> m Value
lookupA ref = lookupClaim ref >>= forceA where
  forceA (Just OutcomeT, _) = let Ref n = ref in refError $ ExpectingA n
  forceA (_, v) = return v

lookupO :: MonadCompile m => Ref Value -> m Value
lookupO ref = lookupClaim ref >>= forceO where
  forceO (Just ActionT, _) = let Ref n = ref in refError $ ExpectingO n
  forceO (_, v) = return v

defaultAction :: MonadCompile m => m Value
defaultAction = gets actionList >>= getFirst where
  getFirst [] = actionListError EnumMissing
  getFirst (a:_) = return a

argumentError :: MonadCompile m => ArgumentError -> m a
argumentError err = gets agentName >>= throwError . flip ArgErr err

actionListError :: MonadCompile m => EnumError -> m a
actionListError err = gets agentName >>= throwError . flip AListErr err

outcomeListError :: MonadCompile m => EnumError -> m a
outcomeListError err = gets agentName >>= throwError . flip OListErr err

refError :: MonadCompile m => RefError -> m a
refError err = gets agentName >>= throwError . flip RefErr err

defError :: MonadCompile m => DefError -> m a
defError err = gets agentName >>= throwError . flip DefErr err

type MonadCompile m = (MonadError CompileError m, MonadState CompileContext m)

-------------------------------------------------------------------------------

data ArgumentError
  = UnknownArgs (Set Name)
  | TooManyArgs Int Int
  | ArgMissing Name VarType
  | ArgIsNotNum Name Value
  | ArgIsNotIn Name Value [Value]
  deriving (Eq, Read)

instance Show ArgumentError where
  show (UnknownArgs ns) =
    printf "unknown keyword arguments: {%s}" (renderArgs id $ Set.toList ns)
  show (TooManyArgs x y) =
    printf "too many arguments: expected %d, got %d" x y
  show (ArgMissing n t) =
    printf "%s argument %s not given" (show t) n
  show (ArgIsNotNum n v) =
    printf "argument type mismatch for %s: expected a number, got %s" n (show v)
  show (ArgIsNotIn n v vs) =
    printf "argument type mismatch for %s: expected one of {%s}, got %s"
      n (renderArgs show vs) (show v)

data EnumError
  = EnumMissing
  | EnumExcludes [Value] (Set Value)
  | EnumMismatch [Value] [Value]
  deriving (Eq, Ord, Read)

instance Show EnumError where
  show EnumMissing = "enumeration missing."
  show (EnumExcludes xs vs) =
    printf "enumeration {%s} excludes {%s}, used in the code"
      (renderArgs show xs)
      (renderArgs show $ Set.toList vs)
  show (EnumMismatch vs ws) =
    printf "enumeration mismatch: [%s] / [%s]" (renderArgs show vs) (renderArgs show ws)

data RefError
  = UnknownNumVar Name
  | UnknownClaimVar Name
  | ExpectingNum Name ClaimType
  | ExpectingClaim Name
  | ExpectingA Name
  | ExpectingO Name
  deriving (Eq, Read)

instance Show RefError where
  show (UnknownNumVar n) = printf "unknown number var %s" n
  show (UnknownClaimVar n) = printf "unknown var %s used in action claim" n
  show (ExpectingNum n t) = printf "%s variable %s used as a number" (show t) n
  show (ExpectingClaim n) = printf "number variable %s used in an action claim" n
  show (ExpectingA n) = printf "outcome variable %s used as an action" n
  show (ExpectingO n) = printf "action variable %s used as an outcome" n

data DefError
  = IsUnmodalized (ModalFormula String)
  | InvalidValue ClaimType Value [Value]
  | InvalidClaim CompiledClaim String
  deriving (Eq, Read)

instance Show DefError where
  show (IsUnmodalized s) = printf "unmodalized statement: %s" (show s)
  show (InvalidValue t v vs) = printf "invalid %s %s: expected one of [%s]"
    (show t) (show v) (renderArgs show vs)
  show (InvalidClaim c s) = printf "invalid claim: %s (%s)" (show c) s

data CompileError
  = ArgErr Name ArgumentError
  | AListErr Name EnumError
  | OListErr Name EnumError
  | RefErr Name RefError
  | DefErr Name DefError
  deriving (Eq, Read)

instance Show CompileError where
  show (ArgErr n e) = printf "error while compiling %s: %s" n (show e)
  show (AListErr n e) = printf "error while compiling %s: action %s" n (show e)
  show (OListErr n e) = printf "error while compiling %s: outcome %s" n (show e)
  show (RefErr n e) = printf "error while compiling %s: %s" n (show e)
  show (DefErr n e) = printf "error while compiling %s: %s" n (show e)

-- TODO: Not yet in use.
data ExecutionError
  = FixpointError String
  deriving (Eq, Read)

instance Show ExecutionError where
  show (FixpointError v) = printf "unknown variable when finding fixpoint: %s" v

data FileError
  = UnknownDef DefType Name
  | NameCollision DefType Name
  deriving (Eq, Read)

instance Show FileError where
  show (UnknownDef t n) = printf "unknown %s: %s" (show t) n
  show (NameCollision t n) = printf "name collision: %s %s is already defined" (show t) n

data RuntimeError
  = FileErr FilePath FileError
  | ExecErr FilePath String ExecutionError
  | CompileErr FilePath CompileError
  deriving (Eq, Read)

instance Show RuntimeError where
  show (FileErr f g) = printf "error in %s: %s" f (show g)
  show (ExecErr f x r) = printf "error running %s in %s: %s" x f (show r)
  show (CompileErr f c) = printf "error running %s: %s" f (show c)

-------------------------------------------------------------------------------
-- Testing

main :: IO ()
main = do
  _testRefParser
  _testRelationParser
  _testCallParser
  _testParsedClaimParser
  putStrLn ""
