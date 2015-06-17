{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Modal.CompilerBase where
import Prelude hiding (readFile, sequence, mapM, foldr1, concat, concatMap)
import Control.Arrow (first)
import Control.Applicative
import Data.Maybe (fromMaybe)
import Control.Monad.Except hiding (mapM, sequence)
import Control.Monad.State hiding (mapM, sequence, state)
import Data.Foldable
import Data.Map (Map)
import Data.Set (Set)
import Data.Traversable
import Modal.Display (renderArgs)
import Modal.Formulas (ModalFormula)
import Modal.Parser
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Text (Parser)
import Text.Printf (printf)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Modal.Formulas as F

-------------------------------------------------------------------------------

data VarVal = Number Int | Action Value | Outcome Value deriving (Eq, Ord, Read)

instance Show VarVal where
    show (Number n) = '#' : show n
    show (Action v) = '@' : v
    show (Outcome v) = '$' : v

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

instance Show ClaimType where
    show ActionT = "action"
    show OutcomeT = "outcome"

instance Parsable ClaimType where
    parser =   try (keyword "action" $> ActionT)
           <|> (keyword "outcome" $> OutcomeT)

-------------------------------------------------------------------------------

data VarType = NumberT | ClaimT ClaimType deriving (Eq, Read)

instance Show VarType where
  show NumberT = "number"
  show (ClaimT t) = show t

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

-------------------------------------------------------------------------------

data ParsedClaim = ParsedClaim Name (Maybe Name) (Relation (Ref Value))
  deriving (Eq, Ord, Read)

instance Show ParsedClaim where
  show (ParsedClaim n o r) = printf "%s(%s)%s" n (fromMaybe "" o) (show r)

instance Parsable ParsedClaim where
  parser = ParsedClaim <$>
             name <*>
             optional (parens name) <*>
             relationParser (refParser value)

-------------------------------------------------------------------------------

data CompiledClaim = CompiledClaim
  { claimNameIs :: Name
  , claimPlayedVs :: Maybe Name
  , claimType :: Maybe ClaimType
  , claimAgentPlays :: Value
  } deriving (Eq, Ord, Read)

instance Show CompiledClaim where
  show (CompiledClaim n o t v) = printf "%s(%s)=%s%s" n (fromMaybe "" o) showt v where
    showt = maybe ("" :: String) (printf "%s " . tSymbol) t
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

type MonadCompile m = (CompileErrorM m, MonadState CompileContext m)

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
    printf "argument type mismatch for %s: expected one of {%s}, got %s" n (renderArgs id vs) (show v)

data EnumError
  = EnumMissing
  | EnumExcludes (Set Value)
  | EnumMismatch [Value] [Value]
  deriving (Eq, Ord, Read)

instance Show EnumError where
  show EnumMissing = "enumeration missing."
  show (EnumExcludes vs) =
    printf "enumeration excludes {%s}, used in the code" (renderArgs show $ Set.toList vs)
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
  = UnmodalizedStatement (ModalFormula CompiledClaim)
  | OtherError String
  deriving (Eq, Read)

instance Show DefError where
  show (UnmodalizedStatement s) = printf "unmodalized statement: %s" (show s)
  show (OtherError s) = s

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

type CompileErrorM m = (Applicative m, MonadError CompileError m)
