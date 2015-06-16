{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Modal.CompileContext where
import Prelude hiding (readFile, sequence, mapM, foldr1, concat, concatMap)
import Control.Applicative
import Control.Monad.Except hiding (mapM, sequence)
import Control.Monad.State hiding (mapM, sequence, state)
import Data.Map (Map)
import Modal.Parser
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Text (Parser)
import Text.Printf (printf)
import qualified Data.Map as Map

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

data Val = Number Int | Action Value | Outcome Value deriving (Eq, Ord, Read)

instance Show Val where
  show (Number i) = '#' : show i
  show (Action v) = '@' : show v
  show (Outcome v) = '$' : show v

-------------------------------------------------------------------------------

data ValType = NumberT | ActionT | OutcomeT deriving (Eq, Ord, Read, Enum)

instance Show ValType where
  show NumberT = "number"
  show ActionT = "action"
  show OutcomeT = "outcome"

typeOf :: Val -> ValType
typeOf (Number _) = NumberT
typeOf (Action _) = ActionT
typeOf (Outcome _) = OutcomeT

typesMatch :: Val -> Val -> Bool
typesMatch x y = typeOf x == typeOf y

-------------------------------------------------------------------------------

data ArgumentError
  = UnknownArg Name
  | TooManyArgs Int Int
  | ArgMismatch Name ValType ValType
  deriving (Eq, Ord, Read)

instance Show ArgumentError where
  show (UnknownArg n) = printf "unknown argument: %s" n
  show (TooManyArgs x y) = printf "too many arguments: expected %d, got %d" x y
  show (ArgMismatch a v u) = printf "argument type mismatch for %s: expected a %s, got a %s" a (show v) (show u)

data EnumError
  = EnumMissing
  | CodeValueExcluded Value
  deriving (Eq, Ord, Read)

instance Show EnumError where
  show EnumMissing = "enumeration missing."
  show (CodeValueExcluded v) = printf "enumeration excludes %s, which is used in the code" (show v)

data RefError
  = UnknownVar Name ValType
  | WrongType Name ValType ValType
  deriving (Eq, Ord, Read)

instance Show RefError where
  show (UnknownVar n t) = printf "unknown %s var %s" (show t) (show n)
  show (WrongType n t u) = printf "variable %s used as a %s, but it is a %s" n (show u) (show t)

data CompileError
  = ArgErr Name ArgumentError
  | AListErr Name EnumError
  | OListErr Name EnumError
  | RefErr Name RefError
  deriving (Eq, Ord)

instance Show CompileError where
  show (ArgErr n e) = printf "error while compiling %s: %s" n (show e)
  show (AListErr n e) = printf "error while compiling %s: action %s" n (show e)
  show (OListErr n e) = printf "error while compiling %s: outcome %s" n (show e)
  show (RefErr n e) = printf "error while compiling %s: %s" n (show e)

type CompileErrorM m = (Applicative m, MonadError CompileError m)

-------------------------------------------------------------------------------

data Context  = Context
  { variables :: Map Name Val
  , actionList :: [Value]
  , outcomeList :: [Value]
  , agentName :: Name
  } deriving (Eq, Show)

withN :: Name -> Int -> Context -> Context
withN n i c = c{variables=Map.insert n (Number i) $ variables c}

withA :: Name -> Value -> Context -> Context
withA n a c = c{variables=Map.insert n (Action a) $ variables c}

withO :: Name -> Value -> Context -> Context
withO n o c = c{variables=Map.insert n (Outcome o) $ variables c}

lookupN :: (MonadError CompileError m, MonadState Context m) => Ref Int -> m Int
lookupN (Ref n) = get >>= \c -> case Map.lookup n (variables c) of
  (Just (Number i)) -> return i
  (Just (Outcome _)) -> compileErr c $ WrongType n ActionT OutcomeT
  (Just (Action _)) -> compileErr c $ WrongType n OutcomeT ActionT
  Nothing -> compileErr c $ UnknownVar n NumberT
  where compileErr c = throwError . RefErr (agentName c)
lookupN (Lit i) = return i

lookupA :: (MonadError CompileError m, MonadState Context m) => Ref Value -> m Value
lookupA (Ref n) = get >>= \c -> case Map.lookup n (variables c) of
  (Just (Outcome o)) -> return o
  (Just (Action _)) -> compileErr c $ WrongType n OutcomeT ActionT
  (Just (Number _)) -> compileErr c $ WrongType n OutcomeT NumberT
  Nothing -> compileErr c $ UnknownVar n OutcomeT
  where compileErr c = throwError . RefErr (agentName c)
lookupA (Lit a) = return a

lookupO :: (MonadError CompileError m, MonadState Context m) => Ref Value -> m Value
lookupO (Ref n) = get >>= \c -> case Map.lookup n (variables c) of
  (Just (Outcome o)) -> return o
  (Just (Action _)) -> compileErr c $ WrongType n OutcomeT ActionT
  (Just (Number _)) -> compileErr c $ WrongType n OutcomeT NumberT
  Nothing -> compileErr c $ UnknownVar n OutcomeT
  where compileErr c = throwError . RefErr (agentName c)
lookupO (Lit o) = return o

defaultAction :: MonadError CompileError m => Context -> m Value
defaultAction c = case (actionList c) of
  [] -> throwError $ AListErr (agentName c) EnumMissing 
  (a:_) -> return a

type MonadCompile m = (CompileErrorM m, MonadState Context m)
