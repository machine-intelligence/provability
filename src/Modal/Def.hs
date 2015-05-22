{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Modal.Def where
import Prelude hiding (readFile, sequence, mapM, foldr1, concat, concatMap)
import Control.Applicative
import Control.Monad.Except hiding (mapM, sequence)
import Data.Map (Map)
import Data.Maybe
import Data.Set (Set)
import Data.Traversable
import Modal.Code
import Modal.Display
import Modal.Parser
import Modal.Statement
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Text (Parser)
import Text.Printf (printf)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Modal.Formulas as F

-------------------------------------------------------------------------------

type CompileErrorM m = (Applicative m, MonadError CompileError m)

data CompileError
  = WrapEvalErr EvalError
  | UnknownArgs Name (Set Name)
  | ArgMismatch Name Name ValType ValType
  | ArgMissing Name Name
  | TooManyArgs Name
  | NoList Name ValType
  | DefCodeListConflict Name ValType [String] [String]
  | CodeCallListConflict Name ValType [String] [String]
  deriving (Eq, Ord)

instance Show CompileError where
  show (WrapEvalErr e) = show e
  show (TooManyArgs n) =
    printf "too many arguments given to %s" (show n)
  show (UnknownArgs n as) =
    printf "unknown args given to %s: %s" n (List.intercalate "," $ Set.toAscList as)
  show (ArgMismatch n a x y) =
    printf "type mismatch for arg %s of %s: needed %s, got %s" a n (show x) (show y)
  show (ArgMissing n a) =
    printf "missing arg %s of %s" a n
  show (NoList n x) =
    printf "%s list missing for %s" (show x) (show n)
  show (DefCodeListConflict n x as bs) =
    printf "def/code %s conflict for %s (%s/%s)"
      (show x) (show n) (List.intercalate "," as) (List.intercalate "," bs)
  show (CodeCallListConflict n x as bs) =
    printf "code/call %s conflict for %s (%s/%s)"
      (show x) (show n) (List.intercalate "," as) (List.intercalate "," bs)

-------------------------------------------------------------------------------

type Args a o = [(Name, Maybe (Val a o))]

data Def s = Def
  { defArgs :: Args (Act s) (Out s)
  , defActions :: [Act s]
  , defOutcomes :: [Out s]
  , defName :: Name
  , defCode :: Code s }

instance Show (Def s) where show = defName

defheadParser :: PConf (Act s) (Out s) -> Parser (Code s -> Def s)
defheadParser pconf = do
  n <- anyname
  ps <- option [] (try argsParser)
  let aorder = orderParser (actSym pconf) (parseA pconf)
  let oorder = orderParser (outSym pconf) (parseO pconf)
  (as, os) <- anyComboOf aorder oorder
  return $ Def ps (fromMaybe [] as) (fromMaybe [] os) n
  where
    argsParser = parens (arg `sepBy` comma) where
      arg = try num <|> try act <|> try out
      param sym p = symbol sym *> ((,) <$> name <*> optional (symbol "=" *> p))
      num = param (numSym pconf) (Number <$> parser)
      act = param (actSym pconf) (Action <$> parseA pconf)
      out = param (outSym pconf) (Outcome <$> parseO pconf)
    orderParser sym p = symbol sym *> try acts <|> try dunno where
      acts = brackets (p `sepEndBy` comma)
      dunno = brackets (string "...") $> []

-------------------------------------------------------------------------------

data Call a o = Call
  { callName :: Name
  , callArgs :: [Val a o]
  , callKwargs :: Map Name (Val a o)
  , callActions :: [a]
  , callOutcomes :: [o]
  , callAlias :: Maybe Name
  } deriving (Eq, Ord)

instance (Show a, Show o) => Show (Call a o) where
  show (Call n args kwargs _ _ alias) = n ++ paramstr ++ aliasstr where
    aliasstr = maybe "" (printf " as %s") alias
    paramstr = printf "(%s%s%s)" argstr mid kwargstr
    argstr = renderArgs renderVal args
    mid = if List.null args || Map.null kwargs then "" else "," :: String
    kwargstr = renderArgs (uncurry showKwarg) (Map.toAscList kwargs)
    showKwarg k v = printf "%s=%s" k (renderVal v)

callHandle :: (Show x, Show y) => Call x y -> Name
callHandle call = fromMaybe (show call) (callAlias call)

callParser :: PConf x y -> Parser (Call x y)
callParser pconf = do
  n <- anyname
  (args, kwargs) <- option ([], Map.empty) (try argsParser)
  as <- orderParser (actSym pconf) (parseA pconf)
  os <- orderParser (outSym pconf) (parseO pconf)
  alias <- optional (try (keyword "as" *> anyname))
  return $ Call n args kwargs as os alias
  where
    orderParser sym p = option [] $ try (symbol sym *> orderP) where
      orderP = try (listParser p) <|> (brackets (string "...") $> [])
    argsParser = parens argsThenKwargs where
      argsThenKwargs = (,) <$> allArgs <*> allKwargs
      allArgs = arg `sepEndBy` comma
      allKwargs = Map.fromList <$> (kwarg `sepEndBy` comma)
      kwarg = (,) <$> name <*> (symbol "=" *> arg)
      arg = try num <|> try act <|> try out <?> "an argument"
      num = symbol (numSym pconf) *> (Number <$> parser)
      act = symbol (actSym pconf) *> (Action <$> parseA pconf)
      out = symbol (outSym pconf) *> (Outcome <$> parseO pconf)

-------------------------------------------------------------------------------

defcallAOlists :: (IsStatement s, MonadError CompileError m) =>
  Def s -> Call (Act s) (Out s) -> m ([Act s], [Out s])
defcallAOlists def call = do
  let (codeAs, codeOs) = (getActs (defCode def), getOuts (defCode def))
  let (defAs, defOs) = (defActions def, defOutcomes def)
  let (callAs, callOs) = (callActions call, callOutcomes call)
  as <- ensureRisL (ccerr ActionT) callAs =<< ensureRinL (dcerr ActionT) defAs codeAs
  os <- ensureRisL (ccerr OutcomeT) callOs =<< ensureRinL (dcerr OutcomeT) defOs codeOs
  return (as, os)
  where
    dcerr, ccerr :: Show x => ValType -> [x] -> [x] -> CompileError
    dcerr t xs ys = DefCodeListConflict (defName def) t (map show xs) (map show ys)
    ccerr t xs ys = CodeCallListConflict (defName def) t (map show xs) (map show ys)
    ensureRrelL _ _ [] olds = return olds
    ensureRrelL rel err news olds
     | Set.fromList olds `rel` Set.fromList news = return news
     | otherwise = throwError $ err olds news
    ensureRinL = ensureRrelL Set.isSubsetOf
    ensureRisL = ensureRrelL (\old new -> Set.null old || old == new)

defcallArgs :: (IsStatement s, Functor m, MonadError CompileError m) =>
  Def s -> Call (Act s) (Out s) -> m (Map Name (Val (Act s) (Out s)))
defcallArgs def call = do
  let paramlist = callArgs call
  let parammap = callKwargs call
  let varlist = defArgs def
  let unknowns = Set.fromList (Map.keys parammap) Set.\\ Set.fromList (map fst varlist)
  when (length paramlist > length varlist) (throwError $ TooManyArgs $ show call)
  unless (Set.null unknowns) (throwError $ UnknownArgs (show call) unknowns)
  arglist <- mapM (uuncurry joinArgs) (zip (defArgs def) infiniteCallArgs)
  Map.fromList <$> mapM handleKwargs arglist
  where
    uuncurry = uncurry . uncurry
    infiniteCallArgs = (Just <$> callArgs call) ++ repeat Nothing
    handleKwargs (k, v) = joinKwargs k (Map.lookup k (callKwargs call)) v
    joinArgs argname Nothing mval = return (argname, mval)
    joinArgs argname mdflt Nothing = return (argname, mdflt)
    joinArgs argname (Just dflt) (Just val)
      | typesMatch dflt val = return (argname, Just val)
      | otherwise = throwError (ArgMismatch (defName def) argname (typeOf dflt) (typeOf val))
    joinKwargs argname Nothing Nothing  = throwError (ArgMissing (defName def) argname)
    joinKwargs argname (Just dflt) (Just val)
      | typesMatch dflt val = return (argname, val)
      | otherwise = throwError (ArgMismatch (defName def) argname (typeOf dflt) (typeOf val))
    joinKwargs argname mdflt mval = return (argname, fromMaybe (fromJust mdflt) mval)

makeContext :: (IsStatement s, Functor m, MonadError CompileError m) =>
  Def s -> Call (Act s) (Out s) -> m (Context (Act s) (Out s))
makeContext def call = do
  args <- defcallArgs def call
  (as, os) <- defcallAOlists def call
  when (List.null as) (throwError (NoList (defName def) ActionT))
  when (List.null os) (throwError (NoList (defName def) OutcomeT))
  return $ Context args as os

compile :: IsStatement s =>
  Def s -> Call (Act s) (Out s) ->
  Either CompileError (CompiledAgent s)
compile def call = do
  context <- makeContext def call
  program <- either (throwError . WrapEvalErr) pure (codeToProgram context (defCode def))
  return $ Map.map F.simplify program
