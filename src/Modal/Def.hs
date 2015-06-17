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
import Data.Set ((\\))
import Data.Traversable
import Modal.Code
import Modal.CompileContext
import Modal.Display
import Modal.Parser
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Text (Parser)
import Text.Printf (printf)
import Text.Read (readMaybe)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Modal.Formulas as F

-------------------------------------------------------------------------------

data Def = Def
  { defArgs :: [(Name, VarType, Maybe VarVal)]
  , defActions :: [Value]
  , defOutcomes :: [Value]
  , defName :: Name
  , defCode :: Code
  } deriving Eq

instance Show Def where show = defName

defheadParser :: CodeConfig -> Parser (Code -> Def)
defheadParser conf = do
  n <- value
  ps <- option [] (try argsParser)
  let aorder = orderParser (actionsString conf)
  let oorder = orderParser (outcomesString conf)
  (as, os) <- anyComboOf aorder oorder
  return $ Def ps (fromMaybe [] as) (fromMaybe [] os) n
  where
    argsParser = parens (arg `sepBy` comma) where
      arg = try num <|> try act <|> try out
      param kwd t p = (,,) <$>
        (keyword kwd *> name) <*>
        return t <*>
        optional (symbol "=" *> p)
      num = param "number" NumberT (Number <$> parser)
      act = param (actionString conf) (ClaimT ActionT) (Action <$> value)
      out = param (outcomeString conf) (ClaimT OutcomeT) (Outcome <$> value)
    orderParser kwd = keyword kwd *> try acts <|> try dunno where
      acts = brackets (value `sepEndBy` comma)
      dunno = brackets (string "...") $> []

-------------------------------------------------------------------------------

data Call = Call
  { callName :: Name
  , callArgs :: [Value]
  , callKwargs :: Map Name Value
  , callActions :: [Value]
  , callOutcomes :: [Value]
  , callAlias :: Maybe Name
  } deriving (Eq, Ord)

instance Show Call where
  show (Call n args kwargs _ _ alias) = n ++ paramstr ++ aliasstr where
    aliasstr = maybe "" (printf " as %s") alias
    paramstr = printf "(%s%s%s)" argstr mid kwargstr
    argstr = renderArgs id args
    mid = if List.null args || Map.null kwargs then "" else "," :: String
    kwargstr = renderArgs (uncurry showKwarg) (Map.toAscList kwargs)
    showKwarg k v = printf "%s=%s" k v

callHandle :: Call -> Name
callHandle call = fromMaybe (show call) (callAlias call)

callParser :: Parser Call
callParser = do
  n <- value
  (args, kwargs) <- option ([], Map.empty) (try argsParser)
  as <- option [] valuesParser
  os <- option [] valuesParser
  alias <- optional (try (keyword "as" *> value))
  return $ Call n args kwargs as os alias
  where
    valuesParser = try (brackets (string "...") $> []) <|> listParser value
    argsParser = parens argsThenKwargs where
      argsThenKwargs = (,) <$> allArgs <*> allKwargs
      allArgs = value `sepEndBy` comma
      allKwargs = Map.fromList <$> (kwarg `sepEndBy` comma)
      kwarg = (,) <$> name <*> (symbol "=" *> value)

-------------------------------------------------------------------------------

data Setting = Setting
  { settingActions :: [Value]
  , settingOutcomes :: [Value]
  } deriving (Eq, Ord, Read, Show)

checkEnumMatchR :: MonadError EnumError m => [Value] -> [Value] -> m [Value]
checkEnumMatchR xs [] = return xs
checkEnumMatchR [] ys = return ys
checkEnumMatchR xs ys
  | Set.fromList xs == Set.fromList ys = return ys
  | otherwise = throwError $ EnumMismatch xs ys

joinSettingWithCall :: CompileErrorM m => Name -> Call -> Setting -> m Setting
joinSettingWithCall defname call setting = do
  let getAEnum = checkEnumMatchR (settingActions setting) (callActions call)
  let getOEnum = checkEnumMatchR (settingOutcomes setting) (callOutcomes call)
  let wrapAerr = throwError . AListErr defname
  let wrapOerr = throwError . OListErr defname
  as <- either wrapAerr return (runExcept getAEnum)
  os <- either wrapOerr return (runExcept getOEnum)
  return setting{settingActions=as, settingOutcomes=os}

initialVariables :: CompileErrorM m =>
  Name ->
  Setting ->
  [(Name, VarType, Maybe VarVal)] ->
  [Value] ->
  Map Name Value ->
  m (Map Name VarVal)
initialVariables defname setting vars args kwargs = updateVars where
  updateVars = do
    when (length args > length vars)
      (throwError $ ArgErr defname $ TooManyArgs (length vars) (length args))
    unless (Set.null unknowns)
      (throwError $ ArgErr defname $ UnknownArgs unknowns)
    varsWithArgs <- mapM (uncurry applyArg) (zip vars extendedArgs)
    updatedVars <- mapM applyKwarg varsWithArgs
    return $ Map.fromList updatedVars
  fst3 (x, _, _) = x
  unknowns = Set.fromList (Map.keys kwargs) \\ Set.fromList (map fst3 vars)
  extendedArgs = (map Just args) ++ repeat Nothing
  applyArg (varname, t, mdflt) Nothing = return (varname, t, mdflt)
  applyArg (varname, t, _) (Just val) = (,,) varname t . Just <$> cast varname t val
  applyKwarg (varname, t, mval) = case (mval, Map.lookup varname kwargs) of
    (Nothing, Nothing) -> throwError $ ArgErr defname $ ArgMissing varname t
    (Just dflt, Nothing) -> return (varname, dflt)
    (_, Just val) -> (,) varname <$> cast varname t val
  cast vname NumberT v = maybe
    (throwError $ ArgErr defname $ ArgIsNotNum vname v)
    (return . Number)
    (readMaybe v)
  cast vname (ClaimT ActionT) v = if v `elem` settingActions setting
    then throwError $ ArgErr defname $ ArgIsNotIn vname v $ settingActions setting
    else return $ Action v
  cast vname (ClaimT OutcomeT) v = if v `elem` settingOutcomes setting
    then throwError $ ArgErr defname $ ArgIsNotIn vname v $ settingOutcomes setting
    else return $ Outcome v

-------------------------------------------------------------------------------
  
makeContext :: CompileErrorM m => Setting -> Call -> Def -> m Context
makeContext setting call def = do
  let n = defName def
  setting' <- joinSettingWithCall n call setting
  when (null $ settingActions setting') (throwError $ AListErr n EnumMissing)
  when (null $ settingOutcomes setting') (throwError $ OListErr n EnumMissing)
  vars <- initialVariables n setting' (defArgs def) (callArgs call) (callKwargs call)
  return $ Context vars (settingActions setting') (settingOutcomes setting') n

-- TODO: It is now the user's job to both (a) draw the action/outcome lists
-- from the code (using actionsMentioned / outcomesMentioned / claimsMade), and
-- (b) check that statements which are supposed to be modalized are in fact
-- modalized (using isModalized).
compile :: CompileErrorM m => Setting -> Call -> Def -> m CompiledAgent
compile setting call def = do
  context <- makeContext setting call def
  program <- codeToProgram context (defCode def)
  return $ Map.map F.simplify program
