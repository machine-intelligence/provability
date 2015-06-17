{-# LANGUAGE Rank2Types #-}
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
import Data.Either (partitionEithers)
import Data.Map (Map)
import Data.Maybe
import Data.Set (Set, (\\))
import Data.Traversable
import Modal.Code
import Modal.CompilerBase
import Modal.Display
import Modal.Formulas (ModalFormula)
import Modal.Parser
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Text (Parser)
import Text.Printf (printf)
import Text.Read (readMaybe)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

-------------------------------------------------------------------------------

data Def = Def
  { defArgs :: [(Name, VarType, Maybe VarVal)]
  , defActions :: [Value]
  , defOutcomes :: [Value]
  , defName :: Name
  , defCode :: Code
  } deriving Eq

instance Show Def where show = defName

data DefConfig = DefConfig
  { defKw :: Name
  , defAllowsOrderings :: Bool
  , defActionKw :: Name
  , defActionsKw :: Name
  , defOutcomeKw :: Name
  , defOutcomesKw :: Name
  } deriving (Eq, Ord, Read, Show)

makeCodeConfig :: DefConfig -> CodeConfig
makeCodeConfig dconf = CodeConfig
  { actionKw = defActionKw dconf
  , actionsKw = defActionsKw dconf
  , outcomeKw = defOutcomeKw dconf
  , outcomesKw = defOutcomesKw dconf }

defheadParser :: DefConfig -> Parser (Code -> Def)
defheadParser conf = makeDef where
  makeDef = do
    n <- value
    ps <- option [] (try argsParser)
    let aorder = orderParser (defActionsKw conf)
    let oorder = orderParser (defOutcomesKw conf)
    let eitherOrder = anyComboOf aorder oorder
    let neither = return (Just [], Just [])
    (as, os) <- if defAllowsOrderings conf then eitherOrder else neither
    return $ Def ps (fromMaybe [] as) (fromMaybe [] os) n
  argsParser = parens (arg `sepBy` comma) where
    arg = try num <|> try act <|> try out
    param kwd t p = (,,) <$>
      (keyword kwd *> name) <*>
      return t <*>
      optional (symbol "=" *> p)
    num = param "number" NumberT (Number <$> parser)
    act = param (defActionKw conf) (ClaimT ActionT) (Action <$> value)
    out = param (defOutcomeKw conf) (ClaimT OutcomeT) (Outcome <$> value)
  orderParser kwd = keyword kwd *> try acts <|> try dunno where
    acts = brackets (value `sepEndBy` comma)
    dunno = brackets (string "...") $> []

defParser :: DefConfig -> Parser Def
defParser conf = keyword (defKw conf) *> (try mapDef <|> codeDef) where
  mapDef = keyword "map" *> (defheadParser conf <*> codeMapParser <* end)
  codeDef = defheadParser conf <*> codeParser (makeCodeConfig conf) <* end

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
    kwargstr = renderArgs (uncurry $ printf "%s=%s") (Map.toAscList kwargs)

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

checkEnumMatchR :: MonadError EnumError m => [Value] -> [Value] -> m [Value]
checkEnumMatchR xs [] = return xs
checkEnumMatchR [] ys = return ys
checkEnumMatchR xs ys
  | Set.fromList xs == Set.fromList ys = return ys
  | otherwise = throwError $ EnumMismatch xs ys

ensureEnumContains :: MonadError EnumError m => [Value] -> [Value] -> m ()
ensureEnumContains xs enum =
  let missing = Set.fromList xs \\ Set.fromList enum
  in unless (Set.null missing) (throwError $ EnumExcludes missing)

-------------------------------------------------------------------------------

data Setting = Setting
  { settingActions :: [Value]
  , settingOutcomes :: [Value]
  } deriving (Eq, Ord, Read, Show)

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
    varsWithArgs <- zipWithM applyArg vars extendedArgs
    updatedVars <- mapM applyKwarg varsWithArgs
    return $ Map.fromList updatedVars
  fst3 (x, _, _) = x
  unknowns = Set.fromList (Map.keys kwargs) \\ Set.fromList (map fst3 vars)
  extendedArgs = map Just args ++ repeat Nothing
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

data CompileConfig = CompileConfig
    { confSetting :: Setting
    , claimValues :: forall m. CompileErrorM m =>
        ParsedClaim -> m (ClaimType, Set Value)
    -- Recommendation: use finalizeFormula = return . simplify
    -- (with perhaps an isModalized check in there somewhere.)
    , finalizeFormula :: forall m. CompileErrorM m =>
        ModalFormula CompiledClaim -> m (ModalFormula CompiledClaim) }

codeAOs :: CompileErrorM m => CompileConfig -> Code -> m ([Value], [Value])
codeAOs conf code = do
  let aMentions = actionsMentioned code
  let oMentions = outcomesMentioned code
  let claims = claimsMade code
  let aLoR (t, vs) = if t == ActionT then Left vs else Right vs
  (aSets, oSets) <- partitionEithers <$> mapM (fmap aLoR . claimValues conf) claims
  let listify = Set.toList . Set.unions
  return (aMentions ++ listify aSets, oMentions ++ listify oSets)

settingSuitableForCode :: CompileErrorM m =>
  Name -> CompileConfig -> Code -> m Setting
settingSuitableForCode defname conf code = do
  (as, os) <- codeAOs conf code
  let wrapAerr = throwError . AListErr defname
  let wrapOerr = throwError . OListErr defname
  either wrapAerr return $ ensureEnumContains as (settingActions $ confSetting conf)
  either wrapOerr return $ ensureEnumContains os (settingOutcomes $ confSetting conf)
  return $ confSetting conf
  
-------------------------------------------------------------------------------

makeContext :: CompileErrorM m => CompileConfig -> Call -> Def -> m CompileContext
makeContext conf call def = do
  let n = defName def
  suitableSetting <- settingSuitableForCode n conf (defCode def)
  setting <- joinSettingWithCall n call suitableSetting
  when (null $ settingActions setting) (throwError $ AListErr n EnumMissing)
  when (null $ settingOutcomes setting) (throwError $ OListErr n EnumMissing)
  vars <- initialVariables n setting (defArgs def) (callArgs call) (callKwargs call)
  return $ CompileContext vars (settingActions setting) (settingOutcomes setting) n

compile :: CompileErrorM m => CompileConfig -> Call -> Def -> m CompiledAgent
compile conf call def = do
  context <- makeContext conf call def
  program <- codeToProgram context (defCode def)
  let finalize k v = (,) k <$> finalizeFormula conf v
  Map.fromList <$> mapM (uncurry finalize) (Map.toList program)
