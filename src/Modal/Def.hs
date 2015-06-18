{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Modal.Def where
import Prelude hiding (readFile, sequence, mapM, foldr1, concat)
import Control.Applicative
import Control.Monad.Except hiding (mapM, sequence)
import Data.Either (partitionEithers)
import Data.Map (Map)
import Data.Set ((\\))
import Data.Traversable
import Modal.Code
import Modal.CompilerBase
import Modal.Formulas (ModalFormula)
import Modal.Parser
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Text (Parser)
import Text.Read (readMaybe)
import qualified Data.Map as Map
import qualified Data.Set as Set

-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------

data Def = Def
  { defArgs :: [(Name, VarType, Maybe VarVal)]
  , defName :: Name
  , defCode :: Code
  } deriving Eq

instance Show Def where show = defName

defHeadParser :: DefConfig -> Parser (Code -> Def)
defHeadParser conf = makeDef where
  makeDef = flip Def <$> name <*> option [] (try argsParser)
  argsParser = parens (arg `sepBy` comma) where
    arg = try num <|> try act <|> try out
    param kwd t p = (,,) <$>
      (keyword kwd *> name) <*>
      return t <*>
      optional (symbol "=" *> p)
    num = param "number" NumberT (Number <$> parser)
    act = param (defActionKw conf) (ClaimT ActionT) (Action <$> value)
    out = param (defOutcomeKw conf) (ClaimT OutcomeT) (Outcome <$> value)

defParser :: DefConfig -> Parser Def
defParser = fmap fst . defParserWithExtras (pure ())

defParserWithExtras :: Parser x -> DefConfig -> Parser (Def, x)
defParserWithExtras px conf = keyword (defKw conf) *> (try mapDef <|> codeDef) where
  mapDef = do
    keyword "map"
    h <- defHeadParser conf
    x <- px
    c <- codeMapParser
    end
    return (h c, x)
  codeDef = do
    h <- defHeadParser conf
    x <- px
    c <- codeParser (makeCodeConfig conf)
    end
    return (h c, x)

-------------------------------------------------------------------------------

-- Errors unless the left list is a subset of the right one.
ensureEnumContains :: MonadError EnumError m => [Value] -> [Value] -> m ()
ensureEnumContains xs enum =
  let missing = Set.fromList xs \\ Set.fromList enum
  in unless (Set.null missing) (throwError $ EnumExcludes missing)

-- Checks that the first list and the second list are equivalent up to
-- ordering, where an empty list is treated as missing (and ignored). Returns
-- the non-missing list if any, preferring the ordering of the right list.
matchEnumsR :: MonadError EnumError m => [Value] -> [Value] -> m [Value]
matchEnumsR xs [] = return xs
matchEnumsR [] ys = return ys
matchEnumsR xs ys
  | Set.fromList xs == Set.fromList ys = return ys
  | otherwise = throwError $ EnumMismatch xs ys

-------------------------------------------------------------------------------

data CompileConfig a v = CompileConfig
    { availableActions :: [Value]
    , availableOutcomes :: [Value]
    , claimValues :: ParsedClaim -> [(ClaimType, Value)]
    , handleClaim :: forall m. MonadError DefError m => CompiledClaim -> m v
    , compileAction :: forall m. MonadError DefError m => Value -> m a
    , finalizeFormula :: forall m. MonadError DefError m => ModalFormula v -> m (ModalFormula v) }

-- Finds all actions & outcomes mentioned in the code.
codeAOs :: (ParsedClaim -> [(ClaimType, Value)]) -> Code -> ([Value], [Value])
codeAOs valsIn code = (aMentions ++ asInClaims, oMentions ++ osInClaims) where
  aMentions = actionsMentioned code
  oMentions = outcomesMentioned code
  aLoR (t, v) = if t == ActionT then Left v else Right v
  aoList = concatMap valsIn (claimsMade code)
  (asInClaims, osInClaims) = partitionEithers (map aLoR aoList)

-- Ensures that all actions (outcomes) mentioned in the code appear in the
-- available action (outcome) list.
reconfigureWithCode :: MonadError CompileError m =>
  Name -> Code -> CompileConfig a v -> m (CompileConfig a v)
reconfigureWithCode defname code conf = do
  let (as, os) = codeAOs (claimValues conf) code
  let ensureA = ensureEnumContains as $ availableActions conf
  let ensureO = ensureEnumContains os $ availableOutcomes conf
  either (throwError . AListErr defname) return ensureA
  either (throwError . OListErr defname) return ensureO
  return conf

-- Allows the call to reorder the available action (outcome) lists.
reconfigureWithCall :: MonadError CompileError m =>
  Name -> Call -> CompileConfig a v -> m (CompileConfig a v)
reconfigureWithCall defname call conf = do
  let (lAs, lOs) = (availableActions conf, availableOutcomes conf)
  let (rAs, rOs) = (callActions call, callOutcomes call)
  as <- wrapError (AListErr defname) (matchEnumsR lAs rAs)
  os <- wrapError (OListErr defname) (matchEnumsR lOs rOs)
  return conf{availableActions=as, availableOutcomes=os}

effectiveAOs ::
  (ParsedClaim -> [(ClaimType, Value)]) -> Code -> Call -> ([Value], [Value])
effectiveAOs valsIn code call = (preferR codeAs callAs, preferR codeOs callOs) where
  (callAs, callOs) = (callActions call, callOutcomes call)
  (codeAs, codeOs) = codeAOs valsIn code
  preferR xs ys = if null ys then xs else ys
  
-------------------------------------------------------------------------------

initialVariables :: MonadError CompileError m =>
  Name ->
  ([Value], [Value]) ->
  [(Name, VarType, Maybe VarVal)] ->
  [Value] ->
  Map Name Value ->
  m (Map Name VarVal)
initialVariables defname (as, os) vars args kwargs = updateVars where
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
  cast vname (ClaimT ActionT) v = if v `elem` as
    then throwError $ ArgErr defname $ ArgIsNotIn vname v as
    else return $ Action v
  cast vname (ClaimT OutcomeT) v = if v `elem` os
    then throwError $ ArgErr defname $ ArgIsNotIn vname v os
    else return $ Outcome v

makeContext :: MonadError CompileError m =>
  CompileConfig a v -> Call -> Def -> m CompileContext
makeContext conf call def = do
  let n = defName def
  reconf <- reconfigureWithCall n call =<< reconfigureWithCode n (defCode def) conf
  let (as, os) = (availableActions reconf, availableOutcomes reconf)
  when (null as) (throwError $ AListErr n EnumMissing)
  when (null os) (throwError $ OListErr n EnumMissing)
  vars <- initialVariables n (as, os) (defArgs def) (callArgs call) (callKwargs call)
  return $ CompileContext vars as os n

compile :: (MonadError CompileError m, Ord a) =>
  CompileConfig a v -> Call -> Def -> m (Map a (ModalFormula v))
compile conf call def = do
  context <- makeContext conf call def
  program <- codeToProgram context (defCode def)
  let wrapDErr = wrapError $ DefErr $ defName def
  Map.fromList <$> mapM (wrapDErr . uncurry finalize) (Map.toList program)
  where finalize val formula = do
          action <- compileAction conf val
          varified <- traverse (handleClaim conf) formula
          finalized <- finalizeFormula conf varified
          return (action, finalized)
