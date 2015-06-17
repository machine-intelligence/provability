{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module Modal.Code where
import Prelude hiding (readFile, sequence, mapM, foldr1, concat, concatMap)
import Control.Applicative
import Control.Monad.Except hiding (mapM, sequence)
import Control.Monad.State hiding (mapM, sequence, state)
import Data.Map (Map)
import Data.Maybe (mapMaybe, maybeToList, fromMaybe)
import Data.Monoid ((<>))
import Data.Foldable
import Data.Traversable
import Modal.CompileContext
import Modal.Display
import Modal.Formulas (ModalFormula, (%^), (%|))
import Modal.Parser
import Modal.Programming
import Modal.Statement
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Expr
import Text.Parsec.Text (Parser)
import Text.Printf (printf)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified Modal.Formulas as F

-------------------------------------------------------------------------------

data CodeConfig = CodeConfig
  { actionString :: String
  , actionsString :: String
  , outcomeString :: String
  , outcomesString :: String
  } deriving (Eq, Ord, Read, Show)

defaultCodeConfig :: CodeConfig
defaultCodeConfig = CodeConfig "action" "actions" "outcome" "outcomes"

-------------------------------------------------------------------------------

data SimpleExpr
  = Num (Ref Int)
  | Add SimpleExpr SimpleExpr
  | Sub SimpleExpr SimpleExpr
  | Mul SimpleExpr SimpleExpr
  | Exp SimpleExpr SimpleExpr
  deriving Eq

instance Show SimpleExpr where
  show (Num v) = show v
  show (Add x y) = show x ++ "+" ++ show y
  show (Sub x y) = show x ++ "-" ++ show y
  show (Mul x y) = show x ++ "*" ++ show y
  show (Exp x y) = show x ++ "^" ++ show y

instance Parsable SimpleExpr where
  parser = buildExpressionParser lTable term where
    lTable =
      [ [Infix (try $ symbol "+" $> Add) AssocRight]
      , [Infix (try $ symbol "-" $> Sub) AssocRight]
      , [Infix (try $ symbol "*" $> Mul) AssocRight]
      , [Infix (try $ symbol "^" $> Exp) AssocRight] ]
    term
      =   parens parser
      <|> try (Num <$> (parser :: Parser (Ref Int)))
      <?> "a math expression"

compileExpr :: MonadCompile m => SimpleExpr -> m Int
compileExpr (Num v) = lookupN v
compileExpr (Add x y) = (+) <$> compileExpr x <*> compileExpr y
compileExpr (Sub x y) = (-) <$> compileExpr x <*> compileExpr y
compileExpr (Mul x y) = (*) <$> compileExpr x <*> compileExpr y
compileExpr (Exp x y) = (^) <$> compileExpr x <*> compileExpr y

-------------------------------------------------------------------------------

data Range x
  = EnumRange (Ref x) (Maybe (Ref x)) (Maybe (Ref Int))
  | ListRange [Ref x]
  | TotalRange
  deriving Eq

instance Show x => Show (Range x) where
  show (EnumRange sta msto mste) = printf "%s..%s%s" (show sta) x y where
    x = maybe ("" :: String) show msto
    y = maybe ("" :: String) (printf " by %s" . show) mste
  show (ListRange xs) = printf "[%s]" (List.intercalate ", " $ map show xs)
  show TotalRange = "..."

instance Parsable x => Parsable (Range x) where
  parser = rangeParser "..." parser

rangeParser :: String -> Parser x -> Parser (Range x)
rangeParser allname x = try rEnum <|> try rList <|> try rAll <?> "a range" where
    rEnum = EnumRange <$>
      (refParser x <* symbol "..") <*>
      optional (refParser x) <*>
      optional (try $ keyword "by" *> parser)
    rList = ListRange <$> listParser (refParser x)
    rAll = keyword allname $> TotalRange

boundedRange :: Parsable x => Parser (Range x)
boundedRange = try rBoundedEnum <|> try rList <?> "a bounded range" where
  rBoundedEnum = EnumRange <$>
    (parser <* symbol "..") <*>
    (Just <$> parser) <*>
    optional (try $ keyword "by" *> parser)
  rList = ListRange <$> parser

rangeLitValues :: Range x -> [x]
rangeLitValues (EnumRange sta sto _) =
  maybeToList (lit sta) ++ maybe [] (maybeToList . lit) sto
rangeLitValues (ListRange refs) = mapMaybe lit refs
rangeLitValues _ = []

compileRange :: (Eq x, MonadCompile m) => m [x] -> (Ref x -> m x) -> Range x -> m [x]
compileRange getXs _    TotalRange = getXs
compileRange _     getX (ListRange xs) = mapM getX xs
compileRange getXs getX (EnumRange sta msto mste) = renum msto mste where
  renum Nothing    Nothing = dropWhile . (/=) <$> getX sta <*> getXs
  renum (Just sto) Nothing = takeWhile . (/=) <$> getX sto <*> renum Nothing Nothing
  renum _ (Just ste) = every <$> lookupN ste <*> renum msto Nothing

-------------------------------------------------------------------------------

data CodeFragment
  = ForA Name (Range Value) [CodeFragment]
  | ForO Name (Range Value) [CodeFragment]
  | ForN Name (Range Int) [CodeFragment]
  | LetN Name SimpleExpr
  | If Statement [CodeFragment]
  | IfElse Statement [CodeFragment] [CodeFragment]
  | Return (Maybe (Ref Name))
  | Pass
  deriving Eq

instance  Blockable CodeFragment where
  blockLines (ForA n r cs) =
    [(0, Text.pack $ printf "for action %s in %s" n (show r))] <>
    increaseIndent (concatMap blockLines cs)
  blockLines (ForO n r cs) =
    [(0, Text.pack $ printf "for outcome %s in %s" n (show r))] <>
    increaseIndent (concatMap blockLines cs)
  blockLines (ForN n r cs) =
    [(0, Text.pack $ printf "for number %s in %s" n (show r))] <>
    increaseIndent (concatMap blockLines cs)
  blockLines (LetN n x) =
    [(0, Text.pack $ printf "let %s = %s" n (show x))]
  blockLines (If s xs) =
    [(0, Text.pack $ printf "if %s" $ show s)] <>
    increaseIndent (concatMap blockLines xs)
  blockLines (IfElse s xs ys) =
    [(0, Text.pack $ printf "if %s" $ show s)] <>
    increaseIndent (concatMap blockLines xs) <>
    [(0, "else")] <>
    increaseIndent (concatMap blockLines ys)
  blockLines (Return Nothing) = [(0, "return")]
  blockLines (Return (Just x)) = [(0, Text.pack $ printf "return %s" (show x))]
  blockLines (Pass) = [(0, "pass")]

instance Show CodeFragment where
  show = Text.unpack . renderBlock

codeFragmentParser :: CodeConfig -> Parser CodeFragment
codeFragmentParser conf = pFrag where
  pFrag =   try (pFor ForA action $ rangeParser actions value)
        <|> try (pFor ForO outcome $ rangeParser outcomes value)
        <|> try (pFor ForN "number" boundedRange)
        <|> try pLetN
        <|> try pIf
        <|> try pIfElse
        <|> try pReturn
        <|> try pPass
  pLetN = LetN
    <$> (keyword "let" *> varname <* symbol "=")
    <*> parser
  pIf = If
    <$> (keyword "if" *> parser)
    <*> pBlock end
  pIfElse = IfElse
    <$> (keyword "if" *> parser)
    <*> pBlock (keyword "else")
    <*> pBlock end
  pFor maker sym rparser = maker
    <$> (keyword "for" *> varname)
    <*> (keyword "in" *> symbol sym *> brackets rparser)
    <*> pBlock end
  pBlock ender =
    try (ender $> []) <|> ((:) <$> codeFragmentParser conf <*> pBlock ender)
  pPass = symbol "pass" $> Pass
  pReturn = try returnThing <|> returnNothing <?> "a return statement"
  returnNothing :: Parser CodeFragment
  returnThing = symbol "return " *> (Return . Just <$> refParser value)
  returnNothing = symbol "return" $> Return Nothing
  action = actionString conf
  outcome = outcomeString conf
  actions = actionsString conf
  outcomes = outcomesString conf
  varname = char '&' *> name

data AgentClaim = AgentClaim
  { claimNameIs :: Name
  , claimPlayedVs :: Maybe Name
  , claimBehaviorT :: Maybe ClaimType
  , claimAgentPlays :: Value
  } deriving (Eq, Ord, Read)

instance Show AgentClaim where
  show (AgentClaim n o t v) = printf "%s(%s)=%s%s" n (fromMaybe "" o) showt v where
    showt = maybe ("" :: String) (printf "%s " . tSymbol) t
    tSymbol ActionT = '@'
    tSymbol OutcomeT = '$'

compileActionClaim :: MonadCompile m => ActionClaim -> m (ModalFormula AgentClaim)
compileActionClaim (ActionClaim n o rel) = mapM makeClaim (toF rel) where
  makeClaim :: MonadCompile m => Ref Value -> m AgentClaim
  makeClaim ref = uncurry (AgentClaim n o) <$> lookupClaim ref
  toF (Equals a) = F.Var a
  toF (In []) = F.Val False
  toF (In as) = foldr1 F.Or $ map F.Var as
  toF (NotEquals a) = F.Neg $ toF (Equals a)
  toF (NotIn []) = F.Val True
  toF (NotIn as) = F.Neg $ toF (In as)

compileCodeFragment :: MonadCompile m =>
  CodeFragment -> m (PartialProgram Value AgentClaim)
compileCodeFragment code = case code of
  ForA n r x -> loop (withA n) x =<< compileRange (gets actionList) lookupA r
  ForO n r x -> loop (withO n) x =<< compileRange (gets outcomeList) lookupO r
  ForN n r x -> loop (withN n) x =<< compileRange (return [0..]) lookupN r
  LetN n x -> compileExpr x >>= modify . withN n >> return id
  If s block -> compileCodeFragment (IfElse s block [Pass])
  IfElse s tblock eblock -> do
    cond <- compileStatement compileActionClaim s
    thens <- mapM compileCodeFragment tblock
    elses <- mapM compileCodeFragment eblock
    let yes = foldr1 (.) thens
    let no = foldr1 (.) elses
    return (\continue act ->
      (cond %^ yes continue act) %| (F.Neg cond %^ no continue act))
  Return (Just v) -> (\a -> const $ F.Val . (a ==)) <$> lookupA v
  Return Nothing -> (\a -> const $ F.Val . (a ==)) <$> defaultAction
  Pass -> return id
  where loop update block xs
          | null xs = return id
          | otherwise = foldr1 (.) . concat <$> mapM doFragment xs
          where doFragment x = modify (update x) >> mapM compileCodeFragment block

-------------------------------------------------------------------------------

data Code
  = Code [CodeFragment]
  | ActionMap (Map Value Statement)
  deriving Eq

instance Blockable Code where
  blockLines (Code frags) = concatMap blockLines frags
  blockLines (ActionMap a2s) = [
    (0, Text.pack $ printf "%s ↔ %s" a (show s)) | (a, s) <- Map.toList a2s]

instance Show Code where
  show = Text.unpack . renderBlock

codeParser :: CodeConfig -> Parser Code
codeParser conf = Code <$> many (codeFragmentParser conf)

codeMapParser :: Parser Code
codeMapParser = ActionMap . Map.fromList <$> (assignment `sepEndBy` comma) where
  assignment = (,) <$> (value <* pIff) <*> parser
  pIff = void $ choice [try $ symbol "↔", try $ symbol "<->", try $ keyword "iff"]

compileCode :: MonadCompile m => Code -> m (ModalProgram Value AgentClaim)
compileCode (Code frags) = do
  prog <- foldM (\f c -> (f .) <$> compileCodeFragment c) id frags
  dflt <- defaultAction
  return $ prog (F.Val . (dflt ==))
compileCode (ActionMap a2smap) = do
  let a2slist = Map.toList a2smap
  formulas <- mapM (compileStatement compileActionClaim . snd) a2slist
  let a2flist = zip (map fst a2slist) formulas
  return $ \a -> let Just f = List.lookup a a2flist in f

-- Note: Code not dead; just not yet used.
actionsMentioned :: Code -> [Value]
actionsMentioned (ActionMap m) = Map.keys m
actionsMentioned (Code frags) = concatMap fragRets frags where
  fragRets (ForA _ range fs) = rangeLitValues range ++ concatMap fragRets fs
  fragRets (ForO _ _ fs) = concatMap fragRets fs
  fragRets (ForN _ _ fs) = concatMap fragRets fs
  fragRets (If _ fs) = concatMap fragRets fs
  fragRets (IfElse _ fs gs) = concatMap fragRets fs ++ concatMap fragRets gs
  fragRets (Return (Just v)) = maybeToList $ lit v
  fragRets (Return _) = []
  fragRets (LetN _ _) = []
  fragRets Pass = []

-- Note: Code not dead; just not yet used.
outcomesMentioned :: Code -> [Value]
outcomesMentioned (ActionMap _) = []
outcomesMentioned (Code frags) = concatMap fragRets frags where
  fragRets (ForA _ _ fs) = concatMap fragRets fs
  fragRets (ForO _ range fs) = rangeLitValues range ++ concatMap fragRets fs
  fragRets (ForN _ _ fs) = concatMap fragRets fs
  fragRets (If _ fs) = concatMap fragRets fs
  fragRets (IfElse _ fs gs) = concatMap fragRets fs ++ concatMap fragRets gs
  fragRets (Return _) = []
  fragRets (LetN _ _) = []
  fragRets Pass = []

-- Note: Code not dead; just not yet used.
claimsMade :: Code -> [ActionClaim]
claimsMade (ActionMap m) = concatMap actionClaimsMade $ Map.elems m
claimsMade (Code frags) = concatMap fragClaims frags where
  fragClaims (ForA _ _ fs) = concatMap fragClaims fs
  fragClaims (ForO _ _ fs) = concatMap fragClaims fs
  fragClaims (ForN _ _ fs) = concatMap fragClaims fs
  fragClaims (If s fs) = actionClaimsMade s ++ concatMap fragClaims fs
  fragClaims (IfElse s fs gs) =
    actionClaimsMade s ++ concatMap fragClaims fs ++ concatMap fragClaims gs
  fragClaims (LetN _ _) = []
  fragClaims (Return _) = []
  fragClaims Pass = []

-------------------------------------------------------------------------------

type CompiledAgent = Map Value (ModalFormula AgentClaim)

codeToProgram :: CompileErrorM m => Context -> Code -> m CompiledAgent
codeToProgram context code = do
  (prog, state) <- runStateT (compileCode code) context
  return $ Map.fromList [(a, prog a) | a <- actionList state]
