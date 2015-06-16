{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Modal.Code where
import Prelude hiding (readFile, sequence, mapM, foldr1, concat, concatMap)
import Control.Applicative
import Control.Monad.Except hiding (mapM, sequence)
import Control.Monad.State hiding (mapM, sequence, state)
import Data.Map (Map)
import Data.Maybe (maybeToList)
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

evalExpr :: MonadCompile m => SimpleExpr -> m Int
evalExpr (Num v) = lookupN v
evalExpr (Add x y) = (+) <$> evalExpr x <*> evalExpr y
evalExpr (Sub x y) = (-) <$> evalExpr x <*> evalExpr y
evalExpr (Mul x y) = (*) <$> evalExpr x <*> evalExpr y
evalExpr (Exp x y) = (^) <$> evalExpr x <*> evalExpr y

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
  parser = rangeParser parser

rangeParser :: Parser x -> Parser (Range x)
rangeParser x = try rEnum <|> try rList <|> try rAll <?> "a range" where
    rEnum = EnumRange <$> (x <* symbol "..") <*> optional x <*> pEnumBy
    pEnumBy = optional (try $ keyword "by" *> parser)
    rList = ListRange <$> listParser x
    rAll = symbol "..." $> TotalRange

boundedRange :: Parsable x => Parser (Range x)
boundedRange = try rBoundedEnum <|> try rList <?> "a bounded range" where
  rBoundedEnum = EnumRange <$> (parser <* symbol "..") <*> (Just <$> parser) <*> pEnumBy
  pEnumBy = optional (try $ keyword "by" *> parser)
  rList = ListRange <$> parser

rangeLitValues :: Range x -> [x]
rangeLitValues (EnumRange sta sto _) =
  maybeToList (lit sta) ++ maybe [] (maybeToList . lit) sto
rangeLitValues (ListRange refs) = concatMap (maybeToList . lit) refs 
rangeLitValues _ = []

elemsInContext :: (Eq x, MonadCompile m) => m [x] -> (Ref x -> m x) -> Range x -> m [x]
elemsInContext getXs _    TotalRange = getXs
elemsInContext _     getX (ListRange xs) = mapM getX xs
elemsInContext getXs getX (EnumRange sta msto mste) = renum msto mste where
  renum Nothing    Nothing    = dropWhile . (/=) <$> getX sta <*> getXs
  renum (Just sto) Nothing    = takeWhile . (/=) <$> getX sto <*> renum Nothing Nothing
  renum _          (Just ste) = every <$> lookupN ste <*> renum msto Nothing

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

instance Parsable CodeFragment where
  parser = pFrag where
    pFrag =   try (pFor ForA "action" (rangeParser parser $ refParser value))
          <|> try (pFor ForO "outcome" (rangeParser parser $ refParser value))
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
    pFor ::
      (Name -> Range Ref x -> [CodeFragment] -> CodeFragment) ->
      String ->
      Parser (Range Ref x) ->
      Parser CodeFragment
    pFor maker sym rparser = maker
      <$> (keyword "for" *> varname)
      <*> (keyword "in" *> symbol sym *> brackets rparser)
      <*> pBlock end
    pBlock ender = try (ender $> []) <|> ((:) <$> parser <*> pBlock ender)
    pPass = symbol "pass" $> Pass
    pReturn = try returnThing <|> returnNothing <?> "a return statement"
    returnNothing :: Parser CodeFragment
    returnThing = Return . Just <$> (symbol "return" *> parser)
    returnNothing = symbol "return" $> Return Nothing
    varname = name

evalCodeFragment :: MonadCompile m => CodeFragment -> m (PartialProgram Value ActionClaim)
evalCodeFragment code = case code of
  ForA n r inner -> loop (withA n) inner =<< elemsInContext (gets actionList) lookupA r
  ForO n r inner -> loop (withO n) inner =<< elemsInContext (gets outcomeList) lookupO r
  ForN n r inner -> loop (withN n) inner =<< elemsInContext (return [0..]) lookupN r
  LetN n x -> evalExpr x >>= modify . withN n >> return id
  If s block -> evalCodeFragment (IfElse s block [Pass])
  IfElse s tblock eblock -> do
    cond <- evalStatement s
    thens <- mapM evalCodeFragment tblock
    elses <- mapM evalCodeFragment eblock
    let yes = foldr1 (.) thens
    let no = foldr1 (.) elses
    return (\continue act ->
      (cond %^ yes continue act) %| (F.Neg cond %^ no continue act))
  Return (Just v) -> lookupA v >>= \a a' -> F.Val (a == a')
  Return Nothing -> gets defaultAction >>= \a a' -> F.Val (a == a')
  Pass -> return id
  where loop update block xs
          | null xs = return id
          | otherwise = foldr1 (.) . concat <$> mapM doFragment xs
          where doFragment x = modify (update x) >> mapM evalCodeFragment block

-------------------------------------------------------------------------------

data Code
  = Code [CodeFragment]
  | ActionMap (Map Value (ModalFormula ActionClaim))

instance Blockable Code where
  blockLines (Code frags) = concatMap blockLines frags
  blockLines (ActionMap a2s) = [
    (0, Text.pack $ printf "%s ↔ %s" a (show s)) | (a, s) <- Map.toList a2s]

instance Show Code where
  show = Text.unpack . renderBlock

instance Parsable Code where
  parser pconf = try frag <|> try ret where
    frag = Code <$> parser <*> parser
    ret = Return <$> (try retThing <|> retNothing <?> "a return statement")
    retThing = Just <$> (symbol "return" *> refParser value)
    retNothing = symbol "return" $> Nothing

codeMapParser :: Parser Code
codeMapParser = ActionMap . Map.fromList <$> (actionFormulaPair `sepEndBy` comma) where
  actionFormulaPair = (,) <$> (value <* pIff) <*> parser
  pIff = void $ choice [try $ symbol "↔", try $ symbol "<->", try $ keyword "iff"]

evalCode :: MonadCompile m => Code -> m (ModalProgram Value ActionClaim)
evalCode (Code frags) = do
  dflt <- gets defaultAction
  prog <- foldM (\p c -> p <$> evalCodeFragment c) id
  return $ prog (\a -> F.Val (dflt == a))
evalCode (ActionMap a2smap) = do
  let a2slist = Map.toList a2smap
  formulas <- mapM (evalStatement . snd) a2slist
  let a2flist = zip (map fst a2slist) formulas
  return $ \a -> let Just f = List.lookup a a2flist in f

returnValues :: Code -> [Value]
returnValues (ActionMap m) = Map.keys m
returnValues (Code frags) = concatMap fragRets frags where
  fragRets (Return (Just v)) = maybeToList $ lit v
  fragRets (ForA _ _ fs) = concatMap fragRets fs
  fragRets (ForO _ _ fs) = concatMap fragRets fs
  fragRets (ForN _ _ fs) = concatMap fragRets fs
  fragRets (If _ fs) = concatMap fragRets fs
  fragRets (IfElse _ fs gs) = (concatMap fragRets fs) ++ (concatMap fragRets gs)
  fragRets _ = []

-------------------------------------------------------------------------------

type CompiledAgent = Map Value (ModalFormula ActionClaim)

codeToProgram :: CompileErrorM m => Context -> Code -> m CompiledAgent
codeToProgram context code = uncurry toProg <$> runStateT (evalCode code) context where
  toProg prog state = Map.fromList [(a, prog a) | a <- actionList state]
