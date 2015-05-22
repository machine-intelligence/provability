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
import Data.Maybe
import Data.Monoid ((<>))
import Data.Foldable
import Data.Traversable
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
import qualified Data.Set as Set
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

evalExpr :: Contextual a o m => SimpleExpr -> m Int
evalExpr (Num v) = getN v
evalExpr (Add x y) = (+) <$> evalExpr x <*> evalExpr y
evalExpr (Sub x y) = (-) <$> evalExpr x <*> evalExpr y
evalExpr (Mul x y) = (*) <$> evalExpr x <*> evalExpr y
evalExpr (Exp x y) = (^) <$> evalExpr x <*> evalExpr y

-------------------------------------------------------------------------------

data Range m x
  = EnumRange (m x) (Maybe (m x)) (Maybe (m Int))
  | ListRange [m x]
  | TotalRange

instance (Eq (m x), Eq (m Int)) => Eq (Range m x) where
  (EnumRange sta sto ste) == (EnumRange sta' sto' ste') =
    (sta, sto, ste) == (sta', sto', ste')
  (ListRange xs) == (ListRange ys) = xs == ys
  TotalRange == TotalRange = True
  _ == _ = False

instance (Show (m x), Show (m Int)) => Show (Range m x) where
  show (EnumRange sta msto mste) = printf "%s..%s%s" (show sta) x y where
    x = maybe ("" :: String) show msto
    y = maybe ("" :: String) (printf " by %s" . show) mste
  show (ListRange xs) = printf "[%s]" (List.intercalate ", " $ map show xs)
  show TotalRange = "..."

instance (Parsable (m x), Parsable (m Int)) => Parsable (Range m x) where
  parser = rangeParser parser parser

rangeParser :: Parser (m Int) -> Parser (m x) -> Parser (Range m x)
rangeParser n x = try rEnum <|> try rList <|> try rAll <?> "a range" where
    rEnum = EnumRange <$> (x <* symbol "..") <*> optional x <*> pEnumBy
    pEnumBy = optional (try $ keyword "by" *> n)
    rList = ListRange <$> listParser x
    rAll = symbol "..." $> TotalRange

rangeValues :: (m x -> [x]) -> Range m x -> [x]
rangeValues f (EnumRange x my _) = f x ++ maybe [] f my
rangeValues f (ListRange xs) = concatMap f xs
rangeValues _ TotalRange = []

boundedRange :: (Parsable (m x), Parsable (m Int)) => Parser (Range m x)
boundedRange = try rBoundedEnum <|> try rList <?> "a bounded range" where
  rBoundedEnum = EnumRange <$> (parser <* symbol "..") <*> (Just <$> parser) <*> pEnumBy
  pEnumBy = optional (try $ keyword "by" *> parser)
  rList = ListRange <$> parser

elemsIn :: (Enum x, Applicative m, Monad m) =>
  (v Int -> m Int) -> (v x -> m x) -> Range v x -> m [x]
elemsIn getNum getX rng = case rng of
  TotalRange -> pure enumerate
  EnumRange sta Nothing Nothing -> enumFrom <$> getX sta
  EnumRange sta (Just sto) Nothing -> enumFromTo <$> getX sta <*> getX sto
  EnumRange sta Nothing (Just ste) ->
    getX sta >>= \s -> enumFromThen s . toThen s <$> getNum ste
  EnumRange sta (Just sto) (Just ste) ->
    getX sta >>= \s -> enumFromThenTo s . toThen s <$> getNum ste <*> getX sto
  ListRange xs -> mapM getX xs
  where toThen sta ste = toEnum $ fromEnum sta + ste

elemsInContext :: (Eq x, Evalable a o m) => m [x] -> (Ref x -> m x) -> Range Ref x -> m [x]
elemsInContext getXs _    TotalRange = getXs
elemsInContext _     getX (ListRange xs) = mapM getX xs
elemsInContext getXs getX (EnumRange sta msto mste) = renum msto mste where
  renum Nothing    Nothing    = dropWhile . (/=) <$> getX sta <*> getXs
  renum (Just sto) Nothing    = takeWhile . (/=) <$> getX sto <*> renum Nothing Nothing
  renum _          (Just ste) = every <$> getN ste <*> renum msto Nothing

-------------------------------------------------------------------------------

data CodeFragment s
  = ForA Name (Range Ref (Act s)) [CodeFragment s]
  | ForO Name (Range Ref (Out s)) [CodeFragment s]
  | ForN Name (Range Ref Int) [CodeFragment s]
  | LetN Name SimpleExpr
  | If s [CodeFragment s]
  | IfElse s [CodeFragment s] [CodeFragment s]
  | EarlyReturn (Maybe (Ref (Act s)))
  | Pass

-- TODO: If you ever add functionality to Statement that allows us to peak in and see which acts/outs were mentioned, then you'll need to update this code to take that into account.
_getCFActs :: IsStatement s => CodeFragment s -> [Act s]
_getCFActs (ForA _ r fs) = rangeValues (maybe [] pure . lit) r ++ concatMap _getCFActs fs
_getCFActs (ForO _ _ fs) = concatMap _getCFActs fs
_getCFActs (ForN _ _ fs) = concatMap _getCFActs fs
_getCFActs (If _ fs) = concatMap _getCFActs fs
_getCFActs (IfElse _ ts es) = concatMap _getCFActs ts ++ concatMap _getCFActs es
_getCFActs (EarlyReturn (Just (Lit x))) = [x]
_getCFActs _ = []
_getCFOuts :: IsStatement s => CodeFragment s -> [Out s]
_getCFOuts (ForA _ _ fs) = concatMap _getCFOuts fs
_getCFOuts (ForO _ r fs) = rangeValues (maybe [] pure . lit) r ++ concatMap _getCFOuts fs
_getCFOuts (ForN _ _ fs) = concatMap _getCFOuts fs
_getCFOuts (If _ fs) = concatMap _getCFOuts fs
_getCFOuts (IfElse _ ts es) = concatMap _getCFOuts ts ++ concatMap _getCFOuts es
_getCFOuts _ = []

instance (Show s, Show (Act s), Show (Out s)) => Blockable (CodeFragment s) where
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
    [ (0, Text.pack $ printf "if %s" $ show s) ] <>
    increaseIndent (concatMap blockLines xs)
  blockLines (IfElse s xs ys) =
    [ (0, Text.pack $ printf "if %s" $ show s) ] <>
    increaseIndent (concatMap blockLines xs) <>
    [ (0, "else") ] <>
    increaseIndent (concatMap blockLines ys)
  blockLines (EarlyReturn Nothing) = [(0, "return")]
  blockLines (EarlyReturn (Just x)) = [(0, Text.pack $ printf "return %s" (show x))]
  blockLines (Pass) = [(0, "pass")]

instance (Show s, Show (Act s), Show (Out s)) => Show (CodeFragment s) where
  show = Text.unpack . renderBlock

codeFragmentParser :: forall s. IsStatement s =>
  PConf (Act s) (Out s) -> Parser (CodeFragment s)
codeFragmentParser pconf = pFrag where
  pFrag =   try (pFor ForA (actSym pconf) (rangeParser parser $ parseAref pconf))
        <|> try (pFor ForO (outSym pconf) (rangeParser parser $ parseOref pconf))
        <|> try (pFor ForN (numSym pconf) boundedRange)
        <|> try pLetN
        <|> try pIf
        <|> try pIfElse
        <|> try pReturn
        <|> try pPass
  pLetN = LetN
    <$> (keyword "let" *> varname <* symbol "=")
    <*> parser
  pIf = If
    <$> (keyword "if" *> makeStatementParser pconf)
    <*> pBlock "end"
  pIfElse = IfElse
    <$> (keyword "if" *> makeStatementParser pconf)
    <*> pBlock "else"
    <*> pBlock "end"
  pFor ::
    (Name -> Range Ref x -> [CodeFragment s] -> CodeFragment s) ->
    String ->
    Parser (Range Ref x) ->
    Parser (CodeFragment s)
  pFor maker sym rparser = maker
    <$> (keyword "for" *> varname)
    <*> (keyword "in" *> symbol sym *> brackets rparser)
    <*> pBlock "end"
  pBlock kw = try (keyword kw $> []) <|> ((:) <$> recurse <*> pBlock kw)
  pPass = symbol "pass" $> Pass
  pReturn = try returnThing <|> returnNothing <?> "a return statement"
  returnNothing :: Parser (CodeFragment s)
  returnThing = earlyret . Just <$> (symbol "return" *> parseAref pconf)
  returnNothing = symbol "return" $> EarlyReturn Nothing
  varname = name
  recurse = codeFragmentParser pconf :: Parser (CodeFragment s)
  earlyret = EarlyReturn :: Maybe (Ref (Act s)) -> CodeFragment s

evalCodeFragment :: forall s m. (IsStatement s, Evalable (Act s) (Out s) m) =>
  CodeFragment s -> m (PartialProgram (Act s) (Var s (Act s) (Out s)))
evalCodeFragment code = case code of
  ForA n r inner -> loop (withA n) inner =<< elemsInContext getAs getA r
  ForO n r inner -> loop (withO n) inner =<< elemsInContext getOs getO r
  ForN n r inner -> loop (withN n) inner =<< elemsInContext (return [0..]) getN r
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
  EarlyReturn x -> const <$> evalCode (Return x :: Code s)
  Pass -> return id
  where loop ::
          (x -> Context (Act s) (Out s) ->
          Context (Act s) (Out s)) ->
          [CodeFragment s] ->
          [x] ->
          m (PartialProgram (Act s) (Var s (Act s) (Out s)))
        loop update block xs
          | null xs = return id
          | otherwise = foldr1 (.) . concat <$> mapM doFragment xs
          where doFragment x = modify (update x) >> mapM evalCodeFragment block

-------------------------------------------------------------------------------

-- TODO: Figure out what to do with FullMap.
-- As of now, the "normal" code blocks can't parse a FullMap, which I think is
-- probably the right choice. This guarantees that parsed Code is always
-- P.M.E.E. That said, being able to parse a full map is often quite
-- convenient. I haven't thought a lot about whether normal code and maps
-- should be able to overlap, so I'm going to keep them separate.
-- For reference, normal code looks like this:
--
--   agent Agent:
--      if ⊤
--          return @X
--      end
--      return @Y
--   end
--
-- whereas maps might look like this:
--
--   agent map AgentMap:
--      @X ↔ ⊤
--      @Y ↔ ⊥
--   end
--
-- Not clear they should interact at all.
-- Maybe there needs to be another layer between Code and Def?
-- Maybe there needs to be a typeclass for code, such as Compilable?
data Code s
  = Fragment (CodeFragment s) (Code s)
  | Return (Maybe (Ref (Act s)))
  | FullMap (Map (Act s) s)

instance (Show s, Show (Act s), Show (Out s)) => Blockable (Code s) where
  blockLines (Fragment f c) = blockLines f ++ blockLines c
  blockLines (Return Nothing) = [(0, "return")]
  blockLines (Return (Just x)) = [(0, Text.pack $ printf "return %s" (show x))]
  blockLines (FullMap a2s) = [
    (0, Text.pack $ printf "%s ↔ %s" (show a) (show s)) | (a, s) <- Map.toList a2s]

instance (Show s, Show (Act s), Show (Out s)) => Show (Code s) where
  show = Text.unpack . renderBlock

getActs :: IsStatement s => Code s -> [Act s]
getActs (FullMap m) = Map.keys m
getActs (Return (Just (Lit x))) = [x]
getActs (Return _) = []
getActs (Fragment f c) = _getCFActs f ++ getActs c

getOuts :: IsStatement s => Code s -> [Out s]
getOuts (Fragment f c) = _getCFOuts f ++ getOuts c
getOuts _ = []

codeParser :: IsStatement s => PConf (Act s) (Out s) -> Parser (Code s)
codeParser pconf = try frag <|> try ret where
  frag = Fragment <$> codeFragmentParser pconf <*> codeParser pconf
  ret = Return <$> ((try retThing <|> retNothing <?> "a return statement") <* end)
  end = try (keyword "end") <?> "an 'end'"
  retThing = Just <$> (symbol "return" *> parseAref pconf)
  retNothing = symbol "return" $> Nothing

codeMapParser :: IsStatement s => PConf (Act s) (Out s) -> Parser (Map (Act s) s)
codeMapParser pconf = Map.fromList <$> (asPair `sepEndBy` comma) where
  parseAsign = symbol (actSym pconf) *> parseA pconf
  asPair = (,) <$> (parseAsign <* pIff) <*> makeStatementParser pconf
  pIff = void $ choice [try $ symbol "↔", try $ symbol "<->", try $ keyword "iff"]

evalCode :: forall s m. (IsStatement s, Evalable (Act s) (Out s) m) =>
  Code s -> m (ModalProgram (Act s) ((Var s) (Act s) (Out s)))
evalCode (Fragment f cont) = evalCodeFragment f >>= (<$> evalCode cont)
evalCode (Return (Just v)) = (F.Val .) . (==) <$> getA v
evalCode (Return Nothing) = defaultAction >>= evalCode . ret . Just . Lit
  where ret x = Return x :: Code s -- Disambiguates s
evalCode (FullMap a2smap) = do
  let a2slist = Map.toList a2smap
  formulas <- mapM (evalStatement . snd) a2slist
  let a2flist = zip (map fst a2slist) formulas
  return $ \a -> let Just f = List.lookup a a2flist in f

codeToProgram :: IsStatement s =>
  Context (Act s) (Out s) -> Code s ->
  Either CompileError (CompiledAgent s)
codeToProgram context code = runExcept $ do
  (prog, state) <- runStateT (evalCode code) context
  return $ Map.fromList [(a, prog a) | a <- actionList state]

-------------------------------------------------------------------------------
-- TODO: Split this out into Agent.hs or Def.hs or something.

type CompiledAgent s = Map (Act s) (ModalFormula (Var s (Act s) (Out s)))
type Args a o = [(Name, Maybe (Val a o))]

data Def s = Def
  { defArgs :: Args (Act s) (Out s)
  , defActions :: Maybe [Act s]
  , defOutcomes :: Maybe [Out s]
  , defName :: Name
  , defCode :: Code s }

instance Show (Def s) where show = defName

defheadParser :: PConf a o -> Parser (Name, Args a o, Maybe [a], Maybe [o])
defheadParser pconf = do
  n <- anyname
  ps <- option [] (try $ defargsParser pconf)
  let aorder = deforderParser (actSym pconf) (parseA pconf)
  let oorder = deforderParser (outSym pconf) (parseO pconf)
  (as, os) <- anyComboOf aorder oorder
  return (n, ps, join as, join os)

defargsParser :: PConf a o -> Parser (Args a o)
defargsParser pconf = parens (arg `sepBy` comma) where
  arg = try num <|> try act <|> try out
  param sym p = symbol sym *> ((,) <$> name <*> optional (symbol "=" *> p))
  num = param (numSym pconf) (Number <$> parser)
  act = param (actSym pconf) (Action <$> parseA pconf)
  out = param (outSym pconf) (Outcome <$> parseO pconf)

deforderParser :: String -> Parser x -> Parser (Maybe [x])
deforderParser sym p = symbol sym *> try acts <|> try dunno where
  acts = brackets (p `sepEndBy` comma) <$$> Just
  dunno = brackets (string "...") $> Nothing

-------------------------------------------------------------------------------

data Call a o = Call
  { callName :: Name
  , callArgs :: [Val a o]
  , callKwargs :: Map Name (Val a o)
  , callActions :: Maybe [a]
  , callOutcomes :: Maybe [o]
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
  as <- morderParser (actSym pconf) (parseA pconf)
  os <- morderParser (outSym pconf) (parseO pconf)
  alias <- optional (try (keyword "as" *> anyname))
  return $ Call n args kwargs as os alias
  where
    orderParser p = try (Just <$> listParser p) <|> (brackets (string "...") $> Nothing)
    morderParser sym p = option Nothing $ try (symbol sym *> orderParser p)
    argsParser = parens argsThenKwargs where
      argsThenKwargs = (,) <$> allArgs <*> allKwargs
      allArgs = arg `sepEndBy` comma
      allKwargs = Map.fromList <$> (kwarg `sepEndBy` comma)
      kwarg = (,) <$> name <*> (symbol "=" *> arg)
      arg = try num <|> try act <|> try out <?> "an argument"
      num = symbol (numSym pconf) *> (Number <$> parser)
      act = symbol (actSym pconf) *> (Action <$> parseA pconf)
      out = symbol (outSym pconf) *> (Outcome <$> parseO pconf)

compile :: IsStatement s =>
  Def s -> Call (Act s) (Out s) ->
  Either CompileError (CompiledAgent s)
compile def call = do
  context <- makeContext def call
  program <- codeToProgram context (defCode def)
  return $ Map.map F.simplify program

defcallAOlists :: (IsStatement s, MonadError CompileError m) =>
  Def s -> Call (Act s) (Out s) -> m ([Act s], [Out s])
defcallAOlists def call = do
  let (codeAs, codeOs) = (getActs (defCode def), getOuts (defCode def))
  let (defAs, defOs) = (defActions def, defOutcomes def)
  let (callAs, callOs) = (callActions call, callOutcomes call)
  as <- ensureRinL (ccerr "action") callAs =<< ensureRinL (dcerr "action") defAs codeAs
  os <- ensureRinL (ccerr "outcome") callOs =<< ensureRinL (dcerr "outcome") defOs codeOs
  return (as, os)
  where
    dcerr, ccerr :: Show x => String -> [x] -> [x] -> CompileError
    dcerr str xs ys = DefCodeListConflict (defName def) str (map show xs) (map show ys)
    ccerr str xs ys = CodeCallListConflict (defName def) str (map show xs) (map show ys)
    ensureRinL _ Nothing olds = return olds
    ensureRinL err (Just news) olds
     | Set.fromList olds `Set.isSubsetOf` Set.fromList news = return news
     | otherwise = throwError $ err olds news

defcallArgs :: (IsStatement s, Functor m, MonadError CompileError m) =>
  Def s -> Call (Act s) (Out s) -> m (Map Name (Val (Act s) (Out s)))
defcallArgs def call = do
  when (length (callArgs call) > length (defArgs def)) (throwError $ TooManyArgs $ show call)
  arglist <- mapM handleArgs (zip (defArgs def) infiniteCallArgs)
  Map.fromList <$> mapM handleKwargs arglist
  where
    infiniteCallArgs = (Just <$> callArgs call) ++ repeat Nothing
    handleKwargs (k, v) = joinKwargs k (Map.lookup k (callKwargs call)) v
    handleArgs ((n, mdflt), mval) = joinArgs n mdflt mval
    joinArgs n Nothing mval = return (n, mval)
    joinArgs n mdflt Nothing = return (n, mdflt)
    joinArgs n (Just dflt) (Just val)
      | typesMatch dflt val = return (n, Just val)
      | otherwise = throwError (WrongType n (typeOf dflt) (typeOf val))
    joinKwargs n Nothing Nothing  = throwError (ArgMissing (defName def) n)
    joinKwargs n (Just dflt) (Just val)
      | typesMatch dflt val = return (n, val)
      | otherwise = throwError (WrongType n (typeOf dflt) (typeOf val))
    joinKwargs n mdflt mval = return (n, fromMaybe (fromJust mdflt) mval)

-- TODO: Extract as and os from the code. Use them if they aren't present.
-- Verify that they match if they are present.
makeContext :: (IsStatement s, Functor m, MonadError CompileError m) =>
  Def s -> Call (Act s) (Out s) -> m (Context (Act s) (Out s))
makeContext def call = do
  args <- defcallArgs def call
  (as, os) <- defcallAOlists def call
  when (List.null as) (throwError (NoList (defName def) "action"))
  when (List.null os) (throwError (NoList (defName def) "outcome"))
  return $ Context args as os
