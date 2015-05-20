{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Modal.Code where
import Prelude hiding (readFile, sequence, mapM, foldr1, concat, concatMap)
import Control.Applicative
import Control.Monad.Except hiding (mapM, sequence)
import Control.Monad.State hiding (mapM, sequence, state)
import Data.Map (Map)
import Data.Monoid ((<>))
import Data.Text (Text)
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
      <|> try (Num <$> (parser :: Parsec Text s (Ref Int)))
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

rangeParser :: Parsec Text s (m Int) -> Parsec Text s (m x) -> Parsec Text s (Range m x)
rangeParser n x = try rEnum <|> try rList <|> try rAll <?> "a range" where
    rEnum = EnumRange <$> (x <* symbol "..") <*> optional x <*> pEnumBy
    pEnumBy = optional (try $ keyword "by" *> n)
    rList = ListRange <$> listParser x
    rAll = symbol "..." $> TotalRange

boundedRange :: (Parsable (m x), Parsable (m Int)) => Parsec Text s (Range m x)
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
  = ForMe Name (Range Ref (Act s)) [CodeFragment s]
  | ForThem Name (Range Ref (Out s)) [CodeFragment s]
  | ForN Name (Range Ref Int) [CodeFragment s]
  | LetN Name SimpleExpr
  | If s [CodeFragment s]
  | IfElse s [CodeFragment s] [CodeFragment s]
  | EarlyReturn (Maybe (Ref (Act s)))
  | Pass

instance (Show s, Show (Act s), Show (Out s)) => Blockable (CodeFragment s) where
  blockLines (ForMe n r cs) =
    [(0, Text.pack $ printf "for action %s in %s" (Text.unpack n) (show r))] <>
    increaseIndent (concatMap blockLines cs)
  blockLines (ForThem n r cs) =
    [(0, Text.pack $ printf "for outcome %s in %s" (Text.unpack n) (show r))] <>
    increaseIndent (concatMap blockLines cs)
  blockLines (ForN n r cs) =
    [(0, Text.pack $ printf "for number %s in %s" (Text.unpack n) (show r))] <>
    increaseIndent (concatMap blockLines cs)
  blockLines (LetN n x) =
    [(0, Text.pack $ printf "let %s = %s" (Text.unpack n) (show x))]
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

instance (IsStatement s, Parsable (Act s), Parsable (Out s)) =>
  Parsable (CodeFragment s) where parser = codeFragmentParser parser parser

codeFragmentParser :: IsStatement s =>
  Parsec Text u (Act s) -> Parsec Text u (Out s) -> Parsec Text u (CodeFragment s)
codeFragmentParser a o = pFrag where
  pFrag =   try fForMe
        <|> try fForThem
        <|> try fForN
        <|> try fLetN
        <|> try fIf
        <|> try fIfElse
        <|> try fReturn
        <|> try fPass
  fLetN = LetN <$> (keyword "let" *> varname <* symbol "=") <*> parser
  fIf = If <$> (keyword "if" *> makeStatementParser a o) <*> fBlock
  fIfElse = IfElse <$> (keyword "if" *> makeStatementParser a o) <*> bElse <*> fBlock
  fForMe = ForMe <$> (keyword "for" *> keyword "action" *> varname) <*>
    (keyword "in" *> rangeParser parser (refParser a)) <*> fBlock
  fForThem = ForThem <$> (keyword "for" *> keyword "outcome" *> varname) <*>
    (keyword "in" *> rangeParser parser (refParser o)) <*> fBlock
  fForN = ForN <$> (keyword "for" *> keyword "number" *> varname) <*>
    (keyword "in" *> boundedRange) <*> fBlock
  bElse = try (keyword "else" $> [])
        <|> ((:) <$> codeFragmentParser a o <*> bElse)
  fBlock =   try (keyword "end" $> [])
         <|> ((:) <$> codeFragmentParser a o <*> fBlock)
  fPass = symbol "pass" $> Pass
  fReturn = try returnThing <|> returnNothing <?> "a return statement"
  returnThing = EarlyReturn . Just <$> (symbol "return" *> refParser a)
  returnNothing = symbol "return" $> EarlyReturn Nothing
  varname = char '$' *> name

evalCodeFragment :: forall s m. (IsStatement s, Evalable (Act s) (Out s) m) =>
  CodeFragment s -> m (PartialProgram (Act s) ((Var s) (Act s) (Out s)))
evalCodeFragment code = case code of
  ForMe n r inner -> loop (withA n) inner =<< elemsInContext getAs getA r
  ForThem n r inner -> loop (withO n) inner =<< elemsInContext getOs getO r
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
  where loop update block xs
          | null xs = return id
          | otherwise = foldr1 (.) . concat <$> mapM doFragment xs
          where doFragment x = modify (update x) >> mapM evalCodeFragment block

-------------------------------------------------------------------------------

data Code s
  = Fragment (CodeFragment s) (Code s)
  | Return (Maybe (Ref (Act s)))

instance (Show s, Show (Act s), Show (Out s)) => Blockable (Code s) where
  blockLines (Fragment f c) = blockLines f ++ blockLines c
  blockLines (Return Nothing) = [(0, "return")]
  blockLines (Return (Just x)) = [(0, Text.pack $ printf "return %s" (show x))]

instance (Show s, Show (Act s), Show (Out s)) => Show (Code s) where
  show = Text.unpack . renderBlock

instance (IsStatement s, Parsable (Act s), Parsable (Out s)) => Parsable (Code s) where
  parser = codeParser parser parser

codeParser :: IsStatement s =>
  Parsec Text u (Act s) -> Parsec Text u (Out s) -> Parsec Text u (Code s)
codeParser a o = try frag <|> try ret where
  frag = Fragment <$> codeFragmentParser a o <*> codeParser a o
  ret = Return <$> ((try retThing <|> retNothing <?> "a return statement") <* end)
  end = try (keyword "end") <?> "an 'end'"
  retThing = Just <$> (symbol "return" *> refParser a)
  retNothing = symbol "return" $> Nothing

evalCode :: forall s m. (IsStatement s, Evalable (Act s) (Out s) m) =>
  Code s -> m (ModalProgram (Act s) ((Var s) (Act s) (Out s)))
evalCode (Fragment f cont) = evalCodeFragment f >>= (<$> evalCode cont)
evalCode (Return (Just v)) = (F.Val .) . (==) <$> getA v
evalCode (Return Nothing) = defaultAction >>= evalCode . ret . Just . Lit
  where ret x = Return x :: Code s -- Disambiguates s

codeToProgram :: IsStatement s =>
  Context (Act s) (Out s) -> Code s ->
  Either CompileError (CompiledAgent s)
codeToProgram context code = runExcept $ do
  (prog, state) <- runStateT (evalCode code) context
  return $ Map.fromList [(a, prog a) | a <- actionList state]

-------------------------------------------------------------------------------

type CompiledAgent s = Map (Act s) (ModalFormula (Var s (Act s) (Out s)))

data Def s = Def
  { agentArgs :: [(Name, Maybe (Val (Act s) (Out s)))]
  , agentActions :: Maybe [Act s]
  , agentOutcomes :: Maybe [Out s]
  , agentName :: Name
  , agentCode :: Code s }

instance (Show s, Show (Act s), Show (Out s)) => Blockable (Def s) where
  blockLines (Def ps oa oo n c) = (0, header) : increaseIndent (blockLines c) where
    header = Text.pack $ printf "def %s%s%s%s" (Text.unpack n) x y z
    x = if null ps then ""
        else printf "(%s)" $ List.intercalate ("," :: String) $ map showP ps
    showP (var, Nothing) = printf "number %s" (Text.unpack var)
    showP (var, Just (Number i)) = printf "number %s=%d" (Text.unpack var) i
    showP (var, Just (Action a)) = printf "action %s=%s" (Text.unpack var) (show a)
    showP (var, Just (Outcome o)) = printf "outcome %s=%s" (Text.unpack var) (show o)
    y = maybe "" (printf "actions=[%s]" . List.intercalate "," . map show) oa
    z = maybe "" (printf "outcomes=[%s]" . List.intercalate "," . map show) oo
    x, y, z :: String

instance (Show s, Show (Act s), Show (Out s)) => Show (Def s) where
  show = Text.unpack . renderBlock

defParser :: IsStatement s =>
  Parsec Text u (Act s) -> Parsec Text u (Out s) ->
  String -> String -> String ->
  Parsec Text u (Def s)
defParser a o kwa kwo kw = makeDef <$>
  (keyword kw *> name) <*>
  option [] (try $ defargsParser a o) <*>
  deforderParser kwa a <*>
  deforderParser kwo o <*>
  codeParser a o
  where makeDef n ps as os = Def ps as os n

defargsParser ::
  Parsec Text u a -> Parsec Text u o ->
  Parsec Text u [(Name, Maybe (Val a o))]
defargsParser a o = parens (arg `sepBy` comma) where
  arg = try num <|> try act <|> try out
  num = keyword "number" *> ((,) <$> name <*> optional (symbol "=" *> (Number <$> parser)))
  act = keyword "actions" *> ((,) <$> name <*> optional (symbol "=" *> (Action <$> a)))
  out = keyword "outcomes" *> ((,) <$> name <*> optional (symbol "=" *> (Outcome <$> o)))

deforderParser :: String -> Parsec Text u a -> Parsec Text u (Maybe [a])
deforderParser kw p = try acts <|> try dunno <|> pure Nothing where
  acts = Just <$> (keyword kw *> symbol "=" *> brackets (p `sepEndBy` comma))
  dunno = brackets (string "...") $> Nothing

compile :: IsStatement s =>
  Parameters (Act s) (Out s) -> Def s ->
  Either CompileError (Name, CompiledAgent s)
compile params def = do
  context <- makeContext params def
  program <- codeToProgram context (agentCode def)
  return (agentName def, Map.map F.simplify program)

-------------------------------------------------------------------------------

data Parameters a o = Parameters
  { paramArgs :: [Val a o]
  , paramKwargs :: Map Name (Val a o)
  , paramActions :: Maybe [a]
  , paramOutcomes :: Maybe [o]
  } deriving (Eq, Ord, Show)

instance (Parsable a, Parsable o) => Parsable (Parameters a o) where
  parser = paramsParser parser parser

simpleParameters :: [a] -> [o] -> Parameters a o
simpleParameters as os = Parameters [] Map.empty (Just as) (Just os)

paramsParser ::
  Parsec Text s a -> Parsec Text s o ->
  Parsec Text s (Parameters a o)
paramsParser a o = do
  (args, kwargs) <- argsParser a o
  as <- option Nothing (orderParser a)
  os <- option Nothing (orderParser o)
  return $ Parameters args kwargs as os

argsParser ::
  Parsec Text s a -> Parsec Text s o ->
  Parsec Text s ([Val a o], Map Name (Val a o))
argsParser a o = parens argsThenKwargs where
  argsThenKwargs = (,) <$> allArgs <*> allKwargs
  allArgs = arg `sepEndBy` comma
  allKwargs = Map.fromList <$> (kwarg `sepEndBy` comma)
  kwarg = (,) <$> name <*> (symbol "=" *> arg)
  arg = try num <|> try act <|> try out <?> "an argument (starting with one of #@$)"
  num = Number <$> parser
  act = Action <$> a
  out = Outcome <$> o

orderParser :: Parsec Text s x -> Parsec Text s (Maybe [x])
orderParser x = try (Just <$> listParser x) <|> (brackets (string "...") $> Nothing)

makeContext :: IsStatement s =>
  Parameters (Act s) (Out s) -> Def s -> Either CompileError (Context (Act s) (Out s))
makeContext params def = Context <$> vs <*> as <*> os where
  aname = agentName def
  joinArgs argname Nothing Nothing  = return (argname, Nothing)
  joinArgs argname (Just x) Nothing = return (argname, Just x)
  joinArgs argname Nothing (Just y) = return (argname, Just y)
  joinArgs argname (Just x) (Just y)
    | typesMatch x y = return (argname, Just x)
    | otherwise = Left (WrongType argname (typeOf x) (typeOf y))
  joinKwargs argname Nothing Nothing  = Left (ArgMissing aname argname)
  joinKwargs argname (Just x) Nothing = return (argname, x)
  joinKwargs argname Nothing (Just y) = return (argname, y)
  joinKwargs argname (Just x) (Just y)
    | typesMatch x y = return (argname, x)
    | otherwise = Left (WrongType argname (typeOf x) (typeOf y))
  vs = do
    when (length (paramArgs params) > length (agentArgs def)) (Left $ TooManyArgs aname)
    let padded = (Just <$> paramArgs params) ++ repeat Nothing
    arglist <- mapM (\((n, d), v) -> joinArgs n v d) (zip (agentArgs def) padded)
    argmap <- mapM (\(k, v) -> joinKwargs k (Map.lookup k $ paramKwargs params) v) arglist
    return $ Map.fromList argmap
  getMatching str f g = case (f params, g def) of
    (Nothing, Nothing) -> Left $ Missing aname str
    (Just xs, Nothing) -> return xs
    (Nothing, Just xs) -> return xs
    (Just xs, Just ys) -> if xs == ys then return xs else Left (Mismatch aname str)
  as = getMatching "actions" paramActions agentActions
  os = getMatching "outcomes" paramOutcomes agentOutcomes
