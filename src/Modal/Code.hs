{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module Modal.Code where
import Prelude hiding (readFile, sequence, mapM, foldr1, concat, concatMap)
import Control.Applicative
import Control.Monad.Except hiding (mapM, sequence)
import Control.Monad.State hiding (mapM, sequence, state)
import Data.Map (Map)
import Data.Maybe (mapMaybe, maybeToList)
import Data.Monoid ((<>))
import Data.Foldable
import Data.Traversable
import Modal.CompilerBase hiding (main)
import Modal.Display
import Modal.Formulas (ModalFormula, (%^), (%|))
import Modal.Parser hiding (main)
import Modal.Programming
import Modal.Statement hiding (main)
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
  { actionKw :: String
  , actionsKw :: String
  , outcomeKw :: String
  , outcomesKw :: String
  } deriving (Eq, Ord, Read, Show)

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
  show TotalRange = "[...]"

instance Parsable x => Parsable (Range x) where
  parser = rangeParser "[...]" parser

rangeParser :: String -> Parser x -> Parser (Range x)
rangeParser allname x = try rEnum <|> try rList <|> try rAll <?> "a range" where
    rEnum = EnumRange <$>
      (symbol "[" *> refParser x <* symbol "..") <*>
      (optional (refParser x) <* symbol "]") <*>
      optional (try $ keyword "by" *> parser)
    rList = ListRange <$> listParser (refParser x)
    rAll = keyword allname $> TotalRange

_testRangeParser :: IO ()
_testRangeParser = do
  let succeeds = verifyParser (parser :: Parser (Range Int))
  let fails = verifyParserFails (parser :: Parser (Range Int))
  succeeds "[1..]" (EnumRange (Lit 1) Nothing Nothing)
  succeeds "[ 1 ..]" (EnumRange (Lit 1) Nothing Nothing)
  succeeds "[ 1 .. 2 ]" (EnumRange (Lit 1) (Just (Lit 2)) Nothing)
  succeeds "[&n..]" (EnumRange (Ref "n") Nothing Nothing)
  succeeds "[&n..3]" (EnumRange (Ref "n") (Just (Lit 3)) Nothing)
  succeeds "[&n..3] by 2" (EnumRange (Ref "n") (Just (Lit 3)) (Just (Lit 2)))
  fails    "[1..2..3]"
  succeeds "[1, 2, &three]" (ListRange [Lit 1, Lit 2, Ref "three"])
  succeeds "[...]" TotalRange
  succeeds "[ ]" (ListRange [])
  fails    "[  "

boundedRange :: Parsable x => Parser (Range x)
boundedRange = try rBoundedEnum <|> try rList <?> "a bounded range" where
  rBoundedEnum = EnumRange <$>
    (symbol "[" *> parser <* symbol "..") <*>
    (Just <$> parser <* symbol "]") <*>
    optional (try $ keyword "by" *> parser)
  rList = ListRange <$> parser

_testBoundedRangeParser :: IO ()
_testBoundedRangeParser = do
  let succeeds = verifyParser (boundedRange :: Parser (Range Int))
  let fails = verifyParserFails (boundedRange :: Parser (Range Int))
  fails    "[1..]"
  succeeds "[1 .. 2]" (EnumRange (Lit 1) (Just (Lit 2)) Nothing)
  succeeds "[&n .. 2] by 10" (EnumRange (Ref "n") (Just (Lit 2)) (Just (Lit 10)))
  succeeds "[1, 2, &three]" (ListRange [Lit 1, Lit 2, Ref "three"])
  fails    "[...]"

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
  = For ClaimType Name (Range Value) [CodeFragment]
  | ForN Name (Range Int) [CodeFragment]
  | LetN Name SimpleExpr
  | If Statement [CodeFragment]
  | IfElse Statement [CodeFragment] [CodeFragment]
  | Return (Maybe (Ref Value))
  | Pass
  deriving Eq

instance  Blockable CodeFragment where
  blockLines (For t n r cs) =
    [(0, Text.pack $ printf "for %s %s in %s" (show t) n (show r))] <>
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

data CodeFragConfig = CodeFragConfig
  { indentLevel :: Int
  , codeConfig :: CodeConfig
  } deriving (Eq, Ord, Read, Show)

eatIndent :: CodeFragConfig -> Parser ()
eatIndent conf = void (count (indentLevel conf) (char '\t'))
  <?> printf "%d tabs" (indentLevel conf)

codeFragmentParser :: CodeFragConfig -> Parser CodeFragment
codeFragmentParser conf = try indent *> pFrag where
  indent = (many $ try ignoredLine) *> eatIndent conf
  pFrag =   try pForA
        <|> try pForO
        <|> try pForN
        <|> try pLetN
        <|> try pIfElse
        <|> try pIf
        <|> try pReturn
        <|> try pPass
  pForA = pFor ActionT action actions
  pForO = pFor OutcomeT outcome outcomes
  pFor t x xs = For t
    <$> (keyword "for" *> keyword x *> varname)
    <*> (keyword "in" *> rangeParser xs parser <* w <* endOfLine)
    <*> pBlock
  pForN = ForN
    <$> (keyword "for" *> keyword "number" *> varname)
    <*> (keyword "in" *> boundedRange <* w <* endOfLine)
    <*> pBlock
  pLetN = LetN
    <$> (keyword "let" *> varname <* symbol "=")
    <*> parser <* eols
  pIf = If
    <$> (keyword "if" *> parser <* w <* endOfLine)
    <*> pBlock
  pIfElse = IfElse
    <$> (keyword "if" *> parser <* w <* endOfLine)
    <*> pBlock
    <*> (indent *> keyword "else" *> w *> endOfLine *> pBlock)
  pBlock = many1 $ try $ codeFragmentParser conf{indentLevel=succ $ indentLevel conf}
  pPass = symbol "pass" $> Pass <* w <* eol
  pReturn = try returnThing <|> returnNothing <?> "a return statement"
  returnNothing :: Parser CodeFragment
  returnThing = symbol "return " *> (Return . Just <$> parser) <* w <* eol
  returnNothing = symbol "return" $> Return Nothing <* w <* eol
  action = actionKw $ codeConfig conf
  outcome = outcomeKw $ codeConfig conf
  actions = actionsKw $ codeConfig conf
  outcomes = outcomesKw $ codeConfig conf
  varname = char '&' *> name

compileCodeFragment :: MonadCompile m =>
  CodeFragment -> m (PartialProgram Value CompiledClaim)
compileCodeFragment code = case code of
  For ActionT n r x -> loop (withA n) x =<< compileRange (gets actionList) lookupA r
  For OutcomeT n r x -> loop (withO n) x =<< compileRange (gets outcomeList) lookupO r
  ForN n r x -> loop (withN n) x =<< compileRange (return [0..]) lookupN r
  LetN n x -> compileExpr x >>= modify . withN n >> return id
  If s block -> compileCodeFragment (IfElse s block [Pass])
  IfElse s tblock eblock -> do
    cond <- compileStatement compileClaim s
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
    (0, Text.pack $ printf "%s ↔ %s" (show a) (show s)) | (a, s) <- Map.toList a2s]

instance Show Code where
  show = Text.unpack . renderBlock

codeParser :: CodeConfig -> Parser Code
codeParser conf = Code <$> many1 (codeFragmentParser $ CodeFragConfig 1 conf)

_testCodeParser :: IO ()
_testCodeParser = testAllSamples where
  sample1 = Text.unlines
    ["\tlet &step = 0"
    ,"\tfor action &a in actions"
    ,"\t\t-- This is a comment about the inner loop."
    ,"\t\tfor outcome &u in utilities"
    ,"\t\t\tif [&step][A()=&a -> U()=&u]"
    ,"\t\t\t\treturn &a"
    ,"\t\t\tlet &step = &step + 1"
    ,"\treturn"]
  sample2 = Text.unlines
    ["\tif {- IGNORE THIS COMMENT -} [][Them(Me)=C]"
    ,"\t\treturn C  -- Ignore this one too."
    ,""
    ,"\telse"
    ,"\t\treturn D"]
  sample3 = Text.unlines
    ["                   -- Sample 3:"
    ,"\tfor number &n in [0, 1, 2, 3]"
    ,"\t\tif Possible(&n)[Them(Me)=C]"
    ,"\t\t\treturn C"
    ,"   \t      "
    ,""
    ,"\treturn D"]
  sample4 = Text.unlines
    ["\tfor number &n in [...]"
    ,"\t\treturn &n"]
  sample5 = Text.unlines
    ["\tif ⊤"
    ,"\treturn 0"]
  sample6 = Text.unlines
    ["\tif ⊤"
    ,"\t  return 0"]
  sample7 = Text.unlines
    ["\tif ⊤"
    ,"\t\t\treturn 0"]
  conf = CodeConfig "action" "actions" "outcome" "utilities"
  testAllSamples = do
    verifyParser (codeParser conf) sample1 (Code
      [ LetN "step" (Num (Lit 0))
      , For ActionT "a" TotalRange
        [ For OutcomeT "u" TotalRange
          [ If (Provable (Ref "step")
              (Imp
                (Var $ ParsedClaim "A" Nothing (Equals (Ref "a")))
                (Var $ ParsedClaim "U" Nothing (Equals (Ref "u")))))
              [ Return (Just (Ref "a")) ]
          , LetN "step" (Add (Num $ Ref "step") (Num $ Lit 1)) ] ]
      , Return Nothing ])
    verifyParser (codeParser conf) sample2 (Code
      [ IfElse (Provable (Lit 0)
        (Var $ ParsedClaim "Them"
          (Just $ Call "Me" [] Map.empty [] [])
          (Equals $ Lit "C")))
        [ Return (Just (Lit "C")) ]
        [ Return (Just (Lit "D")) ] ])
    verifyParser (codeParser conf) sample3 (Code
      [ ForN "n" (ListRange [Lit 0, Lit 1, Lit 2, Lit 3])
        [ If (Possible (Ref "n")
            (Var $ ParsedClaim "Them"
              (Just $ Call "Me" [] Map.empty [] [])
              (Equals $ Lit "C")))
          [ Return (Just (Lit "C")) ] ]
      , Return (Just (Lit "D")) ])
    verifyParserFails (codeParser conf) sample4
    verifyParserFails (codeParser conf) sample5
    verifyParserFails (codeParser conf) sample6
    verifyParserFails (codeParser conf) sample7

codeMapParser :: Parser Code
codeMapParser = ActionMap . Map.fromList <$> many1 assignment where
  indent = (many (w *> endOfLine)) *> char '\t'
  iffParsers = [symbol "↔", symbol "<->", keyword "iff"]
  pIff = void $ choice $ map try iffParsers
  assignment = (,) <$> (indent *> parser <* pIff) <*> (parser <* eols)

_testCodeMapParser :: IO ()
_testCodeMapParser = testAllSamples where
  sample1 = Text.unlines
    ["\tC ↔ [][Them(Me)=C]"
    ,"\tD ↔ ~[][Them(Me)=C]"]
  sample2 = Text.unlines
    ["\tCD iff A1()=C and A2()=D"
    ,"\tCC iff A1()=C and A2()=C"
    ,"\tDD iff A1()=D and A2()=D"
    ,"\tDC iff A1()=D and A2()=C"]
  sample3 = Text.unlines
    ["\tC ↔ [][Them(Me)=C]"
    ,"\t\tD ↔ ~[][Them(Me)=C]"]
  sample4 = Text.unlines
    ["\tC ↔ [][Them(Me)=C]"
    ,"  D ↔ ~[][Them(Me)=C]"]
  testAllSamples = do
    verifyParser codeMapParser sample1 (ActionMap $ Map.fromList
      [ ("C", Provable (Lit 0) (Var $ ParsedClaim "Them"
              (Just $ Call "Me" [] Map.empty [] [])
              (Equals $ Lit "C")))
      , ("D", Neg $ Provable (Lit 0) (Var $ ParsedClaim "Them"
              (Just $ Call "Me" [] Map.empty [] [])
              (Equals $ Lit "C"))) ])
    verifyParser codeMapParser sample2 (ActionMap $ Map.fromList
      [ ("CD", (And
        (Var $ ParsedClaim "A1" Nothing (Equals $ Lit "C"))
        (Var $ ParsedClaim "A2" Nothing (Equals $ Lit "D"))))
      , ("CC", (And
        (Var $ ParsedClaim "A1" Nothing (Equals $ Lit "C"))
        (Var $ ParsedClaim "A2" Nothing (Equals $ Lit "C"))))
      , ("DD", (And
        (Var $ ParsedClaim "A1" Nothing (Equals $ Lit "D"))
        (Var $ ParsedClaim "A2" Nothing (Equals $ Lit "D"))))
      , ("DC", (And
        (Var $ ParsedClaim "A1" Nothing (Equals $ Lit "D"))
        (Var $ ParsedClaim "A2" Nothing (Equals $ Lit "C")))) ])
    verifyParserFails codeMapParser sample3
    verifyParserFails codeMapParser sample4

compileCode :: MonadCompile m => Code -> m (ModalProgram Value CompiledClaim)
compileCode (Code frags) = do
  prog <- foldM (\f c -> (f .) <$> compileCodeFragment c) id frags
  dflt <- defaultAction
  return $ prog (F.Val . (dflt ==))
compileCode (ActionMap a2smap) = do
  let a2slist = Map.toList a2smap
  formulas <- mapM (compileStatement compileClaim . snd) a2slist
  let a2flist = zip (map fst a2slist) formulas
  return $ \a -> let Just f = List.lookup a a2flist in f

-- Note: Code not dead; just not yet used.
actionsMentioned :: Code -> [Value]
actionsMentioned (ActionMap m) = Map.keys m
actionsMentioned (Code frags) = concatMap fragRets frags where
  fragRets (For ActionT _ range fs) = rangeLitValues range ++ concatMap fragRets fs
  fragRets (For OutcomeT _ _ fs) = concatMap fragRets fs
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
  fragRets (For ActionT _ _ fs) = concatMap fragRets fs
  fragRets (For OutcomeT _ range fs) = rangeLitValues range ++ concatMap fragRets fs
  fragRets (ForN _ _ fs) = concatMap fragRets fs
  fragRets (If _ fs) = concatMap fragRets fs
  fragRets (IfElse _ fs gs) = concatMap fragRets fs ++ concatMap fragRets gs
  fragRets (Return _) = []
  fragRets (LetN _ _) = []
  fragRets Pass = []

-- Note: Code not dead; just not yet used.
claimsMade :: Code -> [ParsedClaim]
claimsMade (ActionMap m) = concatMap claimsParsed $ Map.elems m
claimsMade (Code frags) = concatMap fragClaims frags where
  fragClaims (For _ _ _ fs) = concatMap fragClaims fs
  fragClaims (ForN _ _ fs) = concatMap fragClaims fs
  fragClaims (If s fs) = claimsParsed s ++ concatMap fragClaims fs
  fragClaims (IfElse s fs gs) =
    claimsParsed s ++ concatMap fragClaims fs ++ concatMap fragClaims gs
  fragClaims (LetN _ _) = []
  fragClaims (Return _) = []
  fragClaims Pass = []

-------------------------------------------------------------------------------

type CompiledAgent = Map Value (ModalFormula CompiledClaim)

codeToProgram :: MonadError CompileError m =>
  CompileContext -> Code -> m CompiledAgent
codeToProgram context code = do
  (prog, state) <- runStateT (compileCode code) context
  return $ Map.fromList [(a, prog a) | a <- actionList state]

-------------------------------------------------------------------------------
-- Testing

main :: IO ()
main = do
  _testRangeParser
  _testBoundedRangeParser
  _testCodeParser
  _testCodeMapParser
  putStrLn ""
