import Control.Applicative hiding ((<|>))
import Data.List
import Data.Maybe
import Data.Map.Lazy (Map, (!))
import qualified Data.Map.Lazy as M
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.String
import Text.Parsec.Token

-- Example usage:
-- findGeneralGLFixpoint $ M.fromList [("a",read "~ [] b"), ("b", read "[] (a -> [] ~ b)")]


-- Modal Logic Formula data structure
data ModalFormula = Val {value :: Bool}
                  | Var {name :: String}
                  | Neg {contents :: ModalFormula}
                  | And {left, right :: ModalFormula}
                  | Or  {left, right :: ModalFormula}
                  | Imp {left, right :: ModalFormula}
                  | Iff {left, right :: ModalFormula}
                  | Box {contents :: ModalFormula}
                  | Dia {contents :: ModalFormula}

-- Syntactic Conveniences:
infixr   4 %=
(%=) = Iff

infixr   5 %>
(%>) = Imp

infixl   6 %|
(%|) = Or

infixl   7 %^
(%^) = And

a = Var "a"
b = Var "b"
c = Var "c"
x = Var "x"
y = Var "y"
z = Var "z"

f = Val False
t = Val True

-- Data structure to be mapped across a formula.
data ModalEvaluator a = ModalEvaluator {
    handleVal :: Bool -> a ,
    handleVar :: String -> a,
    handleNeg :: a -> a,
    handleAnd :: a -> a -> a,
    handleOr  :: a -> a -> a,
    handleImp :: a -> a -> a,
    handleIff :: a -> a -> a,
    handleBox :: a -> a,
    handleDia :: a -> a}

-- And how to use it to map:
modalEval :: ModalEvaluator a -> ModalFormula -> a
modalEval m = f where
  f (Val v) = (handleVal m) v
  f (Var s) = (handleVar m) s
  f (Neg x) = (handleNeg m) (f x)
  f (And x y) = (handleAnd m) (f x) (f y)
  f (Or  x y) = (handleOr m) (f x) (f y)
  f (Imp x y) = (handleImp m) (f x) (f y)
  f (Iff x y) = (handleIff m) (f x) (f y)
  f (Box x) = (handleBox m) (f x)
  f (Dia x) = (handleDia m) (f x)

instance Show ModalFormula where
  showsPrec _ (Val l) = showString $ if l then "T" else "F"
  showsPrec _ (Var v) = showString v -- Make it uppercase?
  showsPrec p (Neg x) = showParen (p > 8) $ showString "~ " . showsPrec 8 x
  showsPrec p (And x y) = showParen (p > 7) $ showsPrec 7 x . showString " && " . showsPrec 8 y
  showsPrec p (Or  x y) = showParen (p > 6) $ showsPrec 6 x . showString " || " . showsPrec 7 y
  showsPrec p (Imp x y) = showParen (p > 5) $ showsPrec 6 x . showString " -> " . showsPrec 5 y
  showsPrec p (Iff x y) = showParen (p > 4) $ showsPrec 5 x . showString " <-> " . showsPrec 4 y
  showsPrec p (Box x) = showParen (p > 8) $ showString "[] " . showsPrec 8 x
  showsPrec p (Dia x) = showParen (p > 8) $ showString "<> " . showsPrec 8 x

--------------------------------------------------------------------------------
  
formulaParser :: Parser ModalFormula
formulaParser = buildExpressionParser table term <?> "ModalFormula"
  where
    table = [ [prefix $ choice [ (m_reservedOp "~" >> return Neg)
                               , (m_reservedOp "[]" >> return Box)
                               , (m_reservedOp "<>" >> return Dia)
                               ] ]
            , [Infix (m_reservedOp "&&" >> return And) AssocLeft]
            , [Infix (m_reservedOp "||" >> return  Or) AssocLeft]
            , [Infix (m_reservedOp "->" >> return Imp) AssocRight]
            , [Infix (m_reservedOp "<->" >> return Iff) AssocRight]
            ]
            
    term = m_parens formulaParser
           <|> (m_reserved "T" >> return (Val True))
           <|> (m_reserved "F" >> return (Val False))
           <|> fmap Var m_identifier
           
    -- To work-around Parsec's limitation for prefix operators:
    prefix  p = Prefix  . chainl1 p $ return (.)
                       
    TokenParser { parens = m_parens
                , identifier = m_identifier
                , reservedOp = m_reservedOp
                , reserved = m_reserved
                , semiSep1 = m_semiSep1
                , whiteSpace = m_whiteSpace } = 
      makeTokenParser emptyDef { commentStart = "{-"
                               , commentEnd = "-}"
                               , identStart = letter
                               , identLetter = letter
                               , opStart = oneOf "~-<>[]&|"
                               , opLetter = oneOf "~-<>[]&|"
                               , reservedOpNames = ["~", "&&", "||", "->", "<->", "[]", "<>"]
                               , reservedNames = ["T", "F"]
                               , caseSensitive = False
                               }

instance Read ModalFormula where
  readsPrec _ s = case parse (formulaParser <* eof) "" s of
    Right result -> [(result,"")]
    -- We could just return the remaining string, but Parsec gives
    -- much nicer errors. So we ask it to consume the whole input and
    -- fail if it fails.
    Left err -> error $ show err
  
--------------------------------------------------------------------------------

-- Nesting Depth of Modal Operators
maxModalDepthHandler :: ModalEvaluator Int
maxModalDepthHandler = ModalEvaluator {
    handleVal = const 0, handleVar = const 0,
    handleNeg = id,
    handleAnd = max, handleOr = max, handleImp = max, handleIff = max,
    handleBox = (1+), handleDia = (1+)}
maxModalDepth :: ModalFormula -> Int
maxModalDepth = modalEval maxModalDepthHandler

-- Propositional evaluation of the modal formula

propositionalEvalHandler :: ModalEvaluator (Maybe Bool)
propositionalEvalHandler = ModalEvaluator {
    handleVal = Just,
    handleVar = const Nothing,
    handleNeg = fmap not,
    handleAnd = liftA2 (&&),
    handleOr  = liftA2 (||),
    handleImp = liftA2 (<=),
    handleIff = liftA2 (==),
    handleBox = const Nothing,
    handleDia = const Nothing}

propositionalEval :: ModalFormula -> Maybe Bool
propositionalEval = modalEval propositionalEvalHandler 

-- Evaluate the modal formula assuming the soundness of the system

evalWithSoundnessHandler :: ModalEvaluator (Maybe Bool)
evalWithSoundnessHandler = ModalEvaluator {
    handleVal = Just,
    handleVar = const Nothing,
    handleNeg = fmap not,
    handleAnd = liftA2 (&&),
    handleOr  = liftA2 (||),
    handleImp = liftA2 (<=),
    handleIff = liftA2 (==),
    handleBox = (\x -> if x == Just False then Just False else Nothing),
    handleDia = (\x -> if x == Just True then Just True else Nothing)}

evalWithSoundness :: ModalFormula -> Maybe Bool
evalWithSoundness = modalEval evalWithSoundnessHandler

-- How to simplify modal formulas:
mapFormulaOutput :: (Bool -> Bool) -> ModalFormula -> ModalFormula
mapFormulaOutput f formula = g (f False) (f True) 
  where
    g True True = (Val True)
    g False False = (Val False)
    g False True = formula
    g True False = (Neg formula)

simplifyBinaryOperator :: (ModalFormula -> ModalFormula -> ModalFormula) ->
                          (Bool -> Bool -> Bool) ->
                          ModalFormula -> ModalFormula ->
                          ModalFormula
simplifyBinaryOperator op behavior (Val a) (Val b) = Val (behavior a b)
simplifyBinaryOperator op behavior (Val a) formula =
  mapFormulaOutput (\b -> behavior a b) formula
simplifyBinaryOperator op behavior formula (Val b) =
  mapFormulaOutput (\a -> behavior a b) formula
simplifyBinaryOperator op behavior f1 f2 = op f1 f2

simplifyNeg :: ModalFormula -> ModalFormula
simplifyNeg (Val v) = (Val (not v))
simplifyNeg (Neg x) = x
simplifyNeg x = (Neg x)

simplifyBox :: ModalFormula -> ModalFormula
simplifyBox t@(Val True) = t
simplifyBox x = (Box x)

simplifyDia :: ModalFormula -> ModalFormula
simplifyDia f@(Val False) = f
simplifyDia x = (Dia x)


simplifyHandler :: ModalEvaluator ModalFormula
simplifyHandler =  ModalEvaluator {
    handleVal = Val,
    handleVar = Var,
    handleNeg = simplifyNeg,
    handleAnd = simplifyBinaryOperator And (&&),
    handleOr  = simplifyBinaryOperator Or (||),
    handleImp = simplifyBinaryOperator Imp (<=),
    handleIff = simplifyBinaryOperator Iff (==),
    handleBox = simplifyBox,
    handleDia = simplifyDia}

simplify :: ModalFormula -> ModalFormula
simplify = modalEval simplifyHandler

-- GL Eval in standard model
glEvalHandler :: ModalEvaluator [Bool]
glEvalHandler = ModalEvaluator {
    handleVal = repeat,
    handleVar = error "Variables are not supported in GLEval.",
    handleNeg = fmap not,
    handleAnd = zipWith (&&),
    handleOr  = zipWith (||),
    handleImp = zipWith (<=),
    handleIff = zipWith (==),
    handleBox = scanl (&&) True,
    handleDia = scanl (||) False}

glEval :: ModalFormula -> [Bool]
glEval = modalEval glEvalHandler 

glEvalStandard :: ModalFormula -> Bool
glEvalStandard formula = (glEval formula) !! (maxModalDepth formula)

simplifiedMaxDepth :: ModalFormula -> Int
simplifiedMaxDepth formula = 
  depth - (length $ (!!0) $ group $ reverse results) + 1 where
    results = take (depth+1) (glEval formula)
    depth = maxModalDepth formula

fixpointGLEval :: String -> ModalFormula -> [Bool]
fixpointGLEval var fi = result
  where
    evalHandler = ModalEvaluator {
      handleVal = repeat,
      handleVar = \var' -> if var == var' then result else error "Variable other than the fixpoint in fixpointGLEval",
      handleNeg = fmap not,
      handleAnd = zipWith (&&),
      handleOr  = zipWith (||),
      handleImp = zipWith (<=),
      handleIff = zipWith (==),
      handleBox = scanl (&&) True,
      handleDia = scanl (||) False
      }
    result = modalEval evalHandler fi

generalFixpointGLEval :: Map String ModalFormula -> Map String [Bool]
generalFixpointGLEval formulaMap = evalMap
  where
    evalMap = M.map (modalEval evalHandler) formulaMap
    evalHandler = ModalEvaluator {
      handleVal = repeat,
      handleVar = (\var -> case M.lookup var evalMap of
        Just l -> l
        Nothing -> error "Unmapped variable in generalFixpointGLEval"),
      handleNeg = fmap not,
      handleAnd = zipWith (&&),
      handleOr  = zipWith (||),
      handleImp = zipWith (<=),
      handleIff = zipWith (==),
      handleBox = scanl (&&) True,
      handleDia = scanl (||) False
      }

-- Finding the fixedpoints

-- Check whether the length of a list is at least n without infinite looping.
lengthAtLeast :: Int -> [a] -> Bool
lengthAtLeast 0 _ = True
lengthAtLeast _ [] = False
lengthAtLeast n (x:xs) = lengthAtLeast (n-1) xs

-- Find the fixpoint of a list, given a length of run after which we should conclude we found it.
findFixpoint :: (Eq a) => Int -> [a] -> a
findFixpoint n xs = (!!0) $ fromJust $ find (lengthAtLeast n) $ group xs


-- Find the Fixpoint for a Modal formula
findGLFixpoint :: String -> ModalFormula -> Bool
findGLFixpoint var formula = findFixpoint (1+(maxModalDepth formula)) (fixpointGLEval var formula)

-- Find the Fixpoint for a collection of Modal formulas
findGeneralGLFixpoint :: Map String ModalFormula -> Map String Bool
findGeneralGLFixpoint formulaMap = findFixpoint (1+maxFormulaDepth) (map level [0..]) where
  level n = M.map (!!n) result
  result = generalFixpointGLEval formulaMap
  maxFormulaDepth = maximum $ map maxModalDepth $ M.elems formulaMap
