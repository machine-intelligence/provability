import Control.Applicative

-- Modal Logic Formula data structure
data ModalFormula = Val {value :: Bool}
                  | Var {name :: String}
                  | Neg {contents :: ModalFormula}
                  | And {left, right :: ModalFormula}
                  | Or {left, right :: ModalFormula}
                  | Imp {left, right :: ModalFormula}
                  | Box {contents :: ModalFormula}
                  | Dia {contents :: ModalFormula}

-- Syntactic Conveniences:
infixr   6 %>
(%>) = Imp

infixr   7 %|
(%|) = Or

infixr   8 %^
(%^) = And

neg = Neg
x = Var "x"
y = Var "y"
z = Var "z"

-- Data structure to be mapped across a formula.
data ModalEvaluator a = ModalEvaluator {
    handleVal :: Bool -> a ,
    handleVar :: String -> a,
    handleNeg :: a -> a,
    handleAnd :: a -> a -> a,
    handleOr :: a -> a -> a,
    handleImp :: a -> a -> a,
    handleBox :: a -> a,
    handleDia :: a -> a}

-- And how to use it to map:
modalEval :: ModalEvaluator a -> ModalFormula -> a
modalEval m = f where
  f (Val v) = (handleVal m) v
  f (Var s) = (handleVar m) s
  f (Neg x) = (handleNeg m) (f x)
  f (And x y) = (handleAnd m) (f x) (f y)
  f (Or x y) = (handleOr m) (f x) (f y)
  f (Imp x y) = (handleImp m) (f x) (f y)
  f (Box x) = (handleBox m) (f x)
  f (Dia x) = (handleDia m) (f x)


-- Pretty Printing
modalFormulaPrettyPrinter :: ModalEvaluator String
modalFormulaPrettyPrinter = ModalEvaluator {
    handleVal = (\v -> if v then "T" else "F"),
    handleVar = id,
    handleNeg = (\x -> "(Neg "++x++")"),
    handleAnd = (\x y -> "("++x++" %^ "++y++")"),
    handleOr = (\x y -> "("++x++" %| "++y++")"),
    handleImp = (\x y -> "("++x++" %> "++y++")"),
    handleBox = (\x -> "(Box "++ x ++ ")"),
    handleDia = (\x -> "(Dia "++x++")")}
instance Show ModalFormula where
  show = modalEval modalFormulaPrettyPrinter
 
-- Propositional evaluation of the modal formula

propositionalEvalHandler = ModalEvaluator {
    handleVal = Just,
    handleVar = const Nothing,
    handleNeg = fmap not,
    handleAnd = liftA2 (&&),
    handleOr = liftA2 (||),
    handleImp = liftA2 (<=),
    handleBox = const Nothing,
    handleDia = const Nothing}

propositionalEval = modalEval propositionalEvalHandler 

-- Evaluate the modal formula assuming the soundness of the system
evalWithSoundnessHandler :: ModalEvaluator (Maybe Bool)

evalWithSoundnessHandler = ModalEvaluator {
    handleVal = Just,
    handleVar = const Nothing,
    handleNeg = fmap not,
    handleAnd = liftA2 (&&),
    handleOr = liftA2 (||),
    handleImp = liftA2 (<=),
    handleBox = (\x -> if x == Just False then Just False else Nothing),
    handleDia = (\x -> if x == Just True then Just True else Nothing)}

evalWithSoundness :: ModalFormula -> Maybe Bool
evalWithSoundness = modalEval evalWithSoundnessHandler

-- How to simplify modal formulas:
mapFormulaOutput f formula =
  g (f False) (f True) where
    g True True = (Val True)
    g False False = (Val False)
    g False True = formula
    g True False = (Neg formula)

simplifyBinaryOperator op behavior (Val a) (Val b) = Val (behavior a b)
simplifyBinaryOperator op behavior (Val a) formula =
  mapFormulaOutput (\b -> behavior a b) formula
simplifyBinaryOperator op behavior formula (Val b) =
  mapFormulaOutput (\a -> behavior a b) formula
simplifyBinaryOperator op behavior f1 f2 = op f1 f2


simplifyNeg (Val v) = (Val (not v))
simplifyNeg (Neg x) = x
simplifyNeg x = (Neg x)

simplifyBox t@(Val True) = t
simplifyBox x = (Box x)
simplifyDia f@(Val False) = f
simplifyDia x = (Dia x)


simplifyHandler :: ModalEvaluator ModalFormula
simplifyHandler =  ModalEvaluator {
    handleVal = Val,
    handleVar = Var,
    handleNeg = simplifyNeg,
    handleAnd = simplifyBinaryOperator And (&&),
    handleOr = simplifyBinaryOperator Or (||),
    handleImp = simplifyBinaryOperator Imp (<=),
    handleBox = simplifyBox,
    handleDia = simplifyDia}

simplify :: ModalFormula -> ModalFormula
simplify = modalEval simplifyHandler
