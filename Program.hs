import Modal
import Data.Map hiding (map)
import Data.Maybe (fromJust)
import Data.List (find)

type ModalProgram v a = a -> ModalFormula v
data ProgFrag v a = ProgFrag (ModalProgram v a -> ModalProgram v a)

enumerate :: Enum a => [a]
enumerate = enumFrom (toEnum 0)

progToList :: Enum a => ModalProgram v a -> [ModalFormula v]
progToList f = map f enumerate

modalProgram :: (Enum a,Eq a) => a -> ProgFrag v a -> ModalProgram v a
modalProgram dflt (ProgFrag f) = f $ \a -> Val (a == dflt)


mReturn :: Eq a => a -> ProgFrag v a
mReturn a = ProgFrag $ const $ \a' -> Val (a == a')

mPass :: ProgFrag v a
mPass = ProgFrag id

mIf' :: ModalFormula v -> ProgFrag v a -> ProgFrag v a -> ProgFrag v a
mIf' cond (ProgFrag t) (ProgFrag e) = ProgFrag $ \prog a ->
  And (Imp cond       (t prog a))
      (Imp (Neg cond) (e prog a))

mIf :: ModalFormula v -> ProgFrag v a -> ProgFrag v a
mIf cond t = mIf' cond t mPass

(>->) :: ProgFrag v a -> ProgFrag v a -> ProgFrag v a
ProgFrag f >-> ProgFrag g = ProgFrag (f . g)

mFor' :: [c] -> (c -> ProgFrag v a) -> ProgFrag v a
mFor' []     _ = mPass
mFor' (c:cs) f = f c >-> mFor' cs f

mFor :: Enum c => (c -> ProgFrag v a) -> ProgFrag v a
mFor = mFor' enumerate


evalProgram :: (Ord a,Show a,Read a,Enum a) => ModalProgram a a -> a
evalProgram prog = fst $ fromJust $ find snd $ Data.Map.toList $
  findGeneralGLFixpoint $ Data.Map.fromList $
    flip map enumerate $ \a -> (a, prog a)


udt :: (Enum a,Ord b,Show b,Enum b)
    => Int -> ModalProgram b a -> b -> ModalProgram b b
udt level univ dflt = modalProgram dflt $
  mFor $ \a ->
    mFor $ \b ->
      mIf (boxk level (Var b %> univ a)) (mReturn b)

evalUDT :: (Enum a,Ord b,Show b,Read b,Enum b)
        => Int -> ModalProgram b a -> b -> b
evalUDT level univ dflt = evalProgram $ udt level univ dflt


data FiveOrTen = Ten | Five deriving (Eq,Ord,Show,Read,Enum)

fiveAndTen :: ModalProgram FiveOrTen FiveOrTen
fiveAndTen Five = Var Five
fiveAndTen Ten = Var Ten


data NewcombAction = OneBox | TwoBox deriving (Eq,Ord,Show,Read,Enum)
data NewcombOutcome = MillionThousand | Million | Thousand | Naught
  deriving (Eq,Ord,Show,Read,Enum)

onebox = Var OneBox
twobox = Neg onebox

newcomb :: Int -> ModalProgram NewcombAction NewcombOutcome
newcomb k MillionThousand = twobox %^      boxk k onebox
newcomb k Million         = onebox %^      boxk k onebox
newcomb k Thousand        = twobox %^ Neg (boxk k onebox)
newcomb k Naught          = onebox %^ Neg (boxk k onebox)


main = do
  print $ evalUDT 0 fiveAndTen Five
  print $ evalUDT 0 (newcomb 0) OneBox
  print $ udt 0 (newcomb 0) OneBox OneBox
