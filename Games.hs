module Games where
import Modal
import Programs
import Data.Map hiding (map)
import Text.Printf (printf)

data FiveOrTen = Ten | Five deriving (Eq, Ord, Read, Enum)
instance Show FiveOrTen where
  show Ten  = "10"
  show Five = "5"

fiveAndTen :: ModalProgram FiveOrTen FiveOrTen
fiveAndTen Five = Var Five
fiveAndTen Ten = Var Ten


data NewcombAction = OneBox | TwoBox deriving (Eq, Ord, Read, Enum)
instance Show NewcombAction where
  show OneBox = "1"
  show TwoBox = "2"

data NewcombOutcome = MillionThousand | Million | Thousand | Naught
  deriving (Eq, Ord, Read, Enum)
instance Show NewcombOutcome where
  show MillionThousand = "$1001000"
  show Million         = "$1000000"
  show Thousand        = "$1000"
  show Naught          = "$0"

onebox, twobox :: ModalFormula NewcombAction
onebox = Var OneBox
twobox = Neg onebox

newcomb :: Int -> ModalProgram NewcombAction NewcombOutcome
newcomb k MillionThousand = twobox %^      boxk k onebox
newcomb k Million         = onebox %^      boxk k onebox
newcomb k Thousand        = twobox %^ Neg (boxk k onebox)
newcomb k Naught          = onebox %^ Neg (boxk k onebox)


data AorB = A | B deriving (Eq, Ord, Show, Read, Enum)
data GoodOrBad = Good | Bad deriving (Eq, Ord, Show, Read, Enum)

doesA, doesB :: ModalFormula AorB
doesA = Var A
doesB = Neg doesA

aGame :: Int -> ModalProgram AorB GoodOrBad
aGame k Good = boxk k doesA
aGame k Bad  = Neg (boxk k doesA)

bGame :: Int -> ModalProgram AorB GoodOrBad
bGame k Good = boxk k doesB
bGame k Bad  = Neg (boxk k doesB)


data Strangeverse = Three | Two | One deriving (Eq, Ord, Read, Enum)
instance Show Strangeverse where
  show Three = "3"
  show Two   = "2"
  show One   = "1"
data Strangeact = Alpha | Beta deriving (Eq, Ord, Read, Enum)
instance Show Strangeact where
  show Alpha = "α"
  show Beta  = "β"

doesAlpha, doesBeta :: ModalFormula Strangeact
doesAlpha = Var Alpha
doesBeta  = Neg doesAlpha

strangeverse :: Int -> ModalProgram Strangeact Strangeverse
strangeverse k Three  = doesAlpha %^ boxk k doesBeta
strangeverse _ Two = doesBeta
strangeverse k One = doesAlpha %^ Neg (boxk k doesBeta)

displayGame :: (Enum a, Ord a, Show a) => (a -> ModalProgram a a) -> IO ()
displayGame prog = mapM_ display enumerate where
  display dflt = printf "Default=%s → Action=%s\n" (show dflt) (show action) where
    action = evalProgram $ prog dflt

main :: IO ()
main = do
  print $ evalUDT 0 fiveAndTen Five
  putStrLn ""
  putStrLn "In Newcomb's problem, if the predictor uses a box to predict"
  putStrLn "the agent's action, UDT takes whatever its default action was:"
  print $ evalUDT 0 (newcomb 0) OneBox
  print $ evalUDT 0 (newcomb 0) TwoBox
  putStrLn ""
  putStrLn "This is the modal formula that's true if UDT one-boxes:"
  print $ udt 0 (newcomb 0) OneBox OneBox
  putStrLn ""
  putStrLn "These are the modal formulas for UDT in the newcomb problem:"
  print $ progToMap $ udt 0 (newcomb 0) OneBox
  where evalUDT level univ = evalProgram . udt level univ
