module Modal.Games where
import Data.Map hiding (map)
import Modal.Display
import Modal.Formulas
import Modal.GameTools
import Modal.Programming
import Modal.Programs

data FiveOrTen = Ten | Five deriving (Eq, Ord, Read, Enum)
instance Show FiveOrTen where
  show Ten  = "10"
  show Five = "5"

fiveAndTen :: ModalProgram FiveOrTen FiveOrTen
fiveAndTen = ModalProgram game where
  game Five = Var Five
  game Ten = Var Ten


data OneOrTwo = OneBox | TwoBox deriving (Eq, Ord, Read, Enum)
instance Show OneOrTwo where
  show OneBox = "1"
  show TwoBox = "2"

data NewcombOutcome = MillionThousand | Million | Thousand | Naught
  deriving (Eq, Ord, Read, Enum)
instance Show NewcombOutcome where
  show MillionThousand = "$1001000"
  show Million         = "$1000000"
  show Thousand        = "$1000"
  show Naught          = "$0"

oneboxes, twoboxes :: ModalFormula OneOrTwo
oneboxes = Var OneBox
twoboxes = Neg oneboxes

newcomb :: Int -> ModalProgram NewcombOutcome OneOrTwo
newcomb k = ModalProgram game where
  game MillionThousand = twoboxes %^      boxk k oneboxes
  game Million         = oneboxes %^      boxk k oneboxes
  game Thousand        = twoboxes %^ Neg (boxk k oneboxes)
  game Naught          = oneboxes %^ Neg (boxk k oneboxes)


data AorB = A| B deriving (Eq, Ord, Read, Enum)
instance Show AorB where
  show A = "A"
  show B = "B"
data GoodOrBad = Good | Bad deriving (Eq, Ord, Show, Read, Enum)

doesA, doesB :: ModalFormula AorB
doesA = Var A
doesB = Neg doesA

aGame :: Int -> ModalProgram GoodOrBad AorB
aGame k = ModalProgram game where
  game Good = boxk k doesA
  game Bad  = Neg (boxk k doesA)

bGame :: Int -> ModalProgram GoodOrBad AorB
bGame k = ModalProgram game where
  game Good = boxk k doesB
  game Bad  = Neg (boxk k doesB)

abAgent :: ModalProgram GoodOrBad AorB -> ModalProgram AorB AorB
abAgent univ = ModalProgram f where
  f A = Box $ Var A %> formulaFor univ Good
  f B = Neg $ Box $ Var A %> formulaFor univ Good


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

strangeverse :: Int -> ModalProgram Strangeverse Strangeact
strangeverse k = ModalProgram game where
  game Three  = doesAlpha %^ boxk k doesBeta
  game Two = doesBeta
  game One = doesAlpha %^ Neg (boxk k doesBeta)


data PD = DC | CC | DD | CD deriving (Eq, Ord, Read, Enum)
instance Show PD where
  show DC = "[D₁C₂]"
  show CC = "[C₁C₂]"
  show DD = "[D₁D₁]"
  show CD = "[C₁D₂]"
data CorD = C | D deriving (Eq, Ord, Read, Enum)
instance Show CorD where
  show C = "C"
  show D = "D"

prisonersDilemma :: ModalProgram PD (Either CorD CorD)
prisonersDilemma = ModalProgram game where
  game DC = And (Var $ Left D) (Var $ Right C)
  game CC = And (Var $ Left C) (Var $ Right C)
  game DD = And (Var $ Left D) (Var $ Right D)
  game CD = And (Var $ Left C) (Var $ Right D)

pdGameMap :: Map (U2 PD CorD CorD) (ModalFormula (U2 PD CorD CorD))
pdGameMap = gameMap2 prisonersDilemma udtA udtB where
  udtA = udt' [DC, CC, DD, CD] [D, C] D
  udtB = udt' [CD, CC, DD, DC] [D, C] D


main :: IO ()
main = do
  putStrLn "In Newcomb's problem, if the predictor uses a box to predict"
  putStrLn "the agent's action, UDT takes whatever its default action was:"
  displayGame (newcomb 0) (udt OneBox)
  displayGame (newcomb 0) (udt TwoBox)
  putStrLn ""
  putStrLn "These are the modal formulas for UDT in the newcomb problem:"
  displayMap $ gameMap (newcomb 0) (udt TwoBox)
  putStrLn ""
  putStrLn "Time for the five and ten game!"
  displayGame fiveAndTen (udt Five)
  putStrLn ""
  putStrLn "These are the modal formulas for UDT in the 5-and-10 game:"
  displayMap $ gameMap fiveAndTen (udt Five)
