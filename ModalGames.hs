module ModalGames where
import Data.Map hiding (map)
import Display
import ModalFormulas
import ModalGameTools
import ModalPrograms

data FiveOrTen = Ten | Five deriving (Eq, Ord, Read, Enum)
instance Show FiveOrTen where
  show Ten  = "10"
  show Five = "5"

fiveAndTen :: ModalProgram FiveOrTen FiveOrTen
fiveAndTen Five = Var Five
fiveAndTen Ten = Var Ten


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

newcomb :: Int -> ModalProgram OneOrTwo NewcombOutcome
newcomb k MillionThousand = twoboxes %^      boxk k oneboxes
newcomb k Million         = oneboxes %^      boxk k oneboxes
newcomb k Thousand        = twoboxes %^ Neg (boxk k oneboxes)
newcomb k Naught          = oneboxes %^ Neg (boxk k oneboxes)


data AorB = A| B deriving (Eq, Ord, Read, Enum)
instance Show AorB where
  show A = "A"
  show B = "B"
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

abAgent :: ModalProgram AorB GoodOrBad -> ModalProgram AorB AorB
abAgent univ A = Box $ Var A %> univ Good
abAgent univ B = Neg $ Box $ Var A %> univ Good


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

prisonersDilemma :: ModalProgram (Either CorD CorD) PD
prisonersDilemma DC = And (Var $ Left D) (Var $ Right C)
prisonersDilemma CC = And (Var $ Left C) (Var $ Right C)
prisonersDilemma DD = And (Var $ Left D) (Var $ Right D)
prisonersDilemma CD = And (Var $ Left C) (Var $ Right D)

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
