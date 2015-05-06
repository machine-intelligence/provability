module Games where
import Display
import Modal
import Programs
import Data.Map hiding (map)
import qualified Data.Map as Map
import Text.Printf (printf)

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

onebox, twobox :: ModalFormula OneOrTwo
onebox = Var OneBox
twobox = Neg onebox

newcomb :: Int -> ModalProgram OneOrTwo NewcombOutcome
newcomb k MillionThousand = twobox %^      boxk k onebox
newcomb k Million         = onebox %^      boxk k onebox
newcomb k Thousand        = twobox %^ Neg (boxk k onebox)
newcomb k Naught          = onebox %^ Neg (boxk k onebox)


data AorB = A_| B_ deriving (Eq, Ord, Read, Enum)
instance Show AorB where
  show A_ = "A"
  show B_ = "B"
data GoodOrBad = Good | Bad deriving (Eq, Ord, Show, Read, Enum)

doesA, doesB :: ModalFormula AorB
doesA = Var A_
doesB = Neg doesA

aGame :: Int -> ModalProgram AorB GoodOrBad
aGame k Good = boxk k doesA
aGame k Bad  = Neg (boxk k doesA)

bGame :: Int -> ModalProgram AorB GoodOrBad
bGame k Good = boxk k doesB
bGame k Bad  = Neg (boxk k doesB)

testAgent :: ModalProgram AorB GoodOrBad -> ModalProgram AorB AorB
testAgent univ A_ = Box $ Var A_ %> univ Good
testAgent univ B_ = Neg $ Box $ Var A_ %> univ Good


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
pdGameMap = u2GameMap prisonersDilemma udtA udtB where
  udtA = udt' [DC, CC, DD, CD] [D, C] D
  udtB = udt' [CD, CC, DD, DC] [D, C] D


main :: IO ()
main = do
  putStrLn "In Newcomb's problem, if the predictor uses a box to predict"
  putStrLn "the agent's action, UDT takes whatever its default action was:"
  displayU1 (newcomb 0) (udt OneBox)
  displayU1 (newcomb 0) (udt TwoBox)
  putStrLn ""
  let newcombUDT0 = udt TwoBox :: ModalProgram (U1 NewcombOutcome OneOrTwo) OneOrTwo
  putStrLn "These are the modal formulas true of UDT in Newcomb's problem:"
  displayAgent newcombUDT0
  putStrLn "These are the modal formulas for UDT in the newcomb problem:"
  displayMap $ u1GameMap (newcomb 0) (udt TwoBox)
