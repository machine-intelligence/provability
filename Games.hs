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

displayGame :: (Ord a, Enum a, Show a, Ord u, Enum u, Show u) =>
  ModalProgram (UA u a) a -> ModalProgram a u -> IO ()
displayGame agent univ = do
  let (action, outcome) = playGame agent univ
  printf "A=%s, U=%s\n" (show action) (show outcome)


data PD = DC | CC | DD | CD deriving (Eq, Ord, Read, Enum)
instance Show PD where
  show DC = "[D, C]"
  show CC = "[C, C]"
  show DD = "[D, D]"
  show CD = "[C, D]"
data CorD = C | D deriving (Eq, Ord, Read, Enum)
instance Show CorD where
  show C = "C"
  show D = "D"
data DorC = AltD | AltC deriving (Eq, Ord, Read, Enum)
instance Show DorC where
  show AltD = "D'"
  show AltC = "C'"

data U2 u a1 a2 = U2 u | A1 a1 | A2 a2 | Q2 String deriving (Eq, Ord, Read)
instance (Show u, Show a1, Show a2) => Show (U2 u a1 a2) where
  show (U2 u) = show u
  show (A1 a1) = show a1 ++ "₁"
  show (A2 a2) = show a2 ++ "₂"
  show (Q2 s) = show s ++ "?"

multiplayerGame :: (Ord u, Ord a1, Ord a2, Enum u, Enum a1, Enum a2) =>
  ModalProgram (Either a1 a2) u ->
  ModalProgram (UA u a1) a1 ->
  ModalProgram (UA u a2) a2 ->
  Map (U2 u a1 a2) (ModalFormula (U2 u a1 a2))
multiplayerGame univ agent1 agent2 = Map.fromList $ us ++ a1s ++ a2s where
  us = [(U2 u, mapVariable promoteToAgent $ univ u) | u <- enumerate]
  a1s = [(A1 a1, mapVariable promoteToA1 $ agent1 a1) | a1 <- enumerate]
  a2s = [(A2 a2, mapVariable promoteToA2 $ agent2 a2) | a2 <- enumerate]
  promoteToAgent (Left a) = A1 a
  promoteToAgent (Right a) = A2 a
  promoteToA1 (U u) = U2 u
  promoteToA1 (A a) = A1 a
  promoteToA1 (Query s) = Q2 s
  promoteToA2 (U u) = U2 u
  promoteToA2 (A a) = A2 a
  promoteToA2 (Query s) = Q2 s

prisonersDilemma :: ModalProgram (Either CorD CorD) PD
prisonersDilemma DC = And (Var $ Left D) (Var $ Right C)
prisonersDilemma CC = And (Var $ Left C) (Var $ Right C)
prisonersDilemma DD = And (Var $ Left D) (Var $ Right D)
prisonersDilemma CD = And (Var $ Left C) (Var $ Right D)

prisonersDilemma' :: ModalProgram (Either CorD DorC) PD
prisonersDilemma' DC = And (Var $ Left D) (Var $ Right AltC)
prisonersDilemma' CC = And (Var $ Left C) (Var $ Right AltC)
prisonersDilemma' DD = And (Var $ Left D) (Var $ Right AltD)
prisonersDilemma' CD = And (Var $ Left C) (Var $ Right AltD)


main :: IO ()
main = do
  putStrLn "In Newcomb's problem, if the predictor uses a box to predict"
  putStrLn "the agent's action, UDT takes whatever its default action was:"
  displayGame (udt 0 OneBox) (newcomb 0)
  displayGame (udt 0 TwoBox) (newcomb 0)
  putStrLn ""
  let newcombUDT0 = udt 0 TwoBox :: ModalProgram (UA NewcombOutcome OneOrTwo) OneOrTwo
  putStrLn "This is the modal formula that's true if UDT one-boxes:"
  print $ newcombUDT0 OneBox
  putStrLn "This is the modal formula that's true if UDT two-boxes:"
  print $ newcombUDT0 TwoBox
  putStrLn ""
  putStrLn "These are the modal formulas for UDT in the newcomb problem:"
  displayMap $ gameMap (udt 0 TwoBox) (newcomb 0)
