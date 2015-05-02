module Agents where
import Control.Applicative hiding ((<|>))
import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as M
import Display
import Modal
import Text.Printf (printf)

-- AgentVar is stringly typed, which is kind of annoying, but this
-- string-typing runs deep. Basically, we want to give ModalAgent an
-- "environment" type (and, ideally, enforce that that environment only
-- contains modal agents of lower rank) and do some shennanegans to ensure that
-- we can only specify modal formulas that refer to modal agents of lesser
-- rank. But that's hard (especially without dependent types), so we bite the
-- bullet and resort to strings.
data AgentVar = Me | Them | Agent String deriving (Eq, Ord)
instance Show AgentVar where
  show Me = "a"
  show Them = "b"
  show (Agent str) = str
instance Read AgentVar where
  readsPrec _ str = [(from name, rest) | not $ null name] where
      name = takeWhile (`elem` '_' : ['a' .. 'z']) str
      rest = dropWhile (`elem` '_' : ['a' .. 'z']) str
      from "a" = Me
      from "b" = Them
      from str = Agent str

data ModalAgent = MA { agentName :: String,
                       agentFormula :: ModalFormula AgentVar,
                       agentEvals :: Map String ModalAgent }
                  deriving (Eq, Show)

-- Bots
-- A bot is represented as a modal formula in which:
--  - The box represents provability
--  - The variable "a" represents whether this bot cooperates against its opponent
--  - The variable "b" represents whether the opponent cooperates with us.

-- Some Bots:

-- isLegalBot: Make sure all variables are inside modal operators.
isLegalBot :: ModalFormula v -> Bool
isLegalBot = modalEval ModalEvaluator {
  handleVar = const False,
  handleVal = const True,
  handleNeg = id,
  handleAnd = (&&), handleOr = (&&), handleImp = (&&), handleIff = (&&),
  handleBox = const True, handleDia = const True}

simpleAgent :: ModalFormula AgentVar -> ModalAgent
simpleAgent formula = MA ("AGENT(" ++ show formula ++ ")") formula M.empty

simpleNamedAgent :: String -> ModalFormula AgentVar -> ModalAgent
simpleNamedAgent name formula = MA name formula M.empty

coopBot = simpleNamedAgent "coop" tt
defectBot = simpleNamedAgent "dbot" ff
fairBot = simpleNamedAgent "fair" $ read "[] b"
fairBot1 = simpleNamedAgent "fair1" $ read "[1] b"
fairBot1' = simpleNamedAgent "fair1'" $ read "[] ([] F -> b)"
fairBot2 = simpleNamedAgent "fair2" $ read "[2] b"
fairBot3 = simpleNamedAgent "fair3" $ read "[3] b"
fairBot4 = simpleNamedAgent "fair4" $ read "[4] b"
fairBot5 = simpleNamedAgent "fair5" $ read "[5] b"
toughButFairBot = simpleNamedAgent "tbfair" $ read "[] b || (<> b && [1] b) || (<> b && <1> b && [2] b)"
reverseFairBot = simpleNamedAgent "rfair" $ read "(~ [] ~ b) && [] b"
magicBot = simpleNamedAgent "magic" $ read "[1]([] a -> b)"
waitBot = simpleNamedAgent "wait" $ read "~ [] F && [1] b "
waitBot2 = simpleNamedAgent "wait2" $ read "~ ([] a) && ([] ~a || [1] b)"
almostMagicBot = simpleNamedAgent "amb" $ read "~ [1]([] ~ a -> b) && [2] (~ [1]([] ~ a -> b) -> b)"
simpleMagicBot = simpleNamedAgent "smagic" $ read "[] (<> a -> b)" -- Behaves exactly like magicBot
indignationBot = simpleNamedAgent "indignant" $ read "~ ([] (a -> ~ b))"

prudentBot = MA "pbot" (read "[1] ~ dbot && []b") (M.fromList [("dbot", defectBot)])
niceBot = MA "nice" (read "[] coop") (M.fromList [("coop", coopBot)])
justBot = MA "just" (read "[] fair") (M.fromList [("fair", fairBot)])
trollBot = MA "troll" (read "[] dbot") (M.fromList [("dbot", defectBot)])


layeredBot :: String -> ModalFormula AgentVar -> Int -> ModalAgent
layeredBot name base n = MA (name ++ show n) (thebot n) M.empty
  where
    cond k = Neg (boxk k base) `And` Neg (boxk k (Neg base))

    level 0 = Box base
    level k = foldl1 And (map cond [0..k-1]) `And` boxk k base

    thebot k = foldl1 Or (map level [0..k])

toughButFairBotN = layeredBot "tbfair" (read "b")

layeredCheckBot n = (layeredBot "check" (read "~ dbot && b") n) {
  agentEvals = M.fromList [("dbot", defectBot)] }

loopBreakDBot :: ModalFormula AgentVar -> ModalFormula AgentVar ->
                 Int -> ModalFormula AgentVar -> ModalFormula AgentVar
loopBreakDBot fbreak fdefect x cont = breakOut x `And` cont
  where
    cond n = foldl1 And $ map (\k -> Neg (boxk k fbreak) `And` Neg (boxk k fdefect)) [0..n]

    breakOut 0 = Box fbreak
    breakOut n = breakOut (n-1) `Or` (cond (n-1) `And` boxk n fbreak)

masqueBot n = MA ("masque" ++ show n) masque agentEvals
  where
    agentEvals = M.fromList [("dbot", defectBot), ("tbf", toughButFairBot)]
    masque = loopBreakDBot (read "~ dbot") (read "dbot") n $
             loopBreakDBot (read "tbf") (read "~tbf") n $
             foldl1 Or (map (\k -> boxk k (read "b")) [0..n])

-- Working version of CheckBot, created by hand by constructing
-- possible cooperation matrices for successive Kripke levels. And
-- then simplified repeatedly till it looked exactly like Check bot
-- should look like.
--
-- Increasing the number in the second "box" makes it cooperate with
-- higher and higher levels of fair bots. Generally, the number in the
-- second box should be at least 1 higher than the one in the first
-- bot.
checkBot = MA "check" f (M.fromList [("dbot", defectBot)])
  where
    f = read "[] b && [1] ~ dbot"

-- all the bots
unaryCombinations :: [[a]] -> (a -> a) -> [[a]]
unaryCombinations lists f = map (map f) lists

binaryCombinations :: [[a]] -> (a -> a -> a) -> [[a]]
binaryCombinations lists f = map level [1..] where
  level n = let r = take n lists in concat $ zipWith (liftA2 f) r (reverse r)

allFormulasTiered :: [v] -> [[ModalFormula v]]
allFormulasTiered names = formulas where
  formulas = atoms : compounds
  atoms = map Var names -- we don't include true and false because they bloat the space without adding expressive power
  a1 = [Neg, Box, Dia] -- arity 1 connectors
  a2 = [And, Or, Imp, Iff] -- arity 2 connectors
  compounds = merge (map (unaryCombinations formulas) a1 ++ map (binaryCombinations formulas) a2)
  merge :: [[[a]]] -> [[a]]
  merge = foldl (zipWith (++)) (repeat [])

allFormulas :: [v] -> [ModalFormula v]
allFormulas = concat . allFormulasTiered

allBots :: [ModalFormula AgentVar]
allBots = filter isLegalBot (allFormulas [Me, Them])

-- How bots compete:
flipBot :: ModalFormula AgentVar -> ModalFormula AgentVar
flipBot = mapVariable (\s -> if s == Me then Them else (if s == Them then Me else s))

vs, dot :: String -> String -> String
x `vs` y = x ++ "(" ++ y ++ ")"
x `dot` y = x ++ "." ++ y

competition :: ModalAgent -> ModalAgent -> Map AgentVar (ModalFormula AgentVar)
competition a1@(MA n1 f1 vs1) a2@(MA n2 f2 vs2)
  | n1 == n2 && a1 /= a2 = competition a1{agentName=n1 ++ "1"} a2{agentName=n2 ++ "2"}
  | otherwise = top `M.union` left `M.union` right
  where
    top = M.fromList [
      (Agent $ n1 `vs` n2, makeNamesExplicit n1 n2 f1),
      (Agent $ n2 `vs` n1, makeNamesExplicit n2 n1 f2)]
    left = M.unions [ competition a2 ax{agentName=n1 `dot` nx} | (nx, ax) <- M.toList vs1]
    right = M.unions [competition a1 ax{agentName=n2 `dot` nx} | (nx, ax) <- M.toList vs2]
    makeNamesExplicit myName theirName = mapVariable expandName
      where
        expandName Me = Agent $ myName `vs` theirName
        expandName Them = Agent $ theirName `vs` myName
        expandName (Agent x) = Agent $ theirName `vs` (myName `dot` x)

compete :: ModalAgent -> ModalAgent -> (Bool, Bool)
compete agent1 agent2 = simplifyOutput $ findGeneralGLFixpoint $ competition agent1 agent2
  where
    n1v2 = Agent $ agentName agent1 `vs` agentName agent2
    n2v1 = Agent $ agentName agent2 `vs` agentName agent1
    simplifyOutput map = (map ! n1v2, map ! n2v1)

simpleCompete :: ModalFormula AgentVar -> ModalFormula AgentVar -> (Bool, Bool)
simpleCompete f1 f2 = compete (simpleAgent f1) (simpleAgent f2)

describeGame :: ModalAgent -> ModalAgent -> IO ()
describeGame agent1 agent2 = do
  let formulaMap = competition agent1 agent2
  printf "%s vs %s\n\n" (agentName agent1) (agentName agent2)
  displayMap formulaMap
  displayKripkeFrames $ kripkeFrames formulaMap
  let (score1, score2) = compete agent1 agent2
  displayMap $ M.fromList [
    (Agent $ agentName agent1, score1),
    (Agent $ agentName agent2, score2)]

-- Sanity checks

allPairs :: [a] -> [(a,a)]
allPairs l = [ (a,b) | (a,bs) <- zip l (tail $ inits l), b <- bs ]

allPairsSym :: [a] -> [(a,a)]
allPairsSym l = [ x | ini <- inits l, x <- zip ini (reverse ini) ]

isSuckerPunched :: ModalFormula AgentVar -> ModalFormula AgentVar -> Bool
isSuckerPunched bot1 bot2 = simpleCompete bot1 bot2 == (True, False)

isMutualCoop :: ModalFormula AgentVar -> ModalFormula AgentVar -> Bool
isMutualCoop bot1 bot2 = simpleCompete bot1 bot2 == (True, True)

mutualCooperations :: [(ModalFormula AgentVar, ModalFormula AgentVar)]
mutualCooperations = filter (uncurry isMutualCoop) (allPairs allBots)

suckerPayoffs :: [(ModalFormula AgentVar, ModalFormula AgentVar)]
suckerPayoffs = filter (uncurry isSuckerPunched) (allPairsSym allBots)

sortUniq :: Ord a => [a] -> [a]
sortUniq l = case sort l of
  [] -> []
  (h:t) -> snub h t
    where
      snub x [] = [x]
      snub x (y:ys) | x /= y    = x : snub y ys
                    | otherwise = snub x ys

niceBots :: Int -> [ModalFormula AgentVar]
niceBots n = sortUniq [f c | c <- take n mutualCooperations, f <- [fst, snd]]

exploitableBots :: Int -> [ModalFormula AgentVar]
exploitableBots n = sortUniq [fst c | c <- take n suckerPayoffs]

-- Does any bot ever sucker punch this one?
checkSucker :: ModalFormula AgentVar -> Int -> Maybe (ModalFormula AgentVar)
checkSucker bot n = find (isSuckerPunched bot) (take n allBots)

-- Did a niceBot ever defect against us?
checkNiceBots :: ModalFormula AgentVar -> Int -> Maybe (ModalFormula AgentVar)
checkNiceBots bot n = find defectsAgainstMe (niceBots n) where
  defectsAgainstMe bot' = not $ snd $ simpleCompete bot bot'

-- Did this bot ever fail to exploit a suckerBot?

checkExploitableBots :: ModalFormula AgentVar -> Int -> Maybe (ModalFormula AgentVar)
checkExploitableBots bot n = find notSuckered (exploitableBots n) where
  notSuckered bot' = not $ isSuckerPunched bot' bot
