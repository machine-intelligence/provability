module Agents where
import Control.Applicative hiding ((<|>))
import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as M
import Modal

data Variable = V String deriving (Eq, Ord)

instance Show Variable where show (V s) = s

instance Read Variable where
    readsPrec _ str = [(V name, rest) | not $ null name] where
        name = takeWhile (`elem` ['a' .. 'z']) str
        rest = dropWhile (`elem` ['a' .. 'z']) str

data ModalAgent = MA { aname :: String,
                       agentFormula :: ModalFormula Variable,
                       helpers :: Map String ModalAgent }
                  deriving (Eq,Show)

-- Bots
-- A bot is represented as a modal formula in which:
--  - The box represents provability
--  - The variable "A" represents whether this bot cooperates against its opponent
--  - The variable "B" represents whether the opponent cooperates with us.

-- Some Bots:

-- isLegalBot: Make sure all variables are inside modal operators.
isLegalBot :: ModalFormula v -> Bool
isLegalBot = modalEval ModalEvaluator {
  handleVar = const False,
  handleVal = const True,
  handleNeg = id,
  handleAnd = (&&), handleOr = (&&), handleImp = (&&), handleIff = (&&),
  handleBox = const True, handleDia = const True}

simpleAgent :: ModalFormula Variable -> ModalAgent
simpleAgent formula = MA ("AGENT(" ++ show formula ++ ")") formula M.empty

simpleNamedAgent :: String -> ModalFormula Variable -> ModalAgent
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

niceBot = MA "nice" (read "[] coop") (M.fromList [("coop", coopBot)])
justBot = MA "just" (read "[] fair") (M.fromList [("fair", fairBot)])
trollBot = MA "troll" (read "[] dbot") (M.fromList [("dbot", defectBot)])

layeredBot :: String -> ModalFormula Variable -> Int -> ModalAgent
layeredBot name base n = MA (name ++ show n) (thebot n) M.empty
  where
    cond k = Neg (boxk k base) `And` Neg (boxk k (Neg base))

    level 0 = Box base
    level k = foldl1 And (map cond [0..k-1]) `And` boxk k base

    thebot k = foldl1 Or (map level [0..k])

toughButFairBotN = layeredBot "tbfair" (read "b")

layeredCheckBot n = (layeredBot "check" (read "~ dbot && b") n) { helpers = M.fromList [("dbot", defectBot)] }

loopBreakDBot :: ModalFormula Variable -> ModalFormula Variable ->
                 Int -> ModalFormula Variable -> ModalFormula Variable
loopBreakDBot fbreak fdefect x cont = breakOut x `And` cont
  where
    cond n = foldl1 And $ map (\k -> Neg (boxk k fbreak) `And` Neg (boxk k fdefect)) [0..n]

    breakOut 0 = Box fbreak
    breakOut n = breakOut (n-1) `Or` (cond (n-1) `And` boxk n fbreak)

masqueBot n = MA ("masque" ++ show n) masque (M.fromList [("db", defectBot), ("tbf", toughButFairBot)])
  where
    masque = loopBreakDBot (read "~ db") (read "db") n $
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

allBots :: [ModalFormula Variable]
allBots = filter isLegalBot (allFormulas [V "a", V "b"])

-- How bots compete:
mapVars :: (v -> v) -> ModalFormula v -> ModalFormula v
mapVars f = modalEval idModalEvaluator { handleVar = Var . f }

flipBot :: ModalFormula Variable -> ModalFormula Variable
flipBot = mapVars (\s -> if s == V "a" then V "b" else (if s == V "b" then V "a" else s))

competitionNameCat :: String -> String -> String
competitionNameCat name1 name2 = name1 ++ "_vs_" ++ name2

competitionSloppyNames :: ModalAgent -> ModalAgent -> Map String (ModalFormula Variable)
competitionSloppyNames na1@(MA n1 a1 helpers1) na2@(MA n2 a2 helpers2)
  | n1 == n2 && na1 /= na2 = error "Different agents competing with same names"
  | otherwise = top `M.union` left `M.union` right
  where
    ncat = competitionNameCat
    top = M.fromList [ (ncat n1 n2, renameFormula a1 n1 n2), (ncat n2 n1, renameFormula a2 n2 n1) ]

    left  = M.unions [ competitionSloppyNames na2 (rename nha1) | nha1 <- M.toList helpers1 ]
    right = M.unions [ competitionSloppyNames na1 (rename nha2) | nha2 <- M.toList helpers2 ]

    rename (name,agent) = agent { aname = name }

    renameFormula :: ModalFormula Variable -> String -> String -> ModalFormula Variable
    renameFormula formula myName oppName = mapVars f formula
      where
        f (V "a") = V $ ncat myName oppName
        f (V "b") = V $ ncat oppName myName
        f (V   x) = V $ ncat oppName x

competition :: ModalAgent -> ModalAgent -> Map Variable (ModalFormula Variable)
competition na1@(MA n1 a1 helpers1) na2@(MA n2 a2 helpers2)
  | n1 == n2 && na1 /= na2 = error "Different agents competing with same names"
  | otherwise = top `M.union` left `M.union` right
  where
    ncat = competitionNameCat
    scat n sn = n ++ "." ++ sn

    top = M.fromList [ (V $ ncat n1 n2, renameFormula a1 n1 n2), (V $ ncat n2 n1, renameFormula a2 n2 n1) ]

    left  = M.unions [ competition na2 (rename n1 nha1) | nha1 <- M.toList helpers1 ]
    right = M.unions [ competition na1 (rename n2 nha2) | nha2 <- M.toList helpers2 ]

    rename superName (name,agent) = agent { aname = scat superName name }

    renameFormula formula myName oppName = mapVars f formula
      where
        f (V "a") = V $ ncat myName oppName
        f (V "b") = V $ ncat oppName myName
        f (V   x) = V $ ncat oppName x

compete :: ModalAgent -> ModalAgent -> (Bool, Bool)
compete agent1 agent2 = simplifyOutput $ findGeneralGLFixpoint $ competition agent1 agent2
  where
    n1 = aname agent1
    n2 = aname agent2
    ncat = competitionNameCat
    simplifyOutput map = (map ! (V $ ncat n1 n2), map ! (V $ ncat n2 n1))

simpleCompete :: ModalFormula Variable -> ModalFormula Variable -> (Bool, Bool)
simpleCompete f1 f2 = compete (simpleAgent f1) (simpleAgent f2)

-- Sanity checks

allPairs :: [a] -> [(a,a)]
allPairs l = [ (a,b) | (a,bs) <- zip l (tail $ inits l), b <- bs ]

allPairsSym :: [a] -> [(a,a)]
allPairsSym l = [ x | ini <- inits l, x <- zip ini (reverse ini) ]

isSuckerPunched :: ModalFormula Variable -> ModalFormula Variable -> Bool
isSuckerPunched bot1 bot2 = simpleCompete bot1 bot2 == (True, False)

isMutualCoop :: ModalFormula Variable -> ModalFormula Variable -> Bool
isMutualCoop bot1 bot2 = simpleCompete bot1 bot2 == (True, True)

mutualCooperations :: [(ModalFormula Variable, ModalFormula Variable)]
mutualCooperations = filter (uncurry isMutualCoop) (allPairs allBots)

suckerPayoffs :: [(ModalFormula Variable, ModalFormula Variable)]
suckerPayoffs = filter (uncurry isSuckerPunched) (allPairsSym allBots)

sortUniq :: Ord a => [a] -> [a]
sortUniq l = case sort l of
  [] -> []
  (h:t) -> snub h t
    where
      snub x [] = [x]
      snub x (y:ys) | x /= y    = x : snub y ys
                    | otherwise = snub x ys

niceBots :: Int -> [ModalFormula Variable]
niceBots n = sortUniq [f c | c <- take n mutualCooperations, f <- [fst, snd]]

exploitableBots :: Int -> [ModalFormula Variable]
exploitableBots n = sortUniq [fst c | c <- take n suckerPayoffs]

-- Does any bot ever sucker punch this one?
checkSucker :: ModalFormula Variable -> Int -> Maybe (ModalFormula Variable)
checkSucker bot n = find (isSuckerPunched bot) (take n allBots)

-- Did a niceBot ever defect against us?
checkNiceBots :: ModalFormula Variable -> Int -> Maybe (ModalFormula Variable)
checkNiceBots bot n = find defectsAgainstMe (niceBots n) where
  defectsAgainstMe bot' = not $ snd $ simpleCompete bot bot'

-- Did this bot ever fail to exploit a suckerBot?

checkExploitableBots :: ModalFormula Variable -> Int -> Maybe (ModalFormula Variable)
checkExploitableBots bot n = find notSuckered (exploitableBots n) where
  notSuckered bot' = not $ isSuckerPunched bot' bot
