{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Modal.Agents where
import Control.Applicative
import Data.Monoid
import Modal.Code (Agent, ModalVar(..), Program, agent, ContextError, forceCompile)
import Modal.Formulas
import Modal.Environment
import Modal.Parser
import qualified Data.Text as Text
import Text.Parsec (oneOf, ParseError)
import Modal.Display

data CorD = C | D deriving (Eq, Ord, Enum, Read, Show)
instance Parsable CorD where parser = read . pure <$> oneOf "CD"

instance Read (ModalVar CorD CorD) where
  readsPrec _ str = [(from name, rest) | not $ null name] where
      name = takeWhile (`elem` '_' : ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9']) str
      rest = dropWhile (`elem` '_' : ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9']) str
      from "a" = MeVsThemIs C
      from "b" = ThemVsMeIs C
      from  n  = ThemVsOtherIs (Text.pack n) C

type AgentVar = ModalVar CorD CorD

layeredBot :: Int -> ModalFormula AgentVar -> ModalFormula AgentVar
layeredBot n base = foldl1 Or (map level [0..n]) where
  cond k = Neg (boxk k base) %^ diak k base
  level 0 = Box base
  level k = foldl1 And (map cond [0..pred k]) %^ boxk k base

masqueBot :: Int -> ModalFormula AgentVar
masqueBot n = dbLoop $ tbfLoop disjunct where
  dbLoop = loopBreakDBot (read "¬DB") (read "DB")
  tbfLoop = loopBreakDBot (read "TbF_2") (read "¬TbF_2")
  disjunct = foldl1 Or (map (\k -> boxk k $ read "b") [0..n])
  loopBreakDBot fbreak fdefect cont = breakOut n %^ cont where
    cond m = foldl1 And $ map (\k -> Neg (boxk k fbreak) %^ Neg (boxk k fdefect)) [0..m]
    breakOut 0 = Box fbreak
    breakOut m = breakOut (pred m) %| (cond (pred m) %^ boxk m fbreak)

modalUDT :: (Agent CorD CorD)
Right modalUDT = agent $
  "def UDT\n" <>
  "  let $level = 0\n" <>
  "  for outcome $o in ...\n" <>
  "    for action $a in ...\n" <>
  "      if [] $level [Me(Them)=$a -> Them(Me)=$o]\n" <>
  "        return $a\n" <>
  "      end\n" <>
  "      let $level = $level + 1\n" <>
  "    end\n" <>
  "  end\n" <>
  "  return\n"

prg :: ModalFormula AgentVar -> Program CorD CorD
prg f C = f
prg f D = Neg f

bot :: String -> Program CorD CorD
bot = prg . read

env :: Env CorD CorD
Right env = nobody @<
  -- Rank 0 bots
  ("CB", bot "⊤") @+
  ("DB", bot "⊥") @+
  ("FB", bot "□ b") @+
  ("FB_1", bot "[1] b") @+
  ("FB_2", bot "[2] b") @+
  ("FB_3", bot "[3] b") @+
  ("FB_4", bot "[4] b") @+
  ("FB_5", bot "[5] b") @+
  ("TbF_1", prg $ layeredBot 1 $ read "b") @+
  ("TbF_2", prg $ layeredBot 2 $ read "b") @+
  ("TbF_3", prg $ layeredBot 3 $ read "b") @+
  ("FB_r", bot "¬□¬b ∧ □b") @+
  ("MB", bot "[1](□a → b)") @+
  ("WB", bot "¬□⊥ ∧ [1]b") @+
  ("WB_2", bot "¬□a ∧ (□¬a ∨ [1]b)") @+
  ("aMB", bot "¬[1](□¬a → b) ∧ [2](¬[1](□¬a → b) → b)") @+
  ("sMB", bot "□(◇a → b)") @+
  ("IB", bot "¬(□(a → ¬b))") @+
  -- Rank 1 bots
  ("PB", bot "□b ∧ [1]¬DB") @+
  ("PB_2", prg $ layeredBot 2 $ read "¬DB ∧ b") @+
  ("PB_3", prg $ layeredBot 3 $ read "¬DB ∧ b") @+
  ("NB", bot "□CB") @+
  ("JB", bot "□FB") @+
  ("TB", bot "□DB") @+
  ("QB_1", prg $ masqueBot 1) @+
  ("QB_2", prg $ masqueBot 2) @+
  ("QB_3", prg $ masqueBot 3)
