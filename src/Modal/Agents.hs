{-# LANGUAGE OverloadedStrings #-}
module Modal.Agents where
import Modal.Formulas
import Modal.Environment

layeredBot :: Int -> ModalFormula AgentVar -> ModalFormula AgentVar
layeredBot n base = foldl1 Or (map level [0..n]) where
  cond k = Neg (boxk k base) %^ diak k base
  level 0 = Box base
  level k = foldl1 And (map cond [0..pred k]) %^ boxk k base

masqueBot :: Int -> ModalFormula AgentVar
masqueBot n = dbLoop $ tbfLoop disjunct where
  dbLoop = loopBreakDBot (read "¬DB") (read "DB")
  tbfLoop = loopBreakDBot (read "TbF_2") (read "¬TbF_2")
  disjunct = foldl1 Or (map (\k -> boxk k $ Var ThemVsMe) [0..n])
  loopBreakDBot fbreak fdefect cont = breakOut n %^ cont where
    cond m = foldl1 And $ map (\k -> Neg (boxk k fbreak) %^ Neg (boxk k fdefect)) [0..m]
    breakOut 0 = Box fbreak
    breakOut m = breakOut (pred m) %| (cond (pred m) %^ boxk m fbreak)


env :: Env
Right env = nobody @<
  -- Rank 0 bots
  ("CB", read "⊤") @+
  ("DB", read "⊥") @+
  ("FB", read "□ b") @+
  ("FB_1", read "[1] b") @+
  ("FB_2", read "[2] b") @+
  ("FB_3", read "[3] b") @+
  ("FB_4", read "[4] b") @+
  ("FB_5", read "[5] b") @+
  ("TbF_1", layeredBot 1 $ Var ThemVsMe) @+
  ("TbF_2", layeredBot 2 $ Var ThemVsMe) @+
  ("TbF_3", layeredBot 3 $ Var ThemVsMe) @+
  ("FB_r", read "¬□¬b ∧ □b") @+
  ("MB", read "[1](□a → b)") @+
  ("WB", read "¬□⊥ ∧ [1]b") @+
  ("WB_2", read "¬□a ∧ (□¬a ∨ [1]b)") @+
  ("aMB", read "¬[1](□¬a → b) ∧ [2](¬[1](□¬a → b) → b)") @+
  ("sMB", read "□(◇a → b)") @+
  ("IB", read "¬(□(a → ¬b))") @+
  -- Rank 1 bots
  ("PB", read "□b ∧ [1]¬DB") @+
  ("PB_2", layeredBot 2 $ read "¬DB ∧ b") @+
  ("PB_3", layeredBot 3 $ read "¬DB ∧ b") @+
  ("NB", read "□CB") @+
  ("JB", read "□FB") @+
  ("TB", read "□DB") @+
  ("QB_1", masqueBot 1) @+
  ("QB_2", masqueBot 2) @+
  ("QB_3", masqueBot 3)
