import Lean
-- ▶ Block 407 · Chapter 23: Metaprogramming · Level 4: elaborators · page 189 (French edition: page 196)
open Lean Elab Tactic Meta

elab "show_goal" : tactic => do
  let g ← getMainGoal
  logInfo m!"The goal is: {← g.getType}"

example : 1 + 1 = 2 := by
  show_goal        -- The goal is: 1 + 1 = 2
  rfl
