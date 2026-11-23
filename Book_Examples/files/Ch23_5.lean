import Lean
-- ▶ Block 409 · Chapter 23: Metaprogramming · Writing a tactic · page 190 (French edition: page 197)
open Lean Elab Tactic Meta

elab "my_assumption" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← isDefEq d.type target then
      goal.assign d.toExpr
      return
  throwError "my_assumption: no hypothesis matches {target}"

example (p q : Prop) (hp : p) (hq : q) : q := by my_assumption

-- ▶ Block 410 · Chapter 23: Metaprogramming · Writing a tactic · page 190 (French edition: page 197)
elab "apply_any" : tactic => withMainContext do
  let goal ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    try
      let newGoals ← goal.apply d.toExpr
      replaceMainGoal newGoals
      return
    catch _ => continue
  throwError "apply_any: no hypothesis applies to {← goal.getType}"

example (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  apply_any
  -- ⊢ q
  apply_any
  -- ⊢ p
  apply_any

-- ▶ Block 411 · Chapter 23: Metaprogramming · Writing a tactic · page 191 (French edition: page 198)
elab "sides" : tactic => withMainContext do
  let t ← getMainTarget
  match t.eq? with
  | some (_, lhs, rhs) => logInfo m!"left: {lhs}, right: {rhs}"
  | none => throwError "the goal is not an equality"

example (a b : Nat) : a + b = b + a := by
  sides                            -- left: a + b, right: b + a
  exact Nat.add_comm a b

elab "finish" : tactic => do
  evalTactic (← `(tactic| first | rfl | assumption | omega | simp_all))

example (a : Nat) (h : 0 < a) : a ≠ 0 := by finish

-- ▶ Block 412 · Chapter 23: Metaprogramming · Tactics are not trusted · page 191 (French edition: page 198) · the book shows an error here
elab "wrong_assign" : tactic => do
  let goal ← getMainGoal
  goal.assign (mkNatLit 3)         -- claims that 3 is a proof

example : True := by wrong_assign
-- error: (kernel) declaration type mismatch, '_example' has type
--   Nat
-- but it is expected to have type
--   True
