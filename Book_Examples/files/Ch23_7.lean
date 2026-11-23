import Mathlib
-- ▶ Block 414 · Chapter 23: Metaprogramming · Exercises · page 193 (French edition: page 200) · exercise: errors are normal until you solve it
open Lean Elab Tactic Meta

-- Exercise 1. Declare a notation  a ≈[ε] b  for  near ε a b,
-- then state and prove that 2 is within 1 of 5/2.
def near (ε a b : ℝ) : Prop := |a - b| < ε

-- notation ...

example : near 1 2 (5 / 2) := by
  sorry

-- Exercise 2. Write a macro `my_field` that tries `ring1`, and if that fails
-- runs `field_simp`, then `ring1` on the goal that remains, if any.
-- (`ring1` fails when it cannot close the goal. `ring` does not always fail.)

example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : 1 / x + 1 / y = (x + y) / (x * y) := by
  sorry   -- by my_field

-- Exercise 3. Write a macro `use_and_norm x` that runs `use x`, then
-- `norm_num` on the goal that remains, if any.

example : ∃ x : ℝ, x ^ 2 = 4 := by
  sorry   -- by use_and_norm 2

-- Exercise 4. Write an elaborator `count_hyps` that prints the number of
-- hypotheses of the main goal.

example (a b : ℕ) (h : a = b) : b = a := by
  -- count_hyps      -- should print: 3 hypotheses
  exact h.symm

-- Exercise 5. Write an elaborator `list_hyps` that prints every hypothesis
-- as  name : type.

example (a b : ℕ) (h : a = b) : b = a := by
  -- list_hyps
  exact h.symm
