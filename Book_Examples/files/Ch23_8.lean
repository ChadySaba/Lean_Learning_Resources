import Mathlib
-- ▶ Block 415 · Chapter 23: Metaprogramming · Solutions · page 194 (French edition: page 202)
open Lean Elab Tactic Meta

-- Exercise 1.
def near (ε a b : ℝ) : Prop := |a - b| < ε

notation:50 a " ≈[" ε "] " b => near ε a b

example : (2 : ℝ) ≈[1] (5 / 2) := by
  unfold near
  -- ⊢ |2 - 5 / 2| < 1
  rw [abs_lt]
  constructor <;> norm_num

-- Exercise 2. `a <;> b` runs `b` on every goal that `a` leaves, so it also
-- works when `field_simp` closes the goal by itself.
macro "my_field" : tactic => `(tactic| first | ring1 | (field_simp <;> ring1))

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by my_field
example (x y : ℝ) (hx : x ≠ 0) : (x + y) / x = 1 + y / x := by my_field
example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : 1 / x + 1 / y = (x + y) / (x * y) := by
  my_field

-- Exercise 3. `$x:term` tells the parser which kind of argument `use` receives.
macro "use_and_norm " x:term : tactic => `(tactic| (use $x:term <;> norm_num))

example : ∃ x : ℝ, x ^ 2 = 4 := by use_and_norm 2
example : ∃ n : ℕ, n * 2 = 10 := by use_and_norm 5
example : ∃ x : ℝ, 0 < x ∧ x < 1 := by use_and_norm 1 / 2

-- Exercise 4.
elab "count_hyps" : tactic => withMainContext do
  let mut n : Nat := 0
  for d in ← getLCtx do
    if !d.isImplementationDetail then n := n + 1
  logInfo m!"{n} hypotheses"

example (a b : ℕ) (h : a = b) : b = a := by
  count_hyps        -- 3 hypotheses
  exact h.symm

-- Exercise 5.
elab "list_hyps" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    logInfo m!"{d.userName} : {d.type}"

example (a b : ℕ) (h : a = b) : b = a := by
  list_hyps         -- a : ℕ,  b : ℕ,  h : a = b
  exact h.symm
