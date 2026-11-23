import Mathlib
-- ▶ Block 440 · Chapter 26: Lean and AI Tools · Exercises · page 218 (French edition: page 228) · exercise: errors are normal until you solve it

-- Exercise 1. An assistant returns this as a proof of:
-- "for natural numbers, (a - b) + b = a".
-- Does it prove that sentence? Find a and b for which the sentence is false.
theorem sub_add_or (a b : ℕ) : a - b + b = a ∨ a < b := by omega

-- Exercise 2. Which of these two statements says "f has a critical point at 0"?
-- Explain what the other one allows.
def crit1 (f : ℝ → ℝ) : Prop := deriv f 0 = 0
def crit2 (f : ℝ → ℝ) : Prop := HasDerivAt f 0 0

-- Exercise 3. This is the statement you wanted:
--   theorem mine (x : ℝ) (hx : 0 < x) : Real.log (x ^ 2) = 2 * Real.log x
-- and this is what you received. Use point 4 of the checklist: prove `mine`
-- from `theirs`. Does it work? What does that tell you?
theorem theirs (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) : Real.log (x ^ 2) = 2 * Real.log x := by
  rw [Real.log_pow]
  norm_num

theorem mine (x : ℝ) (hx : 0 < x) : Real.log (x ^ 2) = 2 * Real.log x := by
  sorry
