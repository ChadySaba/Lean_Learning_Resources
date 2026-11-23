import Mathlib
-- ▶ Block 253 · Chapter 14: Numbers, Casts and Their Traps · Exercises · page 111 (French edition: page 115) · exercise: errors are normal until you solve it

-- Exercise 1. Before running anything, say which of these are true. Then prove
-- the true ones and correct the false ones.
example : (7 / 2 : ℕ) = 3 := by
  sorry
example : (7 / 2 : ℝ) = 3.5 := by
  sorry
example : ((1 / 3 : ℕ) : ℝ) * 3 = 1 := by
  sorry

-- Exercise 2. A fact crosses from ℝ to ℕ.
example (a b : ℕ) (h : (a : ℝ) + 1 ≤ b) : a < b := by
  sorry

-- Exercise 3. The cast of a truncated subtraction.
example (n : ℕ) (h : 5 ≤ n) : ((n - 5 : ℕ) : ℝ) = n - 5 := by
  sorry

-- Exercise 4. Unfold the absolute value into two inequalities.
example (x a : ℝ) (h : |x - a| < 2) : a - 2 < x := by
  sorry

-- Exercise 5. First obtain 1 ≤ n in ℝ. Then use div_le_one.
example (n : ℕ) (hn : 0 < n) : (1 : ℝ) / n ≤ 1 := by
  sorry

-- Exercise 6. Both bounds on the floor.
example (x : ℝ) : (⌊x⌋ : ℝ) ≤ x ∧ x < ⌊x⌋ + 1 := by
  sorry

-- Exercise 7. Move to ℤ, where subtraction is honest.
example (a b : ℕ) (h : b ≤ a) (h' : a - b = 7) : a = b + 7 := by
  sorry

-- Exercise 8. A nonlinear fact across a cast.
example (n : ℕ) (h : 3 ≤ n) : (9 : ℝ) ≤ n ^ 2 := by
  sorry
