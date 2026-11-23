import Mathlib
-- ▶ Block 254 · Chapter 14: Numbers, Casts and Their Traps · Solutions · page 112 (French edition: page 116)

-- Exercise 1. The first two are true. The third is false: 1 / 3 is 0 in ℕ.
example : (7 / 2 : ℕ) = 3 := by
  norm_num
example : (7 / 2 : ℝ) = 3.5 := by
  norm_num
example : ((1 / 3 : ℕ) : ℝ) * 3 = 0 := by
  norm_num
example : (1 / 3 : ℝ) * 3 = 1 := by
  norm_num

-- Exercise 2.
example (a b : ℕ) (h : (a : ℝ) + 1 ≤ b) : a < b := by
  have h' : a + 1 ≤ b := by exact_mod_cast h
  omega

-- Exercise 3.
example (n : ℕ) (h : 5 ≤ n) : ((n - 5 : ℕ) : ℝ) = n - 5 := by
  push_cast [h]
  rfl

-- Exercise 4.
example (x a : ℝ) (h : |x - a| < 2) : a - 2 < x := by
  have h' := abs_lt.mp h
  -- h' : -2 < x - a ∧ x - a < 2
  linarith

-- Exercise 5.
example (n : ℕ) (hn : 0 < n) : (1 : ℝ) / n ≤ 1 := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_one (by positivity)]
  -- ⊢ 1 ≤ ↑n
  exact h

-- Exercise 6.
example (x : ℝ) : (⌊x⌋ : ℝ) ≤ x ∧ x < ⌊x⌋ + 1 :=
  ⟨Int.floor_le x, Int.lt_floor_add_one x⟩

-- Exercise 7.
example (a b : ℕ) (h : b ≤ a) (h' : a - b = 7) : a = b + 7 := by
  zify [h] at h' ⊢
  linarith

-- Exercise 8.
example (n : ℕ) (h : 3 ≤ n) : (9 : ℝ) ≤ n ^ 2 := by
  have h' : (3 : ℝ) ≤ n := by exact_mod_cast h
  nlinarith
