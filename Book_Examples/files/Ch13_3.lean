import Mathlib
-- ▶ Block 228 · Chapter 13: Automation · Solutions · page 102 (French edition: page 108)

example (a b : ℝ) : (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  ring

example (x y : ℝ) (h₁ : x + y = 10) (h₂ : x - y = 2) : x = 6 := by
  linarith

example : (3 : ℝ) / 4 + 1 / 4 = 1 := by
  norm_num

example (n : ℕ) (h : 3 ≤ n) : n - 2 + 2 = n := by
  omega

example (x : ℝ) : 0 < x ^ 4 + x ^ 2 + 1 := by
  positivity

example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c + 1 ≤ b * c + 1 := by
  gcongr

example (x : ℝ) (hx : x ≠ 0) : x ^ 2 / x = x := by
  field_simp

example (p q : Prop) : p ∧ q → q ∧ p := by
  tauto

example (x y : ℝ) : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by
  nlinarith [sq_nonneg (x - y)]

example (a b : ℝ) (h : a = 2 * b) (h' : b = 3) : a ^ 2 = 36 := by
  rw [h, h']
  -- ⊢ (2 * 3) ^ 2 = 36
  norm_num

example (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, δ < ε := by
  refine ⟨ε / 2, ?_, ?_⟩
  · positivity
  · linarith

example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x / (x + y) < 1 := by
  have h : 0 < x + y := by positivity
  rw [div_lt_one h]
  -- ⊢ x < x + y
  linarith

example (x : ℝ) (h : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h' : (x - 1) * (x - 2) = 0 := by linarith
  -- mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
  rcases mul_eq_zero.mp h' with h1 | h2
  · left
    linarith
  · right
    linarith
