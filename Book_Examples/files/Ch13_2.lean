import Mathlib
-- ▶ Block 227 · Chapter 13: Automation · Exercises · page 101 (French edition: page 106) · exercise: errors are normal until you solve it

-- Each goal is closed by one tactic from this chapter, sometimes with a fact in
-- brackets or one preparatory step. Choose the tactic before you type it.

example (a b : ℝ) : (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  sorry

example (x y : ℝ) (h₁ : x + y = 10) (h₂ : x - y = 2) : x = 6 := by
  sorry

example : (3 : ℝ) / 4 + 1 / 4 = 1 := by
  sorry

example (n : ℕ) (h : 3 ≤ n) : n - 2 + 2 = n := by
  sorry

example (x : ℝ) : 0 < x ^ 4 + x ^ 2 + 1 := by
  sorry

example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c + 1 ≤ b * c + 1 := by
  sorry

example (x : ℝ) (hx : x ≠ 0) : x ^ 2 / x = x := by
  sorry

example (p q : Prop) : p ∧ q → q ∧ p := by
  sorry

example (x y : ℝ) : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by
  sorry

example (a b : ℝ) (h : a = 2 * b) (h' : b = 3) : a ^ 2 = 36 := by
  sorry

-- Two tactics, one per component.
example (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, δ < ε := by
  refine ⟨ε / 2, ?_, ?_⟩
  · sorry
  · sorry

-- Three steps: a sign fact, a rewrite with div_lt_one, a linear conclusion.
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x / (x + y) < 1 := by
  sorry

-- Factor first: (x - 1) * (x - 2) = 0. Then use mul_eq_zero.
example (x : ℝ) (h : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  sorry
