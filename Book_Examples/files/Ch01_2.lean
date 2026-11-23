import Mathlib
-- ▶ Block 4 · Chapter 1: What Lean Is · What working in Lean feels like · page 9 (French edition: page 10)

example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  nlinarith

-- ▶ Block 6 · Chapter 1: What Lean Is · Solutions · page 10 (French edition: page 12)
def triple (n : Nat) : Nat := 3 * n

theorem triple_eq (n : Nat) : triple n = n + n + n := by
  unfold triple
  omega
