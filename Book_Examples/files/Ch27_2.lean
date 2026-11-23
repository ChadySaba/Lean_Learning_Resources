import Mathlib
-- ▶ Block 444 · Chapter 27: Community, Contributing, and Where to Go Next · Asking a question that gets answered · page 221 (French edition: page 231) · the book shows an error here

example (a : ℝ) (ha : 0 ≤ a) : a / (1 + a) ≤ 1 := by
  rw [div_le_one]
  linarith
-- error: unsolved goals
-- ⊢ 0 < 1 + a
