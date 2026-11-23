import Mathlib
-- ▶ Block 443 · Chapter 27: Community, Contributing, and Where to Go Next · Asking a question that gets answered · page 221 (French edition: page 231) · the book shows an error here
open Real Filter Topology

noncomputable def myF (x : ℝ) : ℝ := x ^ 2 + 3 * x

lemma myF_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ myF x := by
  unfold myF
  positivity

theorem stuck (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (n : ℕ) :
    myF (u n) / (1 + myF (u n)) ≤ 1 := by
  rw [div_le_one]
  linarith
-- error: unsolved goals
-- ⊢ 0 < 1 + myF (u n)
