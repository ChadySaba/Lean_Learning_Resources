import Mathlib
-- ▶ Block 446 · Chapter 27: Community, Contributing, and Where to Go Next · Exercises · page 223 (French edition: page 235) · exercise: errors are normal until you solve it
open Real Filter Topology

-- Exercise 1. Reduce this to a minimal working example, then repair it.
noncomputable def g (x : ℝ) : ℝ := Real.exp x + x ^ 2

lemma g_pos (x : ℝ) : 0 < g x := by
  unfold g
  positivity

theorem bound (v : ℕ → ℝ) (n : ℕ) (h : g (v n) ≤ 5) : g (v n) / 5 ≤ 1 := by
  rw [div_le_one]
  exact h
