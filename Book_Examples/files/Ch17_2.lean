import Mathlib
-- ▶ Block 319 · Chapter 17: Filters, Limits and Topology · Exercises · page 140 (French edition: page 147) · exercise: errors are normal until you solve it

open Filter Topology Set

-- Exercise 1. Combine the standard limit with const_mul and const_add.
example : Tendsto (fun n : ℕ ↦ 3 + 2 * (1 / (n + 1 : ℝ))) atTop (𝓝 3) := by
  sorry

-- Exercise 2. Squeeze between 0 and 1 / (n + 1).
example : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ) ^ 2) atTop (𝓝 0) := by
  sorry

-- Exercise 3. A bound passes to the limit.
example (u : ℕ → ℝ) (a : ℝ) (hu : Tendsto u atTop (𝓝 a)) (h : ∀ n, u n ≤ 5) : a ≤ 5 := by
  sorry

-- Exercise 4. Combine two eventual facts.
example (u v : ℕ → ℝ) (hu : ∀ᶠ n in atTop, 1 < u n) (hv : ∀ᶠ n in atTop, u n < v n) :
    ∀ᶠ n in atTop, 1 < v n := by
  sorry

-- Exercise 5. Once with fun_prop, once with ε and δ.
example : Continuous (fun x : ℝ ↦ 3 * x - 2) := by
  sorry

-- Exercise 6. A convergent sequence is eventually bounded. Use ε = 1.
example (u : ℕ → ℝ) (a : ℝ) (hu : Tendsto u atTop (𝓝 a)) :
    ∃ N, ∀ n ≥ N, |u n| < |a| + 1 := by
  sorry

-- Exercise 7. A closed set defined by an inequality.
example : IsClosed {x : ℝ | x ^ 2 ≤ 4} := by
  sorry

-- Exercise 8. The intermediate value theorem.
example : ∃ x ∈ Icc (0 : ℝ) 2, x ^ 2 + x = 3 := by
  sorry

-- Exercise 9. A geometric series.
example : ∑' n : ℕ, (1 / 4 : ℝ) ^ n = 4 / 3 := by
  sorry
