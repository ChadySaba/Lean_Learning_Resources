import Mathlib
-- ▶ Block 362 · Chapter 20: A Worked Project in Analysis · Exercises · page 167 (French edition: page 174) · exercise: errors are normal until you solve it

open Filter Topology

def UnifConv (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, |F n x - f x| < ε

-- Exercise 1. A uniform limit of bounded functions is bounded.
-- Paper proof: take ε = 1, get N, and let M bound F N. Then M + 1 bounds f.
theorem bounded_of_unifConv (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hF : ∀ n, ∃ M, ∀ x, |F n x| ≤ M) (hunif : UnifConv F f) : ∃ M, ∀ x, |f x| ≤ M := by
  sorry

-- Exercise 2. The uniform limit is unique.
-- Start with `ext x` and `apply eq_of_abs_sub_le_all`.
theorem unifConv_unique (F : ℕ → ℝ → ℝ) (f g : ℝ → ℝ)
    (hf : UnifConv F f) (hg : UnifConv F g) : f = g := by
  sorry

-- Exercise 3. The main theorem between metric spaces. Rewrite the proof of this
-- chapter with `dist` in place of absolute values, and `dist_triangle4`.
theorem continuous_of_unifConv_metric {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y) (hF : ∀ n, Continuous (F n))
    (hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, dist (F n x) (f x) < ε) : Continuous f := by
  sorry
