import Mathlib
-- ▶ Block 320 · Chapter 17: Filters, Limits and Topology · Solutions · page 141 (French edition: page 147)

open Filter Topology Set

-- Exercise 1.
example : Tendsto (fun n : ℕ ↦ 3 + 2 * (1 / (n + 1 : ℝ))) atTop (𝓝 3) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 := (h.const_mul 2).const_add 3
  -- h2 : Tendsto (fun x ↦ 3 + 2 * (1 / (↑x + 1))) atTop (𝓝 (3 + 2 * 0))
  simpa using h2

-- Exercise 2.
example : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ) ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero (g := fun n : ℕ ↦ 1 / (n + 1 : ℝ))
  · intro n
    positivity
  · intro n
    -- ⊢ 1 / (↑n + 1) ^ 2 ≤ 1 / (↑n + 1)
    have h : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have h2 : (n + 1 : ℝ) ≤ (n + 1) ^ 2 := by nlinarith
    gcongr
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

-- Exercise 3.
example (u : ℕ → ℝ) (a : ℝ) (hu : Tendsto u atTop (𝓝 a)) (h : ∀ n, u n ≤ 5) : a ≤ 5 :=
  le_of_tendsto' hu h

-- Exercise 4.
example (u v : ℕ → ℝ) (hu : ∀ᶠ n in atTop, 1 < u n) (hv : ∀ᶠ n in atTop, u n < v n) :
    ∀ᶠ n in atTop, 1 < v n := by
  filter_upwards [hu, hv] with n h1 h2
  linarith

-- Exercise 5.
example : Continuous (fun x : ℝ ↦ 3 * x - 2) := by fun_prop

example : Continuous (fun x : ℝ ↦ 3 * x - 2) := by
  rw [Metric.continuous_iff]
  intro a ε hε
  refine ⟨ε / 3, by positivity, ?_⟩
  intro x hx
  rw [Real.dist_eq] at hx ⊢
  have h : 3 * x - 2 - (3 * a - 2) = 3 * (x - a) := by ring
  rw [h, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  -- hx : |x - a| < ε / 3     ⊢ 3 * |x - a| < ε
  linarith

-- Exercise 6.
example (u : ℕ → ℝ) (a : ℝ) (hu : Tendsto u atTop (𝓝 a)) :
    ∃ N, ∀ n ≥ N, |u n| < |a| + 1 := by
  rw [Metric.tendsto_atTop] at hu
  obtain ⟨N, hN⟩ := hu 1 (by norm_num)
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := hN n hn
  rw [Real.dist_eq] at h
  -- h : |u n - a| < 1
  have h2 : |u n| - |a| ≤ |u n - a| := abs_sub_abs_le_abs_sub _ _
  linarith

-- Exercise 7.
example : IsClosed {x : ℝ | x ^ 2 ≤ 4} :=
  isClosed_le (by fun_prop) continuous_const

-- Exercise 8.
example : ∃ x ∈ Icc (0 : ℝ) 2, x ^ 2 + x = 3 := by
  have hf : ContinuousOn (fun x : ℝ ↦ x ^ 2 + x) (Icc 0 2) := by fun_prop
  have h := intermediate_value_Icc (show (0 : ℝ) ≤ 2 by norm_num) hf
  apply h
  constructor <;> norm_num

-- Exercise 9.
example : ∑' n : ℕ, (1 / 4 : ℝ) ^ n = 4 / 3 := by
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num
