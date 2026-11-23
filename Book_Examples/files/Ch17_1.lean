import Mathlib
-- ▶ Block 297 · Chapter 17: Filters, Limits and Topology · One definition for all limits · page 131 (French edition: page 137)

open Filter Topology

#check @Tendsto       -- (α → β) → Filter α → Filter β → Prop

-- ▶ Block 298 · Chapter 17: Filters, Limits and Topology · What a filter is · page 132 (French edition: page 138)
#check @Filter.mem_atTop_sets -- s ∈ atTop ↔ ∃ a, ∀ (b : α), a ≤ b → b ∈ s
#check @Metric.mem_nhds_iff   -- s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s

-- ▶ Block 299 · Chapter 17: Filters, Limits and Topology · What a filter is · page 132 (French edition: page 138)
#check @tendsto_def      -- Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁

-- ▶ Block 300 · Chapter 17: Filters, Limits and Topology · Getting the ε back · page 132 (French edition: page 138)
#check @Metric.tendsto_atTop
-- Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε

#check @Metric.tendsto_nhds_nhds
-- Tendsto f (𝓝 a) (𝓝 b) ↔
--   ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, dist x a < δ → dist (f x) b < ε

#check Real.dist_eq      -- dist x y = |x - y|

-- ▶ Block 301 · Chapter 17: Filters, Limits and Topology · Getting the ε back · page 132 (French edition: page 138)
example : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- ⊢ ∃ N, ∀ n ≥ N, dist (1 / (↑n + 1)) 0 < ε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε       -- hN : 1 / (↑N + 1) < ε
  use N
  intro n hn
  rw [Real.dist_eq, sub_zero]
  -- ⊢ |1 / (↑n + 1)| < ε
  have h1 : (0 : ℝ) < 1 / (n + 1) := by positivity
  rw [abs_of_pos h1]
  have h2 : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by gcongr
  linarith

-- ▶ Block 302 · Chapter 17: Filters, Limits and Topology · Getting the ε back · page 133 (French edition: page 139)
example : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

-- ▶ Block 303 · Chapter 17: Filters, Limits and Topology · The algebra of limits · page 133 (French edition: page 139)
example (u v : ℕ → ℝ) (a b : ℝ) (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n ↦ u n + v n) atTop (𝓝 (a + b)) := hu.add hv

example (u v : ℕ → ℝ) (a b : ℝ) (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n ↦ u n * v n) atTop (𝓝 (a * b)) := hu.mul hv

example (u : ℕ → ℝ) (a : ℝ) (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n ↦ u n ^ 2 + 3) atTop (𝓝 (a ^ 2 + 3)) := (hu.pow 2).add_const 3

-- ▶ Block 304 · Chapter 17: Filters, Limits and Topology · The algebra of limits · page 134 (French edition: page 140)
example : Tendsto (fun n : ℕ ↦ 2 + 1 / (n + 1 : ℝ)) atTop (𝓝 2) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 := h.const_add 2
  -- h2 : Tendsto (fun x ↦ 2 + 1 / (↑x + 1)) atTop (𝓝 (2 + 0))
  simpa using h2

-- ▶ Block 305 · Chapter 17: Filters, Limits and Topology · Eventually · page 134 (French edition: page 140)
example : ∀ᶠ n : ℕ in atTop, 100 < n := eventually_gt_atTop 100

example (p : ℕ → Prop) (h : ∀ᶠ n in atTop, p n) : ∃ N, ∀ n ≥ N, p n :=
  eventually_atTop.mp h

-- ▶ Block 306 · Chapter 17: Filters, Limits and Topology · Eventually · page 135 (French edition: page 141)
example (u v : ℕ → ℝ) (hu : ∀ᶠ n in atTop, 0 < u n) (hv : ∀ᶠ n in atTop, u n ≤ v n) :
    ∀ᶠ n in atTop, 0 < v n := by
  filter_upwards [hu, hv] with n h1 h2
  -- h1 : 0 < u n     h2 : u n ≤ v n     ⊢ 0 < v n
  linarith

-- ▶ Block 307 · Chapter 17: Filters, Limits and Topology · Eventually · page 135 (French edition: page 141)
example (u : ℕ → ℝ) (a : ℝ) (hu : Tendsto u atTop (𝓝 a)) (ha : 0 < a) :
    ∃ N, ∀ n ≥ N, a / 2 < u n := by
  have h : ∀ᶠ n in atTop, a / 2 < u n := hu.eventually_const_lt (by linarith)
  exact eventually_atTop.mp h

-- ▶ Block 308 · Chapter 17: Filters, Limits and Topology · An ε proof, when you want one · page 135 (French edition: page 141)
example (u v : ℕ → ℝ) (a b : ℝ) (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n ↦ u n + v n) atTop (𝓝 (a + b)) := by
  rw [Metric.tendsto_atTop] at *
  intro ε hε
  obtain ⟨N₁, h₁⟩ := hu (ε / 2) (by positivity)
  obtain ⟨N₂, h₂⟩ := hv (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : n ≥ N₁ := le_trans (le_max_left _ _) hn
  have hn₂ : n ≥ N₂ := le_trans (le_max_right _ _) hn
  have e₁ := h₁ n hn₁
  have e₂ := h₂ n hn₂
  rw [Real.dist_eq] at *
  -- e₁ : |u n - a| < ε / 2     e₂ : |v n - b| < ε / 2     ⊢ |u n + v n - (a + b)| < ε
  calc |u n + v n - (a + b)| = |(u n - a) + (v n - b)| := by ring_nf
    _ ≤ |u n - a| + |v n - b| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by gcongr
    _ = ε := by ring

-- ▶ Block 309 · Chapter 17: Filters, Limits and Topology · Continuity · page 136 (French edition: page 142)
example : Continuous (fun x : ℝ ↦ x ^ 2 + 3 * x + 1) := by fun_prop

example : Continuous (fun x : ℝ ↦ Real.exp (x ^ 2) * |x|) := by fun_prop

example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ f x * g (x + 1)) := by fun_prop

-- ▶ Block 310 · Chapter 17: Filters, Limits and Topology · Continuity · page 136 (French edition: page 142)
example (x : ℝ) (hx : x ≠ 0) : ContinuousAt (fun x : ℝ ↦ 1 / x) x := by
  fun_prop (disch := assumption)

-- ▶ Block 311 · Chapter 17: Filters, Limits and Topology · Continuity · page 136 (French edition: page 142)
example : Continuous (fun x : ℝ ↦ 2 * x + 1) := by
  rw [Metric.continuous_iff]
  intro a ε hε
  -- ⊢ ∃ δ > 0, ∀ (a_1 : ℝ), dist a_1 a < δ → dist (2 * a_1 + 1) (2 * a + 1) < ε
  refine ⟨ε / 2, by positivity, ?_⟩
  intro x hx
  rw [Real.dist_eq] at hx ⊢
  -- hx : |x - a| < ε / 2     ⊢ |2 * x + 1 - (2 * a + 1)| < ε
  have h : 2 * x + 1 - (2 * a + 1) = 2 * (x - a) := by ring
  rw [h, abs_mul, abs_two]
  linarith

-- ▶ Block 312 · Chapter 17: Filters, Limits and Topology · Open, closed, compact · page 137 (French edition: page 143)
open Set

example : IsOpen (Ioo (0 : ℝ) 1) := isOpen_Ioo
example : IsClosed (Icc (0 : ℝ) 1) := isClosed_Icc
example : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc

-- ▶ Block 313 · Chapter 17: Filters, Limits and Topology · Open, closed, compact · page 137 (French edition: page 143)
example (f : ℝ → ℝ) (hf : Continuous f) : IsOpen {x | 0 < f x} :=
  isOpen_lt continuous_const hf

example (f : ℝ → ℝ) (hf : Continuous f) : IsClosed {x | f x ≤ 3} :=
  isClosed_le hf continuous_const

example (f : ℝ → ℝ) (hf : Continuous f) : IsOpen (f ⁻¹' Ioo 0 1) :=
  isOpen_Ioo.preimage hf

-- ▶ Block 314 · Chapter 17: Filters, Limits and Topology · Open, closed, compact · page 137 (French edition: page 143)
example : IsOpen {x : ℝ | 0 < x} := by
  rw [Metric.isOpen_iff]
  intro x hx
  -- hx : x ∈ {x | 0 < x}     ⊢ ∃ ε > 0, Metric.ball x ε ⊆ {x | 0 < x}
  refine ⟨x, hx, ?_⟩
  intro y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have h := abs_lt.mp hy
  -- h : -x < y - x ∧ y - x < x     ⊢ y ∈ {x | 0 < x}
  change 0 < y
  linarith

-- ▶ Block 315 · Chapter 17: Filters, Limits and Topology · The big theorems of one-variable analysis · page 138 (French edition: page 144)
example (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    ∃ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, f y ≤ f x := by
  have hne : (Icc (0 : ℝ) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hf
  exact ⟨x, hx, fun y hy ↦ hmax hy⟩

-- ▶ Block 316 · Chapter 17: Filters, Limits and Topology · The big theorems of one-variable analysis · page 138 (French edition: page 144)
#check @intermediate_value_Icc
-- a ≤ b → ∀ {f : α → δ},
--   ContinuousOn f (Icc a b) → Icc (f a) (f b) ⊆ f '' Icc a b

example : ∃ x ∈ Icc (0 : ℝ) 1, x ^ 3 + x = 1 := by
  have hf : ContinuousOn (fun x : ℝ ↦ x ^ 3 + x) (Icc 0 1) := by fun_prop
  have h := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf
  -- h : Icc (0 ^ 3 + 0) (1 ^ 3 + 1) ⊆ (fun x ↦ x ^ 3 + x) '' Icc 0 1
  apply h
  -- ⊢ 1 ∈ Icc (0 ^ 3 + 0) (1 ^ 3 + 1)
  constructor <;> norm_num

-- ▶ Block 317 · Chapter 17: Filters, Limits and Topology · Metric and normed spaces · page 138 (French edition: page 144)
section
variable {X : Type*} [MetricSpace X] (x y z : X)

example : dist x z ≤ dist x y + dist y z := dist_triangle x y z
example : dist x y = dist y x := dist_comm x y
example : dist x y = 0 ↔ x = y := dist_eq_zero
end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) (c : ℝ)

example : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
example : ‖c • x‖ = |c| * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs]
example : dist x y = ‖x - y‖ := dist_eq_norm x y
example : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
end

-- ▶ Block 318 · Chapter 17: Filters, Limits and Topology · Series · page 139 (French edition: page 145)
example : ∑' n : ℕ, (1 / 2 : ℝ) ^ n = 2 := tsum_geometric_two

example : Summable (fun n : ℕ ↦ (1 / 3 : ℝ) ^ n) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

example : ∑' n : ℕ, (1 / 3 : ℝ) ^ n = 3 / 2 := by
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  -- ⊢ (1 - 1 / 3)⁻¹ = 3 / 2
  norm_num
