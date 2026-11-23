import Mathlib
-- ▶ Block 338 · Chapter 19: Measure Theory and Integration · The objects · page 153 (French edition: page 160)

open MeasureTheory Set Filter Topology ENNReal

example : volume (Icc (0 : ℝ) 1) = 1 := by simp

example : volume (Icc (2 : ℝ) 5) = 3 := by
  rw [Real.volume_Icc]
  -- ⊢ ENNReal.ofReal (5 - 2) = 3
  norm_num

example : volume ({3} : Set ℝ) = 0 := by simp

-- ▶ Block 339 · Chapter 19: Measure Theory and Integration · Measurability · page 154 (French edition: page 161)
example : MeasurableSet (Icc (0 : ℝ) 1) := measurableSet_Icc

example (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) : MeasurableSet (s ∪ tᶜ) :=
  hs.union ht.compl

example (s : Set ℝ) (hs : IsOpen s) : MeasurableSet s := hs.measurableSet

example (f : ℝ → ℝ) (hf : Continuous f) : Measurable f := hf.measurable

example : Measurable (fun x : ℝ ↦ x ^ 2 + Real.exp x) := by fun_prop

example : MeasurableSet {x : ℝ | 0 < x ∧ x ^ 2 < 2} := by measurability

-- ▶ Block 340 · Chapter 19: Measure Theory and Integration · Measures · page 154 (French edition: page 161)
section
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

example : μ ∅ = 0 := measure_empty

example (s t : Set α) (h : s ⊆ t) : μ s ≤ μ t := measure_mono h

example (s t : Set α) : μ (s ∪ t) ≤ μ s + μ t := measure_union_le s t

example (s t : Set α) (hd : Disjoint s t) (ht : MeasurableSet t) : μ (s ∪ t) = μ s + μ t :=
  measure_union hd ht

example (s : ℕ → Set α) : μ (⋃ n, s n) ≤ ∑' n, μ (s n) := measure_iUnion_le s

-- ▶ Block 341 · Chapter 19: Measure Theory and Integration · Measures · page 154 (French edition: page 161)
example (s t : Set α) (hs : μ s = 0) (ht : μ t = 0) : μ (s ∪ t) = 0 := by
  have h := measure_union_le (μ := μ) s t
  rw [hs, ht, add_zero] at h
  -- h : μ (s ∪ t) ≤ 0
  exact nonpos_iff_eq_zero.mp h

-- ▶ Block 342 · Chapter 19: Measure Theory and Integration · Almost everywhere · page 155 (French edition: page 162)
example (p : α → Prop) : (∀ᵐ x ∂μ, p x) ↔ μ {x | ¬p x} = 0 := ae_iff

-- ▶ Block 343 · Chapter 19: Measure Theory and Integration · Almost everywhere · page 155 (French edition: page 162)
example (f g : α → ℝ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hg : ∀ᵐ x ∂μ, f x ≤ g x) :
    ∀ᵐ x ∂μ, 0 ≤ g x := by
  filter_upwards [hf, hg] with x h1 h2
  -- h1 : 0 ≤ f x     h2 : f x ≤ g x     ⊢ 0 ≤ g x
  linarith

example (f g : α → ℝ) (h : ∀ x, f x = g x) : f =ᵐ[μ] g := Eventually.of_forall h

example (f g h : α → ℝ) (h₁ : f =ᵐ[μ] g) (h₂ : g =ᵐ[μ] h) : f =ᵐ[μ] h := h₁.trans h₂
end

-- ▶ Block 344 · Chapter 19: Measure Theory and Integration · Three integrals · page 155 (French edition: page 163)
example (f : ℝ → ℝ) (a b : ℝ) (h : a ≤ b) : ∫ x in a..b, f x = ∫ x in Ioc a b, f x :=
  intervalIntegral.integral_of_le h

-- ▶ Block 345 · Chapter 19: Measure Theory and Integration · Proving integrability · page 156 (French edition: page 163)
section
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

-- Sums and constant multiples.
example (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x ↦ f x + 2 * g x) μ := by
  fun_prop

-- Constants, on a finite measure space.
example [IsFiniteMeasure μ] (c : ℝ) : Integrable (fun _ : α ↦ c) μ := integrable_const c

-- Domination by an integrable function.
example (f g : α → ℝ) (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ)
    (h : ∀ x, |f x| ≤ g x) : Integrable f μ :=
  hg.mono' hf (Eventually.of_forall h)

-- A continuous function on a compact interval.
example (f : ℝ → ℝ) (hf : Continuous f) : IntegrableOn f (Icc 0 1) := hf.integrableOn_Icc

-- ▶ Block 346 · Chapter 19: Measure Theory and Integration · The rules of the integral · page 157 (French edition: page 164)
example (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, (2 * f x - g x) ∂μ = 2 * ∫ x, f x ∂μ - ∫ x, g x ∂μ := by
  rw [integral_sub (hf.const_mul 2) hg, integral_const_mul]

example (f : α → ℝ) (h : f =ᵐ[μ] 0) : ∫ x, f x ∂μ = 0 := by
  rw [integral_congr_ae h]
  -- ⊢ ∫ (a : α), 0 a ∂μ = 0
  simp

-- ▶ Block 347 · Chapter 19: Measure Theory and Integration · The convergence theorems · page 158 (French edition: page 165)
#check @tendsto_integral_of_dominated_convergence
-- (bound : α → ℝ),
-- (∀ (n : ℕ), AEStronglyMeasurable (F n) μ) →
-- Integrable bound μ →
-- (∀ (n : ℕ), ∀ᵐ (a : α) ∂μ, ‖F n a‖ ≤ bound a) →
-- (∀ᵐ (a : α) ∂μ, Tendsto (fun n ↦ F n a) atTop (𝓝 (f a))) →
-- Tendsto (fun n ↦ ∫ (a : α), F n a ∂μ) atTop (𝓝 (∫ (a : α), f a ∂μ))

-- ▶ Block 348 · Chapter 19: Measure Theory and Integration · The convergence theorems · page 158 (French edition: page 165)
example (F : ℕ → α → ℝ) (f g : α → ℝ) (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hg : Integrable g μ) (hbound : ∀ n x, |F n x| ≤ g x)
    (hlim : ∀ x, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence g hF hg
  · intro n
    filter_upwards with x
    -- ⊢ ‖F n x‖ ≤ g x
    rw [Real.norm_eq_abs]
    exact hbound n x
  · filter_upwards with x
    exact hlim x
end

-- ▶ Block 349 · Chapter 19: Measure Theory and Integration · The convergence theorems · page 158 (French edition: page 165)
example : Tendsto (fun n : ℕ ↦ ∫ x in (0:ℝ)..1, x ^ n) atTop (𝓝 0) := by
  have h : ∀ n : ℕ, ∫ x in (0:ℝ)..1, x ^ n = 1 / (n + 1 : ℝ) := by
    intro n
    rw [integral_pow]
    simp
  simp only [h]
  -- ⊢ Tendsto (fun n ↦ 1 / (↑n + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

-- ▶ Block 350 · Chapter 19: Measure Theory and Integration · Lᵖ spaces · page 159 (French edition: page 166)
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : MemLp (f + g) 2 μ :=
  hf.add hg
