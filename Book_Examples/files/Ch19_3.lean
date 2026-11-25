import Mathlib
-- ▶ Block 352 · Chapter 19: Measure Theory and Integration · Solutions · page 161 (French edition: page 169)

open MeasureTheory Set Filter Topology ENNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

-- Exercise 1.
example : volume (Ioo (1 : ℝ) 4) = 3 := by
  rw [Real.volume_Ioo]
  norm_num

-- Exercise 2.
example : MeasurableSet (Icc (0 : ℝ) 1 ∪ {5}) :=
  measurableSet_Icc.union (measurableSet_singleton 5)

-- Exercise 3.
example (s t : Set α) : μ (s ∩ t) ≤ μ s := measure_mono inter_subset_left

-- Exercise 4.
example (f g h : α → ℝ) (h₁ : f ≤ᵐ[μ] g) (h₂ : g ≤ᵐ[μ] h) : f ≤ᵐ[μ] h := by
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  -- hx₁ : f x ≤ g x     hx₂ : g x ≤ h x     ⊢ f x ≤ h x
  exact le_trans hx₁ hx₂

-- Exercise 5.
example (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, (f x + 3 * g x) ∂μ = ∫ x, f x ∂μ + 3 * ∫ x, g x ∂μ := by
  rw [integral_add hf (hg.const_mul 3), integral_const_mul]

-- Exercise 6.
example (f : α → ℝ) (hf : Integrable f μ) (h0 : ∀ x, 0 ≤ f x) (h : ∫ x, f x ∂μ = 0) :
    f =ᵐ[μ] 0 :=
  (integral_eq_zero_iff_of_nonneg h0 hf).mp h

-- Exercise 7.
example [IsFiniteMeasure μ] (f : α → ℝ) (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (h : ∀ x, |f x| ≤ C) : Integrable f μ := by
  apply (integrable_const C).mono' hf
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact h x

-- Exercise 8.
example : Tendsto (fun n : ℕ ↦ ∫ x in (0:ℝ)..1, x ^ n) atTop (𝓝 0) := by
  have h : ∀ n : ℕ, ∫ x in (0:ℝ)..1, x ^ n = 1 / (n + 1 : ℝ) := by
    intro n
    rw [integral_pow]
    simp
  simp only [h]
  exact tendsto_one_div_add_atTop_nhds_zero_nat
