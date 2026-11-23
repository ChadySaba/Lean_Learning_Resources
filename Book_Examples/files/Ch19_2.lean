import Mathlib
-- ▶ Block 351 · Chapter 19: Measure Theory and Integration · Exercises · page 160 (French edition: page 168) · exercise: errors are normal until you solve it

open MeasureTheory Set Filter Topology ENNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

-- Exercise 1.
example : volume (Ioo (1 : ℝ) 4) = 3 := by
  sorry

-- Exercise 2.
example : MeasurableSet (Icc (0 : ℝ) 1 ∪ {5}) := by
  sorry

-- Exercise 3.
example (s t : Set α) : μ (s ∩ t) ≤ μ s := by
  sorry

-- Exercise 4. Almost-everywhere inequalities are transitive.
example (f g h : α → ℝ) (h₁ : f ≤ᵐ[μ] g) (h₂ : g ≤ᵐ[μ] h) : f ≤ᵐ[μ] h := by
  sorry

-- Exercise 5. Linearity, with the integrability it needs.
example (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, (f x + 3 * g x) ∂μ = ∫ x, f x ∂μ + 3 * ∫ x, g x ∂μ := by
  sorry

-- Exercise 6. A nonnegative function with zero integral vanishes almost everywhere.
example (f : α → ℝ) (hf : Integrable f μ) (h0 : ∀ x, 0 ≤ f x) (h : ∫ x, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  sorry

-- Exercise 7. A bounded measurable function is integrable on a finite measure space.
example [IsFiniteMeasure μ] (f : α → ℝ) (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (h : ∀ x, |f x| ≤ C) : Integrable f μ := by
  sorry

-- Exercise 8. Compute the integrals, then take the limit.
example : Tendsto (fun n : ℕ ↦ ∫ x in (0:ℝ)..1, x ^ n) atTop (𝓝 0) := by
  sorry
