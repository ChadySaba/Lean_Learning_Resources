import Mathlib
-- ▶ Block 14 · Chapter 2: Installing Lean and Starting a Project · Checking the installation · page 14 (French edition: page 16)

#check TopologicalSpace

example : (2 : ℝ) + 2 = 4 := by norm_num

-- ▶ Block 16 · Chapter 2: Installing Lean and Starting a Project · Font · page 18 (French edition: page 20)
-- v ν ∨ ∧ ⊢ ↦ ⟨x, y⟩ x⁻¹ x₁ 𝓝 ∑ ∫ ‖x‖ ∀ ε > 0, ∃ δ > 0

-- ▶ Block 19 · Chapter 2: Installing Lean and Starting a Project · Exercises · page 21 (French edition: page 24) · exercise: errors are normal until you solve it
example : ∀ ε : ℝ, ε > 0 → ∃ δ > 0, δ ≤ ε := fun ε hε ↦ ⟨ε, hε, le_refl ε⟩
