import Mathlib
-- ▶ Block 336 · Chapter 18: Calculus · Exercises · page 150 (French edition: page 158) · exercise: errors are normal until you solve it

open Real Set

-- Exercise 1. Two rules, then add.
example (x : ℝ) : HasDerivAt (fun x : ℝ ↦ x ^ 4 + 2 * x) (4 * x ^ 3 + 2) x := by
  sorry

-- Exercise 2. The product rule, with no adjustment needed.
example (x : ℝ) : HasDerivAt (fun x : ℝ ↦ Real.exp x * Real.cos x)
    (Real.exp x * Real.cos x + Real.exp x * (-Real.sin x)) x := by
  sorry

-- Exercise 3. The chain rule through sin.
example (x : ℝ) : HasDerivAt (fun x : ℝ ↦ Real.sin (x ^ 2)) (Real.cos (x ^ 2) * (2 * x)) x := by
  sorry

-- Exercise 4.
example : Differentiable ℝ (fun x : ℝ ↦ Real.sin (x ^ 2) + Real.exp (3 * x)) := by
  sorry

-- Exercise 5. Reduce to the sign of the derivative.
example : StrictMono (fun x : ℝ ↦ x ^ 5 + 2 * x) := by
  sorry

-- Exercise 6.
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) (h : ∀ x, deriv f x = 0) : f 1 = f 0 := by
  sorry

-- Exercise 7.
example : ∫ x in (0:ℝ)..2, x ^ 3 = 4 := by
  sorry

-- Exercise 8. A constant factor, then the integral of the identity.
example : ∫ x in (1:ℝ)..2, (2 * x) = 3 := by
  sorry

-- Exercise 9. Find the primitive, then use the fundamental theorem.
example : ∫ x in (0:ℝ)..1, 3 * x ^ 2 * Real.exp (x ^ 3) = Real.exp 1 - 1 := by
  sorry
