import Mathlib
-- ▶ Block 337 · Chapter 18: Calculus · Solutions · page 151 (French edition: page 159)

open Real Set

-- Exercise 1.
example (x : ℝ) : HasDerivAt (fun x : ℝ ↦ x ^ 4 + 2 * x) (4 * x ^ 3 + 2) x := by
  have h1 : HasDerivAt (fun x : ℝ ↦ x ^ 4) (4 * x ^ 3) x := by simpa using hasDerivAt_pow 4 x
  have h2 : HasDerivAt (fun x : ℝ ↦ 2 * x) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
  exact h1.add h2

-- Exercise 2.
example (x : ℝ) : HasDerivAt (fun x : ℝ ↦ Real.exp x * Real.cos x)
    (Real.exp x * Real.cos x + Real.exp x * (-Real.sin x)) x :=
  (Real.hasDerivAt_exp x).mul (Real.hasDerivAt_cos x)

-- Exercise 3.
example (x : ℝ) : HasDerivAt (fun x : ℝ ↦ Real.sin (x ^ 2)) (Real.cos (x ^ 2) * (2 * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  exact h1.sin

-- Exercise 4.
example : Differentiable ℝ (fun x : ℝ ↦ Real.sin (x ^ 2) + Real.exp (3 * x)) := by
  fun_prop

-- Exercise 5.
example : StrictMono (fun x : ℝ ↦ x ^ 5 + 2 * x) := by
  apply strictMono_of_deriv_pos
  intro x
  have h : HasDerivAt (fun x : ℝ ↦ x ^ 5 + 2 * x) (5 * x ^ 4 + 2) x := by
    have h1 : HasDerivAt (fun x : ℝ ↦ x ^ 5) (5 * x ^ 4) x := by simpa using hasDerivAt_pow 5 x
    have h2 : HasDerivAt (fun x : ℝ ↦ 2 * x) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
    exact h1.add h2
  rw [h.deriv]
  -- ⊢ 0 < 5 * x ^ 4 + 2
  positivity

-- Exercise 6.
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) (h : ∀ x, deriv f x = 0) : f 1 = f 0 :=
  is_const_of_deriv_eq_zero hf h 1 0

-- Exercise 7.
example : ∫ x in (0:ℝ)..2, x ^ 3 = 4 := by
  rw [integral_pow]
  norm_num

-- Exercise 8.
example : ∫ x in (1:ℝ)..2, (2 * x) = 3 := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  norm_num

-- Exercise 9. The primitive is exp (x ^ 3).
example : ∫ x in (0:ℝ)..1, 3 * x ^ 2 * Real.exp (x ^ 3) = Real.exp 1 - 1 := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ ↦ Real.exp (x ^ 3)) (3 * x ^ 2 * Real.exp (x ^ 3)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ ↦ x ^ 3) (3 * x ^ 2) x := by simpa using hasDerivAt_pow 3 x
    convert h1.exp using 1
    ring
  have hcont : Continuous (fun x : ℝ ↦ 3 * x ^ 2 * Real.exp (x ^ 3)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x)
    (hcont.intervalIntegrable 0 1)]
  norm_num
