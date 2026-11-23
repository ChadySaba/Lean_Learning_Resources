import Mathlib
-- ▶ Block 321 · Chapter 18: Calculus · Three ways to speak of a derivative · page 143 (French edition: page 149)

open Real Set

example (f : ℝ → ℝ) (f' x : ℝ) (h : HasDerivAt f f' x) : deriv f x = f' := h.deriv

example (f : ℝ → ℝ) (f' x : ℝ) (h : HasDerivAt f f' x) : DifferentiableAt ℝ f x :=
  h.differentiableAt

example (f : ℝ → ℝ) (x : ℝ) (h : DifferentiableAt ℝ f x) : HasDerivAt f (deriv f x) x :=
  h.hasDerivAt

-- ▶ Block 322 · Chapter 18: Calculus · Computing a derivative · page 144 (French edition: page 150)
example (x : ℝ) : HasDerivAt (fun x : ℝ ↦ Real.sin x * Real.exp x)
    (Real.cos x * Real.exp x + Real.sin x * Real.exp x) x :=
  (Real.hasDerivAt_sin x).mul (Real.hasDerivAt_exp x)

-- ▶ Block 323 · Chapter 18: Calculus · Computing a derivative · page 144 (French edition: page 150)
example (x : ℝ) : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * x) x := by
  have h := hasDerivAt_pow 2 x
  -- h : HasDerivAt (fun x ↦ x ^ 2) (↑2 * x ^ (2 - 1)) x
  simpa using h

-- ▶ Block 324 · Chapter 18: Calculus · Computing a derivative · page 145 (French edition: page 151)
example (x : ℝ) : HasDerivAt (fun x : ℝ ↦ (x ^ 2 + 1) ^ 5) (10 * x * (x ^ 2 + 1) ^ 4) x := by
  have h1 : HasDerivAt (fun x : ℝ ↦ x ^ 2 + 1) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const 1
  have h2 := h1.pow 5
  -- h2 : HasDerivAt ((fun x ↦ x ^ 2 + 1) ^ 5) (↑5 * (x ^ 2 + 1) ^ (5 - 1) * (2 * x)) x
  convert h2 using 1
  -- ⊢ 10 * x * (x ^ 2 + 1) ^ 4 = ↑5 * (x ^ 2 + 1) ^ (5 - 1) * (2 * x)
  ring

-- ▶ Block 325 · Chapter 18: Calculus · Computing a derivative · page 145 (French edition: page 151)
example (x : ℝ) : HasDerivAt (fun x : ℝ ↦ x ^ 2 + 3 * x) (2 * x + 3) x := by
  have h1 : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun x : ℝ ↦ 3 * x) 3 x := by simpa using (hasDerivAt_id x).const_mul 3
  exact h1.add h2

example (x : ℝ) : HasDerivAt (fun x : ℝ ↦ Real.exp (x ^ 2)) (Real.exp (x ^ 2) * (2 * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  exact h1.exp

-- ▶ Block 326 · Chapter 18: Calculus · Statements with deriv · page 145 (French edition: page 151)
example (x : ℝ) : deriv (fun x : ℝ ↦ Real.sin (x ^ 2)) x = 2 * x * Real.cos (x ^ 2) := by
  have h : HasDerivAt (fun x : ℝ ↦ Real.sin (x ^ 2)) (Real.cos (x ^ 2) * (2 * x)) x := by
    have h1 : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    exact h1.sin
  rw [h.deriv]
  ring

-- ▶ Block 327 · Chapter 18: Calculus · Statements with deriv · page 145 (French edition: page 152)
example (x : ℝ) : deriv (fun x : ℝ ↦ x ^ 2) x = 2 * x := by simp
example (x : ℝ) : deriv Real.exp x = Real.exp x := by simp

#check @deriv_fun_add
-- DifferentiableAt 𝕜 f x → DifferentiableAt 𝕜 g x →
--   deriv (fun y ↦ f y + g y) x = deriv f x + deriv g x

example (x : ℝ) : deriv (fun x : ℝ ↦ x ^ 2 + 3 * x) x = 2 * x + 3 := by
  rw [deriv_fun_add (by fun_prop) (by fun_prop)]
  simp

-- ▶ Block 328 · Chapter 18: Calculus · Differentiability · page 146 (French edition: page 152)
example : Differentiable ℝ (fun x : ℝ ↦ Real.exp (x ^ 2) * Real.sin x) := by fun_prop

example (x : ℝ) (hx : x ≠ 0) : DifferentiableAt ℝ (fun x : ℝ ↦ 1 / x) x := by
  fun_prop (disch := assumption)

example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : Continuous f := hf.continuous

-- ▶ Block 329 · Chapter 18: Calculus · The theorems · page 146 (French edition: page 153)
example (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hfc hfd

example (f : ℝ → ℝ) (hf : Differentiable ℝ f) (h : ∀ x, deriv f x = 0) (x y : ℝ) :
    f x = f y :=
  is_const_of_deriv_eq_zero hf h x y

-- ▶ Block 330 · Chapter 18: Calculus · Monotonicity from the sign of the derivative · page 147 (French edition: page 153)
example : StrictMono (fun x : ℝ ↦ x ^ 3 + x) := by
  apply strictMono_of_deriv_pos
  intro x
  -- ⊢ 0 < deriv (fun x ↦ x ^ 3 + x) x
  have h : HasDerivAt (fun x : ℝ ↦ x ^ 3 + x) (3 * x ^ 2 + 1) x := by
    have h1 : HasDerivAt (fun x : ℝ ↦ x ^ 3) (3 * x ^ 2) x := by simpa using hasDerivAt_pow 3 x
    exact h1.add (hasDerivAt_id x)
  rw [h.deriv]
  -- ⊢ 0 < 3 * x ^ 2 + 1
  positivity

-- ▶ Block 331 · Chapter 18: Calculus · Monotonicity from the sign of the derivative · page 147 (French edition: page 153)
example (x : ℝ) (hx : 0 ≤ x) : 1 + x ≤ Real.exp x := by
  have hmono : MonotoneOn (fun t : ℝ ↦ Real.exp t - t) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop          -- continuity on [0, ∞)
    · fun_prop          -- differentiability on the interior
    · intro t ht
      rw [interior_Ici] at ht
      -- ht : t ∈ Ioi 0     ⊢ 0 ≤ deriv (fun t ↦ rexp t - t) t
      have h : HasDerivAt (fun t : ℝ ↦ Real.exp t - t) (Real.exp t - 1) t :=
        (Real.hasDerivAt_exp t).sub (hasDerivAt_id t)
      rw [h.deriv]
      have h1 : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp (le_of_lt ht)
      linarith
  have h0 := hmono (mem_Ici.mpr le_rfl) hx hx
  -- h0 : (fun t ↦ rexp t - t) 0 ≤ (fun t ↦ rexp t - t) x
  dsimp only at h0
  rw [Real.exp_zero] at h0
  -- h0 : 1 - 0 ≤ rexp x - x
  linarith

-- ▶ Block 332 · Chapter 18: Calculus · Integrals over an interval · page 147 (French edition: page 154)
example : ∫ x in (0:ℝ)..1, x ^ 2 = 1 / 3 := by
  rw [integral_pow]
  -- ⊢ (1 ^ (2 + 1) - 0 ^ (2 + 1)) / (↑2 + 1) = 1 / 3
  norm_num

example : ∫ x in (0:ℝ)..π, Real.sin x = 2 := by
  rw [integral_sin]
  -- ⊢ cos 0 - cos π = 2
  norm_num [Real.cos_zero, Real.cos_pi]

example (a b : ℝ) : ∫ x in a..b, Real.exp x = Real.exp b - Real.exp a := integral_exp

-- ▶ Block 333 · Chapter 18: Calculus · Integrals over an interval · page 149 (French edition: page 155)
example : ∫ x in (0:ℝ)..2, (3 * x ^ 2 + 1) = 10 := by
  have h1 : IntervalIntegrable (fun x : ℝ ↦ 3 * x ^ 2) MeasureTheory.volume 0 2 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ 3 * x ^ 2)).intervalIntegrable 0 2
  have h2 : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) MeasureTheory.volume 0 2 :=
    continuous_const.intervalIntegrable 0 2
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const]
  -- ⊢ 3 * ((2 ^ (2 + 1) - 0 ^ (2 + 1)) / (↑2 + 1)) + (2 - 0) • 1 = 10
  norm_num

-- ▶ Block 334 · Chapter 18: Calculus · The fundamental theorem of calculus · page 149 (French edition: page 156)
-- The integral of a derivative.
example (f f' : ℝ → ℝ) (a b : ℝ) (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') :
    ∫ x in a..b, f' x = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hf x) (hf'.intervalIntegrable a b)

-- The derivative of an integral.
example (f : ℝ → ℝ) (hf : Continuous f) (a x : ℝ) :
    deriv (fun u ↦ ∫ t in a..u, f t) x = f x :=
  hf.deriv_integral f a x

-- ▶ Block 335 · Chapter 18: Calculus · The fundamental theorem of calculus · page 149 (French edition: page 156)
example : ∫ x in (0:ℝ)..1, 2 * x * Real.exp (x ^ 2) = Real.exp 1 - 1 := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ ↦ Real.exp (x ^ 2)) (2 * x * Real.exp (x ^ 2)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have h2 := h1.exp
    -- h2 : HasDerivAt (fun x ↦ rexp (x ^ 2)) (rexp (x ^ 2) * (2 * x)) x
    convert h2 using 1
    ring
  have hcont : Continuous (fun x : ℝ ↦ 2 * x * Real.exp (x ^ 2)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x)
    (hcont.intervalIntegrable 0 1)]
  -- ⊢ rexp (1 ^ 2) - rexp (0 ^ 2) = rexp 1 - 1
  norm_num
