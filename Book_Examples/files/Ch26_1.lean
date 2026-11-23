import Mathlib
-- ▶ Block 439 · Chapter 26: Lean and AI Tools · Checking a proof you did not write · page 216 (French edition: page 226)
open Filter Topology

-- "The square of a real number is positive."
axiom helper (x : ℝ) : 0 < x ^ 2
theorem thmA (x : ℝ) : 0 < x ^ 2 := helper x

#print axioms thmA
-- 'thmA' depends on axioms: [helper, propext, Classical.choice, Quot.sound]

-- "Every real sequence converges."
theorem thmC (u : ℕ → ℝ) (h : ∀ n, u (n + 1) < u n ∧ u n < u (n + 1)) :
    ∃ l, Tendsto u atTop (𝓝 l) := by
  have := h 0
  linarith [this.1, this.2]

-- "Every real number can be divided by zero."
theorem thmD (x : ℝ) : x / 0 = 0 := div_zero x

-- "2 to the power 20 is 1048576."  True, and proved outside the kernel.
theorem thmE : (2 : ℕ) ^ 20 = 1048576 := by native_decide

#print axioms thmE
-- 'thmE' depends on axioms: [propext, thmE._native.native_decide.ax_1_1]
