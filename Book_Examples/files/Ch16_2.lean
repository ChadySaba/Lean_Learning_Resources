import Mathlib
-- ▶ Block 295 · Chapter 16: Algebraic Structures · Exercises · page 129 (French edition: page 134) · exercise: errors are normal until you solve it

variable {G H : Type*} [Group G] [Group H]

-- Exercise 1. If a and b commute, so do a and b⁻¹. A calc with three lines:
-- the first and last are closed by `group`.
example (a b : G) (h : a * b = b * a) : a * b⁻¹ = b⁻¹ * a := by
  sorry

-- Exercise 2. The kernel is stable under conjugation.
example (f : G →* H) (a : G) (ha : a ∈ f.ker) (g : G) : g * a * g⁻¹ ∈ f.ker := by
  sorry

-- Exercise 3. The intersection of two subgroups is closed under multiplication.
example (K L : Subgroup G) (a b : G) (ha : a ∈ K ⊓ L) (hb : b ∈ K ⊓ L) : a * b ∈ K ⊓ L := by
  sorry

-- Exercise 4. Define multiplication by 3 as an additive homomorphism.
def tripleHom : ℤ →+ ℤ where
  toFun n := 3 * n
  map_zero' := sorry
  map_add' := sorry

-- Exercise 5. A homomorphism with trivial kernel is injective.
-- First show f (a * b⁻¹) = 1.
example (f : G →* H) (hf : ∀ a, f a = 1 → a = 1) : Function.Injective f := by
  sorry

-- Exercise 6. In any ring, an element equal to its double is zero.
example {R : Type*} [Ring R] (a : R) (h : a + a = a) : a = 0 := by
  sorry
