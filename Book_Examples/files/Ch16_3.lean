import Mathlib
-- ▶ Block 296 · Chapter 16: Algebraic Structures · Solutions · page 130 (French edition: page 136)

variable {G H : Type*} [Group G] [Group H]

-- Exercise 1.
example (a b : G) (h : a * b = b * a) : a * b⁻¹ = b⁻¹ * a := by
  calc a * b⁻¹ = b⁻¹ * (b * a) * b⁻¹ := by group
    _ = b⁻¹ * (a * b) * b⁻¹ := by rw [h]
    _ = b⁻¹ * a := by group

-- Exercise 2.
example (f : G →* H) (a : G) (ha : a ∈ f.ker) (g : G) : g * a * g⁻¹ ∈ f.ker := by
  rw [MonoidHom.mem_ker] at *
  -- ha : f a = 1     ⊢ f (g * a * g⁻¹) = 1
  rw [map_mul, map_mul, ha, mul_one, ← map_mul, mul_inv_cancel, map_one]

-- Exercise 3.
example (K L : Subgroup G) (a b : G) (ha : a ∈ K ⊓ L) (hb : b ∈ K ⊓ L) : a * b ∈ K ⊓ L := by
  rw [Subgroup.mem_inf] at *
  exact ⟨K.mul_mem ha.1 hb.1, L.mul_mem ha.2 hb.2⟩

-- Exercise 4.
def tripleHom : ℤ →+ ℤ where
  toFun n := 3 * n
  map_zero' := by simp
  map_add' := by
    intro a b
    ring

-- Exercise 5.
example (f : G →* H) (hf : ∀ a, f a = 1 → a = 1) : Function.Injective f := by
  intro a b h
  have h1 : f (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := hf _ h1
  -- h2 : a * b⁻¹ = 1
  calc a = a * b⁻¹ * b := by group
    _ = 1 * b := by rw [h2]
    _ = b := one_mul b

-- Exercise 6.
example {R : Type*} [Ring R] (a : R) (h : a + a = a) : a = 0 := by
  have h' : a + a = a + 0 := by rw [h, add_zero]
  exact add_left_cancel h'
