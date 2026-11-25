import Mathlib
-- ▶ Block 278 · Chapter 16: Algebraic Structures · Working in an arbitrary group · page 123 (French edition: page 129)

section
variable {G : Type*} [Group G] (a b c : G)

#check mul_assoc a b c        -- a * b * c = a * (b * c)
#check one_mul a              -- 1 * a = a
#check mul_one a              -- a * 1 = a
#check inv_mul_cancel a       -- a⁻¹ * a = 1
#check mul_inv_cancel a       -- a * a⁻¹ = 1
#check inv_inv a              -- a⁻¹⁻¹ = a
#check mul_inv_rev a b        -- (a * b)⁻¹ = b⁻¹ * a⁻¹

-- ▶ Block 279 · Chapter 16: Algebraic Structures · Working in an arbitrary group · page 123 (French edition: page 129)
example (h : a * b = 1) : b = a⁻¹ := by
  calc b = 1 * b := (one_mul b).symm
    _ = a⁻¹ * a * b := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * b) := mul_assoc _ _ _
    _ = a⁻¹ * 1 := by rw [h]
    _ = a⁻¹ := mul_one _

-- ▶ Block 280 · Chapter 16: Algebraic Structures · Working in an arbitrary group · page 123 (French edition: page 129)
example : a * b * b⁻¹ * a⁻¹ = 1 := by group
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by simp
example (h : a * b = a * c) : b = c := mul_left_cancel h

-- ▶ Block 281 · Chapter 16: Algebraic Structures · Working in an arbitrary group · page 123 (French edition: page 129)
example (h : ∀ x : G, x * x = 1) : a * b = b * a := by
  have h1 : a * b * (a * b) = 1 := h (a * b)
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h b)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha, hb]
end

-- ▶ Block 282 · Chapter 16: Algebraic Structures · Multiplicative and additive · page 124 (French edition: page 130)
example {A : Type*} [AddCommGroup A] (x y z : A) : x - (y - z) = x - y + z := by abel

-- ▶ Block 283 · Chapter 16: Algebraic Structures · Rings, fields, modules · page 124 (French edition: page 130)
section
variable {R : Type*} [CommRing R] (a b : R)

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (h : a + b = 0) : b = -a := by
  linear_combination h
end

example {K : Type*} [Field K] (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    1 / x + 1 / y = (x + y) / (x * y) := by
  field_simp
  ring

-- ▶ Block 284 · Chapter 16: Algebraic Structures · Rings, fields, modules · page 125 (French edition: page 131)
#synth CommRing ℤ             -- Int.instCommRing
#synth Field ℚ                -- Rat.instField
#synth CommRing (ZMod 6)      -- ZMod.commRing 6

#eval (3 : ZMod 7) * 5        -- 1

example : ∀ x : ZMod 4, x ^ 2 = 0 ∨ x ^ 2 = 1 := by decide

-- ▶ Block 285 · Chapter 16: Algebraic Structures · Homomorphisms are bundled · page 125 (French edition: page 131)
section
variable {G H K : Type*} [Group G] [Group H] [Group K]

example (f : G →* H) (a b : G) : f (a * b) = f a * f b := map_mul f a b
example (f : G →* H) : f 1 = 1 := map_one f
example (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ := map_inv f a
example (f : G →* H) (a : G) (n : ℕ) : f (a ^ n) = f a ^ n := map_pow f a n

example (f : G →* H) (g : H →* K) : G →* K := g.comp f
end

-- ▶ Block 286 · Chapter 16: Algebraic Structures · Homomorphisms are bundled · page 126 (French edition: page 132)
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : R) :
    f (a * b + 1) = f a * f b + 1 := by
  rw [map_add, map_mul, map_one]

example {E F : Type*} [AddCommGroup E] [AddCommGroup F] [Module ℝ E] [Module ℝ F]
    (f : E →ₗ[ℝ] F) (c : ℝ) (x y : E) : f (c • x + y) = c • f x + f y := by
  simp

-- ▶ Block 287 · Chapter 16: Algebraic Structures · Homomorphisms are bundled · page 126 (French edition: page 132)
def doubleHom : ℤ →+ ℤ where
  toFun n := 2 * n
  map_zero' := by simp
  map_add' := by
    intro a b
    ring

#eval doubleHom 21        -- 42

example (a b : ℤ) : doubleHom (a + b) = doubleHom a + doubleHom b :=
  map_add doubleHom a b

-- ▶ Block 288 · Chapter 16: Algebraic Structures · Subobjects · page 126 (French edition: page 132)
section
variable {G H : Type*} [Group G] [Group H]

example (K : Subgroup G) (a b : G) (ha : a ∈ K) (hb : b ∈ K) : a * b ∈ K := K.mul_mem ha hb
example (K : Subgroup G) : (1 : G) ∈ K := K.one_mem
example (K : Subgroup G) (a : G) (ha : a ∈ K) : a⁻¹ ∈ K := K.inv_mem ha

-- ▶ Block 289 · Chapter 16: Algebraic Structures · Subobjects · page 126 (French edition: page 133)
example (K L : Subgroup G) (a : G) : a ∈ K ⊓ L ↔ a ∈ K ∧ a ∈ L := Subgroup.mem_inf
example (a : G) : a ∈ (⊥ : Subgroup G) ↔ a = 1 := Subgroup.mem_bot

-- ▶ Block 290 · Chapter 16: Algebraic Structures · Subobjects · page 126 (French edition: page 133)
def evenInts : AddSubgroup ℤ where
  carrier := {n | Even n}
  zero_mem' := Even.zero
  add_mem' := by
    intro a b ha hb
    exact Even.add ha hb
  neg_mem' := by
    intro a ha
    exact Even.neg ha

example : (4 : ℤ) ∈ evenInts := ⟨2, rfl⟩

-- ▶ Block 291 · Chapter 16: Algebraic Structures · Subobjects · page 127 (French edition: page 133)
def myCenter : Subgroup G where
  carrier := {z | ∀ g : G, g * z = z * g}
  one_mem' := by
    intro g
    rw [mul_one, one_mul]
  mul_mem' := by
    intro a b ha hb g
    -- ha : a ∈ {z | ∀ (g : G), g * z = z * g}, that is, ∀ g, g * a = a * g; hb alike
    -- ⊢ g * (a * b) = a * b * g
    rw [← mul_assoc, ha g, mul_assoc, hb g, ← mul_assoc]
  inv_mem' := by
    intro a ha g
    -- ⊢ g * a⁻¹ = a⁻¹ * g
    have h := congrArg (·⁻¹) (ha g⁻¹)
    -- h : (g⁻¹ * a)⁻¹ = (a * g⁻¹)⁻¹
    simp only [mul_inv_rev, inv_inv] at h
    -- h : a⁻¹ * g = g * a⁻¹
    exact h.symm

-- ▶ Block 292 · Chapter 16: Algebraic Structures · Subobjects · page 127 (French edition: page 133)
example (K : Subgroup G) : Group K := inferInstance
example (K : Subgroup G) (x : K) : (x : G) ∈ K := x.property

-- ▶ Block 293 · Chapter 16: Algebraic Structures · Kernels, images, quotients · page 127 (French edition: page 133)
example (f : G →* H) (a : G) : a ∈ f.ker ↔ f a = 1 := MonoidHom.mem_ker
example (f : G →* H) (y : H) : y ∈ f.range ↔ ∃ x, f x = y := MonoidHom.mem_range

example (f : G →* H) (a b : G) (ha : a ∈ f.ker) (hb : b ∈ f.ker) : a * b ∈ f.ker := by
  rw [MonoidHom.mem_ker] at *
  -- ha : f a = 1     hb : f b = 1     ⊢ f (a * b) = 1
  rw [map_mul, ha, hb, mul_one]

example (f : G →* H) : f.ker = ⊥ ↔ Function.Injective f := MonoidHom.ker_eq_bot_iff f
end

-- ▶ Block 294 · Chapter 16: Algebraic Structures · Kernels, images, quotients · page 128 (French edition: page 134)
section
variable {G H : Type*} [Group G] [Group H] (N : Subgroup G) [N.Normal]

example : Group (G ⧸ N) := inferInstance

example (a : G) : (a : G ⧸ N) = 1 ↔ a ∈ N := QuotientGroup.eq_one_iff a

example (f : G →* H) (h : N ≤ f.ker) : G ⧸ N →* H := QuotientGroup.lift N f h

-- The first isomorphism theorem.
noncomputable example (f : G →* H) : G ⧸ f.ker ≃* f.range :=
  QuotientGroup.quotientKerEquivRange f
end
