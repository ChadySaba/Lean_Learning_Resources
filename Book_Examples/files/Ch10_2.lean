import Mathlib
-- ▶ Block 158 · Chapter 10: Structures and Type Classes · Exercises · page 71 (French edition: page 73) · exercise: errors are normal until you solve it

-- Exercise 1. A closed interval, and the fact that its length is nonnegative.
structure ClosedInterval where
  lo : ℝ
  hi : ℝ
  le : lo ≤ hi

def ClosedInterval.length (I : ClosedInterval) : ℝ := I.hi - I.lo

def ClosedInterval.unit : ClosedInterval := { lo := 0, hi := 1, le := sorry }

theorem ClosedInterval.length_nonneg (I : ClosedInterval) : 0 ≤ I.length := by
  sorry

-- Exercise 2. Give Point a negation, so that the example below holds by rfl.
structure Point where
  x : ℝ
  y : ℝ

instance : Neg Point where
  neg p := sorry

example (p : Point) : (-p).x = -p.x := rfl

-- Exercise 3. The composition of two linear maps is linear.
structure IsLinear (f : ℝ → ℝ) : Prop where
  map_add : ∀ x y, f (x + y) = f x + f y
  map_smul : ∀ c x, f (c * x) = c * f x

theorem IsLinear.comp {f g : ℝ → ℝ} (hf : IsLinear f) (hg : IsLinear g) :
    IsLinear (fun x ↦ f (g x)) where
  map_add := by
    sorry
  map_smul := by
    sorry

-- Exercise 4. Valid in every group. Use ← mul_assoc, inv_mul_cancel, one_mul.
example {G : Type*} [Group G] (a b : G) : a⁻¹ * (a * b) = b := by
  sorry

-- Exercise 5. Declare the instance: the area of a triangle is base * height / 2.
class HasArea (α : Type) where
  area : α → ℝ

structure Triangle where
  base : ℝ
  height : ℝ

-- instance : HasArea Triangle where …

-- Exercise 6. Move a fact from ℕ to ℝ.
example (n : ℕ) (h : n < 5) : (n : ℝ) < 5 := by
  sorry

-- Exercise 7. Valid in every linear order. Use min_le_right and le_trans.
example {α : Type*} [LinearOrder α] (a b c : α) (h : b ≤ c) : min a b ≤ c := by
  sorry
