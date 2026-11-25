import Mathlib
-- ▶ Block 159 · Chapter 10: Structures and Type Classes · Solutions · page 72 (French edition: page 76)

-- Exercise 1.
structure ClosedInterval where
  lo : ℝ
  hi : ℝ
  le : lo ≤ hi

def ClosedInterval.length (I : ClosedInterval) : ℝ := I.hi - I.lo

def ClosedInterval.unit : ClosedInterval := { lo := 0, hi := 1, le := by norm_num }

theorem ClosedInterval.length_nonneg (I : ClosedInterval) : 0 ≤ I.length := by
  unfold ClosedInterval.length
  -- ⊢ 0 ≤ I.hi - I.lo
  have h := I.le
  -- h : I.lo ≤ I.hi
  linarith

-- Exercise 2.
structure Point where
  x : ℝ
  y : ℝ

instance : Neg Point where
  neg p := { x := -p.x, y := -p.y }

example (p : Point) : (-p).x = -p.x := rfl

-- Exercise 3.
structure IsLinear (f : ℝ → ℝ) : Prop where
  map_add : ∀ x y, f (x + y) = f x + f y
  map_smul : ∀ c x, f (c * x) = c * f x

theorem IsLinear.comp {f g : ℝ → ℝ} (hf : IsLinear f) (hg : IsLinear g) :
    IsLinear (fun x ↦ f (g x)) where
  map_add := by
    intro x y
    -- ⊢ f (g (x + y)) = f (g x) + f (g y)
    rw [hg.map_add, hf.map_add]
  map_smul := by
    intro c x
    rw [hg.map_smul, hf.map_smul]

-- Exercise 4.
example {G : Type*} [Group G] (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

-- Exercise 5.
class HasArea (α : Type) where
  area : α → ℝ

structure Triangle where
  base : ℝ
  height : ℝ

noncomputable instance : HasArea Triangle where
  area t := t.base * t.height / 2

-- Exercise 6.
example (n : ℕ) (h : n < 5) : (n : ℝ) < 5 := by
  exact_mod_cast h

-- Exercise 7.
example {α : Type*} [LinearOrder α] (a b c : α) (h : b ≤ c) : min a b ≤ c :=
  le_trans (min_le_right a b) h
