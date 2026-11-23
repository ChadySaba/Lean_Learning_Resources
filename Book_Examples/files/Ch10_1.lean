import Mathlib
-- ▶ Block 135 · Chapter 10: Structures and Type Classes · Structures · page 66 (French edition: page 68)

structure Point where
  x : ℝ
  y : ℝ

-- ▶ Block 136 · Chapter 10: Structures and Type Classes · Structures · page 66 (French edition: page 68)
#check Point.mk     -- Point.mk (x y : ℝ) : Point
#check Point.x      -- Point.x (self : Point) : ℝ

-- ▶ Block 137 · Chapter 10: Structures and Type Classes · Structures · page 66 (French edition: page 68)
def origin : Point := { x := 0, y := 0 }    -- named fields
def p1 : Point := ⟨1, 2⟩                    -- anonymous constructor
def p2 : Point := Point.mk 3 4              -- explicit constructor

#check p1.x         -- p1.x : ℝ

-- ▶ Block 138 · Chapter 10: Structures and Type Classes · Structures · page 66 (French edition: page 68)
def Point.add (p q : Point) : Point :=
  { x := p.x + q.x, y := p.y + q.y }

example : (p1.add p2).x = 1 + 3 := rfl

-- ▶ Block 139 · Chapter 10: Structures and Type Classes · Structures · page 66 (French edition: page 68)
def p3 : Point := { p1 with y := 10 }

example : p3.x = 1 := rfl

-- ▶ Block 140 · Chapter 10: Structures and Type Classes · When are two structures equal? · page 66 (French edition: page 68)
@[ext] structure Vec2 where
  x : ℝ
  y : ℝ

#check @Vec2.ext    -- ∀ {x y : Vec2}, x.x = y.x → x.y = y.y → x = y

example (v w : Vec2) (hx : v.x = w.x) (hy : v.y = w.y) : v = w := by
  ext
  -- two goals:  ⊢ v.x = w.x   and   ⊢ v.y = w.y
  · exact hx
  · exact hy

-- ▶ Block 141 · Chapter 10: Structures and Type Classes · Fields can be proofs · page 67 (French edition: page 69)
structure PosReal where
  val : ℝ
  pos : 0 < val

def PosReal.one : PosReal := { val := 1, pos := by norm_num }

def PosReal.double (a : PosReal) : PosReal where
  val := 2 * a.val
  pos := by
    have h := a.pos
    -- h : 0 < a.val   ⊢ 0 < 2 * a.val
    linarith

-- ▶ Block 142 · Chapter 10: Structures and Type Classes · Structures of hypotheses · page 67 (French edition: page 69)
structure IsLinear (f : ℝ → ℝ) : Prop where
  map_add : ∀ x y, f (x + y) = f x + f y
  map_smul : ∀ c x, f (c * x) = c * f x

-- ▶ Block 143 · Chapter 10: Structures and Type Classes · Structures of hypotheses · page 67 (French edition: page 69)
theorem isLinear_three : IsLinear (fun x ↦ 3 * x) where
  map_add := by
    intro x y
    -- ⊢ 3 * (x + y) = 3 * x + 3 * y
    ring
  map_smul := by
    intro c x
    ring

-- ▶ Block 144 · Chapter 10: Structures and Type Classes · Structures of hypotheses · page 67 (French edition: page 69)
theorem IsLinear.map_zero {f : ℝ → ℝ} (hf : IsLinear f) : f 0 = 0 := by
  have h := hf.map_smul 0 0
  -- h : f (0 * 0) = 0 * f 0
  rw [zero_mul, zero_mul] at h
  -- h : f 0 = 0
  exact h

-- ▶ Block 145 · Chapter 10: Structures and Type Classes · Type classes: one name, many types · page 68 (French edition: page 70)
class HasArea (α : Type) where
  area : α → ℝ

structure Rect where
  w : ℝ
  h : ℝ

structure Square where
  side : ℝ

instance : HasArea Rect where
  area r := r.w * r.h

instance : HasArea Square where
  area s := s.side ^ 2

-- ▶ Block 146 · Chapter 10: Structures and Type Classes · Type classes: one name, many types · page 68 (French edition: page 70)
def twiceArea {α : Type} [HasArea α] (a : α) : ℝ := 2 * HasArea.area a

#check @twiceArea   -- @twiceArea : {α : Type} → [HasArea α] → α → ℝ

example : twiceArea (Rect.mk 2 3) = 12 := by
  norm_num [twiceArea, HasArea.area]

example : twiceArea (Square.mk 3) = 18 := by
  norm_num [twiceArea, HasArea.area]

-- ▶ Block 148 · Chapter 10: Structures and Type Classes · Notation is type classes · page 69 (French edition: page 71)
instance : Add Point where
  add p q := { x := p.x + q.x, y := p.y + q.y }

#check p1 + p2      -- p1 + p2 : Point

example : (p1 + p2).x = 1 + 3 := rfl

-- ▶ Block 149 · Chapter 10: Structures and Type Classes · The algebraic hierarchy · page 69 (French edition: page 71) · the book shows an error here
#synth Field ℝ            -- Real.instField
#synth LinearOrder ℝ      -- Real.linearOrder
#synth Ring ℤ             -- Int.instRing
#synth Field ℤ            -- error: failed to synthesize  Field ℤ

-- ▶ Block 150 · Chapter 10: Structures and Type Classes · The algebraic hierarchy · page 69 (French edition: page 71)
#check @mul_comm
-- ∀ {G : Type u_1} [inst : CommMagma G] (a b : G), a * b = b * a

#check @mul_inv_cancel
-- ∀ {G : Type u_1} [inst : Group G] (a : G), a * a⁻¹ = 1

#check @le_trans
-- ∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b ≤ c → a ≤ c

-- ▶ Block 151 · Chapter 10: Structures and Type Classes · The algebraic hierarchy · page 69 (French edition: page 71)
example {G : Type*} [Group G] (a b : G) : a * b * b⁻¹ = a := by
  -- ⊢ a * b * b⁻¹ = a
  rw [mul_assoc]
  -- ⊢ a * (b * b⁻¹) = a
  rw [mul_inv_cancel]
  -- ⊢ a * 1 = a
  rw [mul_one]

-- ▶ Block 152 · Chapter 10: Structures and Type Classes · The algebraic hierarchy · page 69 (French edition: page 72)
example {R : Type*} [CommRing R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

example {α : Type*} [LinearOrder α] (a b : α) : min a b ≤ max a b :=
  le_trans (min_le_left a b) (le_max_left a b)

-- ▶ Block 153 · Chapter 10: Structures and Type Classes · Building a class from other classes · page 70 (French edition: page 72)
class MyMonoid (α : Type) extends Mul α, One α where
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a

instance : MyMonoid ℕ where
  mul_assoc := Nat.mul_assoc
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one

-- ▶ Block 154 · Chapter 10: Structures and Type Classes · Building a class from other classes · page 70 (French edition: page 72)
theorem MyMonoid.one_unique {α : Type} [MyMonoid α] (e : α)
    (h : ∀ a : α, e * a = a) : e = 1 := by
  have h1 := h 1
  -- h1 : e * 1 = 1
  rw [MyMonoid.mul_one] at h1
  -- h1 : e = 1
  exact h1

-- ▶ Block 155 · Chapter 10: Structures and Type Classes · Coercions · page 70 (French edition: page 72)
#check ((3 : ℕ) : ℝ)       -- ↑3 : ℝ

example (n : ℕ) (x : ℝ) : x + n = n + x := by
  -- ⊢ x + ↑n = ↑n + x
  ring

-- ▶ Block 156 · Chapter 10: Structures and Type Classes · Coercions · page 71 (French edition: page 73)
structure EvenNat where
  val : ℕ
  even : Even val

instance : Coe EvenNat ℕ := ⟨EvenNat.val⟩

def four : EvenNat := ⟨4, by decide⟩

#eval (four : ℕ) + 1        -- 5

-- ▶ Block 157 · Chapter 10: Structures and Type Classes · Coercions · page 71 (French edition: page 73)
example (n : ℕ) (h : 2 ≤ n) : (2 : ℝ) ≤ n := by
  exact_mod_cast h
