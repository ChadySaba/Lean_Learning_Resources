import Mathlib
-- ▶ Block 114 · Chapter 9: Inductive Types, Recursion and Induction · Types defined by their constructors · page 58 (French edition: page 61)

inductive Weekday where
  | monday | tuesday | wednesday
  deriving Repr, DecidableEq

-- ▶ Block 115 · Chapter 9: Inductive Types, Recursion and Induction · Types defined by their constructors · page 58 (French edition: page 61)
#print Nat
-- inductive Nat : Type
-- number of parameters: 0
-- constructors:
-- Nat.zero : ℕ
-- Nat.succ : ℕ → ℕ

#print List
-- inductive List.{u} : Type u → Type u
-- number of parameters: 1
-- constructors:
-- List.nil : {α : Type u} → List α
-- List.cons : {α : Type u} → α → List α → List α

-- ▶ Block 116 · Chapter 9: Inductive Types, Recursion and Induction · Functions by cases · page 58 (French edition: page 61)
def Weekday.next : Weekday → Weekday
  | .monday => .tuesday
  | .tuesday => .wednesday
  | .wednesday => .monday

#eval Weekday.monday.next       -- Weekday.tuesday

-- ▶ Block 117 · Chapter 9: Inductive Types, Recursion and Induction · Proofs by cases · page 59 (French edition: page 62)
theorem Weekday.next3 (d : Weekday) : d.next.next.next = d := by
  cases d <;> rfl

-- ▶ Block 119 · Chapter 9: Inductive Types, Recursion and Induction · Recursive functions · page 59 (French edition: page 62)
def sumList : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + sumList xs

#eval sumList [1, 2, 3]         -- 6

def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval (List.range 10).map fib   -- [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]

-- ▶ Block 120 · Chapter 9: Inductive Types, Recursion and Induction · Induction · page 59 (French edition: page 62)
theorem sumTo_eq (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumTo]
    rw [mul_add, ih]
    ring

-- ▶ Block 122 · Chapter 9: Inductive Types, Recursion and Induction · Induction · page 60 (French edition: page 63)
theorem sumList_append (xs ys : List ℕ) :
    sumList (xs ++ ys) = sumList xs + sumList ys := by
  induction xs with
  | nil => simp [sumList]
  | cons x xs ih => simp [sumList, ih, add_assoc]

-- ▶ Block 123 · Chapter 9: Inductive Types, Recursion and Induction · Other induction principles · page 60 (French edition: page 63)
theorem two_mul_add_one_le (n : ℕ) (hn : 3 ≤ n) : 2 * n + 1 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    -- hk : 3 ≤ k,  ih : 2 * k + 1 ≤ 2 ^ k   ⊢ 2 * (k + 1) + 1 ≤ 2 ^ (k + 1)
    rw [pow_succ]
    omega

-- ▶ Block 124 · Chapter 9: Inductive Types, Recursion and Induction · Other induction principles · page 60 (French edition: page 63)
theorem fib_le : ∀ n, fib n ≤ 2 ^ n
  | 0 => by simp [fib]
  | 1 => by simp [fib]
  | n + 2 => by
    have h1 := fib_le n             -- h1 : fib n ≤ 2 ^ n
    have h2 := fib_le (n + 1)       -- h2 : fib (n + 1) ≤ 2 ^ (n + 1)
    rw [fib, pow_succ, pow_succ]    -- ⊢ fib n + fib (n + 1) ≤ 2 ^ n * 2 * 2
    rw [pow_succ] at h2             -- h2 : fib (n + 1) ≤ 2 ^ n * 2
    omega

-- ▶ Block 125 · Chapter 9: Inductive Types, Recursion and Induction · Other induction principles · page 61 (French edition: page 64)
example (n : ℕ) (h : n ≠ 0) : ∃ k, n = k + 1 := by
  obtain _ | k := n
  · contradiction           -- h : 0 ≠ 0
  · exact ⟨k, rfl⟩          -- ⊢ ∃ k_1, k + 1 = k_1 + 1

-- ▶ Block 126 · Chapter 9: Inductive Types, Recursion and Induction · Inductive predicates · page 61 (French edition: page 64)
inductive IsEven : ℕ → Prop where
  | zero : IsEven 0
  | add_two (n : ℕ) (h : IsEven n) : IsEven (n + 2)

-- ▶ Block 127 · Chapter 9: Inductive Types, Recursion and Induction · Inductive predicates · page 61 (French edition: page 64)
example : IsEven 4 := by
  apply IsEven.add_two      -- ⊢ IsEven 2
  apply IsEven.add_two      -- ⊢ IsEven 0
  exact IsEven.zero

-- ▶ Block 128 · Chapter 9: Inductive Types, Recursion and Induction · Inductive predicates · page 61 (French edition: page 64)
theorem not_isEven_one : ¬ IsEven 1 := by
  intro h
  cases h       -- no constructor can prove IsEven 1: no cases remain

-- ▶ Block 129 · Chapter 9: Inductive Types, Recursion and Induction · Inductive predicates · page 61 (French edition: page 64)
theorem IsEven.exists_two_mul {n : ℕ} (h : IsEven n) : ∃ k, n = 2 * k := by
  induction h with
  | zero => exact ⟨0, rfl⟩
  | add_two m hm ih =>
    -- ih : ∃ k, m = 2 * k    ⊢ ∃ k, m + 2 = 2 * k
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by omega⟩

-- ▶ Block 130 · Chapter 9: Inductive Types, Recursion and Induction · Logic is made of inductive types · page 62 (French edition: page 65)
#print Or
-- inductive Or : Prop → Prop → Prop
-- number of parameters: 2
-- constructors:
-- Or.inl : ∀ {a b : Prop}, a → a ∨ b
-- Or.inr : ∀ {a b : Prop}, b → a ∨ b

#print False
-- inductive False : Prop
-- number of parameters: 0
-- constructors:

#print Eq
-- inductive Eq.{u_1} : {α : Sort u_1} → α → α → Prop
-- number of parameters: 2
-- constructors:
-- Eq.refl : ∀ {α : Sort u_1} (a : α), a = a

-- ▶ Block 131 · Chapter 9: Inductive Types, Recursion and Induction · Recursion that is not structural · page 62 (French edition: page 65)
def gcdA : ℕ → ℕ → ℕ
  | a, 0 => a
  | a, b + 1 => gcdA (b + 1) (a % (b + 1))
termination_by _ b => b
decreasing_by exact Nat.mod_lt a (Nat.succ_pos b)

#eval gcdA 12 18        -- 6

-- ▶ Block 132 · Chapter 9: Inductive Types, Recursion and Induction · Recursion that is not structural · page 62 (French edition: page 65) · the book shows an error here
def bad (n : ℕ) : ℕ := bad (n + 1)
-- error: fail to show termination for bad …
-- failed to prove termination, possible solutions:
--   - Use `have`-expressions to prove the remaining goals
--   - Use `termination_by` to specify a different well-founded relation
--   - Use `decreasing_by` to specify your own tactic …
