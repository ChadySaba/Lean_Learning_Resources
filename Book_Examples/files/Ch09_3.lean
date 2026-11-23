import Mathlib
-- ▶ Block 134 · Chapter 9: Inductive Types, Recursion and Induction · Solutions · page 63 (French edition: page 66)

-- Exercise 1.
def len {α : Type} : List α → ℕ
  | [] => 0
  | _ :: xs => 1 + len xs
example : len [7, 8, 9] = 3 := rfl

-- Exercise 2.
inductive Color where
  | red | green | blue

def Color.swap : Color → Color
  | .red => .green
  | .green => .red
  | .blue => .blue

example (c : Color) : c.swap.swap = c := by
  cases c <;> rfl

-- Exercise 3.
def sumOdd : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumOdd n + (2 * n + 1)

theorem sumOdd_eq (n : ℕ) : sumOdd n = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumOdd, ih]     -- ⊢ k ^ 2 + (2 * k + 1) = (k + 1) ^ 2
    ring

-- Exercise 4.
theorem len_append {α : Type} (xs ys : List α) :
    len (xs ++ ys) = len xs + len ys := by
  induction xs with
  | nil => simp [len]
  | cons x xs ih => simp [len, ih, add_assoc]

-- Exercise 5.
theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]       -- ih : k + 1 ≤ 2 ^ k   ⊢ k + 1 + 1 ≤ 2 ^ k * 2
    omega

-- Exercise 6. `n + 4` computes to `n + 2 + 2`, so the constructor applies.
inductive IsEven : ℕ → Prop where
  | zero : IsEven 0
  | add_two (n : ℕ) (h : IsEven n) : IsEven (n + 2)

example (n : ℕ) (h : IsEven n) : IsEven (n + 4) := by
  apply IsEven.add_two
  apply IsEven.add_two
  exact h

-- Exercise 7. A proof of IsEven 3 must come from a proof of IsEven 1,
-- and nothing proves IsEven 1.
example : ¬ IsEven 3 := by
  intro h
  cases h with
  | add_two n h' => cases h'

-- Exercise 8. m + (k + 2) computes to (m + k) + 2.
theorem IsEven.add {m n : ℕ} (hm : IsEven m) (hn : IsEven n) : IsEven (m + n) := by
  induction hn with
  | zero => exact hm
  | add_two k hk ih => exact IsEven.add_two (m + k) ih
