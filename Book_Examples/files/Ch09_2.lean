import Mathlib
-- ▶ Block 133 · Chapter 9: Inductive Types, Recursion and Induction · Exercises · page 63 (French edition: page 66) · exercise: errors are normal until you solve it

-- Exercise 1. The length of a list.
def len {α : Type} : List α → ℕ
  | [] => sorry
  | _ :: xs => sorry
example : len [7, 8, 9] = 3 := rfl

-- Exercise 2. A proof by cases.
inductive Color where
  | red | green | blue

def Color.swap : Color → Color
  | .red => .green
  | .green => .red
  | .blue => .blue

example (c : Color) : c.swap.swap = c := by
  sorry

-- Exercise 3. The sum of the first n odd numbers is n².
def sumOdd : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumOdd n + (2 * n + 1)

theorem sumOdd_eq (n : ℕ) : sumOdd n = n ^ 2 := by
  sorry

-- Exercise 4. Induction on xs. Needs your `len` from Exercise 1.
theorem len_append {α : Type} (xs ys : List α) :
    len (xs ++ ys) = len xs + len ys := by
  sorry

-- Exercise 5. Use pow_succ in the inductive step, then omega.
theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  sorry

-- Exercise 6. Apply a constructor twice.
inductive IsEven : ℕ → Prop where
  | zero : IsEven 0
  | add_two (n : ℕ) (h : IsEven n) : IsEven (n + 2)

example (n : ℕ) (h : IsEven n) : IsEven (n + 4) := by
  sorry

-- Exercise 7. Two rounds of `cases`.
example : ¬ IsEven 3 := by
  sorry

-- Exercise 8. Induction on the proof hn.
theorem IsEven.add {m n : ℕ} (hm : IsEven m) (hn : IsEven n) : IsEven (m + n) := by
  sorry
