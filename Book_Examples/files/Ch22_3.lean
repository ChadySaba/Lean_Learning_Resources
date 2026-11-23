-- ▶ Block 397 · Chapter 22: Verified Programs · Exercises · page 183 (French edition: page 190) · exercise: errors are normal until you solve it
-- Exercise 1.
def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

theorem double_eq (n : Nat) : double n = 2 * n := by
  sorry

-- Exercise 2. Use Nat.pow_succ : b ^ (n + 1) = b ^ n * b.
def pow2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * pow2 n

theorem pow2_eq (n : Nat) : pow2 n = 2 ^ n := by
  sorry

-- Exercise 3. An accumulator: find the invariant, and generalize.
def revAcc {α : Type} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => revAcc xs (x :: acc)

theorem revAcc_eq {α : Type} (xs acc : List α) : revAcc xs acc = xs.reverse ++ acc := by
  sorry

-- Exercise 4. Insertion adds exactly one element.
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

theorem mem_insertSorted (x y : Nat) (xs : List Nat) :
    y ∈ insertSorted x xs ↔ y = x ∨ y ∈ xs := by
  sorry

-- Exercise 5. Use fun_induction. In the second case, apply the induction
-- hypothesis, then Nat.pow_add and Nat.pow_one, then omega.
def log2 (n : Nat) : Nat :=
  if n < 2 then 0 else 1 + log2 (n / 2)

theorem pow_log2_le (n : Nat) (h : 1 ≤ n) : 2 ^ log2 n ≤ n := by
  sorry
