-- ▶ Block 398 · Chapter 22: Verified Programs · Solutions · page 184 (French edition: page 191)
-- Exercise 1.
def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

theorem double_eq (n : Nat) : double n = 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [double, ih]
    -- ⊢ 2 * k + 2 = 2 * (k + 1)
    omega

-- Exercise 2.
def pow2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * pow2 n

theorem pow2_eq (n : Nat) : pow2 n = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [pow2, ih, Nat.pow_succ, Nat.mul_comm]

-- Exercise 3.
def revAcc {α : Type} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => revAcc xs (x :: acc)

theorem revAcc_eq {α : Type} (xs acc : List α) : revAcc xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [revAcc, ih]
    -- ⊢ xs.reverse ++ x :: acc = (x :: xs).reverse ++ acc
    simp

-- Exercise 4.
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

theorem mem_insertSorted (x y : Nat) (xs : List Nat) :
    y ∈ insertSorted x xs ↔ y = x ∨ y ∈ xs := by
  induction xs with
  | nil => simp [insertSorted]
  | cons z zs ih =>
    simp only [insertSorted]
    split
    · simp
    · simp only [List.mem_cons, ih]
      -- ⊢ y = z ∨ y = x ∨ y ∈ zs ↔ y = x ∨ y = z ∨ y ∈ zs
      grind

-- Exercise 5.
def log2 (n : Nat) : Nat :=
  if n < 2 then 0 else 1 + log2 (n / 2)

theorem pow_log2_le (n : Nat) (h : 1 ≤ n) : 2 ^ log2 n ≤ n := by
  fun_induction log2 n with
  | case1 n hn =>
    -- hn : n < 2     ⊢ 2 ^ 0 ≤ n
    simp
    omega
  | case2 n hn ih =>
    -- ih : 1 ≤ n / 2 → 2 ^ log2 (n / 2) ≤ n / 2     ⊢ 2 ^ (1 + log2 (n / 2)) ≤ n
    have ih' := ih (by omega)
    rw [Nat.pow_add, Nat.pow_one]
    omega
