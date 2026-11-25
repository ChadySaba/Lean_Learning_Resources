-- ▶ Block 384 · Chapter 22: Verified Programs · A function and its specification · page 179 (French edition: page 187)
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

#eval sumTo 100                              -- 5050
example : sumTo 100 = 5050 := by decide      -- a test, checked by the kernel

-- ▶ Block 385 · Chapter 22: Verified Programs · A function and its specification · page 179 (French edition: page 187)
theorem sumTo_eq (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumTo]
    -- ih : 2 * sumTo k = k * (k + 1)
    -- ⊢ 2 * (k + 1 + sumTo k) = (k + 1) * (k + 1 + 1)
    grind

-- ▶ Block 386 · Chapter 22: Verified Programs · Two implementations, one specification · page 179 (French edition: page 187)
def sumAcc : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => sumAcc n (acc + (n + 1))

def sumFast (n : Nat) : Nat := sumAcc n 0

-- ▶ Block 387 · Chapter 22: Verified Programs · Two implementations, one specification · page 179 (French edition: page 187)
theorem sumAcc_zero_bad (n : Nat) : sumAcc n 0 = sumTo n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumAcc, sumTo]
    -- ih : sumAcc k 0 = sumTo k
    -- ⊢ sumAcc k (0 + (k + 1)) = k + 1 + sumTo k
    sorry

-- ▶ Block 388 · Chapter 22: Verified Programs · Two implementations, one specification · page 180 (French edition: page 188)
theorem sumAcc_eq (n acc : Nat) : sumAcc n acc = acc + sumTo n := by
  induction n generalizing acc with
  | zero => rfl
  | succ k ih =>
    simp only [sumAcc, sumTo]
    -- ih : ∀ (acc : Nat), sumAcc k acc = acc + sumTo k
    -- ⊢ sumAcc k (acc + (k + 1)) = acc + (k + 1 + sumTo k)
    rw [ih]
    omega

theorem sumFast_eq (n : Nat) : sumFast n = sumTo n := by
  simp [sumFast, sumAcc_eq]

-- ▶ Block 389 · Chapter 22: Verified Programs · A sorting algorithm · page 180 (French edition: page 188)
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

def isort : List Nat → List Nat
  | [] => []
  | x :: xs => insertSorted x (isort xs)

#eval isort [3, 1, 4, 1, 5, 9, 2, 6]         -- [1, 1, 2, 3, 4, 5, 6, 9]
example : isort [3, 1, 2] = [1, 2, 3] := rfl

-- ▶ Block 390 · Chapter 22: Verified Programs · A sorting algorithm · page 180 (French edition: page 188)
inductive Sorted : List Nat → Prop
  | nil : Sorted []
  | single (x : Nat) : Sorted [x]
  | cons (x y : Nat) (ys : List Nat) : x ≤ y → Sorted (y :: ys) → Sorted (x :: y :: ys)

-- ▶ Block 391 · Chapter 22: Verified Programs · A sorting algorithm · page 181 (French edition: page 189)
theorem sorted_insertSorted (x : Nat) (xs : List Nat) (h : Sorted xs) :
    Sorted (insertSorted x xs) := by
  induction h with
  | nil => exact Sorted.single x
  | single y =>
    simp only [insertSorted]
    split
    · exact Sorted.cons x y [] (by assumption) (Sorted.single y)
    · exact Sorted.cons y x [] (by omega) (Sorted.single x)
  | cons y z zs hyz hzs ih =>
    simp only [insertSorted] at ih ⊢
    -- ih : Sorted (if x ≤ z then x :: z :: zs else z :: insertSorted x zs)
    -- ⊢ Sorted (if x ≤ y then x :: y :: z :: zs
    --           else y :: if x ≤ z then x :: z :: zs else z :: insertSorted x zs)
    split
    · exact Sorted.cons x y (z :: zs) (by assumption) (Sorted.cons y z zs hyz hzs)
    · split
      · exact Sorted.cons y x (z :: zs) (by omega) (by simp_all)
      · exact Sorted.cons y z _ hyz (by simp_all)

theorem sorted_isort (xs : List Nat) : Sorted (isort xs) := by
  induction xs with
  | nil => exact Sorted.nil
  | cons x xs ih => exact sorted_insertSorted x (isort xs) ih

-- ▶ Block 392 · Chapter 22: Verified Programs · A sorting algorithm · page 181 (French edition: page 189)
theorem perm_insertSorted (x : Nat) (xs : List Nat) : (insertSorted x xs).Perm (x :: xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    simp only [insertSorted]
    split
    · exact List.Perm.refl _
    · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

theorem perm_isort (xs : List Nat) : (isort xs).Perm xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih => exact (perm_insertSorted x (isort xs)).trans (List.Perm.cons x ih)

-- ▶ Block 393 · Chapter 22: Verified Programs · Let automation follow the program · page 182 (French edition: page 190)
theorem length_insertSorted (x : Nat) (xs : List Nat) :
    (insertSorted x xs).length = xs.length + 1 := by
  induction xs <;> grind [insertSorted]

-- ▶ Block 394 · Chapter 22: Verified Programs · Let automation follow the program · page 182 (French edition: page 190)
def digits (n : Nat) : List Nat :=
  if n < 10 then [n] else digits (n / 10) ++ [n % 10]

theorem digits_lt (n : Nat) : ∀ d ∈ digits n, d < 10 := by
  fun_induction digits n with
  | case1 n h =>
    -- h : n < 10      ⊢ ∀ (d : Nat), d ∈ [n] → d < 10
    simp
    omega
  | case2 n h ih =>
    -- h : ¬n < 10     ih : ∀ (d : Nat), d ∈ digits (n / 10) → d < 10
    -- ⊢ ∀ (d : Nat), d ∈ digits (n / 10) ++ [n % 10] → d < 10
    intro d hd
    simp at hd
    rcases hd with hd | hd
    · exact ih d hd
    · omega

-- ▶ Block 395 · Chapter 22: Verified Programs · Specifications in the type · page 182 (French edition: page 190)
def isqrt (n : Nat) : { r : Nat // r * r ≤ n ∧ n < (r + 1) * (r + 1) } :=
  ⟨Nat.sqrt n, Nat.sqrt_le n, Nat.lt_succ_sqrt n⟩
