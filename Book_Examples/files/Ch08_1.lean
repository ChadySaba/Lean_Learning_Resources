import Mathlib
-- ▶ Block 93 · Chapter 8: Equality, Rewriting and calc · Two kinds of equal · page 51 (French edition: page 54)

example : (2 : ℕ) + 2 = 4 := rfl
example (n : ℕ) : n + 0 = n := rfl

-- ▶ Block 94 · Chapter 8: Equality, Rewriting and calc · Two kinds of equal · page 51 (French edition: page 54) · the book shows an error here
example (n : ℕ) : 0 + n = n := rfl
-- error: Type mismatch … rfl … is expected to have type 0 + n = n

example (n : ℕ) : 0 + n = n := zero_add n     -- a lemma, proved by induction
example (x : ℝ) : x + 0 = x := add_zero x     -- on ℝ, even this needs a lemma

-- ▶ Block 95 · Chapter 8: Equality, Rewriting and calc · rw · page 51 (French edition: page 54)
example (a b c : ℝ) (h₁ : a = b) (h₂ : b = c) : a = c := by
  rw [h₁]         -- ⊢ b = c
  exact h₂

-- ▶ Block 96 · Chapter 8: Equality, Rewriting and calc · rw · page 52 (French edition: page 55)
example (a b : ℝ) (h : a = b + 1) : b + 1 = a := by
  rw [← h]       -- ⊢ a = a, closed by rfl

example (a b : ℝ) (h : a + 0 = b) : a = b := by
  rw [add_zero] at h      -- h : a = b
  exact h

-- ▶ Block 97 · Chapter 8: Equality, Rewriting and calc · Rewriting with lemmas · page 52 (French edition: page 55)
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm]           -- ⊢ c * (a * b) = b * (a * c)
  sorry

-- ▶ Block 98 · Chapter 8: Equality, Rewriting and calc · Rewriting with lemmas · page 52 (French edition: page 55)
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]       -- ⊢ b * a * c = b * (a * c)
  rw [mul_assoc]          -- ⊢ b * (a * c) = b * (a * c), closed by rfl

-- ▶ Block 99 · Chapter 8: Equality, Rewriting and calc · Rewriting with lemmas · page 52 (French edition: page 55)
example (a b : ℝ) (h : a - b = 0) : a = b := by
  rw [sub_eq_zero] at h   -- h : a = b
  exact h

-- ▶ Block 100 · Chapter 8: Equality, Rewriting and calc · When rw fails · page 52 (French edition: page 55) · the book shows an error here
example (a b : ℝ) : a + b = b + a := by
  rw [mul_comm]
-- error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
--   ?a * ?b
-- in the target expression
--   a + b = b + a

-- ▶ Block 101 · Chapter 8: Equality, Rewriting and calc · When rw fails · page 52 (French edition: page 55) · the book shows an error here
example (f : ℕ → ℕ) (h : ∀ x, f x = x) : (fun x => f x + 0) = fun x => x := by
  rw [h]
-- error: Did not find an occurrence of the pattern  f ?x

example (f : ℕ → ℕ) (h : ∀ x, f x = x) : (fun x => f x + 0) = fun x => x := by
  simp only [h, add_zero]       -- works: simp rewrites under binders

-- ▶ Block 102 · Chapter 8: Equality, Rewriting and calc · calc · page 53 (French edition: page 56)
example (a b c d : ℝ) (h₁ : a = b + 1) (h₂ : b = c * 2) (h₃ : c = d) :
    a = d * 2 + 1 := by
  calc a = b + 1     := h₁
    _ = c * 2 + 1    := by rw [h₂]
    _ = d * 2 + 1    := by rw [h₃]

-- ▶ Block 103 · Chapter 8: Equality, Rewriting and calc · calc · page 53 (French edition: page 56)
example (x y : ℝ) (h₁ : x ≤ y) (h₂ : y < 3) : 2 * x + 1 < 7 := by
  calc 2 * x + 1 ≤ 2 * y + 1 := by linarith
    _ < 2 * 3 + 1             := by linarith
    _ = 7                     := by norm_num

-- ▶ Block 104 · Chapter 8: Equality, Rewriting and calc · calc · page 53 (French edition: page 56)
example (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
  calc |a - c| = |(a - b) + (b - c)| := by rw [sub_add_sub_cancel]
    _ ≤ |a - b| + |b - c|            := abs_add_le (a - b) (b - c)

-- ▶ Block 105 · Chapter 8: Equality, Rewriting and calc · simp · page 53 (French edition: page 56)
example (xs : List ℕ) : (xs ++ []).length = xs.length := by simp

-- ▶ Block 106 · Chapter 8: Equality, Rewriting and calc · simp · page 53 (French edition: page 57) · the book shows an error here
example (a b : ℝ) (h : a = b) : a + 0 = b * 1 := by simp
-- error: unsolved goals  … ⊢ a = b

example (a b : ℝ) (h : a = b) : a + 0 = b * 1 := by simp [h]

-- ▶ Block 108 · Chapter 8: Equality, Rewriting and calc · simp · page 54 (French edition: page 57)
example (x : ℝ) (h : x + 0 = 2 * 1) : x = 2 := by
  simpa using h

-- ▶ Block 109 · Chapter 8: Equality, Rewriting and calc · Definitions: unfold · page 54 (French edition: page 57)
def double (x : ℝ) : ℝ := 2 * x

example (x : ℝ) : double x = x + x := by
  unfold double       -- ⊢ 2 * x = x + x
  ring

-- ▶ Block 110 · Chapter 8: Equality, Rewriting and calc · Equality of functions: ext · page 54 (French edition: page 58)
example : (fun x : ℝ ↦ x + 0) = (fun x ↦ x) := by
  ext x               -- x : ℝ  ⊢ x + 0 = x
  simp

-- ▶ Block 111 · Chapter 8: Equality, Rewriting and calc · Other tools for equalities · page 55 (French edition: page 58)
example (f : ℝ → ℝ) (a b : ℝ) (h : a = b) : f (a + 1) = f (b + 1) := by
  congr 1             -- ⊢ a + 1 = b + 1
  rw [h]

example (a b : ℝ) (h : a = b) (h' : a ^ 2 = 4) : b ^ 2 = 4 := by
  subst h             -- b is gone:  h' : a ^ 2 = 4  ⊢ a ^ 2 = 4
  exact h'
