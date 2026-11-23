import Mathlib
-- ▶ Block 113 · Chapter 8: Equality, Rewriting and calc · Solutions · page 56 (French edition: page 58)

-- Exercise 1.
example (a b c : ℝ) (h₁ : a = 2 * b) (h₂ : b = c + 1) : a = 2 * (c + 1) := by
  rw [h₁, h₂]

-- Exercise 2.
example (x y : ℝ) (h : x + 1 = y) : y - 1 = x := by
  rw [← h]            -- ⊢ x + 1 - 1 = x
  ring

-- Exercise 3.
example (a b : ℝ) (h : a * 1 = b + 0) : a = b := by
  rw [mul_one, add_zero] at h
  exact h

-- Exercise 4.
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]        -- ⊢ a * b * c = b * (a * c)
  rw [mul_comm a b]       -- ⊢ b * a * c = b * (a * c)
  rw [mul_assoc]

-- Exercise 5.
example (a b : ℝ) (h₁ : a = 3 * b) (h₂ : b = 2) : a ^ 2 = 36 := by
  calc a ^ 2 = (3 * b) ^ 2 := by rw [h₁]
    _ = (3 * 2) ^ 2        := by rw [h₂]
    _ = 36                 := by norm_num

-- Exercise 6.
example (x y : ℝ) (hx : x ≤ 2) (hy : y ≤ 5) : 3 * x + y ≤ 11 := by
  calc 3 * x + y ≤ 3 * 2 + 5 := by linarith
    _ = 11                   := by norm_num

-- Exercise 7. First go from a to d through c, then from a to c through b.
example (a b c d : ℝ) : |a - d| ≤ |a - b| + |b - c| + |c - d| := by
  calc |a - d| ≤ |a - c| + |c - d|      := abs_sub_le a c d
    _ ≤ |a - b| + |b - c| + |c - d|     := by linarith [abs_sub_le a b c]

-- Exercise 8.
example : (fun x : ℝ ↦ 2 * x) = (fun x ↦ x + x) := by
  ext x
  ring

-- Exercise 9.
example (xs ys : List ℕ) (h : ys = []) : (xs ++ ys).length = xs.length := by
  simp [h]

-- Exercise 10.
noncomputable def avg (a b : ℝ) : ℝ := (a + b) / 2

example (a : ℝ) : avg a a = a := by
  unfold avg          -- ⊢ (a + a) / 2 = a
  ring

example (a b : ℝ) (h : a ≤ b) : avg a b ≤ b := by
  unfold avg          -- ⊢ (a + b) / 2 ≤ b
  linarith
