import Mathlib
-- ▶ Block 112 · Chapter 8: Equality, Rewriting and calc · Exercises · page 55 (French edition: page 58) · exercise: errors are normal until you solve it

-- Exercise 1. Two rewrites in one rw.
example (a b c : ℝ) (h₁ : a = 2 * b) (h₂ : b = c + 1) : a = 2 * (c + 1) := by
  sorry

-- Exercise 2. Rewrite from right to left, then finish with ring.
example (x y : ℝ) (h : x + 1 = y) : y - 1 = x := by
  sorry

-- Exercise 3. Rewrite in the hypothesis with mul_one and add_zero.
example (a b : ℝ) (h : a * 1 = b + 0) : a = b := by
  sorry

-- Exercise 4. Use mul_assoc backwards, then mul_comm a b, then mul_assoc.
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

-- Exercise 5. A calc with three lines.
example (a b : ℝ) (h₁ : a = 3 * b) (h₂ : b = 2) : a ^ 2 = 36 := by
  sorry

-- Exercise 6. A calc mixing ≤ and =.
example (x y : ℝ) (hx : x ≤ 2) (hy : y ≤ 5) : 3 * x + y ≤ 11 := by
  sorry

-- Exercise 7. Two uses of abs_sub_le.
example (a b c d : ℝ) : |a - d| ≤ |a - b| + |b - c| + |c - d| := by
  sorry

-- Exercise 8.
example : (fun x : ℝ ↦ 2 * x) = (fun x ↦ x + x) := by
  sorry

-- Exercise 9. simp needs to be told about h.
example (xs ys : List ℕ) (h : ys = []) : (xs ++ ys).length = xs.length := by
  sorry

-- Exercise 10. Unfold, then conclude.
noncomputable def avg (a b : ℝ) : ℝ := (a + b) / 2

example (a : ℝ) : avg a a = a := by
  sorry

example (a b : ℝ) (h : a ≤ b) : avg a b ≤ b := by
  sorry
