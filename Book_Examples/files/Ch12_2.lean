import Mathlib
-- ▶ Block 199 · Chapter 12: Finding Things in Mathlib · Exercises · page 90 (French edition: page 94) · exercise: errors are normal until you solve it

-- Exercises 1 to 7. Each is closed by one lemma. First guess its name from the
-- convention. Then check your guess with exact?.

example (a b : ℝ) : |a * b| = |a| * |b| := by
  sorry

example (a b : ℝ) (h : a ≤ b) : -b ≤ -a := by
  sorry

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  sorry

example (a b c : ℝ) (h₁ : a < b) (h₂ : b ≤ c) : a < c := by
  sorry

example (x : ℝ) : 0 ≤ x ^ 2 := by
  sorry

example (a b : ℝ) : |a| - |b| ≤ |a - b| := by
  sorry

example (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (i : ℝ) = ∑ i ∈ Finset.range n, (i : ℝ) + n := by
  sorry

-- Exercise 8. Without running Lean, write the statement each name describes.
-- Then run #check.
--   sub_nonneg      mul_self_nonneg      le_div_iff₀      abs_sub_comm

-- Exercise 9. Write a Loogle query for each.
--   (a) lemmas whose conclusion is  |_ - _| ≤ |_ - _| + |_ - _|
--   (b) lemmas about Finset.sum with "comm" in the name
--   (c) lemmas stating that the square root of a square is something
