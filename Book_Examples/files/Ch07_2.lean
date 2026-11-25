import Mathlib
-- ▶ Block 91 · Chapter 7: Tactics, the Core Toolkit · Exercises · page 48 (French edition: page 50) · exercise: errors are normal until you solve it

-- Exercise 1. intro, constructor, exact.
example (p q r : Prop) (hpq : p → q) (hpr : p → r) : p → q ∧ r := by
  sorry

-- Exercise 2. Unpack three parts with one obtain.
example (p q r : Prop) (h : p ∧ q ∧ r) : r ∧ p := by
  sorry

-- Exercise 3. Two cases. One ends with `left`, the other with `right`.
example (p q r : Prop) (h : p ∨ q) (hqr : q → r) : p ∨ r := by
  sorry

-- Exercise 4. Give the witness, then let norm_num check it.
example : ∃ x : ℝ, 2 * x + 1 = 7 := by
  sorry

-- Exercise 5. Unpack the hypothesis, reuse its witness.
example (a : ℝ) (h : ∃ x : ℝ, x > a) : ∃ y : ℝ, y > a - 1 := by
  sorry

-- Exercise 6. Two `have` lines with explicit types, then linarith.
example (f : ℕ → ℝ) (h : ∀ n, f n ≤ f (n + 1)) : f 0 ≤ f 2 := by
  sorry

-- Exercise 7. The goal is a negation.
example (a b : ℝ) (h : a < b) : ¬ b ≤ a := by
  sorry

-- Exercise 8. By contradiction. Use h with a / 2.
example (a : ℝ) (h : ∀ ε > 0, a ≤ ε) : a ≤ 0 := by
  sorry

-- Exercise 9. "f is not bounded above", unfolded.
example (f : ℝ → ℝ) (h : ¬ ∃ M, ∀ x, f x ≤ M) : ∀ M, ∃ x, M < f x := by
  sorry

-- Exercise 10.
example (a b : ℝ) : a ≤ b ↔ 0 ≤ b - a := by
  sorry

-- Exercise 11. by_cases on `0 ≤ x`.
example (x : ℝ) : 0 ≤ x ∨ x < 0 := by
  sorry

-- Exercise 12. The sum of two functions that tend to 0 at 0 tends to 0.
-- Useful lemmas: lt_min, min_le_left, min_le_right, lt_of_lt_of_le, abs_add_le.
example (f g : ℝ → ℝ)
    (hf : ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x| < ε)
    (hg : ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |g x| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x + g x| < ε := by
  sorry
