import Mathlib
-- ▶ Block 200 · Chapter 12: Finding Things in Mathlib · Solutions · page 91 (French edition: page 95)

example (a b : ℝ) : |a * b| = |a| * |b| := abs_mul a b

example (a b : ℝ) (h : a ≤ b) : -b ≤ -a := neg_le_neg h

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := mul_pos ha hb

example (a b c : ℝ) (h₁ : a < b) (h₂ : b ≤ c) : a < c := lt_of_lt_of_le h₁ h₂

example (x : ℝ) : 0 ≤ x ^ 2 := sq_nonneg x

example (a b : ℝ) : |a| - |b| ≤ |a - b| := abs_sub_abs_le_abs_sub a b

example (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (i : ℝ) = ∑ i ∈ Finset.range n, (i : ℝ) + n :=
  Finset.sum_range_succ _ n

-- Exercise 8.
#check @sub_nonneg          -- 0 ≤ a - b ↔ b ≤ a
#check @mul_self_nonneg     -- 0 ≤ a * a
#check @le_div_iff₀         -- 0 < c → (a ≤ b / c ↔ a * c ≤ b)
#check @abs_sub_comm        -- |a - b| = |b - a|
