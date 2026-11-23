import Mathlib
-- ▶ Block 187 · Chapter 12: Finding Things in Mathlib · Let Lean search: exact?, apply?, rw? · page 84 (French edition: page 88)

example (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  exact?      -- Try this: exact abs_add_le a b

example (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := by
  exact?      -- Try this: exact add_le_add_left h c

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  exact?      -- Try this: exact Left.mul_nonneg ha hb

-- ▶ Block 188 · Chapter 12: Finding Things in Mathlib · Let Lean search: exact?, apply?, rw? · page 85 (French edition: page 88)
example (a b c : ℝ) (hc : 0 < c) (h : a ≤ b) : a * c ≤ b * c := by
  apply?      -- Try this: exact (mul_le_mul_iff_of_pos_right hc).mpr h

example (a b : ℝ) : |a * b| = |a| * |b| := by
  rw?         -- Try this: rw [abs_mul]

-- ▶ Block 189 · Chapter 12: Finding Things in Mathlib · Let Lean search: exact?, apply?, rw? · page 85 (French edition: page 88)
example (x : ℝ) (h : 0 < x) : x / x = 1 := by
  simp? [h.ne']
  -- Try this: simp only [ne_eq, h.ne', not_false_eq_true, div_self]

-- ▶ Block 190 · Chapter 12: Finding Things in Mathlib · Guess the name · page 86 (French edition: page 89)
#check abs_mul            -- |a * b| = |a| * |b|
#check add_sq             -- (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2
#check neg_neg            -- - -a = a
#check sub_eq_add_neg     -- a - b = a + -b
#check two_mul            -- 2 * n = n + n

-- ▶ Block 191 · Chapter 12: Finding Things in Mathlib · Guess the name · page 86 (French edition: page 89)
#check @lt_of_lt_of_le    -- a < b → b ≤ c → a < c
#check @le_of_lt          -- a < b → a ≤ b
#check @ne_of_gt          -- b < a → a ≠ b

-- ▶ Block 192 · Chapter 12: Finding Things in Mathlib · Guess the name · page 87 (French edition: page 90)
#check Finset.sum_range_succ
-- ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f n

#check @Finset.sum_le_sum
-- (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i

-- ▶ Block 193 · Chapter 12: Finding Things in Mathlib · Dot notation finds lemmas for you · page 87 (French edition: page 91)
example (a b : ℝ) (h : a < b) : a ≤ b := h.le
example (a b : ℝ) (h : a < b) : a ≠ b := h.ne
example (a b : ℝ) (h : a < b) : b ≠ a := h.ne'
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := h₁.trans h₂
example (a b c : ℝ) (h₁ : a < b) (h₂ : b ≤ c) : a < c := h₁.trans_le h₂
example (a b : ℝ) (h : a ≤ b) (h' : b ≤ a) : a = b := h.antisymm h'

-- ▶ Block 194 · Chapter 12: Finding Things in Mathlib · Dot notation finds lemmas for you · page 88 (French edition: page 91)
example (a b : ℝ) (h : 0 ≤ a - b) : b ≤ a := sub_nonneg.mp h
example (a b : ℝ) (h : b ≤ a) : 0 ≤ a - b := sub_nonneg.mpr h
example (a b : ℝ) (h : b ≤ a) : 0 ≤ a - b := by rwa [sub_nonneg]

-- ▶ Block 197 · Chapter 12: Finding Things in Mathlib · Read the source · page 89 (French edition: page 92)
#check abs_le           -- the statement, all arguments before the colon
#check @abs_le          -- the same statement as one ∀ type, with instance names
#print abs_le           -- the statement and the proof term

-- ▶ Block 198 · Chapter 12: Finding Things in Mathlib · Names change · page 89 (French edition: page 93) · the book shows an error here
#check (Set.mem_setOf_eq)   -- the parentheses matter: a bare #check name skips the warning
-- warning: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead

#check Set.not_mem_empty
-- error: Unknown constant `Set.not_mem_empty`     (it is now Set.notMem_empty)

#check abs_add
-- error: Unknown identifier `abs_add`             (it is now abs_add_le)
