import Mathlib
-- ▶ Block 447 · Chapter 27: Community, Contributing, and Where to Go Next · Solutions · page 224 (French edition: page 235) · the book shows an error here

-- Exercise 1. The function g, the sequence v and the lemma g_pos are not
-- needed to show the problem:
example (a : ℝ) (h : a ≤ 5) : a / 5 ≤ 1 := by
  rw [div_le_one]
  exact h
-- error: unsolved goals
-- ⊢ 0 < 5

-- The hypothesis `0 < b` of div_le_one was left as a goal. Give it directly:
example (a : ℝ) (h : a ≤ 5) : a / 5 ≤ 1 := by
  rw [div_le_one (by norm_num)]
  exact h
