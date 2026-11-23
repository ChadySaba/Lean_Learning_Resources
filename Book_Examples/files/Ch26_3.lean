import Mathlib
-- ▶ Block 442 · Chapter 26: Lean and AI Tools · Solutions · page 219 (French edition: page 228)

-- Exercise 1. No. The theorem has an escape clause, `∨ a < b`. The sentence
-- is false for a = 2, b = 3, since subtraction in ℕ stops at 0:
example : (2 : ℕ) - 3 + 3 = 3 := by norm_num
-- The honest statement carries the hypothesis:
example (a b : ℕ) (h : b ≤ a) : a - b + b = a := Nat.sub_add_cancel h

-- Exercise 2. `crit2`. `crit1` also holds for every function that is not
-- differentiable at 0, such as the absolute value:
example : deriv (fun x : ℝ => |x|) 0 = 0 :=
  deriv_zero_of_not_differentiableAt not_differentiableAt_abs_zero

-- Exercise 3. It does not work directly: `theirs` needs `x ≠ 1`, which `mine`
-- does not have. The received theorem is weaker than the one requested.
-- Here the extra hypothesis was never needed:
theorem mine (x : ℝ) (hx : 0 < x) : Real.log (x ^ 2) = 2 * Real.log x := by
  rw [Real.log_pow]
  norm_num
-- Lean's linter adds a remark of its own: `hx` is not used either.
-- With the convention Real.log (-x) = Real.log x, the identity holds for all x.
