import Mathlib
-- ▶ Block 432 · Chapter 25: Proof Engineering · Slow proofs · page 207 (French edition: page 217)

#count_heartbeats in
theorem expand_ring (a b c : ℝ) :
    (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by
  ring
-- Used 369 heartbeats, which is less than the current maximum of 200000.

#count_heartbeats in
theorem expand_nlinarith (a b c : ℝ) :
    (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
-- Used 3624 heartbeats, which is less than the current maximum of 200000.

-- ▶ Block 433 · Chapter 25: Proof Engineering · Slow proofs · page 209 (French edition: page 218)
set_option maxHeartbeats 400000 in
-- The `simp` call unfolds a large definition.
theorem my_big_theorem : True := trivial
