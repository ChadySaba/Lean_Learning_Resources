import Mathlib
-- ▶ Block 435 · Chapter 25: Proof Engineering · Exercises · page 211 (French edition: page 220) · exercise: errors are normal until you solve it

-- Exercise 1. Fill the three holes of this skeleton.
def TendsToZero (u : ℕ → ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n| < ε

theorem bounded_mul_tendsToZero (u v : ℕ → ℝ) (M : ℝ) (hM : 0 < M)
    (hu : ∀ n, |u n| ≤ M) (hv : TendsToZero v) : TendsToZero (fun n => u n * v n) := by
  intro ε hε
  -- Step 1: use hv with ε / M.
  have h1 : ∃ N, ∀ n ≥ N, |v n| < ε / M := by
    sorry
  obtain ⟨N, hN⟩ := h1
  refine ⟨N, fun n hn => ?_⟩
  -- Step 2: the key inequality.
  have h2 : |u n * v n| ≤ M * |v n| := by
    sorry
  -- Step 3: conclude.
  have h3 : M * |v n| < ε := by
    sorry
  exact lt_of_le_of_lt h2 h3

-- Exercise 2. This proof works and is fragile. Rewrite it in two lines,
-- with names you choose and a decisive closing tactic.
example (a b : ℝ) (h : 0 ≤ a ∧ 0 ≤ b) : 0 ≤ a * b + a := by
  cases h
  rename_i h1 h2
  nlinarith [mul_nonneg h1 h2]

-- Exercise 3. Read the error, find the cause, and repair the proof.
example (n : ℕ) (h : 0 < n) : (0 : ℝ) < n := by
  exact h
