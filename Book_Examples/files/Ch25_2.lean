import Mathlib
-- ▶ Block 425 · Chapter 25: Proof Engineering · Sorry-driven development · page 204 (French edition: page 212) · only its import and open lines, repeated here as context
open Filter Topology

-- ▶ Block 426 · Chapter 25: Proof Engineering · Sorry-driven development · page 205 (French edition: page 213) · repeated here as context
theorem bounded_initial (u : ℕ → ℝ) (N : ℕ) : ∃ B, ∀ n < N, |u n| ≤ B := by
  induction N with
  | zero => exact ⟨0, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | succ k ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨max B |u k|, fun n hn => ?_⟩
    -- hn : n < k + 1     ⊢ |u n| ≤ max B |u k|
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
    · exact (hB n h).trans (le_max_left _ _)
    · rw [h]
      exact le_max_right _ _

-- ▶ Block 427 · Chapter 25: Proof Engineering · Sorry-driven development · page 205 (French edition: page 213)
theorem bounded_of_tendsto (u : ℕ → ℝ) (l : ℝ) (h : Tendsto u atTop (𝓝 l)) :
    ∃ M, ∀ n, |u n| ≤ M := by
  -- Step 1: from some rank N on, u n is within 1 of l.
  have h1 : ∃ N, ∀ n ≥ N, |u n - l| < 1 := by
    have := Metric.tendsto_atTop.mp h 1 one_pos
    -- this : ∃ N, ∀ n ≥ N, dist (u n) l < 1
    simpa only [Real.dist_eq] using this
  obtain ⟨N, hN⟩ := h1
  -- Step 2: the first N terms are bounded.
  obtain ⟨B, hB⟩ := bounded_initial u N
  -- Step 3: the larger of the two bounds works.
  refine ⟨max B (|l| + 1), fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · exact (hB n hn).trans (le_max_left _ _)
  · have h3 : |u n| ≤ |u n - l| + |l| := by
      have := abs_add_le (u n - l) l
      simpa using this
    have h4 := hN n hn
    exact le_trans (by linarith) (le_max_right _ _)

-- ▶ Block 428 · Chapter 25: Proof Engineering · Turning a step into a lemma · page 205 (French edition: page 213)
example (u : ℕ → ℝ) (l : ℝ) (h : Tendsto u atTop (𝓝 l)) : ∃ M, ∀ n, |u n| ≤ M := by
  have h1 : ∃ N, ∀ n ≥ N, |u n - l| < 1 := by
    extract_goal
    sorry
  sorry

-- ▶ Block 429 · Chapter 25: Proof Engineering · Turning a step into a lemma · page 206 (French edition: page 214)
theorem _example.extracted_1 (u : ℕ → ℝ) (l : ℝ) (h : Tendsto u atTop (𝓝 l)) :
    ∃ N, ∀ n ≥ N, |u n - l| < 1 := sorry

-- ▶ Block 430 · Chapter 25: Proof Engineering · Finding the cause of a failure · page 207 (French edition: page 215) · the book shows an error here
example (n m : ℕ) (h : (n : ℤ) < m) : (n : ℝ) < m := by
  exact h
-- error: Type mismatch
--   h
-- has type
--   @Nat.cast ℤ instNatCastInt n < ↑m
-- but is expected to have type
--   @Nat.cast ℝ Real.instNatCast n < ↑m
