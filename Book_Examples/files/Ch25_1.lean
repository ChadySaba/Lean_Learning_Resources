import Mathlib
-- ▶ Block 425 · Chapter 25: Proof Engineering · Sorry-driven development · page 204 (French edition: page 213)
open Filter Topology

theorem bounded_of_tendsto (u : ℕ → ℝ) (l : ℝ) (h : Tendsto u atTop (𝓝 l)) :
    ∃ M, ∀ n, |u n| ≤ M := by
  -- Step 1: from some rank N on, u n is within 1 of l.
  have h1 : ∃ N, ∀ n ≥ N, |u n - l| < 1 := by
    sorry
  obtain ⟨N, hN⟩ := h1
  -- Step 2: the first N terms are bounded.
  have h2 : ∃ B, ∀ n < N, |u n| ≤ B := by
    sorry
  obtain ⟨B, hB⟩ := h2
  -- Step 3: the larger of the two bounds works.
  refine ⟨max B (|l| + 1), fun n => ?_⟩
  sorry

-- ▶ Block 426 · Chapter 25: Proof Engineering · Sorry-driven development · page 205 (French edition: page 214)
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
