import Mathlib
-- ▶ Block 436 · Chapter 25: Proof Engineering · Solutions · page 212 (French edition: page 220)

-- Exercise 1.
def TendsToZero (u : ℕ → ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n| < ε

theorem bounded_mul_tendsToZero (u v : ℕ → ℝ) (M : ℝ) (hM : 0 < M)
    (hu : ∀ n, |u n| ≤ M) (hv : TendsToZero v) : TendsToZero (fun n => u n * v n) := by
  intro ε hε
  -- Step 1: use hv with ε / M.
  have h1 : ∃ N, ∀ n ≥ N, |v n| < ε / M := hv (ε / M) (by positivity)
  obtain ⟨N, hN⟩ := h1
  refine ⟨N, fun n hn => ?_⟩
  -- Step 2: the key inequality.
  have h2 : |u n * v n| ≤ M * |v n| := by
    rw [abs_mul]
    -- ⊢ |u n| * |v n| ≤ M * |v n|
    exact mul_le_mul_of_nonneg_right (hu n) (abs_nonneg _)
  -- Step 3: conclude.
  have h3 : M * |v n| < ε := by
    calc M * |v n| < M * (ε / M) := by gcongr; exact hN n hn
      _ = ε := by field_simp
  exact lt_of_le_of_lt h2 h3

-- Exercise 2.
example (a b : ℝ) (h : 0 ≤ a ∧ 0 ≤ b) : 0 ≤ a * b + a := by
  obtain ⟨ha, hb⟩ := h
  positivity

-- Exercise 3. The error says: h has type (0 : ℕ) < n, and the expected
-- type is (0 : ℝ) < ↑n. The hypothesis is about natural numbers and the
-- goal about real numbers.
example (n : ℕ) (h : 0 < n) : (0 : ℝ) < n := by
  exact_mod_cast h
