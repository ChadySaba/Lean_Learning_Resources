import Mathlib
-- ▶ Block 363 · Chapter 20: A Worked Project in Analysis · Solutions · page 168 (French edition: page 176)

open Filter Topology

def UnifConv (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, |F n x - f x| < ε

-- Exercise 1.
theorem bounded_of_unifConv (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hF : ∀ n, ∃ M, ∀ x, |F n x| ≤ M) (hunif : UnifConv F f) : ∃ M, ∀ x, |f x| ≤ M := by
  obtain ⟨N, hN⟩ := hunif 1 (by norm_num)
  obtain ⟨M, hM⟩ := hF N
  refine ⟨M + 1, fun x ↦ ?_⟩
  have h1 := hN N le_rfl x
  have h2 := hM x
  have h3 : |f x| ≤ |f x - F N x| + |F N x| := by
    calc |f x| = |(f x - F N x) + F N x| := by ring_nf
      _ ≤ |f x - F N x| + |F N x| := abs_add_le _ _
  rw [abs_sub_comm] at h1
  -- h1 : |f x - F N x| < 1     h2 : |F N x| ≤ M     ⊢ |f x| ≤ M + 1
  linarith

-- Exercise 2.
theorem unifConv_unique (F : ℕ → ℝ → ℝ) (f g : ℝ → ℝ)
    (hf : UnifConv F f) (hg : UnifConv F g) : f = g := by
  ext x
  apply eq_of_abs_sub_le_all
  intro ε hε
  -- ⊢ |f x - g x| ≤ ε
  obtain ⟨N₁, h₁⟩ := hf (ε / 2) (by positivity)
  obtain ⟨N₂, h₂⟩ := hg (ε / 2) (by positivity)
  have e₁ := h₁ (max N₁ N₂) (le_max_left _ _) x
  have e₂ := h₂ (max N₁ N₂) (le_max_right _ _) x
  have h := abs_sub_le (f x) (F (max N₁ N₂) x) (g x)
  rw [abs_sub_comm] at e₁
  linarith

-- Exercise 3.
theorem continuous_of_unifConv_metric {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y) (hF : ∀ n, Continuous (F n))
    (hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, dist (F n x) (f x) < ε) : Continuous f := by
  rw [Metric.continuous_iff]
  intro a ε hε
  obtain ⟨N, hN⟩ := hunif (ε / 3) (by positivity)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.mp (hF N) a (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun x hx ↦ ?_⟩
  have h1 : dist (f x) (F N x) < ε / 3 := by
    rw [dist_comm]
    exact hN N le_rfl x
  have h2 : dist (F N x) (F N a) < ε / 3 := hδ' x hx
  have h3 : dist (F N a) (f a) < ε / 3 := hN N le_rfl a
  calc dist (f x) (f a)
      ≤ dist (f x) (F N x) + dist (F N x) (F N a) + dist (F N a) (f a) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring
