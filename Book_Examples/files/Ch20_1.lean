import Mathlib
-- ▶ Block 353 · Chapter 20: A Worked Project in Analysis · Step 1: the statement · page 163 (French edition: page 171)

open Filter Topology

/-- `F n` converges uniformly to `f` on `ℝ`. -/
def UnifConv (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, |F n x - f x| < ε

-- ▶ Block 354 · Chapter 20: A Worked Project in Analysis · Step 2: test the definition · page 163 (French edition: page 172)
-- A constant sequence converges uniformly to its value.
example (f : ℝ → ℝ) : UnifConv (fun _ ↦ f) f := by
  intro ε hε
  use 0
  intro n _ x
  simpa using hε

-- x + 1/(n+1) converges uniformly to x.
example : UnifConv (fun n x ↦ x + 1 / (n + 1 : ℝ)) (fun x ↦ x) := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  use N
  intro n hn x
  have h1 : (0 : ℝ) < 1 / (n + 1) := by positivity
  have h2 : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by gcongr
  have h3 : x + 1 / (n + 1 : ℝ) - x = 1 / (n + 1) := by ring
  rw [h3, abs_of_pos h1]
  linarith

-- ▶ Block 355 · Chapter 20: A Worked Project in Analysis · Step 3: the skeleton · page 164 (French edition: page 172)
theorem continuous_of_unifConv_skeleton (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hF : ∀ n, Continuous (F n)) (hunif : UnifConv F f) : Continuous f := by
  rw [Metric.continuous_iff]
  intro a ε hε
  -- ⊢ ∃ δ > 0, ∀ (a_1 : ℝ), dist a_1 a < δ → dist (f a_1) (f a) < ε
  obtain ⟨N, hN⟩ := hunif (ε / 3) (by positivity)                                  -- choice 1
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.mp (hF N) a (ε / 3) (by positivity)  -- choice 2
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  rw [Real.dist_eq]
  have h1 : |f x - F N x| < ε / 3 := sorry
  have h2 : |F N x - F N a| < ε / 3 := sorry
  have h3 : |F N a - f a| < ε / 3 := sorry
  sorry

-- ▶ Block 357 · Chapter 20: A Worked Project in Analysis · Step 4: isolate the algebra · page 165 (French edition: page 173)
theorem abs_sub_three (a b c d : ℝ) : |a - d| ≤ |a - b| + |b - c| + |c - d| := by
  calc |a - d| = |(a - b) + (b - c) + (c - d)| := by ring_nf
    _ ≤ |(a - b) + (b - c)| + |c - d| := abs_add_le _ _
    _ ≤ |a - b| + |b - c| + |c - d| := by gcongr; exact abs_add_le _ _

-- ▶ Block 358 · Chapter 20: A Worked Project in Analysis · Step 5: fill the gaps · page 165 (French edition: page 173)
theorem continuous_of_unifConv (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hF : ∀ n, Continuous (F n)) (hunif : UnifConv F f) : Continuous f := by
  rw [Metric.continuous_iff]
  intro a ε hε
  obtain ⟨N, hN⟩ := hunif (ε / 3) (by positivity)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.mp (hF N) a (ε / 3) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  rw [Real.dist_eq]
  have h1 : |f x - F N x| < ε / 3 := by
    rw [abs_sub_comm]
    exact hN N le_rfl x
  have h2 : |F N x - F N a| < ε / 3 := by
    have h := hδ' x hx
    rwa [Real.dist_eq] at h
  have h3 : |F N a - f a| < ε / 3 := hN N le_rfl a
  calc |f x - f a|
      ≤ |f x - F N x| + |F N x - F N a| + |F N a - f a| := abs_sub_three _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

-- ▶ Block 359 · Chapter 20: A Worked Project in Analysis · Step 6: check the result · page 166 (French edition: page 174)
#print axioms continuous_of_unifConv
-- 'continuous_of_unifConv' depends on axioms: [propext, Classical.choice, Quot.sound]

-- ▶ Block 360 · Chapter 20: A Worked Project in Analysis · Step 7: compare with Mathlib · page 166 (French edition: page 174)
example (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (hF : ∀ n, Continuous (F n))
    (hunif : TendstoUniformly F f atTop) : Continuous f :=
  hunif.continuous (Frequently.of_forall hF)

-- ▶ Block 361 · Chapter 20: A Worked Project in Analysis · Step 7: compare with Mathlib · page 166 (French edition: page 174)
theorem unifConv_iff (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) :
    UnifConv F f ↔ TendstoUniformly F f atTop := by
  rw [Metric.tendstoUniformly_iff]
  -- ⊢ UnifConv F f ↔ ∀ ε > 0, ∀ᶠ (n : ℕ) in atTop, ∀ (x : ℝ), dist (f x) (F n x) < ε
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    rw [eventually_atTop]
    refine ⟨N, fun n hn x ↦ ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    exact hN n hn x
  · intro h ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h ε hε)
    refine ⟨N, fun n hn x ↦ ?_⟩
    have h' := hN n hn x
    rwa [Real.dist_eq, abs_sub_comm] at h'

theorem continuous_of_unifConv' (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hF : ∀ n, Continuous (F n)) (hunif : UnifConv F f) : Continuous f :=
  ((unifConv_iff F f).mp hunif).continuous (Frequently.of_forall hF)
