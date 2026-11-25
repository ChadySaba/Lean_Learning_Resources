import Mathlib
-- ▶ Block 277 · Chapter 15: Sets, Functions, Finsets and Sums · Solutions · page 120 (French edition: page 127)

open Set Function

variable {α β γ : Type*} (s t u : Set α) (f : α → β) (v w : Set β)

-- Exercise 1.
example : s ⊆ s ∪ t := by
  intro x hx
  left
  exact hx

-- Exercise 2.
example : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by
  ext x
  simp only [mem_compl_iff, mem_union, mem_inter_iff]
  -- ⊢ ¬(x ∈ s ∨ x ∈ t) ↔ x ∉ s ∧ x ∉ t
  tauto

-- Exercise 3.
example : Icc (0 : ℝ) 1 ⊆ Icc (-1) 2 := by
  intro x ⟨h0, h1⟩
  constructor <;> linarith

-- Exercise 4.
example : f ⁻¹' (v ∩ w) = f ⁻¹' v ∩ f ⁻¹' w := by
  ext x
  rfl

-- Exercise 5.
example : Injective (fun x : ℝ ↦ 3 * x - 2) := by
  intro a b h
  dsimp only at h
  -- h : 3 * a - 2 = 3 * b - 2
  linarith

-- Exercise 6.
example (g : β → γ) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  intro z
  obtain ⟨y, rfl⟩ := hg z
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨x, rfl⟩

-- Exercise 7.
example (n : ℕ) : ∑ i ∈ Finset.range n, (2 * (i : ℝ) + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

-- Exercise 8.
example (n : ℕ) : ∑ i ∈ Finset.range (n + 1), (i : ℝ) ^ 3 = (n * (n + 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

-- Exercise 9.
example (f : ℕ → ℝ) (n : ℕ) (h : ∀ i, f i ≤ 1) : ∑ i ∈ Finset.range n, f i ≤ n := by
  calc ∑ i ∈ Finset.range n, f i
      ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := by
        gcongr with i hi
        exact h i
    _ = n := by simp

-- Exercise 10.
example (f : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring
