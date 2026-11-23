import Mathlib
-- ▶ Block 276 · Chapter 15: Sets, Functions, Finsets and Sums · Exercises · page 120 (French edition: page 125) · exercise: errors are normal until you solve it

open Set Function

variable {α β γ : Type*} (s t u : Set α) (f : α → β) (v w : Set β)

-- Exercise 1.
example : s ⊆ s ∪ t := by
  sorry

-- Exercise 2. Unfold the memberships, then tauto.
example : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by
  sorry

-- Exercise 3. A subset of the real line.
example : Icc (0 : ℝ) 1 ⊆ Icc (-1) 2 := by
  sorry

-- Exercise 4. Preimages unfold by rfl.
example : f ⁻¹' (v ∩ w) = f ⁻¹' v ∩ f ⁻¹' w := by
  sorry

-- Exercise 5.
example : Injective (fun x : ℝ ↦ 3 * x - 2) := by
  sorry

-- Exercise 6. Choose preimages one at a time with obtain ⟨y, rfl⟩.
example (g : β → γ) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  sorry

-- Exercise 7. The sum of the first n odd numbers.
example (n : ℕ) : ∑ i ∈ Finset.range n, (2 * (i : ℝ) + 1) = n ^ 2 := by
  sorry

-- Exercise 8. The sum of the first cubes.
example (n : ℕ) : ∑ i ∈ Finset.range (n + 1), (i : ℝ) ^ 3 = (n * (n + 1) / 2) ^ 2 := by
  sorry

-- Exercise 9. Bound each term by 1.
example (f : ℕ → ℝ) (n : ℕ) (h : ∀ i, f i ≤ 1) : ∑ i ∈ Finset.range n, f i ≤ n := by
  sorry

-- Exercise 10. Telescoping, by induction.
example (f : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0 := by
  sorry
