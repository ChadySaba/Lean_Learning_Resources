import Mathlib
-- ▶ Block 255 · Chapter 15: Sets, Functions, Finsets and Sums · Sets are predicates · page 113 (French edition: page 119)

open Set

#check ({x : ℝ | 0 < x})         -- {x | 0 < x} : Set ℝ
#check (univ : Set ℝ)            -- univ : Set ℝ      the whole type
#check (∅ : Set ℝ)               -- ∅ : Set ℝ
#check ({1, 2, 3} : Set ℕ)       -- {1, 2, 3} : Set ℕ
#check Icc (0 : ℝ) 1             -- Icc 0 1 : Set ℝ   the closed interval [0, 1]

-- ▶ Block 256 · Chapter 15: Sets, Functions, Finsets and Sums · Membership unfolds to the predicate · page 113 (French edition: page 119)
example : {x : ℝ | 1 < x} ⊆ {x : ℝ | 0 < x} := by
  intro x hx
  -- hx : x ∈ {x | 1 < x}     ⊢ x ∈ {x | 0 < x}
  rw [mem_ofPred_eq] at hx ⊢
  -- hx : 1 < x               ⊢ 0 < x
  linarith

-- ▶ Block 257 · Chapter 15: Sets, Functions, Finsets and Sums · Membership unfolds to the predicate · page 114 (French edition: page 120)
example (x : ℝ) (hx : x ∈ {y : ℝ | 1 < y}) : 0 < x := by
  have h : 1 < x := hx
  linarith

-- ▶ Block 258 · Chapter 15: Sets, Functions, Finsets and Sums · Membership unfolds to the predicate · page 114 (French edition: page 120)
example (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : x ^ 2 ≤ 1 := by
  obtain ⟨h0, h1⟩ := hx
  -- h0 : 0 ≤ x     h1 : x ≤ 1
  nlinarith

example : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by
  constructor <;> norm_num

-- ▶ Block 259 · Chapter 15: Sets, Functions, Finsets and Sums · The operations are the connectives · page 114 (French edition: page 120)
variable {α β : Type*} (s t u : Set α)

example : s ∩ t ⊆ s := by
  intro x hx
  -- hx : x ∈ s ∩ t     ⊢ x ∈ s
  exact hx.1

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rintro x ⟨hs, hu⟩
  exact ⟨h hs, hu⟩

-- ▶ Block 260 · Chapter 15: Sets, Functions, Finsets and Sums · Equality of sets: ext · page 115 (French edition: page 121)
example : s ∩ t = t ∩ s := by
  ext x
  -- ⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨ht, hs⟩
  · rintro ⟨ht, hs⟩
    exact ⟨hs, ht⟩

-- ▶ Block 261 · Chapter 15: Sets, Functions, Finsets and Sums · Equality of sets: ext · page 115 (French edition: page 121)
example : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  ext x
  simp only [mem_inter_iff, mem_union]
  -- ⊢ x ∈ s ∧ (x ∈ t ∨ x ∈ u) ↔ x ∈ s ∧ x ∈ t ∨ x ∈ s ∧ x ∈ u
  tauto

-- ▶ Block 262 · Chapter 15: Sets, Functions, Finsets and Sums · Images and preimages · page 115 (French edition: page 121)
variable (f : α → β) (v : Set β)

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x hx
  -- ⊢ x ∈ f ⁻¹' f '' s,  which means  f x ∈ f '' s
  exact ⟨x, hx, rfl⟩

example : f '' (f ⁻¹' v) ⊆ v := by
  rintro y ⟨x, hx, rfl⟩
  -- hx : x ∈ f ⁻¹' v     ⊢ f x ∈ v
  exact hx

-- ▶ Block 263 · Chapter 15: Sets, Functions, Finsets and Sums · Images and preimages · page 115 (French edition: page 122)
example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨hs, ht⟩, rfl⟩
  -- hs : x ∈ s,  ht : x ∈ t     ⊢ f x ∈ f '' s ∩ f '' t
  exact ⟨⟨x, hs, rfl⟩, ⟨x, ht, rfl⟩⟩

-- ▶ Block 264 · Chapter 15: Sets, Functions, Finsets and Sums · Unions and intersections of families · page 116 (French edition: page 122)
example (A : ℕ → Set ℝ) (x : ℝ) : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := mem_iUnion
example (A : ℕ → Set ℝ) (x : ℝ) : x ∈ ⋂ i, A i ↔ ∀ i, x ∈ A i := mem_iInter

-- ▶ Block 265 · Chapter 15: Sets, Functions, Finsets and Sums · Unions and intersections of families · page 116 (French edition: page 122)
example : ⋃ n : ℕ, Icc (0 : ℝ) n = Ici 0 := by
  ext x
  simp only [mem_iUnion, mem_Icc, mem_Ici]
  -- ⊢ (∃ i, 0 ≤ x ∧ x ≤ ↑i) ↔ 0 ≤ x
  constructor
  · rintro ⟨n, h0, -⟩
    exact h0
  · intro h0
    obtain ⟨n, hn⟩ := exists_nat_gt x      -- hn : x < ↑n
    exact ⟨n, h0, hn.le⟩

-- ▶ Block 266 · Chapter 15: Sets, Functions, Finsets and Sums · Functions · page 116 (French edition: page 122)
open Function

#print Function.Injective     -- ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
#print Function.Surjective    -- ∀ (b : β), ∃ a, f a = b

example : Injective (fun x : ℝ ↦ 2 * x + 1) := by
  intro a b h
  -- h : (fun x ↦ 2 * x + 1) a = (fun x ↦ 2 * x + 1) b     ⊢ a = b
  dsimp only at h
  -- h : 2 * a + 1 = 2 * b + 1
  linarith

example : Surjective (fun x : ℝ ↦ 2 * x + 1) := by
  intro y
  use (y - 1) / 2
  -- ⊢ (fun x ↦ 2 * x + 1) ((y - 1) / 2) = y
  ring

-- ▶ Block 267 · Chapter 15: Sets, Functions, Finsets and Sums · Functions · page 116 (French edition: page 123)
example {γ : Type*} (g : β → γ) (hf : Injective f) (hg : Injective g) :
    Injective (g ∘ f) := by
  intro a b h
  -- h : (g ∘ f) a = (g ∘ f) b     ⊢ a = b
  exact hf (hg h)

-- ▶ Block 268 · Chapter 15: Sets, Functions, Finsets and Sums · Functions · page 117 (French edition: page 123)
example : StrictMono (fun x : ℝ ↦ 2 * x + 1) := by
  intro a b h
  dsimp only
  linarith

-- ▶ Block 269 · Chapter 15: Sets, Functions, Finsets and Sums · Finite sets and sums · page 117 (French edition: page 123)
open Finset

#eval range 5                               -- {0, 1, 2, 3, 4}
#eval Finset.Icc 1 4                        -- {1, 2, 3, 4}
#eval (range 10).filter (fun n ↦ n % 3 = 0) -- {0, 3, 6, 9}
#eval ∑ i ∈ range 5, i ^ 2                  -- 30
#eval ∏ i ∈ range 5, (i + 1)                -- 120

-- ▶ Block 270 · Chapter 15: Sets, Functions, Finsets and Sums · Proving a sum formula · page 117 (French edition: page 123)
#check @sum_range_succ
-- ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f n

-- ▶ Block 271 · Chapter 15: Sets, Functions, Finsets and Sums · Proving a sum formula · page 117 (French edition: page 124)
theorem sum_id (n : ℕ) : ∑ i ∈ range (n + 1), (i : ℝ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    -- ⊢ ↑k * (↑k + 1) / 2 + ↑(k + 1) = ↑(k + 1) * (↑(k + 1) + 1) / 2
    push_cast
    ring

-- ▶ Block 272 · Chapter 15: Sets, Functions, Finsets and Sums · Proving a sum formula · page 118 (French edition: page 124)
example (n : ℕ) : 2 * ∑ i ∈ range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

-- ▶ Block 273 · Chapter 15: Sets, Functions, Finsets and Sums · Proving a sum formula · page 118 (French edition: page 124)
example (x : ℝ) (hx : x ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ i = (x ^ n - 1) / (x - 1) := by
  have h : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    -- ⊢ (x ^ k - 1) / (x - 1) + x ^ k = (x ^ (k + 1) - 1) / (x - 1)
    field_simp
    -- ⊢ x ^ k - 1 + x ^ k * (x - 1) = x ^ (k + 1) - 1
    ring

-- ▶ Block 274 · Chapter 15: Sets, Functions, Finsets and Sums · The algebra of sums · page 119 (French edition: page 125)
example (n : ℕ) : ∑ _i ∈ range n, (1 : ℝ) = n := by simp

-- ▶ Block 275 · Chapter 15: Sets, Functions, Finsets and Sums · Estimating a sum · page 119 (French edition: page 125)
example (f : ℕ → ℝ) (n : ℕ) (M : ℝ) (h : ∀ i, |f i| ≤ M) :
    |∑ i ∈ range n, f i| ≤ n * M := by
  calc |∑ i ∈ range n, f i|
      ≤ ∑ i ∈ range n, |f i| := abs_sum_le_sum_abs f (range n)
    _ ≤ ∑ _i ∈ range n, M := by
        gcongr with i hi
        exact h i
    _ = n * M := by simp
