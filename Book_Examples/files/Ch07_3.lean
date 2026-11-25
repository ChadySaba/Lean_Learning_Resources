import Mathlib
-- ▶ Block 92 · Chapter 7: Tactics, the Core Toolkit · Solutions · page 49 (French edition: page 51)

-- Exercise 1.
example (p q r : Prop) (hpq : p → q) (hpr : p → r) : p → q ∧ r := by
  intro hp
  constructor
  · exact hpq hp
  · exact hpr hp

-- Exercise 2. `p ∧ q ∧ r` means `p ∧ (q ∧ r)`, and the pattern flattens it.
example (p q r : Prop) (h : p ∧ q ∧ r) : r ∧ p := by
  obtain ⟨hp, -, hr⟩ := h
  exact ⟨hr, hp⟩

-- Exercise 3.
example (p q r : Prop) (h : p ∨ q) (hqr : q → r) : p ∨ r := by
  rcases h with hp | hq
  · left
    exact hp
  · right
    exact hqr hq

-- Exercise 4.
example : ∃ x : ℝ, 2 * x + 1 = 7 := by
  use 3
  norm_num

-- Exercise 5.
example (a : ℝ) (h : ∃ x : ℝ, x > a) : ∃ y : ℝ, y > a - 1 := by
  obtain ⟨x, hx⟩ := h
  use x
  linarith

-- Exercise 6.
example (f : ℕ → ℝ) (h : ∀ n, f n ≤ f (n + 1)) : f 0 ≤ f 2 := by
  have h0 : f 0 ≤ f 1 := h 0
  have h1 : f 1 ≤ f 2 := h 1
  linarith

-- Exercise 7.
example (a b : ℝ) (h : a < b) : ¬ b ≤ a := by
  intro hba
  linarith

-- Exercise 8. If a > 0, then a ≤ a / 2, which is absurd.
example (a : ℝ) (h : ∀ ε > 0, a ≤ ε) : a ≤ 0 := by
  by_contra! ha                             -- ha : 0 < a
  have h' := h (a / 2) (by linarith)        -- h' : a ≤ a / 2
  linarith

-- Exercise 9.
example (f : ℝ → ℝ) (h : ¬ ∃ M, ∀ x, f x ≤ M) : ∀ M, ∃ x, M < f x := by
  push Not at h
  exact h

-- Exercise 10.
example (a b : ℝ) : a ≤ b ↔ 0 ≤ b - a := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

-- Exercise 11.
example (x : ℝ) : 0 ≤ x ∨ x < 0 := by
  by_cases h : 0 ≤ x
  · left
    exact h
  · right
    push Not at h
    exact h

-- Exercise 12. Take the smaller of the two δ, then use the triangle inequality.
example (f g : ℝ → ℝ)
    (hf : ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x| < ε)
    (hg : ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |g x| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x + g x| < ε := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg (ε / 2) (by linarith)
  use min δ₁ δ₂, lt_min hδ₁ hδ₂
  intro x hx
  have hx₁ : |x| < δ₁ := lt_of_lt_of_le hx (min_le_left δ₁ δ₂)
  have hx₂ : |x| < δ₂ := lt_of_lt_of_le hx (min_le_right δ₁ δ₂)
  have hf' : |f x| < ε / 2 := h₁ x hx₁
  have hg' : |g x| < ε / 2 := h₂ x hx₂
  have htri : |f x + g x| ≤ |f x| + |g x| := abs_add_le (f x) (g x)
  linarith
