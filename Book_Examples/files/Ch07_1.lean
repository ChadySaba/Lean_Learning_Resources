import Mathlib
-- ▶ Block 68 · Chapter 7: Tactics, the Core Toolkit · Three basic moves: intro, apply, exact · page 41 (French edition: page 44)

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp        -- hp : p        ⊢ r
  apply hqr       --               ⊢ q
  apply hpq       --               ⊢ p
  exact hp        -- no goals

-- ▶ Block 69 · Chapter 7: Tactics, the Core Toolkit · Three basic moves: intro, apply, exact · page 42 (French edition: page 44)
example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  have hq : q := hpq hp     -- new hypothesis hq : q
  exact hqr hq

-- ▶ Block 70 · Chapter 7: Tactics, the Core Toolkit · Forward steps: have and specialize · page 42 (French edition: page 44)
example (f : ℕ → ℕ) (h : ∀ n, f n < f (n + 1)) : f 0 < f 2 := by
  have h0 : f 0 < f 1 := h 0
  have h1 : f 1 < f 2 := h 1
  omega

-- ▶ Block 72 · Chapter 7: Tactics, the Core Toolkit · Forward steps: have and specialize · page 42 (French edition: page 44)
example (f : ℕ → ℕ) (h : ∀ n, f n < f (n + 1)) : f 5 < f 6 := by
  specialize h 5        -- h : f 5 < f (5 + 1)
  exact h

-- ▶ Block 73 · Chapter 7: Tactics, the Core Toolkit · And: constructor, obtain · page 42 (French edition: page 45)
example (a b : ℝ) (h : 0 < a ∧ a < b) : 0 < b ∧ a ≠ b := by
  obtain ⟨ha, hab⟩ := h     -- ha : 0 < a,  hab : a < b
  constructor
  · linarith                -- case left:  ⊢ 0 < b
  · exact ne_of_lt hab      -- case right: ⊢ a ≠ b

-- ▶ Block 75 · Chapter 7: Tactics, the Core Toolkit · Or: left, right, rcases · page 43 (French edition: page 45)
example (x : ℝ) (h : x = 1 ∨ x = -1) : x ^ 2 = 1 := by
  rcases h with h1 | h2
  · rw [h1]          -- case inl: h1 : x = 1    ⊢ 1 ^ 2 = 1
    norm_num
  · rw [h2]          -- case inr: h2 : x = -1   ⊢ (-1) ^ 2 = 1
    norm_num

-- ▶ Block 76 · Chapter 7: Tactics, the Core Toolkit · Or: left, right, rcases · page 43 (French edition: page 45)
example (n : ℕ) : n = 0 ∨ n ≥ 1 := by
  by_cases h : n = 0
  · left             -- case pos: h : n = 0     ⊢ n = 0
    exact h
  · right            -- case neg: h : ¬n = 0    ⊢ n ≥ 1
    omega

-- ▶ Block 77 · Chapter 7: Tactics, the Core Toolkit · Iff · page 43 (French edition: page 46)
example (a b : ℝ) : a - b = 0 ↔ a = b := by
  constructor
  · intro h         -- h : a - b = 0    ⊢ a = b
    linarith
  · intro h         -- h : a = b        ⊢ a - b = 0
    linarith

-- ▶ Block 78 · Chapter 7: Tactics, the Core Toolkit · Exists: use and obtain · page 44 (French edition: page 46)
example : ∀ n : ℕ, ∃ m : ℕ, n < m := by
  intro n           -- n : ℕ    ⊢ ∃ m, n < m
  use n + 1         --          ⊢ n < n + 1
  omega

-- ▶ Block 79 · Chapter 7: Tactics, the Core Toolkit · Exists: use and obtain · page 44 (French edition: page 46)
example (a : ℝ) (h : ∃ x : ℝ, x > a) : ∃ y : ℝ, y > a - 1 := by
  obtain ⟨x, hx⟩ := h     -- x : ℝ,  hx : x > a
  use x                    -- ⊢ x > a - 1
  linarith

-- ▶ Block 80 · Chapter 7: Tactics, the Core Toolkit · Exists: use and obtain · page 44 (French edition: page 46)
example : ∃ n : ℕ, 5 < n ∧ n < 8 := by
  refine ⟨6, ?_, ?_⟩ <;> norm_num

-- ▶ Block 81 · Chapter 7: Tactics, the Core Toolkit · Negation · page 44 (French edition: page 46)
example (a b : ℝ) (h : a ≤ b) : ¬ b < a := by
  intro hba         -- hba : b < a    ⊢ False
  linarith

-- ▶ Block 82 · Chapter 7: Tactics, the Core Toolkit · Negation · page 44 (French edition: page 47)
example (f : ℕ → ℕ) (h : ¬ ∀ n, f n ≤ 10) : ∃ n, 10 < f n := by
  push Not at h     -- h : ∃ n, 10 < f n
  exact h

-- ▶ Block 83 · Chapter 7: Tactics, the Core Toolkit · Negation · page 45 (French edition: page 47)
example (a b : ℝ) (h : ∀ ε > 0, a ≤ b + ε) : a ≤ b := by
  by_contra hab                              -- hab : ¬a ≤ b    ⊢ False
  push Not at hab                            -- hab : b < a
  have h' := h ((a - b) / 2) (by linarith)   -- h' : a ≤ b + (a - b) / 2
  linarith

-- ▶ Block 84 · Chapter 7: Tactics, the Core Toolkit · Negation · page 45 (French edition: page 47)
example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  -- h : 0 < x
  -- ⊢ ∃ ε > 0, ε < x
  use x / 2
  constructor
  · linarith   -- x / 2 > 0
  · linarith   -- x / 2 < x

-- ▶ Block 85 · Chapter 7: Tactics, the Core Toolkit · Combining tactics · page 46 (French edition: page 48)
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption

-- ▶ Block 86 · Chapter 7: Tactics, the Core Toolkit · Terms inside tactics · page 46 (French edition: page 49)
example (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  exact le_trans hab hbc

-- The same, using dot notation on the proof hab : a ≤ b.
example (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := hab.trans hbc

-- ▶ Block 87 · Chapter 7: Tactics, the Core Toolkit · A complete ε–δ proof · page 46 (French edition: page 49)
example (f : ℝ → ℝ) (h : ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |2 * f x| < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hf⟩ := h (ε / 2) (by linarith)
  use δ, hδ
  intro x hx
  have h1 : |f x| < ε / 2 := hf x hx
  rw [abs_mul, abs_two]
  linarith
