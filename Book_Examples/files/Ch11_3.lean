import Mathlib
-- ▶ Block 186 · Chapter 11: Dependent Type Theory, One Level Deeper · Solutions · page 82 (French edition: page 86)

-- Exercise 1. The third line fails. Multiplication recurses on its second
-- argument: n * 1 unfolds to n * 0 + n, then to 0 + n, which is stuck.

-- Exercise 2.
example (n : ℕ) : n * 1 = n := by
  simp

example (n : ℕ) : n * 1 = n := Nat.mul_one n

-- Exercise 3.
noncomputable def half (a : { x : ℝ // 0 < x }) : { x : ℝ // 0 < x } :=
  ⟨a.val / 2, by
    have h := a.property
    -- h : 0 < ↑a    ⊢ 0 < ↑a / 2
    positivity⟩

-- Exercise 4.
def cube (x : ℝ) : ℝ := x * x * x

example (x : ℝ) : cube (2 * x) = 8 * cube x := by
  unfold cube
  -- ⊢ 2 * x * (2 * x) * (2 * x) = 8 * (x * x * x)
  ring

-- Exercise 5.
def parityRel : Setoid ℕ where
  r a b := a % 2 = b % 2
  iseqv := {
    refl := fun _ ↦ rfl
    symm := fun h ↦ h.symm
    trans := fun h₁ h₂ ↦ h₁.trans h₂ }

def Parity : Type := Quotient parityRel

def Parity.mk (n : ℕ) : Parity := Quotient.mk parityRel n

example : Parity.mk 4 = Parity.mk 10 := by
  apply Quotient.sound
  -- ⊢ 4 ≈ 10
  rfl

-- Exercise 6.
example (h : ∀ x : ℝ, ∃ y : ℝ, x < y) : ∃ f : ℝ → ℝ, ∀ x, x < f x := by
  choose f hf using h
  -- f : ℝ → ℝ     hf : ∀ (x : ℝ), x < f x
  exact ⟨f, hf⟩

-- Exercise 7.
noncomputable def absR (x : ℝ) : ℝ := if 0 ≤ x then x else -x

example (x : ℝ) : absR x = absR (-x) := by
  unfold absR
  split_ifs with h₁ h₂ h₃
  · -- h₁ : 0 ≤ x,  h₂ : 0 ≤ -x     ⊢ x = -x
    linarith
  · -- h₁ : 0 ≤ x,  h₂ : ¬0 ≤ -x    ⊢ x = - -x
    ring
  · -- h₁ : ¬0 ≤ x, h₃ : 0 ≤ -x     ⊢ -x = -x
    rfl
  · -- h₁ : ¬0 ≤ x, h₃ : ¬0 ≤ -x    ⊢ -x = - -x
    linarith
