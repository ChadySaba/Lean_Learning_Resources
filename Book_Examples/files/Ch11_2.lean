import Mathlib
-- ▶ Block 185 · Chapter 11: Dependent Type Theory, One Level Deeper · Exercises · page 81 (French edition: page 85) · exercise: errors are normal until you solve it

-- Exercise 1. Predict which of these five lines are accepted. Then check.
example (n : ℕ) : n + 0 = n := rfl
example (n : ℕ) : n * 0 = 0 := rfl
example (n : ℕ) : n * 1 = n := rfl
example (n : ℕ) : n + 1 = Nat.succ n := rfl
example : 2 * 3 = 6 := rfl

-- Exercise 2. Prove the one that failed.
example (n : ℕ) : n * 1 = n := by
  sorry

-- Exercise 3. Half of a positive real is a positive real.
noncomputable def half (a : { x : ℝ // 0 < x }) : { x : ℝ // 0 < x } :=
  ⟨a.val / 2, sorry⟩

-- Exercise 4. Automation does not unfold definitions.
def cube (x : ℝ) : ℝ := x * x * x

example (x : ℝ) : cube (2 * x) = 8 * cube x := by
  sorry

-- Exercise 5. Two numbers with the same parity have the same class.
def parityRel : Setoid ℕ where
  r a b := a % 2 = b % 2
  iseqv := {
    refl := fun _ ↦ rfl
    symm := fun h ↦ h.symm
    trans := fun h₁ h₂ ↦ h₁.trans h₂ }

def Parity : Type := Quotient parityRel

def Parity.mk (n : ℕ) : Parity := Quotient.mk parityRel n

example : Parity.mk 4 = Parity.mk 10 := by
  sorry

-- Exercise 6. Turn "for every x there is a y" into a function.
example (h : ∀ x : ℝ, ∃ y : ℝ, x < y) : ∃ f : ℝ → ℝ, ∀ x, x < f x := by
  sorry

-- Exercise 7. A definition by cases. Four cases appear after split_ifs.
noncomputable def absR (x : ℝ) : ℝ := if 0 ≤ x then x else -x

example (x : ℝ) : absR x = absR (-x) := by
  sorry
