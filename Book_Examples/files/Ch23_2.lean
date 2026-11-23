import Mathlib
-- ▶ Block 400 · Chapter 23: Metaprogramming · Level 2: macros · page 187 (French edition: page 194)

macro "analysis_trivial" : tactic =>
  `(tactic| first | positivity | (norm_num; done) | linarith | nlinarith | fun_prop)

example (x : ℝ) : 0 ≤ x ^ 2 + 1 := by analysis_trivial
example (x y : ℝ) (h : x < y) : x < y + 1 := by analysis_trivial
example : Continuous fun x : ℝ => x ^ 2 + Real.exp x := by analysis_trivial

-- ▶ Block 401 · Chapter 23: Metaprogramming · Level 2: macros · page 187 (French edition: page 194)
macro "exists_and_done " x:term : tactic => `(tactic| (refine ⟨$x, ?_⟩; simp))

example : ∃ n : Nat, n + 2 = 5 := by exists_and_done 3

-- ▶ Block 402 · Chapter 23: Metaprogramming · Hygiene · page 187 (French edition: page 194) · the book shows an error here
macro "intro_h" : tactic => `(tactic| intro h)

example (p : Prop) : p → p := by
  intro_h
  exact h          -- error: Unknown identifier `h`

-- ▶ Block 403 · Chapter 23: Metaprogramming · Hygiene · page 187 (French edition: page 194)
macro "intro_as " x:ident : tactic => `(tactic| intro $x:ident)

example (p : Prop) : p → p := by
  intro_as h
  exact h

-- ▶ Block 404 · Chapter 23: Metaprogramming · Level 3: syntax and macro_rules · page 188 (French edition: page 195)
syntax "close" : tactic

macro_rules
  | `(tactic| close) => `(tactic| rfl)
macro_rules
  | `(tactic| close) => `(tactic| assumption)
macro_rules
  | `(tactic| close) => `(tactic| omega)

example : 3 = 3 := by close
example (p : Prop) (h : p) : p := by close
example (a : Nat) : a ≤ a + 1 := by close

-- ▶ Block 405 · Chapter 23: Metaprogramming · Level 3: syntax and macro_rules · page 188 (French edition: page 195)
syntax "my_split_ands" : tactic   -- Mathlib already has a split_ands

macro_rules
  | `(tactic| my_split_ands) => `(tactic| first | (constructor <;> my_split_ands) | skip)

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  my_split_ands
  -- three goals: ⊢ p, ⊢ q, ⊢ r
  · exact hp
  · exact hq
  · exact hr

-- ▶ Block 406 · Chapter 23: Metaprogramming · Level 3: syntax and macro_rules · page 188 (French edition: page 195)
syntax "mysum! " term,+ : term

macro_rules
  | `(mysum! $x) => `($x)
  | `(mysum! $x, $xs,*) => `($x + mysum! $xs,*)

#eval mysum! 1, 2, 3, 4      -- 10
