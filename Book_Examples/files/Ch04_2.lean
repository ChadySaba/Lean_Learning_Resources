-- ▶ Block 33 · Chapter 4: Your First Hour in the Editor · Exercises · page 27 (French edition: page 29) · exercise: errors are normal until you solve it
-- Exercise 1. Predict each result before looking at the Infoview.
#eval 17 / 5
#eval 17 % 5
#eval 3 - 7
#eval (3 - 7 : Int)

-- Exercise 2. Replace each `sorry` by `rfl` or by `by decide`.
-- One of the three accepts only `by decide`. Which, and why?
example : 2 * 3 = 6 := sorry
example : "ab" ++ "c" = "abc" := sorry
example : 10 < 100 := sorry

-- Exercise 3. Two rewrites: the lemma `Nat.mul_one`, then the hypothesis.
example (a b : Nat) (h : a = b) : a * 1 = b := by
  sorry

-- Exercise 4. Two goals, two bullets.
example (p q : Prop) (hp : p) (hq : q) : q ∧ p := by
  sorry

-- Exercise 5. Let `exact?` find the lemma. Then look at it with `#check`.
example (a b c : Nat) : a * (b + c) = a * b + a * c := by
  sorry

-- Exercise 6. This statement is false. Try `decide` and read the error.
example : 2 + 2 = 5 := by
  sorry
