-- ▶ Block 66 · Chapter 6: Propositions and Proofs · Exercises · page 39 (French edition: page 41) · exercise: errors are normal until you solve it
variable (p q r : Prop)

-- Exercise 1.
example (hp : p) (hq : q) : q ∧ p := sorry

-- Exercise 2. Extract p, then choose the correct side.
example (h : p ∧ q) : p ∨ r := sorry

-- Exercise 3.
example (hpq : p → q) (hqr : q → r) (hp : p) : r := sorry

-- Exercise 4. Nested pairs: h.2.1 is allowed.
example (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := sorry

-- Exercise 5.
example (hnq : ¬q) (h : p ∧ q) : False := sorry

-- Exercise 6. Three assumptions to take: fun hpq hnq hp => …
example : (p → q) → (¬q → ¬p) := sorry

-- Exercise 7.
example (P : Nat → Prop) (h : ∀ n, P n) : P 0 ∧ P 1 := sorry

-- Exercise 8.
example : ∃ n : Nat, n + n = 10 := sorry

-- Exercise 9. Unpack h with a match, then build the new witness.
example (P Q : Nat → Prop) (h : ∃ n, P n) (hPQ : ∀ n, P n → Q n) : ∃ n, Q n := sorry

-- Exercise 10. Two cases.
example (h : p ∨ q) (hpr : p → r) (hqr : q → r) : r := sorry

-- Exercise 11. This direction needs Classical.byContradiction.
example : (¬q → ¬p) → (p → q) := sorry
