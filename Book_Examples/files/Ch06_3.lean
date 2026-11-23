-- ▶ Block 67 · Chapter 6: Propositions and Proofs · Solutions · page 39 (French edition: page 42)
variable (p q r : Prop)

-- Exercise 1.
example (hp : p) (hq : q) : q ∧ p := ⟨hq, hp⟩

-- Exercise 2. h.1 proves p, and p is the left side of p ∨ r.
example (h : p ∧ q) : p ∨ r := Or.inl h.1

-- Exercise 3.
example (hpq : p → q) (hqr : q → r) (hp : p) : r := hqr (hpq hp)

-- Exercise 4. h.1 : p,  h.2.1 : q,  h.2.2 : r.
example (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := ⟨⟨h.1, h.2.1⟩, h.2.2⟩

-- Exercise 5. hnq is a function from q to False.
example (hnq : ¬q) (h : p ∧ q) : False := hnq h.2

-- Exercise 6. The goal ¬p is p → False, hence the third assumption hp.
example : (p → q) → (¬q → ¬p) := fun hpq hnq hp => hnq (hpq hp)

-- Exercise 7.
example (P : Nat → Prop) (h : ∀ n, P n) : P 0 ∧ P 1 := ⟨h 0, h 1⟩

-- Exercise 8. The witness is 5, and 5 + 5 = 10 holds by computation.
example : ∃ n : Nat, n + n = 10 := ⟨5, rfl⟩

-- Exercise 9. The same n works, with hPQ n hn as the proof.
example (P Q : Nat → Prop) (h : ∃ n, P n) (hPQ : ∀ n, P n → Q n) : ∃ n, Q n :=
  match h with
  | ⟨n, hn⟩ => ⟨n, hPQ n hn⟩

-- Exercise 10.
example (h : p ∨ q) (hpr : p → r) (hqr : q → r) : r :=
  match h with
  | Or.inl hp => hpr hp
  | Or.inr hq => hqr hq

-- Exercise 11. Assume ¬q. Then h gives ¬p, which contradicts hp.
example : (¬q → ¬p) → (p → q) :=
  fun h hp => Classical.byContradiction (fun hnq => h hnq hp)
