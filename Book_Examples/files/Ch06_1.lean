-- ▶ Block 54 · Chapter 6: Propositions and Proofs · Propositions are types · page 35 (French edition: page 37)
variable (p q r : Prop)

#check p ∧ q                       -- p ∧ q : Prop
#check p → q                       -- p → q : Prop
#check ∀ n : Nat, n + 0 = n        -- ∀ (n : Nat), n + 0 = n : Prop
#check ∃ n : Nat, n * n = 49       -- ∃ n, n * n = 49 : Prop

-- ▶ Block 55 · Chapter 6: Propositions and Proofs · Implication is a function type · page 35 (French edition: page 37)
-- Use: apply hpq to hp.
example (hp : p) (hpq : p → q) : q := hpq hp

-- Prove: assume hp, then produce a proof of r.
example (hpq : p → q) (hqr : q → r) : p → r :=
  fun hp => hqr (hpq hp)

-- ▶ Block 56 · Chapter 6: Propositions and Proofs · For all is a function type too · page 35 (French edition: page 37)
-- Use: apply h to the value you care about.
example (P : Nat → Prop) (h : ∀ n, P n) : P 5 := h 5

-- A hypothesis "for all n, P n implies Q n" takes a number, then a proof.
example (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (h5 : P 5) : Q 5 := h 5 h5

-- Prove: take an arbitrary n.
example : ∀ n : Nat, n + 0 = n := fun n => rfl

-- ▶ Block 57 · Chapter 6: Propositions and Proofs · And is a pair · page 36 (French edition: page 38)
-- Prove: give both proofs between angle brackets, typed \< and \>.
example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

-- Use: take the first or the second component.
example (h : p ∧ q) : p := h.1
example (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩

-- ▶ Block 58 · Chapter 6: Propositions and Proofs · Or is a choice · page 36 (French edition: page 38)
-- Prove: say which side holds.
example (hp : p) : p ∨ q := Or.inl hp
example (hq : q) : p ∨ q := Or.inr hq

-- Use: handle both cases.
example (h : p ∨ q) : q ∨ p :=
  match h with
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq

-- ▶ Block 59 · Chapter 6: Propositions and Proofs · Not is an implication to False · page 36 (French edition: page 38)
-- Use: a proof of p and a proof of ¬p give False.
example (hp : p) (hnp : ¬p) : False := hnp hp

-- From False, anything follows.
example (hp : p) (hnp : ¬p) : q := (hnp hp).elim
example (hp : p) (hnp : ¬p) : q := absurd hp hnp

-- Prove: assume p and derive False. This is the contrapositive.
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp => hnq (hpq hp)

-- ▶ Block 60 · Chapter 6: Propositions and Proofs · Iff is a pair of implications · page 36 (French edition: page 38)
-- Prove: give both directions.
example : p ∧ q ↔ q ∧ p :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

-- Use: .mp is the forward direction, .mpr the backward one.
example (h : p ↔ q) (hp : p) : q := h.mp hp
example (h : p ↔ q) (hq : q) : p := h.mpr hq

-- ▶ Block 61 · Chapter 6: Propositions and Proofs · Exists is a witness with a proof · page 37 (French edition: page 39)
-- Prove: give the witness and a proof that it works.
example : ∃ n : Nat, n * n = 49 := ⟨7, rfl⟩

-- Use: unpack the witness and its property.
example (P : Nat → Prop) (h : ∃ n, P n ∧ n > 0) : ∃ n, P n :=
  match h with
  | ⟨n, hn, _⟩ => ⟨n, hn⟩

-- ▶ Block 62 · Chapter 6: Propositions and Proofs · Intermediate steps and holes · page 37 (French edition: page 39)
example (hpq : p → q) (hqr : q → r) (hp : p) : r :=
  have hq : q := hpq hp
  hqr hq

-- ▶ Block 63 · Chapter 6: Propositions and Proofs · Intermediate steps and holes · page 37 (French edition: page 40) · the book shows an error here
example (hpq : p → q) (hqr : q → r) (hp : p) : r :=
  hqr _
-- error: don't know how to synthesize placeholder
-- context:
-- p q r : Prop
-- hpq : p → q
-- hqr : q → r
-- hp : p
-- ⊢ q

-- ▶ Block 64 · Chapter 6: Propositions and Proofs · Classical reasoning · page 38 (French edition: page 40)
example : p ∨ ¬p := Classical.em p

example (h : ¬¬p) : p := Classical.byContradiction h

-- ▶ Block 65 · Chapter 6: Propositions and Proofs · A theorem is a function · page 38 (French edition: page 40)
theorem and_of (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

#check @and_of     -- and_of : ∀ (p q : Prop), p → q → p ∧ q

example (a b : Prop) (ha : a) (hb : b) : a ∧ b := and_of a b ha hb
