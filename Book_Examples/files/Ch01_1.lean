-- ▶ Block 1 · Chapter 1: What Lean Is · One system, two uses · page 7 (French edition: page 8)
def double (n : Nat) : Nat := 2 * n

#eval double 21        -- 42

theorem double_eq (n : Nat) : double n = n + n := by
  unfold double
  omega

-- ▶ Block 2 · Chapter 1: What Lean Is · Proofs are terms · page 7 (French edition: page 8)
theorem swap (p q : Prop) (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩

-- ▶ Block 3 · Chapter 1: What Lean Is · Axioms · page 8 (French edition: page 9)
#print axioms double_eq   -- 'double_eq' depends on axioms: [propext, Quot.sound]
#print axioms swap        -- 'swap' does not depend on any axioms
