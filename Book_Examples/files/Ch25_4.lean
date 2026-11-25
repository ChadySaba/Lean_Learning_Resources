import Mathlib
-- ▶ Block 434 · Chapter 25: Proof Engineering · The linters · page 210 (French edition: page 219)

def myDef (n : ℕ) : ℕ := n + 1

theorem unusedArg (a b : ℕ) (h : a = b) : a = a := rfl

#lint
