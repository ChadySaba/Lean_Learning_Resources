-- ▶ Block 20 · Chapter 4: Your First Hour in the Editor · Asking Lean questions · page 23 (French edition: page 25)
#eval 1 + 1                      -- 2
#eval "Hello, " ++ "Lean"        -- "Hello, Lean"
#eval [1, 2, 3].map (· * 2)      -- [2, 4, 6]
#eval 2 ^ 10                     -- 1024
#eval 7 / 2                      -- 3
#eval 2 - 5                      -- 0
#eval (2 - 5 : Int)              -- -3

-- ▶ Block 21 · Chapter 4: Your First Hour in the Editor · Asking Lean questions · page 23 (French edition: page 26)
#check 1 + 1                     -- 1 + 1 : Nat
#check (1 + 1 : Int)             -- 1 + 1 : Int
#check 1 + 1 = 2                 -- 1 + 1 = 2 : Prop
#check Nat.succ                  -- Nat.succ (n : Nat) : Nat
#check Nat.add_comm              -- Nat.add_comm (n m : Nat) : n + m = m + n
#check fun (n : Nat) => n + 1    -- fun n ↦ n + 1 : Nat → Nat

-- ▶ Block 22 · Chapter 4: Your First Hour in the Editor · Asking Lean questions · page 24 (French edition: page 26)
#print Nat
-- inductive Nat : Type
-- number of parameters: 0
-- constructors:
-- Nat.zero : Nat
-- Nat.succ : Nat → Nat

-- ▶ Block 23 · Chapter 4: Your First Hour in the Editor · Statements that need a proof · page 24 (French edition: page 26)
example : 1 + 1 = 2 := rfl

theorem one_add_one : 1 + 1 = 2 := rfl

-- ▶ Block 25 · Chapter 4: Your First Hour in the Editor · A first tactic proof, one step at a time · page 24 (French edition: page 26)
theorem my_first (a b : Nat) (h : a = b) : b + 0 = a := by
  rw [Nat.add_zero]
  rw [h]

-- ▶ Block 28 · Chapter 4: Your First Hour in the Editor · Several goals and bullets · page 25 (French edition: page 27)
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

-- ▶ Block 30 · Chapter 4: Your First Hour in the Editor · sorry, the placeholder · page 25 (French edition: page 27)
theorem hard (a b : Nat) : a + b = b + a := by
  sorry

-- ▶ Block 32 · Chapter 4: Your First Hour in the Editor · Comments · page 26 (French edition: page 28)
-- A comment to the end of the line.

/- A block comment,
   over several lines. -/

/-- A documentation comment. It belongs to the declaration that follows
and appears when you hover over its name. -/
theorem documented : 1 + 1 = 2 := rfl
