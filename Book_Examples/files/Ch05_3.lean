-- ▶ Block 53 · Chapter 5: Terms, Types and Functions · Solutions · page 34 (French edition: page 36)
def square (n : Nat) : Nat := n * n

-- Exercise 1.
def cube (n : Nat) : Nat := n * n * n
example : cube 3 = 27 := rfl

-- Exercise 2.
def myMax (a b : Nat) : Nat := if a ≤ b then b else a
example : myMax 3 7 = 7 := rfl
example : myMax 7 3 = 7 := rfl

-- Exercise 3. The inner call runs first.
def applyTwice {α : Type} (f : α → α) (a : α) : α := f (f a)
example : applyTwice (· + 3) 10 = 16 := rfl
example : applyTwice (fun s => s ++ "!") "hi" = "hi!!" := rfl

-- Exercise 4. The sum up to n + 1 is (n + 1) plus the sum up to n.
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n
example : sumTo 10 = 55 := rfl

-- Exercise 5.
#check applyTwice (· + 3)   -- applyTwice fun x ↦ x + 3 : Nat → Nat
#check @applyTwice Nat      -- applyTwice : (Nat → Nat) → Nat → Nat
#check applyTwice square    -- applyTwice square : Nat → Nat

-- Exercise 6. `(· + 1)` runs first, then `square`.
def succSquare : Nat → Nat := square ∘ (· + 1)
example : succSquare 4 = 25 := rfl
