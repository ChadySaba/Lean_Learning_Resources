-- ▶ Block 52 · Chapter 5: Terms, Types and Functions · Exercises · page 33 (French edition: page 35) · exercise: errors are normal until you solve it
def square (n : Nat) : Nat := n * n

-- Exercise 1.
def cube (n : Nat) : Nat := sorry
example : cube 3 = 27 := rfl

-- Exercise 2. The larger of two numbers, with `if … then … else`.
def myMax (a b : Nat) : Nat := sorry
example : myMax 3 7 = 7 := rfl
example : myMax 7 3 = 7 := rfl

-- Exercise 3. Apply a function twice.
def applyTwice {α : Type} (f : α → α) (a : α) : α := sorry
example : applyTwice (· + 3) 10 = 16 := rfl
example : applyTwice (fun s => s ++ "!") "hi" = "hi!!" := rfl

-- Exercise 4. The sum 0 + 1 + … + n, by cases.
def sumTo : Nat → Nat
  | 0 => sorry
  | n + 1 => sorry
example : sumTo 10 = 55 := rfl

-- Exercise 5. Predict the type of each expression, then check.
#check applyTwice (· + 3)
#check @applyTwice Nat
#check applyTwice square

-- Exercise 6. The function n ↦ (n + 1)², built from `square` with `∘`.
def succSquare : Nat → Nat := sorry
example : succSquare 4 = 25 := rfl
