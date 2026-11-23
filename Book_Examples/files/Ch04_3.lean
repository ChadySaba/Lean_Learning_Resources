-- ▶ Block 34 · Chapter 4: Your First Hour in the Editor · Solutions · page 27 (French edition: page 30)
-- Exercise 1.
#eval 17 / 5            -- 3
#eval 17 % 5            -- 2
#eval 3 - 7             -- 0
#eval (3 - 7 : Int)     -- -4

-- Exercise 2. `10 < 100` is not an equation, so `rfl` does not apply.
-- `decide` evaluates the statement and finds it true.
example : 2 * 3 = 6 := rfl
example : "ab" ++ "c" = "abc" := rfl
example : 10 < 100 := by decide

-- Exercise 3. After the first rewrite the goal is `a = b`.
example (a b : Nat) (h : a = b) : a * 1 = b := by
  rw [Nat.mul_one]      -- ⊢ a = b
  rw [h]                -- ⊢ b = b, closed automatically

-- Several rewrites can share one pair of brackets.
example (a b : Nat) (h : a = b) : a * 1 = b := by
  rw [Nat.mul_one, h]

-- Exercise 4. The order of the bullets follows the order in `q ∧ p`.
example (p q : Prop) (hp : p) (hq : q) : q ∧ p := by
  constructor
  · exact hq            -- case left:  ⊢ q
  · exact hp            -- case right: ⊢ p

-- Exercise 5. `exact?` answers: exact Nat.mul_add a b c
example (a b c : Nat) : a * (b + c) = a * b + a * c := by
  exact Nat.mul_add a b c

#check Nat.mul_add      -- Nat.mul_add (n m k : Nat) : n * (m + k) = n * m + n * k

-- Exercise 6. There is no proof. `decide` reports:
--   Tactic `decide` proved that the proposition 2 + 2 = 5 is false
