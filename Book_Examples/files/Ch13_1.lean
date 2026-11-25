import Mathlib
-- ▶ Block 201 · Chapter 13: Automation · Equalities: ring · page 93 (French edition: page 98)

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
example (a b : ℝ) : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
example (x : ℝ) : (x + 1) / 2 = x / 2 + 1 / 2 := by ring
example (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

-- ▶ Block 202 · Chapter 13: Automation · Equalities: ring · page 93 (French edition: page 98) · the book shows an error here
example (a b : ℝ) (h : a = b + 1) : a ^ 2 = b ^ 2 + 2 * b + 1 := by
  ring
-- error: unsolved goals  ⊢ a ^ 2 = 1 + b * 2 + b ^ 2

-- ▶ Block 203 · Chapter 13: Automation · Equalities: ring · page 93 (French edition: page 99)
-- 1. Rewrite with the hypothesis first.
example (a b : ℝ) (h : a = b + 1) : a ^ 2 = b ^ 2 + 2 * b + 1 := by
  rw [h]
  ring

-- 2. Eliminate the variable.
example (a b : ℝ) (h : a = b + 1) : a ^ 2 = b ^ 2 + 2 * b + 1 := by
  subst h
  ring

-- 3. Say which multiple of the hypothesis gives the goal.
example (a b : ℝ) (h : a = b + 1) : a ^ 2 = b ^ 2 + 2 * b + 1 := by
  linear_combination (a + b + 1) * h

-- ▶ Block 204 · Chapter 13: Automation · Equalities: ring · page 94 (French edition: page 99)
example (a b c : ℝ) : a * (b + c) + 0 = a * b + a * c + 1 := by
  ring_nf
  -- ⊢ a * b + a * c = 1 + a * b + a * c       the statement is false
  sorry

-- ▶ Block 205 · Chapter 13: Automation · Equalities with division: field_simp · page 94 (French edition: page 99)
example (x : ℝ) (hx : x ≠ 0) : (x ^ 2 + x) / x = x + 1 := by
  field_simp

example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    1 / x + 1 / y = (x + y) / (x * y) := by
  field_simp
  -- ⊢ y + x = x + y
  ring

-- ▶ Block 206 · Chapter 13: Automation · Inequalities: linarith · page 94 (French edition: page 99)
example (a b c : ℝ) (h₁ : a < b) (h₂ : b ≤ c) : a < c := by linarith

example (x y : ℝ) (h₁ : 2 * x + y ≤ 5) (h₂ : x - y ≤ 1) : x ≤ 2 := by linarith

example (ε : ℝ) (hε : 0 < ε) : ε / 2 < ε := by linarith

example (x y : ℝ) (h : x < y) (h' : y < x) : False := by linarith

-- ▶ Block 207 · Chapter 13: Automation · Inequalities: linarith · page 95 (French edition: page 100)
example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  linarith [sq_nonneg (a - b)]

example (a b : ℝ) (h : |a - b| < 1) (hb : b = 2) : a < 3 := by
  linarith [abs_lt.mp h]

example (a b : ℝ) (f : ℝ → ℝ) (hf : Monotone f) (h : a ≤ b) : f a ≤ f b + 1 := by
  linarith [hf h]

-- ▶ Block 208 · Chapter 13: Automation · Inequalities: nlinarith · page 95 (French edition: page 100)
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by nlinarith

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by nlinarith

example (x : ℝ) (h : 2 ≤ x) : 4 ≤ x ^ 2 := by nlinarith

-- ▶ Block 209 · Chapter 13: Automation · Inequalities: nlinarith · page 95 (French edition: page 100)
example (a b : ℝ) : a * b ≤ ((a + b) / 2) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

example (a b c : ℝ) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

-- ▶ Block 210 · Chapter 13: Automation · Signs: positivity · page 95 (French edition: page 101)
example (x y : ℝ) : 0 ≤ x ^ 2 + y ^ 2 := by positivity
example (x : ℝ) : 0 < x ^ 2 + 1 := by positivity
example (x : ℝ) (hx : 0 < x) : 0 < x / (x + 1) := by positivity
example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 3 := by positivity
example (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity

-- ▶ Block 211 · Chapter 13: Automation · Signs: positivity · page 95 (French edition: page 101) · the book shows an error here
example (x : ℝ) : 0 ≤ x ^ 2 - x + 1 := by positivity
-- error: failed to prove positivity/nonnegativity/nonzeroness

example (x : ℝ) : 0 ≤ x ^ 2 - x + 1 := by nlinarith [sq_nonneg (x - 1)]

-- ▶ Block 212 · Chapter 13: Automation · Monotonicity: gcongr · page 96 (French edition: page 101)
example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by gcongr

example (a b c : ℝ) (hc : 0 ≤ c) (h : a ≤ b) : a * c ≤ b * c := by gcongr

example (a b : ℝ) (ha : 0 ≤ a) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by gcongr

example (a b : ℝ) (ha : 0 < a) (h : a < b) : 1 / b < 1 / a := by gcongr

-- ▶ Block 213 · Chapter 13: Automation · Monotonicity: gcongr · page 96 (French edition: page 101)
example (f g : ℕ → ℝ) (n : ℕ) (h : ∀ i, f i ≤ g i) :
    ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range n, g i := by
  gcongr with i hi
  -- hi : i ∈ Finset.range n    ⊢ f i ≤ g i
  exact h i

-- ▶ Block 214 · Chapter 13: Automation · Explicit numbers: norm_num · page 96 (French edition: page 102)
example : (2 : ℝ) ^ 10 = 1024 := by norm_num
example : (1 : ℝ) / 3 + 1 / 6 = 1 / 2 := by norm_num
example : (7 : ℝ) / 2 < 4 := by norm_num
example : (3 : ℝ) ≠ 0 := by norm_num
example : |(-3 : ℝ)| = 3 := by norm_num
example : (12345 : ℤ) % 7 = 4 := by norm_num
example : Nat.Prime 101 := by norm_num

-- ▶ Block 215 · Chapter 13: Automation · Explicit numbers: norm_num · page 96 (French edition: page 102)
example (x : ℝ) (h : x = 2) : x ^ 2 + 1 = 5 := by norm_num [h]

example : ∑ i ∈ Finset.range 5, (i : ℝ) = 10 := by
  norm_num [Finset.sum_range_succ]

-- ▶ Block 216 · Chapter 13: Automation · Integers and naturals: omega · page 97 (French edition: page 102)
example (n m : ℕ) (h : n < m) : n + 1 ≤ m := by omega
example (n : ℕ) (h : n % 2 = 1) : (n + 1) % 2 = 0 := by omega
example (n : ℕ) (h : 0 < n) : n - 1 + 1 = n := by omega
example (x y : ℤ) (h : 2 * x + 1 = 2 * y) : False := by omega

-- ▶ Block 217 · Chapter 13: Automation · Integers and naturals: omega · page 97 (French edition: page 102)
example : 7 ∣ 91 := by decide

example (n : ℕ) (h : n < 4) : n ^ 2 < 10 := by
  interval_cases n <;> norm_num

-- ▶ Block 218 · Chapter 13: Automation · simp, in depth · page 98 (French edition: page 103)
example (a b : ℝ) (h : a = 0) : a * b + b = b := by simp [h]

example (f : ℕ → ℕ) (h : ∀ n, f n = n + 1) : f 2 = 3 := by simp [h]

example (a b : ℕ) (h : a = b) : a + 0 = b * 1 := by
  simpa using h

-- ▶ Block 220 · Chapter 13: Automation · simp, in depth · page 98 (French edition: page 103)
example (a b : ℕ) (h : a = b) : a + 0 = b * 1 := by
  simp only [add_zero, mul_one]      -- produced by simp?
  -- ⊢ a = b
  exact h

-- ▶ Block 221 · Chapter 13: Automation · simp, in depth · page 98 (French edition: page 104)
def triple (x : ℝ) : ℝ := 3 * x

@[simp] theorem triple_zero : triple 0 = 0 := by simp [triple]

example (y : ℝ) : (triple 0 + y) * 1 = y := by simp   -- fails without the @[simp] tag

-- ▶ Block 222 · Chapter 13: Automation · Logic and search: tauto, aesop, grind · page 98 (French edition: page 104)
example (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by tauto

example (p q r : Prop) (h : p ∧ (q ∨ r)) : (p ∧ q) ∨ (p ∧ r) := by aesop

example (α : Type) (s t : Set α) : s ∩ t ⊆ s := by aesop

-- ▶ Block 223 · Chapter 13: Automation · Logic and search: tauto, aesop, grind · page 99 (French edition: page 104)
example (f : ℕ → ℕ) (a b : ℕ) (h₁ : f a = b) (h₂ : a = b) : f (f a) = b := by grind

example (a b c : ℤ) (h₁ : a < b) (h₂ : b < c) : a + 2 ≤ c := by grind

example (a b : ℝ) (h : a < b) : a < (a + b) / 2 := by grind

example (xs ys : List ℕ) : (xs ++ ys).length = ys.length + xs.length := by grind

-- ▶ Block 224 · Chapter 13: Automation · Logic and search: tauto, aesop, grind · page 99 (French edition: page 104)
example (a b : ℝ) (h : a ≤ b) : a ≤ b + 1 := by
  try?        -- Try these:  grind    grind only

-- ▶ Block 225 · Chapter 13: Automation · A worked estimate · page 99 (French edition: page 104)
example (a b c ε : ℝ) (h₁ : |a - b| < ε / 2) (h₂ : |b - c| < ε / 2) :
    |a - c| < ε := by
  calc |a - c| = |(a - b) + (b - c)| := by ring_nf
    _ ≤ |a - b| + |b - c| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by gcongr
    _ = ε := by ring

-- ▶ Block 226 · Chapter 13: Automation · A worked estimate · page 99 (French edition: page 105)
example (a b c ε : ℝ) (h₁ : |a - b| < ε / 2) (h₂ : |b - c| < ε / 2) :
    |a - c| < ε := by
  have h := abs_sub_le a b c      -- h : |a - c| ≤ |a - b| + |b - c|
  linarith
