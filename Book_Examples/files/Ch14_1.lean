import Mathlib
-- ▶ Block 229 · Chapter 14: Numbers, Casts and Their Traps · A numeral takes its type from its surroundings · page 104 (French edition: page 108)

#check 2                  -- 2 : ℕ
#check (2 : ℝ)            -- 2 : ℝ
#check (2 : ℝ) + 2        -- 2 + 2 : ℝ
#check (1 / 2 : ℝ)        -- 1 / 2 : ℝ

-- ▶ Block 230 · Chapter 14: Numbers, Casts and Their Traps · A numeral takes its type from its surroundings · page 104 (French edition: page 108)
#eval (1 / 2 : ℕ)                 -- 0
#eval (1 / 2 : ℚ)                 -- 1 / 2

example : (1 / 2 : ℝ) = 0.5 := by norm_num
example : ((1 / 2 : ℕ) : ℝ) = 0 := by norm_num

-- ▶ Block 231 · Chapter 14: Numbers, Casts and Their Traps · A numeral takes its type from its surroundings · page 105 (French edition: page 109)
#check fun (n : ℕ) ↦ (n / 2 : ℝ)            -- fun n ↦ ↑n / 2        real division
#check fun (n : ℕ) ↦ ((n / 2 : ℕ) : ℝ)      -- fun n ↦ ↑(n / 2)      floor, then cast
#check fun (n m : ℕ) ↦ (n + m : ℝ)          -- fun n m ↦ ↑n + ↑m
#check fun (n m : ℕ) ↦ ((n + m : ℕ) : ℝ)    -- fun n m ↦ ↑(n + m)

-- ▶ Block 232 · Chapter 14: Numbers, Casts and Their Traps · Subtraction on ℕ · page 105 (French edition: page 109)
#eval (2 - 5 : ℕ)                 -- 0

example (n : ℕ) (h : 1 ≤ n) : n - 1 + 1 = n := Nat.sub_add_cancel h
example (n : ℕ) (h : 1 ≤ n) : n - 1 + 1 = n := by omega

-- ▶ Block 233 · Chapter 14: Numbers, Casts and Their Traps · Division · page 105 (French edition: page 109)
#eval (7 / 2 : ℕ)                 -- 3
#eval (7 % 2 : ℕ)                 -- 1
#eval (-7 / 2 : ℤ)                -- -4

example (x : ℝ) : x / 0 = 0 := div_zero x
example : (0 : ℝ)⁻¹ = 0 := inv_zero

-- ▶ Block 234 · Chapter 14: Numbers, Casts and Their Traps · Division · page 105 (French edition: page 110)
#check @div_self                  -- a ≠ 0 → a / a = 1
#check @div_add_div               -- b ≠ 0 → d ≠ 0 → a / b + c / d = (a * d + b * c) / (b * d)

example (x : ℝ) (hx : x ≠ 0) : x * x⁻¹ = 1 := mul_inv_cancel₀ hx

-- ▶ Block 235 · Chapter 14: Numbers, Casts and Their Traps · Division · page 106 (French edition: page 110)
example : √(-1 : ℝ) = 0 := Real.sqrt_eq_zero_of_nonpos (by norm_num)
example (x : ℝ) (hx : 0 ≤ x) : √x ^ 2 = x := Real.sq_sqrt hx
example (x : ℝ) : √(x ^ 2) = |x| := Real.sqrt_sq_eq_abs x

-- ▶ Block 236 · Chapter 14: Numbers, Casts and Their Traps · Casts · page 106 (French edition: page 110) · the book shows an error here
example (m n : ℕ) (h : m ≤ n) : (m : ℝ) ≤ n := by
  exact h
-- error: Type mismatch
--   h
-- has type
--   m ≤ n
-- but is expected to have type
--   ↑m ≤ ↑n

-- ▶ Block 237 · Chapter 14: Numbers, Casts and Their Traps · Casts · page 106 (French edition: page 110)
#check @Nat.cast_add      -- ↑(m + n) = ↑m + ↑n
#check @Nat.cast_mul      -- ↑(m * n) = ↑m * ↑n
#check @Nat.cast_pow      -- ↑(m ^ n) = ↑m ^ n
#check @Nat.cast_le       -- ↑m ≤ ↑n ↔ m ≤ n
#check @Nat.cast_lt       -- ↑m < ↑n ↔ m < n
#check @Nat.cast_inj      -- ↑m = ↑n ↔ m = n
#check @Nat.cast_sub      -- m ≤ n → ↑(n - m) = ↑n - ↑m

-- ▶ Block 238 · Chapter 14: Numbers, Casts and Their Traps · Casts · page 107 (French edition: page 111)
example (m n : ℕ) (h : m ≤ n) : (m : ℝ) ≤ n := by exact_mod_cast h

example (m n : ℕ) (h : (m : ℝ) = n) : m = n := by exact_mod_cast h

example (n m : ℕ) : ((n * m + 3 : ℕ) : ℝ) = n * m + 3 := by
  push_cast
  -- ⊢ ↑n * ↑m + 3 = ↑n * ↑m + 3
  ring

example (n : ℕ) (h : 3 ≤ n) : ((n - 3 : ℕ) : ℝ) = n - 3 := by
  push_cast [h]         -- the hypothesis lets it use Nat.cast_sub
  rfl

-- ▶ Block 239 · Chapter 14: Numbers, Casts and Their Traps · Casts · page 107 (French edition: page 111)
example (n : ℕ) (h : 2 ≤ n) : (4 : ℝ) ≤ n ^ 2 := by
  have h' : (2 : ℝ) ≤ n := by exact_mod_cast h
  nlinarith

-- ▶ Block 240 · Chapter 14: Numbers, Casts and Their Traps · Casts · page 107 (French edition: page 111)
example (a b : ℕ) (h : b ≤ a) (h' : a - b = 3) : a = b + 3 := by
  zify [h] at h' ⊢
  -- h' : ↑a - ↑b = 3     ⊢ ↑a = ↑b + 3       both in ℤ
  linarith

-- ▶ Block 241 · Chapter 14: Numbers, Casts and Their Traps · Casts · page 107 (French edition: page 111)
example (n : ℤ) (hn : 0 ≤ n) : ∃ k : ℕ, (k : ℤ) = n := by
  lift n to ℕ using hn
  -- n : ℕ     ⊢ ∃ k, ↑k = ↑n
  exact ⟨n, rfl⟩

-- ▶ Block 242 · Chapter 14: Numbers, Casts and Their Traps · Powers · page 108 (French edition: page 112)
example (x : ℝ) : x ^ 2 = x * x := sq x
example (x : ℝ) (n : ℕ) : x ^ (n + 1) = x ^ n * x := pow_succ x n
example (x : ℝ) (h : 0 < x) (n : ℕ) : 0 < x ^ n := pow_pos h n
example (x y : ℝ) (h : 0 ≤ x) (hxy : x ≤ y) : x ^ 5 ≤ y ^ 5 := pow_le_pow_left₀ h hxy 5

-- ▶ Block 243 · Chapter 14: Numbers, Casts and Their Traps · Powers · page 108 (French edition: page 112)
example (x : ℝ) : x ^ (1 / 2) = 1 := by norm_num

-- ▶ Block 244 · Chapter 14: Numbers, Casts and Their Traps · Powers · page 108 (French edition: page 112)
example (x : ℝ) : x ^ (1 / 2 : ℝ) = √x := (Real.sqrt_eq_rpow x).symm

-- ▶ Block 245 · Chapter 14: Numbers, Casts and Their Traps · Absolute value, min, max · page 108 (French edition: page 112)
example (x ε : ℝ) (h : |x| < ε) : -ε < x ∧ x < ε := abs_lt.mp h

example (x : ℝ) : |x| ≤ 1 ↔ -1 ≤ x ∧ x ≤ 1 := abs_le

example (x a : ℝ) (h : |x - a| < 1) : x < a + 1 := by
  have h' := abs_lt.mp h
  -- h' : -1 < x - a ∧ x - a < 1
  linarith

-- ▶ Block 246 · Chapter 14: Numbers, Casts and Their Traps · Absolute value, min, max · page 109 (French edition: page 113)
example (δ₁ δ₂ : ℝ) (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) : 0 < min δ₁ δ₂ := lt_min h₁ h₂

-- ▶ Block 247 · Chapter 14: Numbers, Casts and Their Traps · Floor and the Archimedean property · page 109 (French edition: page 113)
example (x : ℝ) : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
example (x : ℝ) : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
example : ⌊(2.5 : ℝ)⌋ = 2 := by norm_num

example (x : ℝ) : ∃ n : ℕ, x < n := exists_nat_gt x

example (ε : ℝ) (hε : 0 < ε) : ∃ n : ℕ, 1 / (n + 1 : ℝ) < ε := exists_nat_one_div_lt hε

-- ▶ Block 248 · Chapter 14: Numbers, Casts and Their Traps · Real numbers and decimals · page 109 (French edition: page 113)
example : (0.1 : ℝ) + 0.2 = 0.3 := by norm_num

#eval (0.1 : Float) + 0.2         -- 0.300000
#eval (0.1 : ℚ) + 0.2             -- 3 / 10

-- ▶ Block 249 · Chapter 14: Numbers, Casts and Their Traps · Real numbers and decimals · page 109 (French edition: page 114)
example (x : ℝ) : 0 < Real.exp x := Real.exp_pos x
example (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y := Real.exp_add x y
example (x y : ℝ) (h : x ≤ y) : Real.exp x ≤ Real.exp y := by gcongr
example (x : ℝ) : x + 1 ≤ Real.exp x := Real.add_one_le_exp x

-- ▶ Block 250 · Chapter 14: Numbers, Casts and Their Traps · Complex numbers · page 110 (French edition: page 114)
example : Complex.I ^ 2 = -1 := Complex.I_sq

example (z w : ℂ) (h₁ : z.re = w.re) (h₂ : z.im = w.im) : z = w := Complex.ext h₁ h₂

example (x : ℝ) : (x : ℂ).re = x := Complex.ofReal_re x

example (z : ℂ) (h : z.im = 0) : z = z.re := by
  apply Complex.ext
  · simp
  · simp [h]

-- ▶ Block 251 · Chapter 14: Numbers, Casts and Their Traps · Extended nonnegative reals · page 110 (French edition: page 114)
open scoped ENNReal

example : (2 : ℝ≥0∞) + ∞ = ∞ := by simp
example : (0 : ℝ≥0∞) * ∞ = 0 := by simp
example : (∞ : ℝ≥0∞) - ∞ = 0 := by simp
example (a : ℝ≥0∞) : a ≤ ∞ := le_top

-- ▶ Block 252 · Chapter 14: Numbers, Casts and Their Traps · Extended nonnegative reals · page 110 (French edition: page 114)
example (x : ℝ) (h : 0 ≤ x) : (ENNReal.ofReal x).toReal = x := ENNReal.toReal_ofReal h

example (a : ℝ≥0∞) (h : a ≠ ∞) : ENNReal.ofReal a.toReal = a := ENNReal.ofReal_toReal h
