-- ▶ Block 364 · Chapter 21: Functional Programming and Effects · Data you get for free · page 170 (French edition: page 178)
#eval "Lean" ++ " " ++ "4"                  -- "Lean 4"
#eval s!"2 + 2 = {2 + 2}"                  -- "2 + 2 = 4"
#eval "a,b,c".splitOn ","                  -- ["a", "b", "c"]
#eval "42".toNat?                          -- some 42

#eval [1, 2, 3] ++ [4]                     -- [1, 2, 3, 4]
#eval 0 :: [1, 2]                          -- [0, 1, 2]
#eval #[1, 2, 3].push 4                    -- #[1, 2, 3, 4]
#eval #[10, 20, 30][1]!                    -- 20
#eval #[10, 20, 30][5]?                    -- none

#eval (3, "three").1                       -- 3
#eval Float.sqrt 2                         -- 1.414214
#eval (10 : Nat).toFloat / 3               -- 3.333333

-- ▶ Block 365 · Chapter 21: Functional Programming and Effects · Bool and Prop · page 171 (French edition: page 179)
#check (5 == 5)       -- 5 == 5 : Bool
#check (5 = 5)        -- 5 = 5 : Prop

-- ▶ Block 366 · Chapter 21: Functional Programming and Effects · Lists, the functional way · page 171 (French edition: page 179)
#eval List.range 5                               -- [0, 1, 2, 3, 4]
#eval (List.range 5).map (· ^ 2)                 -- [0, 1, 4, 9, 16]
#eval (List.range 10).filter (· % 2 == 0)        -- [0, 2, 4, 6, 8]
#eval (List.range 5).foldl (· + ·) 0             -- 10
#eval [1, 2, 3].sum                              -- 6
#eval [1, 2, 3].zip ["a", "b", "c"]              -- [(1, "a"), (2, "b"), (3, "c")]
#eval [1, 2, 3] |>.map (· * 2) |>.filter (· > 2) -- [4, 6]

-- ▶ Block 367 · Chapter 21: Functional Programming and Effects · Defining functions · page 171 (French edition: page 179)
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

#eval fact 20          -- 2432902008176640000

def describe (n : Nat) : String :=
  if n == 0 then "zero"
  else if n % 2 == 0 then "even"
  else "odd"

def hypot (a b : Float) : Float :=
  let a2 := a * a
  let b2 := b * b
  Float.sqrt (a2 + b2)

#eval hypot 3 4        -- 5.000000

def mean (xs : List Float) : Float :=
  total / n
where
  total := xs.foldl (· + ·) 0
  n := xs.length.toFloat

#eval mean [1, 2, 3, 4]    -- 2.500000

-- ▶ Block 368 · Chapter 21: Functional Programming and Effects · Defining functions · page 172 (French edition: page 180)
inductive Shape where
  | circle (r : Float)
  | rect (w h : Float)
deriving Repr

def Shape.area : Shape → Float
  | .circle r => 3.14159 * r * r
  | .rect w h => w * h

#eval (Shape.rect 2 3).area    -- 6.000000
#eval Shape.circle 1           -- Shape.circle 1.000000

-- ▶ Block 369 · Chapter 21: Functional Programming and Effects · Values that may be missing · page 172 (French edition: page 180)
def safeDiv (a b : Nat) : Option Nat :=
  if b == 0 then none else some (a / b)

#eval safeDiv 10 2               -- some 5
#eval safeDiv 10 0               -- none
#eval (safeDiv 10 0).getD 0      -- 0

-- ▶ Block 370 · Chapter 21: Functional Programming and Effects · Values that may be missing · page 172 (French edition: page 180)
def addDivs (a b c : Nat) : Option Nat := do
  let x ← safeDiv a c
  let y ← safeDiv b c
  return x + y

#eval addDivs 10 20 5            -- some 6
#eval addDivs 10 20 0            -- none

-- ▶ Block 371 · Chapter 21: Functional Programming and Effects · Values that may be missing · page 172 (French edition: page 180)
def parseAge (s : String) : Except String Nat :=
  match s.toNat? with
  | none => .error s!"not a number: {s}"
  | some n => if n > 150 then .error s!"too old: {n}" else .ok n

#eval parseAge "42"              -- Except.ok 42
#eval parseAge "abc"             -- Except.error "not a number: abc"

-- ▶ Block 372 · Chapter 21: Functional Programming and Effects · Loops and mutable variables · page 173 (French edition: page 181)
def sumTo (n : Nat) : Nat := Id.run do
  let mut total := 0
  for i in [0:n+1] do
    total := total + i
  return total

#eval sumTo 100                  -- 5050

def fib (n : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [0:n] do
    (a, b) := (b, a + b)
  return a

#eval fib 90                     -- 2880067194370816120

-- ▶ Block 373 · Chapter 21: Functional Programming and Effects · Loops and mutable variables · page 173 (French edition: page 181)
def primesUpTo (n : Nat) : Array Nat := Id.run do
  let mut isPrime := Array.replicate (n + 1) true
  let mut primes := #[]
  for i in [2:n+1] do
    if isPrime[i]! then
      primes := primes.push i
      let mut j := i * i
      while j ≤ n do
        isPrime := isPrime.set! j false
        j := j + i
  return primes

#eval primesUpTo 50              -- #[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
#eval (primesUpTo 100000).size   -- 9592
