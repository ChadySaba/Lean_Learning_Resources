import Std.Data.HashMap
-- ▶ Block 374 · Chapter 21: Functional Programming and Effects · Loops and mutable variables · page 173 (French edition: page 180)
open Std

def wordCount (text : String) : HashMap String Nat := Id.run do
  let mut counts : HashMap String Nat := {}
  for w in text.splitOn " " do
    if w != "" then
      counts := counts.insert w (counts.getD w 0 + 1)
  return counts

#eval (wordCount "the cat and the hat and the bat")["the"]?     -- some 3

-- ▶ Block 375 · Chapter 21: Functional Programming and Effects · Recursion that Lean cannot check · page 174 (French edition: page 181) · the book shows an error here
def bad (n : Nat) : Nat :=
  if n = 0 then 0 else bad (n / 2 + 1)
-- error: failed to prove termination …
--   h✝ : ¬n = 0
--   ⊢ n / 2 + 1 < n

-- ▶ Block 376 · Chapter 21: Functional Programming and Effects · Recursion that Lean cannot check · page 174 (French edition: page 181)
def gcd1 (a b : Nat) : Nat :=
  if b = 0 then a else gcd1 b (a % b)
termination_by b
decreasing_by
  apply Nat.mod_lt
  omega

#eval gcd1 48 18                 -- 6

-- ▶ Block 377 · Chapter 21: Functional Programming and Effects · Recursion that Lean cannot check · page 174 (French edition: page 181)
partial def collatzSteps (n : Nat) (steps : Nat := 0) : Nat :=
  if n ≤ 1 then steps
  else if n % 2 == 0 then collatzSteps (n / 2) (steps + 1)
  else collatzSteps (3 * n + 1) (steps + 1)

#eval collatzSteps 27            -- 111

-- ▶ Block 378 · Chapter 21: Functional Programming and Effects · Input and output · page 174 (French edition: page 181)
def greet (name : String) : IO Unit := do
  IO.println s!"Hello, {name}!"

#eval greet "Lean"               -- Hello, Lean!

def countdown : IO Unit := do
  for i in [0:3] do
    IO.println s!"{3 - i}..."
  IO.println "Go!"

-- ▶ Block 379 · Chapter 21: Functional Programming and Effects · A complete program · page 175 (French edition: page 182)
def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln "usage: stats NUMBER..."
    return 1
  | _ =>
    let nums := args.filterMap String.toNat?
    let total := nums.sum
    IO.println s!"count = {nums.length}"
    IO.println s!"sum   = {total}"
    IO.println s!"mean  = {total.toFloat / nums.length.toFloat}"
    return 0
