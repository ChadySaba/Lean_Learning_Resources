-- ▶ Block 383 · Chapter 21: Functional Programming and Effects · Solutions · page 177 (French edition: page 185)
-- Exercise 1.
def sumSquares (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [1:n+1] do
    s := s + i * i
  return s

def sumSquares' (n : Nat) : Nat := ((List.range (n + 1)).map (· ^ 2)).sum

-- Exercise 2.
def isPalindrome (s : String) : Bool := s.toList == s.toList.reverse

-- Exercise 3.
def maxOf : List Int → Option Int
  | [] => none
  | x :: xs =>
    match maxOf xs with
    | none => some x
    | some m => some (max x m)

-- Exercise 4.
def digits (n : Nat) : List Nat :=
  if n < 10 then [n] else digits (n / 10) ++ [n % 10]

-- Exercise 5.
def countPrimes (n : Nat) : Nat := Id.run do
  let mut count := 0
  for k in [2:n+1] do
    let mut isP := true
    for d in [2:k] do
      if d * d > k then break
      if k % d == 0 then
        isP := false
        break
    if isP then count := count + 1
  return count

-- Exercise 6.
def table : IO Unit := do
  for i in [1:4] do
    let row := (List.range 3).map (fun j => toString (i * (j + 1)))
    IO.println (String.intercalate " " row)
