-- ▶ Block 382 · Chapter 21: Functional Programming and Effects · Exercises · page 177 (French edition: page 185) · exercise: errors are normal until you solve it
-- Exercise 1. The sum 1² + 2² + … + n², once with a loop and once with map and sum.
def sumSquares (n : Nat) : Nat := sorry

-- Exercise 2. Is the string equal to its reverse? Use s.toList.
def isPalindrome (s : String) : Bool := sorry

-- Exercise 3. The largest element, if there is one.
def maxOf : List Int → Option Int := sorry

-- Exercise 4. The decimal digits of n, most significant first.
def digits (n : Nat) : List Nat := sorry

-- Exercise 5. The number of primes up to n, by trial division.
def countPrimes (n : Nat) : Nat := sorry

-- Exercise 6. Print the multiplication table of 1, 2, 3 by 1, 2, 3.
def table : IO Unit := sorry

-- Expected:
-- #eval sumSquares 10          -- 385
-- #eval isPalindrome "kayak"   -- true
-- #eval maxOf [3, -1, 7, 2]    -- some 7
-- #eval digits 2026            -- [2, 0, 2, 6]
-- #eval countPrimes 100        -- 25
