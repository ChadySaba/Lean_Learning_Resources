-- ▶ Block 35 · Chapter 5: Terms, Types and Functions · Everything has a type · page 29 (French edition: page 31)
#check 3                -- 3 : Nat
#check (3 : Int)        -- 3 : Int
#check "abc"            -- "abc" : String
#check [1, 2, 3]        -- [1, 2, 3] : List Nat
#check (1, "one")       -- (1, "one") : Nat × String
#check Nat → Nat        -- Nat → Nat : Type
#check Nat              -- Nat : Type
#check Type             -- Type : Type 1

-- ▶ Block 36 · Chapter 5: Terms, Types and Functions · Defining and applying functions · page 29 (French edition: page 31)
def square (n : Nat) : Nat := n * n

#eval square 7          -- 49
#check square           -- square (n : Nat) : Nat

-- ▶ Block 37 · Chapter 5: Terms, Types and Functions · Defining and applying functions · page 29 (French edition: page 31)
#eval square 3 + 1      -- 10, read as (square 3) + 1
#eval square (3 + 1)    -- 16

-- ▶ Block 38 · Chapter 5: Terms, Types and Functions · Functions of several arguments · page 29 (French edition: page 31)
def add (a b : Nat) : Nat := a + b

#check add              -- add (a b : Nat) : Nat
#check add 3            -- add 3 : Nat → Nat
#eval (add 3) 4         -- 7

-- ▶ Block 39 · Chapter 5: Terms, Types and Functions · Functions of several arguments · page 30 (French edition: page 32)
def addThree : Nat → Nat := add 3

#eval addThree 10       -- 13

-- ▶ Block 40 · Chapter 5: Terms, Types and Functions · Anonymous functions · page 30 (French edition: page 32)
#check fun (n : Nat) => n + 1      -- fun n ↦ n + 1 : Nat → Nat
#eval (fun n => n + 1) 5           -- 6
#eval [1, 2, 3].map (fun n => n * n)   -- [1, 4, 9]

-- ▶ Block 41 · Chapter 5: Terms, Types and Functions · Anonymous functions · page 30 (French edition: page 32)
#eval [1, 2, 3].map (· + 10)       -- [11, 12, 13]   (· + 10) is fun x => x + 10
#eval (square ∘ addThree) 2        -- 25             ∘ is composition, typed \o

-- ▶ Block 42 · Chapter 5: Terms, Types and Functions · Anonymous functions · page 30 (French edition: page 32)
def square' : Nat → Nat := fun n => n * n

example : square = square' := rfl

-- ▶ Block 43 · Chapter 5: Terms, Types and Functions · Local names, conditions and cases · page 30 (French edition: page 32)
def hypot2 (a b : Nat) : Nat :=
  let a2 := a * a
  let b2 := b * b
  a2 + b2

#eval hypot2 3 4        -- 25

def absDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

#eval absDiff 3 10      -- 7
#eval absDiff 10 3      -- 7

-- ▶ Block 44 · Chapter 5: Terms, Types and Functions · Local names, conditions and cases · page 30 (French edition: page 32)
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

#eval fact 5            -- 120
#eval fact 30           -- 265252859812191058636308480000000

-- ▶ Block 45 · Chapter 5: Terms, Types and Functions · Implicit arguments · page 31 (French edition: page 33)
def ident (α : Type) (a : α) : α := a

#eval ident Nat 5       -- 5

-- ▶ Block 46 · Chapter 5: Terms, Types and Functions · Implicit arguments · page 31 (French edition: page 33)
def ident' {α : Type} (a : α) : α := a

#eval ident' 5                  -- 5
#eval ident' "x"                -- "x"
#eval @ident' Nat 5             -- 5   @ makes every argument explicit
#eval ident' (α := Nat) 5       -- 5   or name the one you want to give

-- ▶ Block 47 · Chapter 5: Terms, Types and Functions · Implicit arguments · page 31 (French edition: page 33)
#check List.map
-- List.map.{u_1, u_2} {α : Type u_1} {β : Type u_2} (f : α → β) (l : List α) : List β

-- ▶ Block 48 · Chapter 5: Terms, Types and Functions · Namespaces and dot notation · page 31 (French edition: page 33)
#eval [1, 2, 3].length          -- 3   means List.length [1, 2, 3]
#eval (5 : Nat).succ            -- 6   means Nat.succ 5
#eval "abc".length              -- 3   means String.length "abc"

-- ▶ Block 49 · Chapter 5: Terms, Types and Functions · Namespaces and dot notation · page 32 (French edition: page 34)
namespace Geometry

def area (w h : Nat) : Nat := w * h
def perimeter (w h : Nat) : Nat := 2 * (w + h)

#eval area 3 4                  -- 12   inside the namespace, no prefix

end Geometry

#eval Geometry.area 3 4         -- 12   outside, the full name

open Geometry in
#eval perimeter 3 4             -- 14   open for one command only

open Geometry
#eval area 2 2                  -- 4    open for the rest of the file

-- ▶ Block 50 · Chapter 5: Terms, Types and Functions · Variables and sections · page 32 (French edition: page 34)
section
variable (α : Type) (xs : List α)

def twice : List α := xs ++ xs

end

#check twice            -- twice (α : Type) (xs : List α) : List α
#eval twice Nat [1, 2]  -- [1, 2, 1, 2]

-- ▶ Block 51 · Chapter 5: Terms, Types and Functions · Pairs · page 32 (French edition: page 34)
def p : Nat × String := (1, "one")

#eval p.1               -- 1
#eval p.2               -- "one"

def swap {α β : Type} (p : α × β) : β × α := (p.2, p.1)

#eval swap (1, "one")   -- ("one", 1)
