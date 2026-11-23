import Mathlib
-- ▶ Block 160 · Chapter 11: Dependent Type Theory, One Level Deeper · Types have types · page 75 (French edition: page 77)

#check ℕ              -- ℕ : Type
#check 2 + 2 = 4      -- 2 + 2 = 4 : Prop
#check Prop           -- Prop : Type
#check Type           -- Type : Type 1
#check Type 1         -- Type 1 : Type 2
#check ℕ → Type       -- ℕ → Type : Type 1

-- ▶ Block 161 · Chapter 11: Dependent Type Theory, One Level Deeper · Functions whose result type depends on the argument · page 75 (French edition: page 77)
#check Fin 3          -- Fin 3 : Type

def lastOf (n : ℕ) : Fin (n + 1) := Fin.last n

#check @lastOf        -- lastOf : (n : ℕ) → Fin (n + 1)
#eval lastOf 4        -- 4

-- ▶ Block 162 · Chapter 11: Dependent Type Theory, One Level Deeper · Functions whose result type depends on the argument · page 76 (French edition: page 78)
#check ∀ n : ℕ, n = n             -- ∀ (n : ℕ), n = n : Prop
#check (n : ℕ) → Fin (n + 1)      -- (n : ℕ) → Fin (n + 1) : Type

-- ▶ Block 163 · Chapter 11: Dependent Type Theory, One Level Deeper · Equal by computation, equal by proof · page 76 (French edition: page 78) · the book shows an error here
example (n : ℕ) : n + 0 = n := rfl     -- works
example (n : ℕ) : 0 + n = n := rfl     -- error

-- ▶ Block 165 · Chapter 11: Dependent Type Theory, One Level Deeper · Equal by computation, equal by proof · page 76 (French edition: page 78)
def square (x : ℝ) : ℝ := x * x

example (x : ℝ) : square x = x * x := rfl

example (x : ℝ) (h : 0 ≤ x * x) : 0 ≤ square x := h

-- ▶ Block 166 · Chapter 11: Dependent Type Theory, One Level Deeper · Equal by computation, equal by proof · page 76 (French edition: page 79)
example (x : ℝ) (h : 0 ≤ x * x) : 0 ≤ square x := by
  change 0 ≤ x * x
  exact h

-- ▶ Block 167 · Chapter 11: Dependent Type Theory, One Level Deeper · Automation does not look inside your definitions · page 77 (French edition: page 79) · the book shows an error here
example (x : ℝ) : square x = x ^ 2 := by
  ring                -- error: unsolved goals ⊢ square x = x ^ 2

example (x : ℝ) : square x = x ^ 2 := by
  unfold square
  -- ⊢ x * x = x ^ 2
  ring

-- ▶ Block 168 · Chapter 11: Dependent Type Theory, One Level Deeper · Propositions carry no data · page 77 (French edition: page 79)
example (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := rfl

-- ▶ Block 169 · Chapter 11: Dependent Type Theory, One Level Deeper · Propositions carry no data · page 77 (French edition: page 79)
example (h : ∃ n : ℕ, n > 3) : ℕ := by
  obtain ⟨n, hn⟩ := h
  exact n

-- ▶ Block 171 · Chapter 11: Dependent Type Theory, One Level Deeper · Subtypes · page 77 (French edition: page 80)
def two : { x : ℝ // 0 < x } := ⟨2, by norm_num⟩

#check two.val            -- ↑two : ℝ
#check two.property       -- two.property : 0 < ↑two

-- ▶ Block 172 · Chapter 11: Dependent Type Theory, One Level Deeper · Subtypes · page 78 (French edition: page 80)
example (a : { x : ℝ // 0 < x }) : 0 < (a : ℝ) := a.property

def addPos (a b : { x : ℝ // 0 < x }) : { x : ℝ // 0 < x } :=
  ⟨a.val + b.val, add_pos a.property b.property⟩

example (a b : { x : ℝ // 0 < x }) (h : (a : ℝ) = b) : a = b := by
  ext
  exact h

-- ▶ Block 173 · Chapter 11: Dependent Type Theory, One Level Deeper · Subtypes · page 78 (French edition: page 80)
example (s : Set ℝ) (a : s) : (a : ℝ) ∈ s := a.property

-- ▶ Block 174 · Chapter 11: Dependent Type Theory, One Level Deeper · Quotients · page 78 (French edition: page 80)
def parityRel : Setoid ℕ where
  r a b := a % 2 = b % 2
  iseqv := {
    refl := fun _ ↦ rfl
    symm := fun h ↦ h.symm
    trans := fun h₁ h₂ ↦ h₁.trans h₂ }

def Parity : Type := Quotient parityRel

def Parity.mk (n : ℕ) : Parity := Quotient.mk parityRel n

-- ▶ Block 175 · Chapter 11: Dependent Type Theory, One Level Deeper · Quotients · page 78 (French edition: page 81)
example : Parity.mk 3 = Parity.mk 7 := by
  apply Quotient.sound
  -- ⊢ 3 ≈ 7
  rfl

def Parity.toBit : Parity → ℕ :=
  Quotient.lift (fun n ↦ n % 2) (fun _ _ h ↦ h)

#eval (Parity.mk 7).toBit       -- 1

theorem Parity.toBit_lt (p : Parity) : p.toBit < 2 := by
  induction p using Quotient.inductionOn with
  | _ n =>
    -- ⊢ toBit ⟦n⟧ < 2
    exact Nat.mod_lt n (by norm_num)

-- ▶ Block 176 · Chapter 11: Dependent Type Theory, One Level Deeper · Choice and noncomputable · page 79 (French edition: page 81)
#check @Classical.choose        -- {p : α → Prop} → (∃ x, p x) → α
#check @Classical.choose_spec   -- (h : ∃ x, p x), p (Classical.choose h)

noncomputable def pick (h : ∃ x : ℝ, x ^ 2 = 2) : ℝ := Classical.choose h

theorem pick_spec (h : ∃ x : ℝ, x ^ 2 = 2) : pick h ^ 2 = 2 :=
  Classical.choose_spec h

-- ▶ Block 178 · Chapter 11: Dependent Type Theory, One Level Deeper · Choice and noncomputable · page 80 (French edition: page 82)
example (f : ℕ → ℕ) (h : ∀ n, ∃ m, f m > n) :
    ∃ g : ℕ → ℕ, ∀ n, f (g n) > n := by
  choose g hg using h
  -- g : ℕ → ℕ
  -- hg : ∀ (n : ℕ), f (g n) > n
  exact ⟨g, hg⟩

-- ▶ Block 179 · Chapter 11: Dependent Type Theory, One Level Deeper · Decidability and if · page 80 (French edition: page 82)
#eval if 3 < 5 then 1 else 0         -- 1

noncomputable def absR (x : ℝ) : ℝ := if 0 ≤ x then x else -x

-- ▶ Block 180 · Chapter 11: Dependent Type Theory, One Level Deeper · Decidability and if · page 80 (French edition: page 82)
example (x : ℝ) : 0 ≤ absR x := by
  unfold absR
  -- ⊢ 0 ≤ if 0 ≤ x then x else -x
  split_ifs with h
  · -- h : 0 ≤ x      ⊢ 0 ≤ x
    exact h
  · -- h : ¬0 ≤ x     ⊢ 0 ≤ -x
    linarith

-- ▶ Block 181 · Chapter 11: Dependent Type Theory, One Level Deeper · Decidability and if · page 80 (French edition: page 82)
example (x : ℝ) (h : 0 ≤ x) : absR x = x := by
  simp [absR, h]

-- ▶ Block 182 · Chapter 11: Dependent Type Theory, One Level Deeper · Decidability and if · page 80 (French edition: page 83) · the book shows an error here
example : (3 : ℕ) < 5 := by decide       -- works
example : (3 : ℝ) < 5 := by decide       -- error: reduction got stuck at Classical.choice
example : (3 : ℝ) < 5 := by norm_num     -- works: norm_num proves it, it does not compute it

-- ▶ Block 183 · Chapter 11: Dependent Type Theory, One Level Deeper · The axioms, again · page 80 (French edition: page 83)
#print axioms funext          -- 'funext' depends on axioms: [Quot.sound]
#print axioms Classical.em
-- 'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound]

-- ▶ Block 184 · Chapter 11: Dependent Type Theory, One Level Deeper · Errors you will meet here · page 81 (French edition: page 84) · the book shows an error here
example (n m : ℕ) (h : n = m) (v : Fin n) (w : Fin m) (hw : w.val = v.val) :
    (h ▸ v : Fin m) = w := by
  rw [h]              -- error: motive is not type correct

example (n m : ℕ) (h : n = m) (v : Fin n) (w : Fin m) (hw : w.val = v.val) :
    (h ▸ v : Fin m) = w := by
  subst h             -- replaces m by n everywhere, in types as well
  ext
  exact hw.symm
