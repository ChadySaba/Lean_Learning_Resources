import Std.Tactic.Do
-- ▶ Block 396 · Chapter 22: Verified Programs · Loops · page 183 (French edition: page 191)
open Std.Do

def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out

theorem mySum_correct (l : Array Nat) : mySum l = l.sum := by
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  all_goals mleave; grind
