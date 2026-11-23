import Lean
-- ▶ Block 408 · Chapter 23: Metaprogramming · Expressions · page 189 (French edition: page 196)
open Lean Meta

#eval show MetaM Unit from do
  let e ← mkAppM ``Nat.add #[mkNatLit 2, mkNatLit 3]
  logInfo m!"{e}"                  -- Nat.add 2 3
  logInfo m!"{← inferType e}"      -- Nat
  logInfo m!"{← whnf e}"           -- 5
