import Lean
-- ▶ Block 413 · Chapter 23: Metaprogramming · Commands · page 191 (French edition: page 199)
open Lean Elab Meta

elab "#type_of " t:term : command => do
  Command.liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    logInfo m!"{e} : {← inferType e}"

#type_of 1 + 1                     -- 1 + 1 : Nat
#type_of fun (x : Nat) => x        -- fun x ↦ x : Nat → Nat
