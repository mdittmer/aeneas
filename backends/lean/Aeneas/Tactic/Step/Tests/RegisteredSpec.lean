import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace StepStarRegisteredSpecTests

private def advance (x : Nat) : Result Nat :=
  ok (x + 1)

@[local step]
private theorem advance_dspec (x : Nat) :
    WP.dspec (advance x) (fun y => y = x + 1) := by
  simp [advance, WP.dspec]

/- `step*` traverses successive binds under every registered specification statement. -/
example (x : Nat) :
    WP.dspec
      (do
        let y ← advance x
        let z ← advance y
        ok z)
      (fun _ => True) := by
  step*

/--
info: Try this:

  [apply]     let* ⟨ y, y_post ⟩ ← advance_dspec
    let* ⟨ z, z_post ⟩ ← advance_dspec
    agrind
-/
#guard_msgs in
example (x : Nat) :
    WP.dspec
      (do
        let y ← advance x
        let z ← advance y
        ok z)
      (fun _ => True) := by
  step*?

/- Program bifurcations are split before stepping their branches. -/
example (b : Bool) (x : Nat) :
    WP.dspec (if b then advance x else advance (x + 1)) (fun _ => True) := by
  step*

example (x : Option Nat) :
    WP.dspec
      (match x with
      | none => advance 0
      | some x => advance x)
      (fun _ => True) := by
  step*

private def applyContinuation (f : Nat → Result Nat) (x : Nat) : Result Nat :=
  f x

@[local step]
private theorem applyContinuation_dspec
    (f : Nat → Result Nat) (x : Nat) (post : Nat → Prop)
    (hf : ∀ y, y = x → WP.dspec (f y) post) :
    WP.dspec (applyContinuation f x) post := by
  simpa [applyContinuation] using hf x rfl

/- With postcondition inference enabled, recursively process a registered specification nested
under the binders of a higher-order step theorem's precondition. -/
example (x : Nat) :
    WP.dspec (applyContinuation (fun y => advance y) x) (fun _ => True) := by
  step* +inferPost

end StepStarRegisteredSpecTests
