import Aeneas.Std.Scalar
import Aeneas.Std.Array
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result Std.Do
set_option mvcgen.warning false

/-!
# Tests: mvcgen spec generation from @[step]

For every @[step] theorem, the attribute handler also generates an `mvcgen` spec.
-/

example {x y : U8} (hmax : x.val + y.val ≤ U8.max) :
    ⦃ ⌜ True ⌝ ⦄ (x + y) ⦃ ⇓ z => ⌜ z.val = x.val + y.val ⌝ ⦄ := by
  mvcgen; scalar_tac

example {x y : U8} :
    ⦃ ⌜ True ⌝ ⦄
      (do
        if x < 10#u8
        then x * 2#u8
        else pure y)
    ⦃ ⇓ z => ⌜ z.val ≠ y → z.val < 20 ⌝ ⦄ := by
  mvcgen <;> scalar_tac

example (arr : Array U8 25#usize) (i : Usize) (a : U8) (hi : i < arr.length) :
    ⦃ ⌜ True ⌝ ⦄
      Array.update arr i a
    ⦃ ⇓ r => ⌜ r.get? i = some a ⌝ ⦄ := by
  mvcgen; grind

namespace ResultPost

/- `⇓?` constrains successful results while admitting both failure and divergence. -/
example (r : Result Nat) :
    ⦃ ⌜ True ⌝ ⦄ r ⦃ ⇓? n => ⌜ n = n ⌝ ⦄ := by
  cases r <;> simp [Triple, WP.wp, PredTrans.apply]

/- An explicit `Std.Do` postcondition can distinguish all three `Result` constructors. -/
example (r : Result Nat) :
    ⦃ ⌜ True ⌝ ⦄ r ⦃ post⟨
      fun n => ⌜ r = .ok n ⌝,
      fun e => ⌜ r = .fail e.down ⌝,
      fun _ => ⌜ r = .div ⌝⟩ ⦄ := by
  cases r <;> simp [Triple, WP.wp, PredTrans.apply]

/- `resultPost` offers the same full-result view without exposing `ULift` or `PUnit`. -/
example (r : Result Nat) :
    ⦃ ⌜ True ⌝ ⦄ r ⦃ WP.resultPost (· = r) ⦄ := by
  cases r <;> simp [Triple, WP.resultPost, WP.wp, PredTrans.apply]

def requireZero (x : Nat) : Result Nat := .ok x

@[spec]
theorem requireZero_spec (x : Nat) :
    ⦃ ⌜ x = 0 ⌝ ⦄ requireZero x ⦃ ⇓ y => ⌜ y = 0 ⌝ ⦄ := by
  simp [requireZero, Triple, WP.wp, PredTrans.apply]

/- Failure and divergence short-circuit a bind: the continuation's precondition is
required only in the successful branch. -/
example (r : Result Nat)
    (hr : ⦃ ⌜ True ⌝ ⦄ r ⦃ post⟨
      fun n => ⌜ n = 0 ⌝,
      fun e => ⌜ e.down = .panic ⌝,
      fun _ => ⌜ True ⌝⟩ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
      (do
        let n ← r
        requireZero n)
    ⦃ post⟨
      fun n => ⌜ n = 0 ⌝,
      fun e => ⌜ e.down = .panic ⌝,
      fun _ => ⌜ True ⌝⟩ ⦄ := by
  mvcgen [hr]

def returnOrDiverge (b : Bool) : Result Nat :=
  if b then .ok 7 else .div

@[step]
theorem returnOrDiverge_dspec (b : Bool) :
    returnOrDiverge b ⦃ n => n = 7 ⦄div := by
  cases b <;> simp [returnOrDiverge, WP.dspec]

/- The generated mvcgen theorem for a `dspec` preserves its exact outcome policy:
failure is impossible, while divergence remains permitted. -/
example (b : Bool) :
    ⦃ ⌜ True ⌝ ⦄ returnOrDiverge b ⦃ post⟨
      fun n => ⌜ n = 7 ⌝,
      fun _ => ⌜ False ⌝,
      fun _ => ⌜ True ⌝⟩ ⦄ := by
  mvcgen

/- The exact `dspec` bridge can be weakened to successful-return-only correctness. -/
example (b : Bool) :
    ⦃ ⌜ True ⌝ ⦄ returnOrDiverge b ⦃ ⇓? n => ⌜ n = 7 ⌝ ⦄ := by
  mvcgen; simp

/- It cannot be strengthened to total successful correctness: the divergent branch is real. -/
example : ¬(⦃ ⌜ True ⌝ ⦄ returnOrDiverge false ⦃ ⇓ n => ⌜ n = 7 ⌝ ⦄) := by
  simp [returnOrDiverge, Triple, WP.wp, PredTrans.apply]

end ResultPost
