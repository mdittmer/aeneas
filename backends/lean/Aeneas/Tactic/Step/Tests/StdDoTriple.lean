import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result Std.Do

set_option mvcgen.warning false

namespace StdDoTripleStepTests

def echoResult {α : Type} (r : Result α) : Result α := r

@[step]
theorem echoResult_spec {α : Type} (r : Result α) :
    ⦃ ⌜ True ⌝ ⦄ echoResult r ⦃ WP.resultPost (· = r) ⦄ := by
  cases r <;> simp [echoResult, Triple, WP.resultPost, WP.wp, PredTrans.apply]

/- A native Triple tagged with `@[step]` is available through the `step` surface and Std.Do. -/
example {α : Type} (r : Result α) :
    ⦃ ⌜ True ⌝ ⦄ echoResult r ⦃ WP.resultPost (· = r) ⦄ := by
  step

example {α : Type} (r : Result α) :
    ⦃ ⌜ True ⌝ ⦄ echoResult r ⦃ WP.resultPost (· = r) ⦄ := by
  mintro _
  mspec

example {α : Type} (r : Result α) :
    ⦃ ⌜ True ⌝ ⦄ echoResult r ⦃ WP.resultPost (· = r) ⦄ := by
  mvcgen

/- Std.Do applies precondition strengthening and weakens every postcondition branch. -/
example {α : Type} (r : Result α) :
    ⦃ ⌜ r = r ⌝ ⦄ echoResult r ⦃ post⟨
      fun _ => ⌜ True ⌝,
      fun _ => ⌜ True ⌝,
      fun _ => ⌜ True ⌝⟩ ⦄ := by
  step

/- `⇓?` is the native successful-return-only condition: failure and divergence are allowed. -/
example {α : Type} (r : Result α) :
    ⦃ ⌜ True ⌝ ⦄ echoResult r ⦃ ⇓? _ => ⌜ True ⌝ ⦄ := by
  step

def explicitEcho (r : Result Nat) : Result Nat := r

theorem explicitEcho_spec (r : Result Nat) :
    ⦃ ⌜ True ⌝ ⦄ explicitEcho r ⦃ WP.resultPost (· = r) ⦄ := by
  cases r <;> simp [explicitEcho, Triple, WP.resultPost, WP.wp, PredTrans.apply]

/- Keep the theorem argument as syntax so native elaboration supports explicit global theorems,
local hypotheses, and arbitrary theorem terms. -/
example (r : Result Nat) :
    ⦃ ⌜ True ⌝ ⦄ explicitEcho r ⦃ WP.resultPost (· = r) ⦄ := by
  step with explicitEcho_spec

example (r : Result Nat)
    (h : ⦃ ⌜ True ⌝ ⦄ explicitEcho r ⦃ WP.resultPost (· = r) ⦄) :
    ⦃ ⌜ True ⌝ ⦄ explicitEcho r ⦃ WP.resultPost (· = r) ⦄ := by
  step with h

example (r : Result Nat)
    (h : ⦃ ⌜ True ⌝ ⦄ explicitEcho r ⦃ WP.resultPost (· = r) ⦄) :
    ⦃ ⌜ True ⌝ ⦄ explicitEcho r ⦃ WP.resultPost (· = r) ⦄ := by
  step with (show ⦃ ⌜ True ⌝ ⦄ explicitEcho r ⦃ WP.resultPost (· = r) ⦄ from h)

opaque locallySpecified : Result Nat

axiom locallySpecified_spec :
    ⦃ ⌜ True ⌝ ⦄ locallySpecified ⦃ ⇓ n => ⌜ n = 0 ⌝ ⦄

section

attribute [local step] locallySpecified_spec

example : ⦃ ⌜ True ⌝ ⦄ locallySpecified ⦃ ⇓ n => ⌜ n = 0 ⌝ ⦄ := by
  step

end

/- Local native specifications leave the Std.Do database when their section closes. -/
example : ⦃ ⌜ True ⌝ ⦄ locallySpecified ⦃ ⇓ n => ⌜ n = 0 ⌝ ⦄ := by
  fail_if_success step
  exact locallySpecified_spec

opaque scopedSpecified : Result Nat

axiom scopedSpecified_spec :
    ⦃ ⌜ True ⌝ ⦄ scopedSpecified ⦃ ⇓ n => ⌜ n = 1 ⌝ ⦄

scoped[StdDoTripleSpecs] attribute [step] StdDoTripleStepTests.scopedSpecified_spec

section

open scoped StdDoTripleSpecs

example : ⦃ ⌜ True ⌝ ⦄ scopedSpecified ⦃ ⇓ n => ⌜ n = 1 ⌝ ⦄ := by
  step

end

example : ⦃ ⌜ True ⌝ ⦄ scopedSpecified ⦃ ⇓ n => ⌜ n = 1 ⌝ ⦄ := by
  fail_if_success step
  exact scopedSpecified_spec

opaque requireZero (n : Nat) : Result Nat

@[step]
axiom requireZero_spec (n : Nat) :
    ⦃ ⌜ n = 0 ⌝ ⦄ requireZero n ⦃ ⇓ r => ⌜ r = 0 ⌝ ⦄

def okOrDiverge (b : Bool) : Result Nat :=
  if b then .ok 0 else .div

@[step]
theorem okOrDiverge_spec (b : Bool) :
    ⦃ ⌜ True ⌝ ⦄ okOrDiverge b ⦃ post⟨
      fun n => ⌜ n = 0 ⌝,
      fun _ => ⌜ False ⌝,
      fun _ => ⌜ True ⌝⟩ ⦄ := by
  cases b <;> simp [okOrDiverge, Triple, WP.wp, PredTrans.apply]

/- Divergence skips the continuation, so its precondition is needed only on `ok`. -/
example (b : Bool) :
    ⦃ ⌜ True ⌝ ⦄
      (do
        let n ← okOrDiverge b
        requireZero n)
    ⦃ post⟨
      fun n => ⌜ n = 0 ⌝,
      fun _ => ⌜ False ⌝,
      fun _ => ⌜ True ⌝⟩ ⦄ := by
  step*
  simp_all

/- After the initial Triple introduction, subsequent `step` calls remain in Std.Do proof mode. -/
example (b : Bool) :
    ⦃ ⌜ True ⌝ ⦄
      (do
        let n ← okOrDiverge b
        requireZero n)
    ⦃ post⟨
      fun n => ⌜ n = 0 ⌝,
      fun _ => ⌜ False ⌝,
      fun _ => ⌜ True ⌝⟩ ⦄ := by
  step
  step
  simp_all

example (b : Bool) :
    ⦃ ⌜ True ⌝ ⦄
      (do
        let n ← okOrDiverge b
        requireZero n)
    ⦃ post⟨
      fun n => ⌜ n = 0 ⌝,
      fun _ => ⌜ False ⌝,
      fun _ => ⌜ True ⌝⟩ ⦄ := by
  step
  step*
  simp_all

def okOrFail (b : Bool) : Result Nat :=
  if b then .ok 0 else .fail .panic

@[step]
theorem okOrFail_spec (b : Bool) :
    ⦃ ⌜ True ⌝ ⦄ okOrFail b ⦃ post⟨
      fun n => ⌜ n = 0 ⌝,
      fun e => ⌜ e.down = .panic ⌝,
      fun _ => ⌜ False ⌝⟩ ⦄ := by
  cases b <;> simp [okOrFail, Triple, WP.wp, PredTrans.apply]

/- Failure also skips the continuation and is checked against the caller's failure post. -/
example (b : Bool) :
    ⦃ ⌜ True ⌝ ⦄
      (do
        let n ← okOrFail b
        requireZero n)
    ⦃ post⟨
      fun n => ⌜ n = 0 ⌝,
      fun e => ⌜ e.down = .panic ⌝,
      fun _ => ⌜ False ⌝⟩ ⦄ := by
  step*
  simp_all

/- Native dispatch rejects Aeneas-only modifiers rather than changing their meaning. -/
set_option linter.unreachableTactic false in
example {α : Type} (r : Result α) :
    ⦃ ⌜ True ⌝ ⦄ echoResult r ⦃ WP.resultPost (· = r) ⦄ := by
  fail_if_success step -grind
  fail_if_success step as ⟨result⟩
  fail_if_success step by simp
  fail_if_success step?
  fail_if_success let* ⟨result⟩ ← *
  exact echoResult_spec r

example (b : Bool) :
    ⦃ ⌜ True ⌝ ⦄ okOrDiverge b ⦃ post⟨
      fun n => ⌜ n = 0 ⌝,
      fun _ => ⌜ False ⌝,
      fun _ => ⌜ True ⌝⟩ ⦄ := by
  fail_if_success step* 1
  exact okOrDiverge_spec b

/- Deprecated spellings inherit the native dispatch from their `step` replacements. -/
set_option Aeneas.Deprecated.progressWarning false in
example {α : Type} (r : Result α) :
    ⦃ ⌜ True ⌝ ⦄ echoResult r ⦃ WP.resultPost (· = r) ⦄ := by
  progress

set_option Aeneas.Deprecated.progressWarning false in
example (b : Bool) :
    ⦃ ⌜ True ⌝ ⦄ okOrDiverge b ⦃ post⟨
      fun n => ⌜ n = 0 ⌝,
      fun _ => ⌜ False ⌝,
      fun _ => ⌜ True ⌝⟩ ⦄ := by
  progress*

def annotatedTwice : Result Nat := .ok 2

@[step, spec]
theorem annotatedTwice_spec :
    ⦃ ⌜ True ⌝ ⦄ annotatedTwice ⦃ ⇓ n => ⌜ n = 2 ⌝ ⦄ := by
  simp [annotatedTwice, Triple, WP.wp, PredTrans.apply]

example : ⦃ ⌜ True ⌝ ⦄ annotatedTwice ⦃ ⇓ n => ⌜ n = 2 ⌝ ⦄ := by
  step

def reverseAnnotated : Result Nat := .ok 3

@[spec, step]
theorem reverseAnnotated_spec :
    ⦃ ⌜ True ⌝ ⦄ reverseAnnotated ⦃ ⇓ n => ⌜ n = 3 ⌝ ⦄ := by
  simp [reverseAnnotated, Triple, WP.wp, PredTrans.apply]

example : ⦃ ⌜ True ⌝ ⦄ reverseAnnotated ⦃ ⇓ n => ⌜ n = 3 ⌝ ⦄ := by
  step

/--
info: Try this:

  [apply]   mvcgen
-/
#guard_msgs in
example (b : Bool) :
    ⦃ ⌜ True ⌝ ⦄ okOrDiverge b ⦃ post⟨
      fun n => ⌜ n = 0 ⌝,
      fun _ => ⌜ False ⌝,
      fun _ => ⌜ True ⌝⟩ ⦄ := by
  step*?

/--
error: The `step` attribute cannot be erased from native `Std.Do.Triple` theorem `StdDoTripleStepTests.echoResult_spec` because it is forwarded to Std.Do's non-erasable `spec` database. Use a local or scoped `step` attribute when temporary registration is required.
-/
#guard_msgs in
attribute [-step] echoResult_spec

end StdDoTripleStepTests
