import Mathlib
/-!
# Reachability is a CIC inductive; soundness is its recursor

This file spells out the link between certifying model checking and the Calculus
of Inductive Constructions (CIC) that Lean 4 is built on.

The claim in one line: reachability is a CIC inductive family, and the soundness
of an inductive invariant is exactly that family's recursor.

Concretely:

- Reachable is an ordinary Lean inductive. Its two constructors are the rules
  "start in an initial state" and "take one step".
- CIC inductives are least fixed points: Reachable is the smallest predicate
  closed under those two rules (Reachable.least).
- The soundness of certifying model checking, that an inductive invariant holds
  at every reachable state, is literally the recursor Reachable.rec. We give it
  both as a tactic proof (Inductive.reachable) and as a raw recursor application
  (Inductive.reachable'), and show they are the same term.
- Global safety then follows (safety).

So model-checking soundness is not built with induction, it is CIC induction.
Everything here is self-contained.
-/

namespace CICLink

/-- A transition system: initial states and a step relation. The step is a
relation, so a state may have several successors (the nondeterministic case). -/
structure System (σ : Type*) where
  init : σ → Prop
  step : σ → σ → Prop

/-- Reachability as a CIC inductive. `Reachable S s` means `s` is reached from
some initial state in finitely many steps. The two constructors are the only two
ways a state can be reachable. -/
inductive Reachable {σ : Type*} (S : System σ) : σ → Prop
  | start {s : σ} : S.init s → Reachable S s
  | step {s s' : σ} : Reachable S s → S.step s s' → Reachable S s'

/-- An inductive invariant: a predicate true at every initial state and preserved
by every step. This is the certificate a certifying model checker emits. -/
structure Inductive {σ : Type*} (S : System σ) (P : σ → Prop) : Prop where
  init_holds : ∀ s, S.init s → P s
  step_pres : ∀ s s', P s → S.step s s' → P s'

/-- Soundness, tactic form. An inductive invariant holds at every reachable
state, by induction on the Reachable derivation. -/
theorem Inductive.reachable {σ : Type*} {S : System σ} {P : σ → Prop}
    (h : Inductive S P) : ∀ s, Reachable S s → P s := by
  intro s hs
  induction hs with
  | start hi => exact h.init_holds _ hi
  | step _ hstep ih => exact h.step_pres _ _ ih hstep

/-- Soundness, recursor form. The same theorem, but applying the generated
recursor Reachable.rec directly. The two arguments we hand it are exactly
init_holds and step_pres, so soundness really is the CIC eliminator of
Reachable. -/
theorem Inductive.reachable' {σ : Type*} {S : System σ} {P : σ → Prop}
    (h : Inductive S P) : ∀ s, Reachable S s → P s :=
  fun _s hs =>
    Reachable.rec
      (fun hi => h.init_holds _ hi)
      (fun _ hstep ih => h.step_pres _ _ ih hstep)
      hs

/-- The two soundness proofs are the same object: `induction` elaborates to a
Reachable.rec application. -/
example {σ : Type*} {S : System σ} {P : σ → Prop} (h : Inductive S P) :
    Inductive.reachable h = Inductive.reachable' h := rfl

/-- Least fixed point. Reachable is the smallest predicate closed under the two
rules: any `P` closed under init and step contains Reachable. This is the "least
fixed point" reading of inductives in CIC, and again it is just the recursor. -/
theorem Reachable.least {σ : Type*} {S : System σ} (P : σ → Prop)
    (hinit : ∀ s, S.init s → P s)
    (hstep : ∀ s s', P s → S.step s s' → P s') :
    ∀ s, Reachable S s → P s :=
  Inductive.reachable ⟨hinit, hstep⟩

/-- Safety via an inductive invariant. If an inductive invariant `P` implies a
safety property `Safe`, then every reachable state is safe. -/
theorem safety {σ : Type*} {S : System σ} {P Safe : σ → Prop}
    (hind : Inductive S P) (himp : ∀ s, P s → Safe s) :
    ∀ s, Reachable S s → Safe s :=
  fun s hs => himp s (hind.reachable s hs)

/-!
## A one-state sanity check

A trivial system whose only reachable state is `true`, certified by the invariant
"the flag is on".
-/

/-- A one-bit system: start with the flag on, and the step keeps it on. -/
def flagSystem : System Bool where
  init b := b = true
  step b b' := b = true ∧ b' = true

/-- "The flag is on" is an inductive invariant of flagSystem. -/
theorem flag_inductive : Inductive flagSystem (fun b => b = true) :=
  ⟨fun _ hi => hi, fun _ _ _ hstep => hstep.2⟩

/-- So every reachable state has the flag on. -/
theorem flag_reachable : ∀ b, Reachable flagSystem b → b = true :=
  flag_inductive.reachable

end CICLink
