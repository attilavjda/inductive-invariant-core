import Mathlib

/-!
# Transition systems and inductive invariants

The core pattern of certifying model checking, in its smallest form.

A transition system has a set of initial states and a step relation.
Reachable is the set of states you can get to from an initial state.
An inductive invariant is a predicate that holds at the start and survives
every step. The key fact, InductiveInvariant.reachable, is that such a
predicate then holds at every reachable state.

To prove a safety property (nothing bad ever happens), find an inductive
invariant that implies it; see safety_via_invariant. That invariant is the
certificate a model checker emits, and this theorem is the check.

Two instances live in sibling files: MutexExample.lean (lock-based mutual
exclusion) and CrossInvariant.lean (a conserved cross term of a ladder
recurrence).
-/

namespace ModelChecking

/-- A transition system: which states we may start in, and how one state may
step to a next one. The step is a relation, so steps may be nondeterministic. -/
structure TransitionSystem (State : Type*) where
  init : State → Prop
  step : State → State → Prop

variable {State : Type*}

/-- States reachable from an initial state in finitely many steps. -/
inductive Reachable (T : TransitionSystem State) : State → Prop
  | start {s} (h : T.init s) : Reachable T s
  | step {s s'} (h : Reachable T s) (hstep : T.step s s') : Reachable T s'

/-- `P` is an inductive invariant of `T`: it holds at every initial state and is
preserved by every step. -/
structure InductiveInvariant (T : TransitionSystem State) (P : State → Prop) :
    Prop where
  init_holds : ∀ s, T.init s → P s
  step_preserves : ∀ s s', P s → T.step s s' → P s'

/-- An inductive invariant holds at every reachable state. This is the soundness
of the pattern: the invariant is the certificate, and this is the check. -/
theorem InductiveInvariant.reachable {T : TransitionSystem State}
    {P : State → Prop} (h : InductiveInvariant T P) :
    ∀ s, Reachable T s → P s := by
  intro s hs
  induction hs with
  | start hi => exact h.init_holds _ hi
  | step _ hstep ih => exact h.step_preserves _ _ ih hstep

/-- A safety property holds everywhere reachable if some inductive invariant
implies it. The usual recipe: guess an invariant strong enough to prove safety. -/
theorem safety_via_invariant {T : TransitionSystem State}
    {P Safe : State → Prop} (hinv : InductiveInvariant T P)
    (hstr : ∀ s, P s → Safe s) :
    ∀ s, Reachable T s → Safe s :=
  fun s hs => hstr s (hinv.reachable s hs)

/-- The conjunction of two inductive invariants is an inductive invariant, so a
strong enough invariant can be built up piece by piece. -/
theorem InductiveInvariant.and {T : TransitionSystem State} {P Q : State → Prop}
    (hP : InductiveInvariant T P) (hQ : InductiveInvariant T Q) :
    InductiveInvariant T (fun s => P s ∧ Q s) where
  init_holds s hs := ⟨hP.init_holds s hs, hQ.init_holds s hs⟩
  step_preserves s s' hs hstep :=
    ⟨hP.step_preserves s s' hs.1 hstep, hQ.step_preserves s s' hs.2 hstep⟩

end ModelChecking
