import Mathlib
import CertifyingCore.TransitionSystem

/-!
# Mutual exclusion, the textbook model-checking example

The classic "hello world" of safety verification, in the generic vocabulary of
TransitionSystem.lean.

Two processes each move between an idle location and a critical section, guarded
by one boolean lock. A process may enter its critical section only when the lock
is free, taking the lock as it enters; on leaving it releases the lock.

The safety property is mutual exclusion: the two processes are never in their
critical sections at the same time. We prove it by giving an inductive invariant
(lockInv) strong enough to imply it, then calling safety_via_invariant.
-/

namespace ModelChecking.MutexExample

open ModelChecking

/-- Where a single process is: idle or in its critical section. -/
inductive Loc
  | idle
  | crit
  deriving DecidableEq, Repr

open Loc

/-- A global state: the location of each process and the lock bit. -/
structure St where
  p1 : Loc
  p2 : Loc
  lock : Bool
  deriving DecidableEq, Repr

/-- The step relation. A process with a free lock may enter its critical section
and take the lock; a process in its critical section may leave and release it. -/
inductive Step : St → St → Prop
  | acquire1 {s : St} (h1 : s.p1 = idle) (hl : s.lock = false) :
      Step s { s with p1 := crit, lock := true }
  | release1 {s : St} (h1 : s.p1 = crit) :
      Step s { s with p1 := idle, lock := false }
  | acquire2 {s : St} (h2 : s.p2 = idle) (hl : s.lock = false) :
      Step s { s with p2 := crit, lock := true }
  | release2 {s : St} (h2 : s.p2 = crit) :
      Step s { s with p2 := idle, lock := false }

/-- The mutex system: both processes start idle with a free lock. -/
def mutexSystem : TransitionSystem St where
  init := fun s => s = { p1 := idle, p2 := idle, lock := false }
  step := Step

/-- Safety property: the two processes are never both in their critical section. -/
def mutualExclusion (s : St) : Prop := ¬ (s.p1 = crit ∧ s.p2 = crit)

/-- The invariant that certifies mutual exclusion: a process in its critical
section holds the lock and the other process is idle. -/
def lockInv (s : St) : Prop :=
  (s.p1 = crit → s.lock = true ∧ s.p2 = idle) ∧
  (s.p2 = crit → s.lock = true ∧ s.p1 = idle)

/-- `lockInv` is an inductive invariant of the mutex system. -/
theorem lockInv_inductive : InductiveInvariant mutexSystem lockInv := by
  constructor
  · rintro s rfl
    refine ⟨?_, ?_⟩ <;> simp
  · rintro s s' hs hstep
    obtain ⟨h1, h2⟩ := hs
    cases hstep with
    | acquire1 hi hl =>
        cases hp2 : s.p2 <;> simp_all [lockInv]
    | release1 hi =>
        cases hp2 : s.p2 <;> simp_all [lockInv]
    | acquire2 hi hl =>
        cases hp1 : s.p1 <;> simp_all [lockInv]
    | release2 hi =>
        cases hp1 : s.p1 <;> simp_all [lockInv]

/-- `lockInv` implies mutual exclusion. -/
theorem lockInv_imp_mutualExclusion (s : St) : lockInv s → mutualExclusion s := by
  rintro h ⟨hc1, hc2⟩
  exact absurd (h.1 hc1).2 (by simp [hc2])

/-- Mutual exclusion holds at every reachable state, certified by `lockInv`. -/
theorem mutualExclusion_reachable (s : St) (hs : Reachable mutexSystem s) :
    mutualExclusion s :=
  safety_via_invariant lockInv_inductive lockInv_imp_mutualExclusion s hs

end ModelChecking.MutexExample
