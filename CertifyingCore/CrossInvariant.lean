import Mathlib
import CertifyingCore.TransitionSystem

/-!
# The Theorem 6 cross-invariant as an inductive invariant

This file exhibits the "morphism" between the APN/Kasami crypto formalisation
(Dobbertin 1999, Theorem 6) and model checking.

In the proof of Theorem 6 one has two polynomial families `A_i, B_i` obeying a
shared two-step (Fibonacci-like) linear recurrence

  `s (i+2) = u i · s (i+1) + v i · s i`,

and the crux is a conserved *bilinear cross term* (a discrete Wronskian):

  `A_i · B_{i+1} + A_{i+1} · B_i = z_i`,   with   `z_{i+1} = v_i · z_i`

(the diagonal terms cancel in characteristic `2`).

Here we recast that mechanism through the generic model-checking vocabulary of
`RequestProject/ModelChecking/TransitionSystem.lean`:

* the **Frobenius ladder** `i ↦ i+1` becomes a `TransitionSystem` whose state is
  a sliding window `(i, A i, A (i+1), B i, B (i+1))` and whose `step` computes
  the next window from the recurrence;
* the conserved cross term is an **inductive invariant** of that system:
  it holds in the initial window and is preserved by every step
  (`cross_is_inductiveInvariant`);
* consequently it holds at *every reachable window*
  (`cross_holds_of_reachable`), which is precisely the "conserved for all `i`"
  conclusion of Theorem 6's key identity — now obtained as an instance of the
  generic invariant-soundness theorem `InductiveInvariant.reachable`.

To close the loop we show the windows built from genuine solution sequences are
reachable (`windowState_reachable`) and re-derive the original key identity
(`key_identity_via_reachable`).
-/

namespace ModelChecking.CrossInvariant

open ModelChecking

variable {R : Type*} [CommRing R] [CharP R 2]

/-- A state of the recurrence transition system: the level `i` together with a
sliding window `(A i, A (i+1), B i, B (i+1))` of the two solution sequences. -/
abbrev State (R : Type*) := ℕ × R × R × R × R

/-- The **one-step map** of the two-step recurrence with coefficients `u, v`:
from the window at level `i` it computes the window at level `i+1`, i.e. it
shifts each pair forward and appends the next recurrence value
`u i · s (i+1) + v i · s i`. -/
def next (u v : ℕ → R) : State R → State R
  | (i, a0, a1, b0, b1) => (i + 1, a1, u i * a1 + v i * a0, b1, u i * b1 + v i * b0)

/-- The **transition system** of the two-step recurrence.  A state `(i, a0, a1,
b0, b1)` starts the run iff it sits at level `0` with the correct base value of
the cross term (`a0·b1 + a1·b0 = z 0`); the step relation is `next u v`. -/
def recSystem (u v z : ℕ → R) : TransitionSystem (State R) where
  init := fun s => s.1 = 0 ∧ s.2.1 * s.2.2.2.2 + s.2.2.1 * s.2.2.2.1 = z 0
  step := fun s s' => s' = next u v s

/-- The **safety property / candidate invariant**: at level `i` the cross term
equals `z i`. -/
def crossInv (z : ℕ → R) : State R → Prop
  | (i, a0, a1, b0, b1) => a0 * b1 + a1 * b0 = z i

/-- **The cross term is an inductive invariant** of the recurrence transition
system.  The base case is the initial condition; preservation is the
characteristic-`2` cancellation of the diagonal terms (the same computation as
Dobbertin's `cross_invariant`). -/
theorem cross_is_inductiveInvariant (u v z : ℕ → R)
    (hz : ∀ i, z (i + 1) = v i * z i) :
    InductiveInvariant (recSystem u v z) (crossInv z) := by
  constructor
  · rintro ⟨i, a0, a1, b0, b1⟩ ⟨hi, hcross⟩
    subst hi
    exact hcross
  · rintro ⟨i, a0, a1, b0, b1⟩ s' hcross rfl
    simp only [crossInv, next] at hcross ⊢
    have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
    rw [hz i, ← hcross]
    linear_combination (u i * a1 * b1) * h2

/-- **Soundness instance.**  The cross term equals `z i` at every reachable
window — the "conserved for all `i`" conclusion of Theorem 6, obtained as an
instance of the generic `InductiveInvariant.reachable`. -/
theorem cross_holds_of_reachable (u v z : ℕ → R)
    (hz : ∀ i, z (i + 1) = v i * z i) (s : State R)
    (hs : Reachable (recSystem u v z) s) :
    crossInv z s :=
  (cross_is_inductiveInvariant u v z hz).reachable s hs

/-! ## Closing the loop: reachability of genuine solution windows -/

/-- The window `(i, A i, A (i+1), B i, B (i+1))` built from two genuine solution
sequences `A, B` of the shared recurrence. -/
def windowState (A B : ℕ → R) (i : ℕ) : State R :=
  (i, A i, A (i + 1), B i, B (i + 1))

omit [CharP R 2] in
/-- If `A` and `B` both solve the two-step recurrence, the step relation sends
the window at level `i` to the window at level `i+1`.  This is what makes the
abstract transition system a faithful model of the concrete recurrence. -/
theorem step_windowState (u v : ℕ → R) {A B : ℕ → R}
    (recA : ∀ i, A (i + 2) = u i * A (i + 1) + v i * A i)
    (recB : ∀ i, B (i + 2) = u i * B (i + 1) + v i * B i) (i : ℕ) :
    (recSystem u v (fun _ => (0 : R))).step (windowState A B i)
      (windowState A B (i + 1)) := by
  simp only [recSystem, windowState, next]
  rw [recA i, recB i]

omit [CharP R 2] in
/-- Every solution window is reachable from the level-`0` window, provided the
base cross term matches `z 0`. -/
theorem windowState_reachable (u v z : ℕ → R) {A B : ℕ → R}
    (recA : ∀ i, A (i + 2) = u i * A (i + 1) + v i * A i)
    (recB : ∀ i, B (i + 2) = u i * B (i + 1) + v i * B i)
    (h0 : A 0 * B 1 + A 1 * B 0 = z 0) (i : ℕ) :
    Reachable (recSystem u v z) (windowState A B i) := by
  induction i with
  | zero => exact Reachable.start ⟨rfl, h0⟩
  | succ n ih =>
      refine Reachable.step ih ?_
      simp only [recSystem, windowState, next]
      rw [recA n, recB n]

/-- **Recovering Theorem 6's key identity.**  From the generic invariant
machinery we re-derive the concrete statement `A_i B_{i+1} + A_{i+1} B_i = z_i`
for all `i`: build the reachable solution windows and read off the invariant.
This shows the abstraction is faithful — it reproves the original result. -/
theorem key_identity_via_reachable (u v z : ℕ → R)
    (hz : ∀ i, z (i + 1) = v i * z i) {A B : ℕ → R}
    (recA : ∀ i, A (i + 2) = u i * A (i + 1) + v i * A i)
    (recB : ∀ i, B (i + 2) = u i * B (i + 1) + v i * B i)
    (h0 : A 0 * B 1 + A 1 * B 0 = z 0) (i : ℕ) :
    A i * B (i + 1) + A (i + 1) * B i = z i :=
  cross_holds_of_reachable u v z hz (windowState A B i)
    (windowState_reachable u v z recA recB h0 i)

end ModelChecking.CrossInvariant
