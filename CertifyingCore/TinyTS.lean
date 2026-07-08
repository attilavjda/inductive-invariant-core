import Mathlib
/-!
# A tiny transition system with a conserved quantity

The same inductive-invariant pattern as TransitionSystem.lean, but with a
deterministic step (a function instead of a relation). We use it to show that a
cross term of a ladder recurrence is conserved along the whole run.

The pattern, once more: an inductive invariant holds at every initial state and
survives every step, so it holds at every reachable state, which lets us conclude
a global fact about the run.

The concrete instance is the second-order recurrence
  X_{i+1} = c_i * X_i - X_{i-1}
whose Casoratian A_i B_{i+1} - A_{i+1} B_i stays constant. In characteristic two
minus is plus, so this is A_i B_{i+1} + A_{i+1} B_i, the Frobenius-ladder cross
term. Everything here is self-contained.

This is the deterministic twin of the nondeterministic pattern in
TransitionSystem.lean and CrossInvariant.lean; see
model-checking-invariant-artifact.md for the side-by-side.
-/
namespace TinyTS

/-- A deterministic transition system: initial states and a step function. -/
structure System (σ : Type*) where
  init : σ → Prop
  step : σ → σ

/-- States reachable from an initial state by finitely many steps. -/
inductive Reachable {σ : Type*} (S : System σ) : σ → Prop
  | base {s : σ} : S.init s → Reachable S s
  | step {s : σ} : Reachable S s → Reachable S (S.step s)

/-- An inductive invariant: a predicate that holds at every initial state and is
preserved by the step. -/
structure Inductive {σ : Type*} (S : System σ) (P : σ → Prop) : Prop where
  init_holds : ∀ s, S.init s → P s
  step_pres : ∀ s, P s → P (S.step s)

/-- An inductive invariant holds at every reachable state. -/
theorem Inductive.reachable {σ : Type*} {S : System σ} {P : σ → Prop}
    (h : Inductive S P) : ∀ s, Reachable S s → P s := by
  intro s hs
  induction hs with
  | base hi => exact h.init_holds _ hi
  | step _ ih => exact h.step_pres _ ih

/-- A safety property holds everywhere reachable if some inductive invariant
implies it. -/
theorem safety {σ : Type*} {S : System σ} {P Safe : σ → Prop}
    (hind : Inductive S P) (himp : ∀ s, P s → Safe s) :
    ∀ s, Reachable S s → Safe s :=
  fun s hs => himp s (hind.reachable s hs)

end TinyTS

/-!
## The conserved cross term of a ladder

We track one rung of the ladder: the index `i` and a window of two consecutive
values of each solution sequence `A` and `B`.
-/
namespace TinyTS.Ladder
variable {R : Type*} [CommRing R]

/-- One rung: index `i` and the window (A_i, B_i, A_{i+1}, B_{i+1}). -/
structure Rung (R : Type*) where
  i : ℕ
  a : R
  b : R
  a' : R
  b' : R

/-- The cross term (Casoratian) of a rung: A_i B_{i+1} - A_{i+1} B_i. -/
def cross (r : Rung R) : R := r.a * r.b' - r.a' * r.b

/-- One ladder step for X_{i+1} = c_i * X_i - X_{i-1}: slide the window forward,
applying the recurrence to both `A` and `B` with coefficient `c i`. -/
def ladderStep (c : ℕ → R) (r : Rung R) : Rung R :=
  { i := r.i + 1
    a := r.a'
    b := r.b'
    a' := c r.i * r.a' - r.a
    b' := c r.i * r.b' - r.b }

/-- The ladder system started from `start`, driven by coefficients `c`. -/
def system (c : ℕ → R) (start : Rung R) : System (Rung R) where
  init s := s = start
  step := ladderStep c

/-- The step conserves the cross term, whatever the coefficient is. -/
theorem cross_ladderStep (c : ℕ → R) (r : Rung R) :
    cross (ladderStep c r) = cross r := by
  simp only [cross, ladderStep]
  ring

/-- Holding the cross term at its starting value is an inductive invariant. -/
theorem cross_isInductive (c : ℕ → R) (start : Rung R) :
    Inductive (system c start) (fun r => cross r = cross start) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    simp only [system] at hs
    subst hs
    rfl
  · intro s hs
    simp only [system]
    rw [cross_ladderStep]
    exact hs

/-- Conservation law: on every reachable rung the cross term equals its starting
value. -/
theorem cross_conserved (c : ℕ → R) (start : Rung R) :
    ∀ r, Reachable (system c start) r → cross r = cross start :=
  (cross_isInductive c start).reachable

/-- In characteristic two the cross term is A_i B_{i+1} + A_{i+1} B_i. -/
theorem cross_char_two [CharP R 2] (r : Rung R) :
    cross r = r.a * r.b' + r.a' * r.b := by
  simp only [cross, sub_eq_add_neg]
  rw [CharTwo.neg_eq]

/-- Conservation law in characteristic two: A_i B_{i+1} + A_{i+1} B_i is constant
along the run. -/
theorem cross_conserved_char_two [CharP R 2] (c : ℕ → R) (start : Rung R) :
    ∀ r, Reachable (system c start) r →
      r.a * r.b' + r.a' * r.b = start.a * start.b' + start.a' * start.b := by
  intro r hr
  rw [← cross_char_two, ← cross_char_two]
  exact cross_conserved c start r hr

/-- A worked safety property: if the cross term starts nonzero, it stays nonzero
on every reachable rung, so the ladder never degenerates. -/
theorem cross_ne_zero_of_start (c : ℕ → R) (start : Rung R) (h0 : cross start ≠ 0) :
    ∀ r, Reachable (system c start) r → cross r ≠ 0 :=
  safety (cross_isInductive c start) (fun _ hr => hr ▸ h0)

end TinyTS.Ladder
