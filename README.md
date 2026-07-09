This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# One pattern, from a crypto proof to model checking

This is the storyline of a single idea told across a handful of small Lean 4
files: **an inductive invariant.** It shows up first inside a cryptography
proof (Dobbertin 1999, Theorem 6), and it turns out to be the *same* pattern
that sits at the heart of model checking — and, one level down, the same thing
as induction in Lean's own foundations (CIC).

The whole story is minimal and self-contained. Every theorem below builds with
no `sorry`.

---

## 1. Spotting the pattern in Theorem 6

[`Theorem6.lean`](https://github.com/attilavjda/dobbertin1999-thm6/blob/main/Theorem6.lean)

Inside the proof of Theorem 6 there are two polynomial sequences `A` and `B`
that obey the same two-step recurrence

```
s (i+2) = u i · s (i+1) + v i · s i
```

The key step of the proof [(equation (11))](https://github.com/attilavjda/dobbertin1999-thm6/blob/8cd5e14cc960a7233172d2126bc6fc76bf613a9b/Theorem6MVP/CrossInvariant.lean#L36) is a *conserved quantity* — a
bilinear **cross term** of the two sequences:

```
A_i · B_{i+1} + A_{i+1} · B_i = z_i ,    with    z_{i+1} = v_i · z_i
```

Two lemmas capture it:

- `Theorem6.cross_invariant` — the cross term at level `i+1` equals
  `v i` times the cross term at level `i`. (In characteristic 2 the diagonal
  terms cancel; that cancellation is what makes it work.)
- `Theorem6.key_identity` — by induction on `i`, if the cross term is
  right at the base then it equals `z i` for **every** `i`.

Read that again in plain words: *the identity holds at the start, and each step
preserves it, so it holds forever.* That is an **inductive invariant**. The
proof of `key_identity` is a hand-rolled induction — the pattern is there, but
hidden inside a crypto argument.

(The underlying determinant view is `Dobbertin.Theorem6.casoratian`: the cross term
is a discrete Wronskian, conserved up to the companion-matrix determinant.)

---

## 2. Naming the pattern: the model-checking framework

[`CertifyingCore/TransitionSystem.lean`](https://github.com/attilavjda/inductive-invariant-core/blob/main/CertifyingCore/TransitionSystem.lean)

If "holds at the start, preserved by every step, therefore holds everywhere" is
a pattern, it deserves its own vocabulary. That is exactly the vocabulary of
(certifying) model checking:

- `TransitionSystem` — a set of initial states and a step
  relation.
- `Reachable` — the states you can get to from an initial state.
- `InductiveInvariant` — a predicate that holds initially
  (`init_holds`) and survives every step (`step_preserves`).
- `InductiveInvariant.reachable` — **the one load-bearing
  theorem:** an inductive invariant holds at every reachable state. This is the
  "soundness" of the whole method: the invariant is the *certificate*, and this
  theorem is the *check*.
- `safety_via_invariant` — to prove "nothing bad ever happens",
  find an inductive invariant strong enough to imply it.
- `InductiveInvariant.and` — invariants compose, so you can build
  a strong one piece by piece.

This is the same shape as `key_identity`, but abstracted away from the crypto.

---

## 3. The textbook payoff: mutual exclusion

[`CertifyingCore/MutexExample.lean`](https://github.com/attilavjda/inductive-invariant-core/blob/main/CertifyingCore/MutexExample.lean)

The "hello world" of safety verification, now a one-liner in this framework.
Two processes share one lock; the safety property is that they are never both in
their critical section at once.

- `lockInv` — the certificate: a process in its
  critical section holds the lock and the other is idle.
- `lockInv_inductive` — it is an inductive invariant.
- `mutualExclusion_reachable` — mutual exclusion
  holds at every reachable state, proved by feeding `lockInv` to
  `safety_via_invariant`.

Same pattern, familiar example.

---

## 4. The conserved-quantity twin

[`FBK-application/CertifyingCore/TinyTS.lean`](https://github.com/attilavjda/inductive-invariant-core/blob/main/CertifyingCore/TinyTS.lean)

The same pattern with a *deterministic* step (a function, not a relation),
applied to a ladder recurrence `X_{i+1} = c_i · X_i − X_{i-1}`.

- `Inductive.reachable` — the framework's soundness theorem again.
- `Ladder.cross` and `TinyTS.Ladder.cross_ladderStep` — the cross term
  (Casoratian) and the fact that one step conserves it.
- `Ladder.cross_isInductive` — "the cross term keeps its starting value"
  is an inductive invariant.
- `Ladder.cross_conserved` — so it is conserved along the whole run.
- `Ladder.cross_char_two` / `cross_conserved_char_two` — in
  characteristic 2 the cross term becomes exactly the Theorem 6 cross term.

This is the bridge: the "conserved quantity" of Theorem 6 and a "safety
invariant" of a transition system are literally the same object.

---

## 5. The punchline: soundness *is* CIC induction

[`CertifyingCore/CICLink.lean`](https://github.com/attilavjda/inductive-invariant-core/blob/main/CertifyingCore/CICLink.lean)

Why is the framework's soundness theorem true? Because `Reachable` is an
ordinary Lean inductive type, and soundness is just its recursor.

- `Inductive.reachable` — soundness, written as a tactic `induction`.
- `Inductive.reachable'` — the *same* theorem, written by applying the
  auto-generated recursor `Reachable.rec` directly; the two arguments it takes
  are exactly `init_holds` and `step_pres`.
- The `example ... := rfl` right after shows these two proofs are the **same
  term**: `induction` just elaborates to `Reachable.rec`.
- `Reachable.least` — the "least fixed point" reading: `Reachable` is
  the smallest predicate closed under the two rules.

So model-checking soundness is not merely *proved by* induction — it **is** CIC
induction, the same mechanism Lean is built on.

---

## 6. Closing the loop: the crypto identity, re-derived

[`CertifyingCore/CrossInvariant.lean`](https://github.com/attilavjda/inductive-invariant-core/blob/main/CertifyingCore/CrossInvariant.lean)

Finally we go back to Theorem 6 and re-tell its key step entirely in the generic
model-checking vocabulary — the "morphism" between the crypto proof and model
checking. The state is a sliding window `(i, A i, A (i+1), B i, B (i+1))`, and
the step computes the next window from the recurrence.

The storyline, lemma by lemma:

- `cross_is_inductiveInvariant` — the cross term is
  an inductive invariant of the recurrence transition system (base = initial
  condition, step = the characteristic-2 cancellation).
- `cross_holds_of_reachable` — so it holds at every
  reachable window, obtained as an instance of the generic
  `InductiveInvariant.reachable`.
- `windowState_reachable` — the windows built from
  genuine solution sequences really are reachable.
- `key_identity_via_reachable` — putting these
  together **re-derives Dobbertin's equation (11)** as a plain instance of the
  generic soundness theorem.

The circle is closed: the identity we spotted by hand in step 1 comes back out
of the generic machinery in step 6.

---

## The one-sentence summary

> An **inductive invariant** — true at the start, preserved by every step,
> therefore true everywhere — is the same idea in three costumes: a *conserved
> quantity* in a cryptography proof (Theorem 6), a *safety certificate* in model
> checking (mutual exclusion), and the *recursor of an inductive type* in Lean's
> foundations (CIC). These files make that one idea explicit and machine-check
> each retelling.

## Files

| File | Role |
|------|------|
| `Theorem6.lean` | Where the pattern is first spotted: `cross_invariant`, `key_identity`. |
| `FBK-application/CertifyingCore/TransitionSystem.lean` | The framework: `InductiveInvariant.reachable`, `safety_via_invariant`, `InductiveInvariant.and`. |
| `FBK-application/CertifyingCore/MutexExample.lean` | Textbook payoff: `mutualExclusion_reachable`. |
| `FBK-application/CertifyingCore/TinyTS.lean` | Conserved-quantity twin: `cross_conserved`. |
| `FBK-application/CertifyingCore/CICLink.lean` | The punchline: `Inductive.reachable'` = `Reachable.rec`. |
| `FBK-application/CertifyingCore/CrossInvariant.lean` | The morphism: `cross_is_inductiveInvariant` → `cross_holds_of_reachable` → `key_identity_via_reachable`. |

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
