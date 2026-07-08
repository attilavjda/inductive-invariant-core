import CertifyingCore.TransitionSystem
import CertifyingCore.MutexExample
import CertifyingCore.TinyTS
import CertifyingCore.CICLink
import CertifyingCore.CrossInvariant

/-!
# CertifyingCore — the certifying-model-checking core

Umbrella module for the self-contained "transition system + inductive
invariant" pattern that underpins certifying model checking, together with a
worked cryptographic instance.

* `CertifyingCore.TransitionSystem` — the generic framework: `TransitionSystem`,
  `Reachable`, `InductiveInvariant`, `InductiveInvariant.reachable`,
  `safety_via_invariant`.
* `CertifyingCore.MutexExample` — a textbook lock-based mutual-exclusion system
  whose safety property is certified by an inductive invariant.
* `CertifyingCore.TinyTS` — a streamlined deterministic-step twin of the same
  pattern, instantiated on a second-order linear ladder whose Casoratian is a
  conserved inductive invariant.
* `CertifyingCore.CICLink` — the bridge to Lean's own foundations: `Reachable`
  is a CIC inductive family and soundness of an inductive invariant is literally
  its recursor. Certifying-model-checking soundness *is* CIC induction.
* `CertifyingCore.CrossInvariant` — the same pattern applied to a Frobenius
  ladder: the conserved bilinear cross term is an inductive invariant of the
  two-step-recurrence transition system, and the key identity is recovered as an
  instance of the generic soundness theorem.
-/
