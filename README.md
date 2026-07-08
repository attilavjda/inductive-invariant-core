# CertifyingCore — a tiny, machine-checked core for certifying model checking

This is the Lean 4 artifact accompanying the short paper sketch
`CertifyingCore.pdf`. It gives a small, fully self-contained formalisation of the
one pattern that sits under certifying model checking:

> a **transition system** plus an **inductive invariant** proves a **safety
> property**, and that soundness argument is exactly CIC induction.

Everything builds against Mathlib with **no `sorry` and no extra axioms** beyond
Lean's standard `propext`, `Classical.choice`, `Quot.sound`.

## Files

| File | What it contains |
|------|------------------|
| `CertifyingCore/TransitionSystem.lean` | The generic framework: `TransitionSystem`, `Reachable`, `InductiveInvariant`, `InductiveInvariant.reachable`, `safety_via_invariant`. |
| `CertifyingCore/MutexExample.lean` | A textbook lock-based mutual-exclusion system whose safety is certified by an inductive invariant. |
| `CertifyingCore/TinyTS.lean` | A deterministic-step twin of the pattern on a second-order linear ladder whose Casoratian is a conserved inductive invariant. |
| `CertifyingCore/CICLink.lean` | The bridge to Lean's foundations: `Reachable` is a CIC inductive family and invariant-soundness is its recursor. |
| `CertifyingCore/CrossInvariant.lean` | The same pattern applied to a Frobenius ladder; the conserved bilinear cross term is an inductive invariant and the key identity is an instance of the generic soundness theorem. |
| `CertifyingCore.lean` | Umbrella module importing all of the above. |
| `CertifyingCore.pdf` / `.tex` | The picture-heavy paper sketch. |

`CrossInvariant.lean` is self-contained (it re-derives the conserved cross term
from scratch); it does **not** depend on the separate Theorem 6 / Dobbertin
development.

## Building

```bash
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

Requires the Lean toolchain pinned in `lean-toolchain` (Lean 4 / Mathlib
`v4.28.0`).
