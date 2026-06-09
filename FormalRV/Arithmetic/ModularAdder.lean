import FormalRV.Arithmetic.ModularAdder.Gidney
import FormalRV.Arithmetic.ModularAdder.Cuccaro

/-!
# FormalRV.Arithmetic.ModularAdder

**Two** verified implementations of the modular adder `(x + c) mod N`, on two
different base ripple-carry adders. Both compute the same value by the same
textbook algorithm — add `c` (over one extra bit) → subtract `N` → read the
borrow/high bit as a comparison flag → conditionally add `N` back → uncompute
the flag — and differ only in (a) which base adder fills the "add" slot and
(b) whether anything downstream consumes them.

- [`ModularAdder.Gidney`](ModularAdder/Gidney.lean) — built on the **Gidney**
  patched ripple-carry adder. Fully proven, but **standalone** (not wired into
  the verified Shor path).
- [`ModularAdder.Cuccaro`](ModularAdder/Cuccaro.lean) — built on the **Cuccaro**
  adder; a re-export of `Cuccaro/CuccaroSQIRDirtyFlag`. Fully proven and
  **LIVE** — this is the modular adder the verified modular multiplier and Shor
  actually use.

See [`ModularAdder/README.md`](ModularAdder/README.md) for the composition
chains and the live-vs-standalone details.
-/
