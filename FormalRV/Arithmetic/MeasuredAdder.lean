/-
  FormalRV.Arithmetic.MeasuredAdder
  ──────────────────────────────────
  The **measured** Gidney ripple-carry adder family — `n` Toffoli per add (vs the
  reversible `2n`), realising the cost Cain–Xu 2026 / Gidney 2018 charge to an
  adder.  The carry ancillas are released by MEASUREMENT-based AND-uncompute
  (Gidney's temporary AND) instead of a second reversible Toffoli sweep, which is
  Toffoli-free — so the reverse pass costs `0` and the adder collapses to its
  forward sweep's `n` Toffoli, while STILL computing the faithful sum
  `(a + b) % 2^bits` on the target.  The controlled variant gates the addend under
  a control (`ctrl ? (a+b) : b`) at `2n` Toffoli (Cain–Xu's E3 → E4 jump).

  Import this umbrella to get the whole verified measured adder (defs + value
  correctness + Toffoli counts) as the single public entry point.

  See `MeasuredAdder/README.md` for the spine (which file holds which headline
  theorem), the circuit, and a concrete example.
-/
import FormalRV.Arithmetic.MeasuredAdder.MeasuredAdderDef
import FormalRV.Arithmetic.MeasuredAdder.MeasuredAdderCorrectness
import FormalRV.Arithmetic.MeasuredAdder.MeasuredAdderResource
