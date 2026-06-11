/-
  FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup
  ─────────────────────────────────────────────────────
  THE faithful Gidney-2025 (arXiv:2505.15917) `2.5n`-Toffoli modular adder — the
  SUBTRACT-with-underflow + lookup-fixup construction the paper actually uses for
  `X += c (mod p)` (main.tex L972–975). Follows the Def / Correctness / Resource
  spine of the sibling `ModularAdder.Cuccaro` and `ModularAdder.Gidney`.

    • `GidneySubtractFixup/Def.lean`         — `gidneyModAddFixup bits p c`
        (subtract `p−c` → copy underflow `Q` → conditional `+p` → measure-uncompute
        the flag), built on the verified MEASURED Gidney adder
        (`FormalRV.Arithmetic.MeasuredAdder.gidneyAdderMeasured`).
    • `GidneySubtractFixup/Correctness.lean` — `gidneyModAddFixup_correct`: the low
        `bits` target register decodes to `(x + c) % p` for `x < p`, `c < p`, with
        the extra top qubit `Q` AND the fixup flag released to `0`.
    • `GidneySubtractFixup/Resource.lean`    — `toffoli_gidneyModAddFixup = 2·(bits+1)`
        (two `n`-Toffoli measured adds), and `gidneyModAddFixup_meets_g2025_modadd`
        linking it to the paper's `g2025_modadd_toffoli_halves` (`= 2.5n`).

  This is a STANDALONE faithful model of the paper's modular adder; the verified
  Shor multiplier still uses the Cuccaro/SQIR family (`ModularAdder.Cuccaro`). The
  controlled additions of dlogs feeding this adder are bridged to the verified
  residue by `FormalRV.CFS.dlog_reduction_eq_residueAccumulate`.

  Refs: Gidney 2025 arXiv:2505.15917 main.tex L972–975 (construction), L977
  (`2.5n` vs Berry `3.5n`); Gidney arXiv:1709.06648 (temporary AND).
-/
import FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.Def
import FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.Correctness
import FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.Resource
