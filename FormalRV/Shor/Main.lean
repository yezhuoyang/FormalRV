import FormalRV.Shor.PostQFT
import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.VerifiedShorTheorem

/-!
# FormalRV — the main theorem

This file is the single entry point for the headline result of the
development: **Shor's order-finding subroutine succeeds with a
non-negligible, explicitly bounded probability — with no project-specific
axioms** (only Lean's three standard logical axioms `propext`,
`Classical.choice`, `Quot.sound`).

The three results re-exported below are proved elsewhere and verified
axiom-free (check with `#print axioms`):

* `FormalRV.Shor_correct_var`
  (`Shor/PostQFT.lean`) — for any modular-multiplier oracle satisfying
  `ModMulImpl`, order finding succeeds with probability `≥ κ / (log₂ N)⁴`
  where `κ = 4·e⁻²/π²`.
* `FormalRV.Shor_correct_verified_no_modmult_axioms`
  (`Arithmetic/ModMult.lean`) — the same statement instantiated with a
  constructively-defined, SQIR-faithful modular multiplier, so there is no
  oracle placeholder at all.
* `FormalRV.QPE_MMI_correct`
  (`Shor/PostQFT.lean`) — the quantum-phase-estimation peak bound
  `≥ 4/(π²·r)` at the heart of the argument.

See `README.md` for how the four-layer stack (algorithm → arithmetic
gadgets → PPM / lattice surgery → QEC code) sits underneath this theorem.
-/

namespace FormalRV

export FormalRV.SQIRPort (Shor_correct_var QPE_MMI_correct)
export FormalRV.BQAlgo (Shor_correct_verified_no_modmult_axioms)

end FormalRV
