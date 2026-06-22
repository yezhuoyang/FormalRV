/-
  FormalRV.QEC.Codes.LiftedProduct.LP16BitsCert — the FULL lp16 imported
  basis, kernel-certified at the bitset level (`GF2Bits.validBitsCert`):
  all 744 lx in ker(H_Z), all 744 lz in ker(H_X), and the complete 744²
  symplectic δ-pairing — against the REAL constructed lp16 matrices,
  independent of the Python solver.  Pending the tracked `dotBitN`/`dotBit`
  bridge lemma, this is a kernel-checked numerical certificate rather than
  a `LogicalBasis.valid` proof — see `GF2Bits.lean`'s honesty note.

  No `sorry`, no `axiom`, no `native_decide`.
-/

import FormalRV.QEC.Codes.LiftedProduct.LP16BasisImport
import FormalRV.QEC.GF2Bits

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace FormalRV.QEC.Codes.LP

open FormalRV.QEC

theorem lp16_basis_bitsCert :
    validBitsCert (matBits FormalRV.QEC.Instances.lp16.hx)
        (matBits FormalRV.QEC.Instances.lp16.hz)
        lp16Imported_lxBits lp16Imported_lzBits = true := by
  decide

end FormalRV.QEC.Codes.LP
