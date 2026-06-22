/-
  FormalRV\QEC\Codes\LiftedProduct\LP16BasisFullCert.lean — the LIST-LEVEL full-basis certificate for lp16Imported
  (GENERATED; see scripts/find_logicals.py).  At paper scale (k ≈ 10³) the
  k² pairing over `List Bool` makes this a LONG off-path kernel run — build
  on demand (`lake env lean <this file>`); the kernel-fast bitset
  certificate (`GF2Bits.validBitsCert`) and per-measured-logical
  certificates are the scalable alternatives.
-/
import FormalRV.QEC.Codes.LiftedProduct.LP16BasisImport

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace FormalRV.QEC.Codes.LP

open FormalRV.QEC

/-- **The certificate** (kernel `decide`; `valid_basis_genuine` upgrades it
    to genuineness parametrically). -/
theorem lp16ImportedBasis_valid : (lp16ImportedBasis).valid = true := by decide

end FormalRV.QEC.Codes.LP
