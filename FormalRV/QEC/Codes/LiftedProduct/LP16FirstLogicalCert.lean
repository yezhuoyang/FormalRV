/-
  FormalRV.QEC.Codes.LiftedProduct.LP16FirstLogicalCert — the PER-VECTOR
  kernel certificate for the FIRST imported logical of lp16 [[2610,744,≤16]].

  Honest status of the lp16/lp20 imported bases: the FULL-basis certificate
  (`lp16ImportedBasis_valid`, k² = 744² pairing) is a long off-path kernel
  run that has NOT yet been completed — until it (or per-vector coverage of
  every used logical) finishes, the full bases are externally self-checked
  but Lean-UNVERIFIED.  This file verifies vector 0 the cheap way:

    (1) `lz₀ ∈ ker(H_X)`  and  (2) `lx₀ ∈ ker(H_Z)`   — 945 dot products each;
    (3) `dotBit lx₀ lz₀ = true`                        — the pairing dot.

  (1) makes measuring `lz₀` commute with every X-check; (2)+(3) force `lz₀`
  outside `rowspace(H_Z)` by `LogicalGenuine.dotBit_row_combination` (if
  `lz₀` were a Z-stabilizer combination, `lx₀ ⊥ all H_Z rows` would give
  `dotBit lx₀ lz₀ = false`).  So vector 0 is a GENUINE logical-Z operator —
  kernel-checked, no `native_decide`, no trust in the Python solver.

  No Mathlib.  No `sorry`, no `axiom`.
-/

import FormalRV.QEC.Codes.LiftedProduct.LP16BasisImport

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace FormalRV.QEC.Codes.LP

open FormalRV.Framework.LDPC

/-- The first imported logical pair of lp16. -/
def lp16_lz0 : BoolVec := lp16Imported_lz.getD 0 []
def lp16_lx0 : BoolVec := lp16Imported_lx.getD 0 []

/-- (1) `lz₀` commutes with every X-check of lp16. -/
theorem lp16_lz0_in_ker_hx :
    (FormalRV.QEC.Instances.lp16.hx.all (fun r => ! dotBit r lp16_lz0)) = true := by
  decide

/-- (2) `lx₀` commutes with every Z-check of lp16. -/
theorem lp16_lx0_in_ker_hz :
    (FormalRV.QEC.Instances.lp16.hz.all (fun r => ! dotBit r lp16_lx0)) = true := by
  decide

/-- (3) the symplectic pairing dot — with (2), forces `lz₀` outside
    `rowspace(H_Z)` via `dotBit_row_combination`. -/
theorem lp16_lx0_lz0_paired : dotBit lp16_lx0 lp16_lz0 = true := by
  decide

end FormalRV.QEC.Codes.LP
