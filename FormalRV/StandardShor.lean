/-
================================================================================
  FormalRV.StandardShor — START HERE if you are new to this system.
================================================================================
This is the **standard, textbook implementation of Shor's algorithm + surface-code
lattice surgery** — the teaching baseline.  It is the version to read first, *before*
the advanced low-overhead tricks (qLDPC / lifted-product / generalised-bicycle codes,
windowed Ekerå–Håstad, factory sharing, …) that the corpus papers layer on top.

It REDEFINES NOTHING.  It curates and RE-EXPORTS, under the single namespace
`FormalRV.StandardShor`, the verified results that make up the standard pipeline, so a
newcomer has one clean place to find them.  (The underlying proofs of the order-finding
success bound are PORTED FROM the Coq `SQIR` project — that attribution is preserved in
the original `FormalRV.SQIRPort.*` names, which these are aliases of.)

LEARNING PATH — the four steps of "standard Shor on a surface code":

  1. THE ALGORITHM SUCCEEDS.  Order finding succeeds with probability ≥ κ/(log₂N)⁴
     (κ = 4·e⁻²/π²), N-parametric, for any correct modular-multiplier oracle.
  2. THE CIRCUIT IS CORRECT.  A concrete SQIR-faithful modular multiplier (built from
     the verified Cuccaro adder) implements that oracle.
  3. THE LOGICAL GATES ARE LATTICE SURGERY.  On the distance-3 surface code, a logical
     CNOT is a verified ZZ-merge + XX-merge, and a Toffoli is a verified |C̄CZ̄⟩ injection.
  4. END TO END.  The Shor PPM program is physically realized as a surface-code surgery
     schedule that reduces the stabilizer state and satisfies the system invariants.

A reader can verify the whole baseline with:  `lake build FormalRV.StandardShor`.
See FormalRV/StandardShor/README.md for the narrative guide.
-/
import FormalRV.Shor.SuccessSensitivity
import FormalRV.Shor.PostQFT.PostQFTCompletion
import FormalRV.Shor.VerifiedShor.ControlledModAddLayer
import FormalRV.Arithmetic.Cuccaro.CuccaroFull
import FormalRV.LatticeSurgery.SurgeryDemoCNOT
import FormalRV.LatticeSurgery.SurfaceShorPPMEndToEnd
import FormalRV.LatticeSurgery.SurfaceShorFullStack

namespace FormalRV.StandardShor

/-! ### Step 1 — the algorithm succeeds (✅ verified, N-parametric) -/
/-- The Shor order-finding success constant κ = 4·e⁻²/π² ≈ 0.0548 (ported from SQIR). -/
alias successConstant := FormalRV.SQIRPort.κ
/-- Order finding succeeds with probability ≥ κ/(log₂N)⁴ for any correct modular oracle. -/
alias orderFindingSucceeds := FormalRV.SQIRPort.Shor_correct_var
/-- The headline success bound minus a tunable error budget (decoder cutoff + p_L). -/
alias successProbabilityBound := FormalRV.Shor.SuccessSensitivity.master_success_bound

/-! ### Step 2 — the standard circuit is correct (✅ verified) -/
/-- A SQIR-faithful modular multiplier instantiates the oracle of Step 1. -/
alias verifiedModularMultiplier := VerifiedShor.correct_general_via_interface
/-- The n-bit Cuccaro adder computes a+b (the arithmetic the multiplier is built from). -/
alias cuccaroAdderCorrect := FormalRV.BQAlgo.cuccaro_n_bit_adder_full_correct

/-! ### Step 3 — logical gates as distance-3 surface-code lattice surgery (✅ verified) -/
/-- A logical CNOT = a verified ZZ-merge then XX-merge of two [[13,1,3]] surface patches. -/
alias surfaceCnotVerifies := FormalRV.LatticeSurgery.SurgeryDemoCNOT.surface3_cnot_verifies
/-- A logical Toffoli = a verified |C̄CZ̄⟩ magic injection on the surface code. -/
alias surfaceToffoliInjectionVerifies := FormalRV.LatticeSurgery.SurgeryDemoCNOT.surface3_ccx_injection_verifies

/-! ### Step 4 — end to end on the surface code (✅ verified) -/
/-- The Shor PPM program is physically realized as a surface-code surgery schedule. -/
alias surfaceShorEndToEnd := FormalRV.LatticeSurgery.SurfaceShorPPMEndToEnd.surface_shor_ppm_physically_realized
/-- The full surface-code schedule reduces the stabilizer state (whole-stack check). -/
alias surfaceFullStack := FormalRV.LatticeSurgery.SurfaceShorFullStack.surface_schedule_full_stack

end FormalRV.StandardShor

/-! ## The curated baseline, type-checked (a reader confirms these on build) -/
#check @FormalRV.StandardShor.orderFindingSucceeds
#check @FormalRV.StandardShor.successProbabilityBound
#check @FormalRV.StandardShor.verifiedModularMultiplier
#check @FormalRV.StandardShor.cuccaroAdderCorrect
#check @FormalRV.StandardShor.surfaceCnotVerifies
#check @FormalRV.StandardShor.surfaceToffoliInjectionVerifies
#check @FormalRV.StandardShor.surfaceShorEndToEnd
#check @FormalRV.StandardShor.surfaceFullStack
