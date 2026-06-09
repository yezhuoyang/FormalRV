import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.ModMulInterfaceViaExisting

namespace VerifiedShor
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)


/-- **Final R6i certification**: the existing SQIR/Cuccaro instance
of `VerifiedModMulFamily`, with the same conclusion as
`verifiedSqirModMulFamily` but with each field provided by an
interface-routed `_via_interfaces` theorem.

Currently equals `verifiedSqirModMulFamily` by `rfl` because all the
`_via_interfaces` components are fallback wrappers around the
original `ModMul.*` theorems. -/
noncomputable def verifiedSqirModMulFamily_via_interfaces
    (a ainv N bits : Nat) (h_sizing : CircuitSizing N bits)
    (h_N_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    VerifiedModMulFamily a N bits (ModMul.ancillaWidth bits) where
  family := ModMul.circuitFamily a ainv N bits
  mmi := ModMul.circuitFamily_modMulImpl_via_interfaces a ainv N bits
      h_sizing.1 h_N_ge_2 h_sizing.2.1 h_sizing.2.2 h_inv
  wellTyped := ModMul.circuitFamily_wellTyped a ainv N bits
      h_sizing.1 (by omega) h_sizing.2.1 h_sizing.2.2

theorem verifiedSqirModMulFamily_via_interfaces_eq
    (a ainv N bits : Nat) (h_sizing : CircuitSizing N bits)
    (h_N_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    verifiedSqirModMulFamily a ainv N bits h_sizing h_N_ge_2 h_inv
      = verifiedSqirModMulFamily_via_interfaces a ainv N bits
          h_sizing h_N_ge_2 h_inv := rfl

/-! ## R6i-real: SQIR/Cuccaro family certified through real interfaces

These theorems certify `ModMul.circuitFamily` as a `ModMulImpl`
through the R6h-real `MultiplyCircuitProperty` bridge (the genuinely
interface-routed one), and package the result as a
`VerifiedModMulFamily`.

* `ModMul.satisfiesMultiplyCircuitProperty_real_via_interfaces`:
  layout-form `MultiplyCircuitProperty` for `gateMCP`, derived from
  `MCPAdapter.sqirCuccaro_satisfiesMultiplyCircuitProperty_real_via_interfaces`
  (R6h-real) via def-eq.
* `ModMul.circuitFamily_modMulImpl_real_via_interfaces`:
  the per-iterate `ModMulImpl` proof, replaying the structure of
  `f_modmult_circuit_verified_bits_MMI` (ModMult.lean:2639) but
  using `MCPAdapter.sqirCuccaro_satisfiesMultiplyCircuitProperty_real_via_interfaces`
  in place of `modmult_MCP_gate_satisfies_MultiplyCircuitProperty`.
* `verifiedSqirModMulFamily_real_via_interfaces`: the `VerifiedModMulFamily`
  package using the real MMI.
* `verifiedSqirModMulFamily_real_via_interfaces_eq` (rfl): the real
  package equals the existing `verifiedSqirModMulFamily`.

None of these calls
`modmult_MCP_gate_satisfies_MultiplyCircuitProperty`,
`ModMul.circuitFamily_modMulImpl`,
`f_modmult_circuit_verified_bits_MMI`, or any other forbidden
theorem.  Allowed deps: `MultiplyCircuitProperty_of_mod` (mod-up
lift), `pow_iter_inverse_mod` (arithmetic), and the R6h-real
`MCPAdapter` theorem. -/

end VerifiedShor
