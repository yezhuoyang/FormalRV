import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.ShorVerifiedWithRealInterface

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


/-- **Final R6i-real**: the existing SQIR/Cuccaro instance of
`VerifiedModMulFamily`, with the MMI field provided by the
real-interface-routed theorem (R6i-real), which in turn routes
through R6h-real, R6g-real, R6f-real, R6e, R6c, R6b, R5b'/R5c/R5b
aliases.

Currently equals `verifiedSqirModMulFamily` and the R6i fallback
package by `rfl` — the change is only in *which proof certifies*
the MMI field. -/
noncomputable def verifiedSqirModMulFamily_real_via_interfaces
    (a ainv N bits : Nat) (h_sizing : CircuitSizing N bits)
    (h_N_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    VerifiedModMulFamily a N bits (ModMul.ancillaWidth bits) where
  family := ModMul.circuitFamily a ainv N bits
  mmi := ModMul.circuitFamily_modMulImpl_real_via_interfaces a ainv N bits
      h_sizing.1 h_N_ge_2 h_sizing.2.1 h_sizing.2.2 h_inv
  wellTyped := ModMul.circuitFamily_wellTyped a ainv N bits
      h_sizing.1 (by omega) h_sizing.2.1 h_sizing.2.2

theorem verifiedSqirModMulFamily_real_via_interfaces_eq
    (a ainv N bits : Nat) (h_sizing : CircuitSizing N bits)
    (h_N_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    verifiedSqirModMulFamily a ainv N bits h_sizing h_N_ge_2 h_inv
      = verifiedSqirModMulFamily_real_via_interfaces a ainv N bits
          h_sizing h_N_ge_2 h_inv := rfl

/-- **Public consumer**: the generic Shor success-probability bound
applied to the real-interface-routed SQIR/Cuccaro family.  This is
the cleanest demonstration that the new interface-routed proof chain
plugs into `VerifiedModMulFamily.shorCorrect` without changing any
top-level theorem. -/
theorem correct_general_via_real_interface
    {a N bits : Nat} (ainv : Nat)
    (r m : Nat) (h_setting : ShorSetting a r N m bits)
    (h_sizing : CircuitSizing N bits)
    (h_N_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
        (ModMul.ancillaWidth bits)
        (verifiedSqirModMulFamily_real_via_interfaces a ainv N bits
          h_sizing h_N_ge_2 h_inv).family
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 :=
  VerifiedModMulFamily.shorCorrect
    (verifiedSqirModMulFamily_real_via_interfaces a ainv N bits
      h_sizing h_N_ge_2 h_inv) r m h_setting

/-! ## Windowed/lookup backend (Phase R7)

`VerifiedShor.Windowed` defines pure arithmetic specs and interface
structures for a windowed-lookup modular-multiplier backend.

R7 scope (this phase):
* R7a (inspection): the existing `Gate` IR (I/X/CX/CCX/seq) is
  expressive enough for windowed-lookup arithmetic without
  measurement.  Recommendation: interface-first, circuit deferred.
* R7b (arithmetic specs): `windowValue`, `numWindows`, `tableValue`,
  `windowedStepSpec` + bound lemmas.
* R7c (interfaces): `WindowLayout`, `LookupTableImpl`,
  `WindowedLookupModMulSpec`.

R7d (toy circuit) and R7e (`WindowedLookupModMulImpl →
VerifiedModMulFamily`) are reserved for future phases. -/

end VerifiedShor
