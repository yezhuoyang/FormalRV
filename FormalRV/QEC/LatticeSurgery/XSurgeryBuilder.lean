/-
  FormalRV.QEC.LatticeSurgery.XSurgeryBuilder — the GENERIC single-ancilla
  logical-X̄ surgery gadget, for ANY CSS code and any X-type logical support.

  ## The recipe (what the demos hand-rolled, made a function)

  `SurgeryDemoSteane.steane_x_surgery` and `SurgeryDemoSurface.surface3_x_surgery`
  both use the same construction: ONE surgery ancilla, TWO ancilla X-checks on
  it, the connection row carrying the logical support, everything else zero:

      merged_hx = [ H_X | 0 ]      ancilla X-checks: (ℓ | 1), (0 | 1)
                  [ ℓ   | 1 ]
                  [ 0   | 1 ]      merged_hz = [ H_Z | 0 ]   (no ancilla Z-checks)

  The span witness selects the two new checks: (ℓ|1) ⊕ (0|1) = (ℓ|0) — the
  logical X̄ padded onto the ancilla — so `targets_logical_correctly` is the
  GF(2) identity `row_combination witness merged_hx = ℓ ++ [false]`, decidable
  per instance.  CSS-ness of the merged code needs `ℓ ∈ ker(H_Z)`, i.e. that
  `ℓ` really is an X-type logical — exactly what `LogicalFinder.logicalX`
  computes and `logicalX_genuine` certifies.

  Used by the per-family test-case folders `FormalRV/QEC/Codes/*` to build a
  verified logical operation on EVERY code family from its computed logicals.

  No Mathlib.  No `sorry`, no `axiom` (the builder is a pure definition;
  verification stays per-instance `decide`/`native_decide`, the design point
  of `verify_surgery_gadget`).
-/

import FormalRV.QEC.LatticeSurgery.LDPCSurgery
import FormalRV.QEC.LatticeSurgery.SurgeryDemoSteane

namespace FormalRV.QEC

open FormalRV.Framework FormalRV.Framework.LDPC

/-- The canonical single-ancilla logical-X̄ surgery gadget on `qec`, measuring
    the X-type logical with support `ℓ` (length `qec.n`), running `tau`
    syndrome rounds, with declared qLDPC bound `bound`. -/
def canonicalXSurgery (qec : QECCode) (ℓ : BoolVec) (tau bound : Nat) :
    SurgeryGadget :=
  { data_code := qec
    ancilla_n := 1
    ancilla_hx := [[true], [true]]
    ancilla_hz := []
    conn_x := [ℓ, zero_vec qec.n]
    conn_z := List.replicate qec.hz.length [false]
    tau_s := tau
    target_pauli := ℓ ++ [false]
    span_witness := zero_vec qec.hx.length ++ [true, true]
    merged_qldpc_bound := bound }

/-- The builder reproduces the hand-rolled Steane gadget's merged matrices
    (the support `{3,5,6}` of `X̄ = X₃X₅X₆`, `τ_s = 2`, bound 4). -/
theorem steane_x_surgery_hx_canonical :
    (canonicalXSurgery steane_713_with_parity
        [false, false, false, true, false, true, true] 2 4).merged_hx
      = SurgeryGadget.merged_hx
          FormalRV.LatticeSurgery.SurgeryDemoSteane.steane_x_surgery := by
  decide

end FormalRV.QEC
