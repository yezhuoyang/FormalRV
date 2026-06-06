/-
  FormalRV.LatticeSurgery.SurgeryDemoSteane — concrete LDPC lattice
  surgery gadget on Steane [[7,1,3]] code.

  Demonstrates the surgery infrastructure
  (`Framework/LDPCMatrix.lean` + `Framework/LDPCSurgery.lean`)
  on the smallest non-trivial code instance:

    * Data code: Steane [[7, 1, 3]] with explicit parity matrices
      (Hx = Hz = three weight-4 parity-check rows).
    * Target measurement: logical X̄ on the data qubit, with
      X̄ = X_3 X_5 X_6 (the standard Steane weight-3 representative).
    * Ancilla: 2 ancilla X-checks on 1 ancilla qubit — a 1-edge
      tree graph G(V={v_0, v_1}, E={(v_0, v_1)}), satisfying
      `dim ker H_X'^T = 1` (one connected component).
    * Connection f_X': v_0 connects to data qubits 3, 5, 6 (the
      support of L̄_X); v_1 connects to no data qubits.
    * τ_s = 2 cycles, giving 3·τ_s = 6 ≥ 2·d = 6 (the FT cycle
      criterion).

  The framework verifies:
    (1) all matrix dimensions consistent;
    (2) merged code is qLDPC with degree bound 4;
    (3) τ_s sufficient;
    (4) target X̄ lies in the row span of merged H̃_X.

  All four close by `decide`.  This is the concrete physical
  realisation that qianxu's surgery infrastructure makes
  verifiable.

  Per the paper (App. C, qianxu): every PPM in the
  compiled Cuccaro / Shor pipeline is implemented by exactly
  this kind of surgery gadget (plus a bridge for cross-block
  PPMs).  The framework's verifier discharges the structural
  correctness condition for each.
-/

import FormalRV.QEC.LDPCMatrix
import FormalRV.LatticeSurgery.LDPCSurgery
import FormalRV.QEC.QECCodeInstances

namespace FormalRV.LatticeSurgery.SurgeryDemoSteane

open FormalRV.Framework
open FormalRV.Framework.LDPC

/-! ## The Steane X-surgery gadget -/

/-- Connection matrix `f_X'`: 2 rows (one per ancilla X-check),
    each of length 7 (data qubit count).  Row 0 = (0,0,0,1,0,1,1)
    connects v_0 to data qubits 3, 5, 6 (the support of L̄_X).
    Row 1 = all-zeros: v_1 is a "trivial" boundary vertex with no
    data attachment. -/
def steane_x_surgery_conn_x : BoolMat :=
  [ [ false, false, false, true,  false, true,  true  ]
  , [ false, false, false, false, false, false, false ] ]

/-- Connection matrix `f_Z`: 3 rows (one per data Z-check),
    each of length 1 (one ancilla qubit).  All zeros — for
    X-type surgery, the ancilla qubit isn't coupled into the
    data Z-checks. -/
def steane_x_surgery_conn_z : BoolMat :=
  [ [ false ], [ false ], [ false ] ]

/-- Ancilla X-check matrix: 2 rows (one per ancilla X-check S_X'_i),
    each of length 1 (one ancilla qubit).  Both rows have `true`
    on the ancilla qubit — the tree edge connects both vertices.
    `H_X' = [[1], [1]]`, so `H_X'^T = [[1, 1]]` and
    `ker H_X'^T = {(0,0), (1,1)}`, of dimension 1, matching the
    one-connected-component condition. -/
def steane_x_surgery_ancilla_hx : BoolMat :=
  [ [ true ], [ true ] ]

/-- Ancilla Z-check matrix: empty (tree has no cycles ⇒ no
    Z-stabilisers needed for the ancilla). -/
def steane_x_surgery_ancilla_hz : BoolMat := []

/-- The full surgery gadget measuring logical X̄ on Steane. -/
def steane_x_surgery : SurgeryGadget :=
  { data_code         := steane_713_with_parity
  , ancilla_n         := 1
  , ancilla_hx        := steane_x_surgery_ancilla_hx
  , ancilla_hz        := steane_x_surgery_ancilla_hz
  , conn_x            := steane_x_surgery_conn_x
  , conn_z            := steane_x_surgery_conn_z
  , tau_s             := 2
  -- Target = X̄ on data extended by 0 on ancilla, length 8.
  -- X̄ = X_3 X_5 X_6 ⟹ data side = [0,0,0,1,0,1,1]; ancilla = [0].
  , target_pauli      :=
      [ false, false, false, true,  false, true,  true, false ]
  -- Witness selects the two bottom rows of merged_hx (the two
  -- ancilla X-checks coupled to data via f_X').  Their XOR has
  -- ancilla side (true ⊕ true) = false and data side (X̄ ⊕ 0) = X̄.
  , span_witness      :=
      [ false, false, false, true,  true ]
  , merged_qldpc_bound := 4
  }

/-! ## Verifier closures -/

theorem steane_x_surgery_dimensions :
    SurgeryGadget.dimensions_consistent steane_x_surgery = true := by decide

theorem steane_x_surgery_tau_s :
    SurgeryGadget.tau_s_sufficient steane_x_surgery = true := by decide

theorem steane_x_surgery_qldpc :
    SurgeryGadget.merged_is_qldpc steane_x_surgery = true := by decide

theorem steane_x_surgery_targets_correctly :
    SurgeryGadget.targets_logical_correctly steane_x_surgery = true := by decide

/-- **Headline:** the Steane logical-X̄ surgery gadget passes
    the framework's complete structural verifier. -/
theorem steane_x_surgery_verifies :
    SurgeryGadget.verify_surgery_gadget steane_x_surgery = true := by decide

/-! ## A "wrong target" counter-example: same gadget but with a
    target that ISN'T in the row span.  Verifier MUST reject. -/

def steane_x_surgery_WRONG : SurgeryGadget :=
  { steane_x_surgery with
    target_pauli :=
      [ true, false, false, false, false, false, false, false ]
    -- Claims L̄_X = X_0, which is NOT a logical X of Steane
    -- (single-qubit X_0 anticommutes with Z-stabiliser S^Z_2).
  }

theorem steane_x_surgery_WRONG_rejected :
    SurgeryGadget.verify_surgery_gadget steane_x_surgery_WRONG = false := by decide

/-! ## A "wrong tau_s" counter-example: tau_s too small.  Verifier
    MUST reject. -/

def steane_x_surgery_TAU_TOO_SMALL : SurgeryGadget :=
  { steane_x_surgery with tau_s := 1 }   -- 3·1 = 3 < 2·d = 6

theorem steane_x_surgery_TAU_TOO_SMALL_rejected :
    SurgeryGadget.verify_surgery_gadget steane_x_surgery_TAU_TOO_SMALL
      = false := by decide

end FormalRV.LatticeSurgery.SurgeryDemoSteane
