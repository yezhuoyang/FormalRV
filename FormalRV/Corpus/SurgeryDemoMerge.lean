/-
  FormalRV.Corpus.SurgeryDemoMerge — a MULTI-PATCH lattice-surgery gadget on the
  surface code, verified by the SAME general framework (`verify_surgery_gadget`).

  Until now every verified `SurgeryGadget` measured ONE logical operator on ONE code
  patch (surface3, Steane, bbSmall — all single-patch X̄ measurements).  This file
  builds the first MULTI-PATCH gadget: it merges TWO surface [[13,1,3]] patches and
  measures the JOINT logical X̄₁X̄₂ — i.e. the `XX`-merge that is one of the two merges
  of a lattice-surgery CNOT.  It is NOT a standalone construction: it is an instance of
  the same `SurgeryGadget` structure, discharged by the same `verify_surgery_gadget`
  and the same code-general `surgery_implements_logical_measurement`.

  Data code = surface3 ⊕ surface3 (block-diagonal [[26,2,3]]); logical X̄₁X̄₂ has support
  {6,7,8} ∪ {19,20,21}; 1 ancilla qubit with 2 X-checks (`H_X' = [[1],[1]]`, a 1-edge
  tree) coupled by `f_X'` to that joint support; τ_s = 2 (3·2 = 6 ≥ 2·3).  The span
  witness selects the two ancilla merged X-checks whose GF(2) sum is exactly X̄₁X̄₂.

  No `sorry`, no `axiom`.
-/
import FormalRV.Corpus.SurgeryDemoSurface
import FormalRV.LatticeSurgery.SurgeryCorrect
import FormalRV.QEC.LogicalFinder

namespace FormalRV.Corpus.SurgeryDemoMerge

open FormalRV.Framework
open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.Framework.SurgeryReadout
open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp
open FormalRV.QEC.LogicalFinder
open FormalRV.Corpus.SurgeryDemoSurface

/-! ## §1. Two surface3 patches as one block-diagonal [[26,2,3]] code -/

/-- surface3 ⊕ surface3: 2 logical qubits, d = 3, parity checks block-diagonal.
    Patch 1 occupies qubits 0..12, patch 2 occupies qubits 13..25. -/
def surface3x2_qec : Framework.QECCode :=
  { n  := 26
    k  := 2
    d  := 3
    hx := (surface3_qec.hx.map (fun r => r ++ zero_vec 13))
            ++ (surface3_qec.hx.map (fun r => zero_vec 13 ++ r))
    hz := (surface3_qec.hz.map (fun r => r ++ zero_vec 13))
            ++ (surface3_qec.hz.map (fun r => zero_vec 13 ++ r)) }

/-- The joint logical X̄₁X̄₂ support: X̄ on {6,7,8} of patch 1 AND {19,20,21} of patch 2,
    i.e. `supp678 ++ supp678` over the 26 data qubits. -/
def supp_X1X2 : BoolVec := supp678 ++ supp678

/-! ## §2. The XX-merge gadget (joint X̄₁X̄₂ measurement) -/

/-- **The XX-merge of a lattice-surgery CNOT**, as a `SurgeryGadget` on surface3 ⊕ surface3.
    Same shape as the single-patch gadgets: ancilla `H_X' = [[1],[1]]`, `f_X'` couples the
    ancilla to the joint support {6,7,8,19,20,21}, τ_s = 2; the span witness selects the
    two ancilla X-checks whose GF(2) sum is X̄₁X̄₂ (extended by 0 on the ancilla). -/
def surface3_xx_merge : SurgeryGadget :=
  { data_code          := surface3x2_qec
    ancilla_n          := 1
    ancilla_hx         := [[true], [true]]
    ancilla_hz         := []
    conn_x             := [supp_X1X2, zero_vec 26]
    conn_z             := surface3x2_qec.hz.map (fun _ => [false])
    tau_s              := 2
    target_pauli       := supp_X1X2 ++ [false]
    span_witness       := (List.replicate surface3x2_qec.hx.length false) ++ [true, true]
    merged_qldpc_bound := 8 }

/-! ## §3. The gadget passes the SAME structural verifier -/

theorem surface3_xx_merge_dimensions :
    SurgeryGadget.dimensions_consistent surface3_xx_merge = true := by decide

theorem surface3_xx_merge_tau_s :
    SurgeryGadget.tau_s_sufficient surface3_xx_merge = true := by decide

theorem surface3_xx_merge_qldpc :
    SurgeryGadget.merged_is_qldpc surface3_xx_merge = true := by decide

theorem surface3_xx_merge_targets_correctly :
    SurgeryGadget.targets_logical_correctly surface3_xx_merge = true := by decide

/-- **The two-patch XX-merge passes the framework's complete structural verifier**
    (dimensions + qLDPC + τ_s = Θ(d) + the row-span kernel condition), `decide` at 27
    merged qubits — the SAME `verify_surgery_gadget` used for the single-patch gadgets. -/
theorem surface3_xx_merge_verifies :
    SurgeryGadget.verify_surgery_gadget surface3_xx_merge = true := by decide

/-! ## §4. The target is a GENUINE joint logical of the two-patch code -/

/-- **X̄₁X̄₂ is a genuine logical X of surface3 ⊕ surface3**: it commutes with every
    Z-check (in ker H_Z) and is outside the X-stabilizer rowspace — so the merge measures
    a real joint logical operator, not an arbitrary Pauli. -/
theorem surface3_xx_merge_target_is_logical :
    (surface3x2_qec.hz.all (fun r => ! gf2dot r supp_X1X2)
      && ! inRowspace surface3x2_qec.hx supp_X1X2) = true := by decide

/-! ## §5. Semantic correctness: the gadget IMPLEMENTS the joint logical measurement -/

/-- **The XX-merge implements the joint logical Pauli measurement of X̄₁X̄₂** (R ∧ N), via
    the code-general `surgery_implements_logical_measurement` discharged on the two-patch
    surface code. Same theorem as the single-patch gadgets — this is the general framework,
    instantiated at a multi-patch merge. -/
theorem surface3_xx_merge_implements_logical
    (signs : List Bool) (hsig : signs.length = surface3_xx_merge.merged_hx.length) :
    (selectedSignedProduct surface3_xx_merge.span_witness surface3_xx_merge.merged_hx signs
        = signedXRow (selectedParity surface3_xx_merge.span_witness signs)
            surface3_xx_merge.target_pauli)
    ∧ (∀ (L : PauliString) (s : StabilizerState), L ∈ s →
        (∀ P ∈ merged_stabilizers_X surface3_xx_merge, L.commutes P = true) →
        L ∈ measureChecks (merged_stabilizers_X surface3_xx_merge) s)
    ∧ (∀ p ∈ merged_stabilizers_X surface3_xx_merge, ∀ q ∈ merged_stabilizers_X surface3_xx_merge,
        p.commutes q = true) :=
  surgery_implements_logical_measurement surface3_xx_merge surface3_xx_merge.merged_n signs
    (by decide) (by decide) hsig surface3_xx_merge_verifies

/-! ## §6. A THREE-patch joint measurement (X̄₁X̄₂X̄₃) — same framework, scales up

    The same construction measures the joint logical of THREE surface3 patches at once
    (the kind of multi-qubit joint operation a CCZ / Toffoli needs).  Block-diagonal
    [[39,3,3]] data code; ancilla coupled to {6,7,8} of each patch. -/

def surface3x3_qec : Framework.QECCode :=
  { n  := 39
    k  := 3
    d  := 3
    hx := (surface3_qec.hx.map (fun r => r ++ zero_vec 26))
            ++ (surface3_qec.hx.map (fun r => zero_vec 13 ++ r ++ zero_vec 13))
            ++ (surface3_qec.hx.map (fun r => zero_vec 26 ++ r))
    hz := (surface3_qec.hz.map (fun r => r ++ zero_vec 26))
            ++ (surface3_qec.hz.map (fun r => zero_vec 13 ++ r ++ zero_vec 13))
            ++ (surface3_qec.hz.map (fun r => zero_vec 26 ++ r)) }

/-- Joint logical X̄₁X̄₂X̄₃ support over the 39 data qubits. -/
def supp_X1X2X3 : BoolVec := supp678 ++ supp678 ++ supp678

/-- **A three-patch joint-X̄ surgery gadget** (measures X̄₁X̄₂X̄₃) — the same `SurgeryGadget`
    framework at 40 merged qubits. -/
def surface3_xxx_merge : SurgeryGadget :=
  { data_code          := surface3x3_qec
    ancilla_n          := 1
    ancilla_hx         := [[true], [true]]
    ancilla_hz         := []
    conn_x             := [supp_X1X2X3, zero_vec 39]
    conn_z             := surface3x3_qec.hz.map (fun _ => [false])
    tau_s              := 2
    target_pauli       := supp_X1X2X3 ++ [false]
    span_witness       := (List.replicate surface3x3_qec.hx.length false) ++ [true, true]
    merged_qldpc_bound := 12 }

/-- **The three-patch joint-X̄ merge passes the same structural verifier** (`native_decide`
    at 40 merged qubits). -/
theorem surface3_xxx_merge_verifies :
    SurgeryGadget.verify_surgery_gadget surface3_xxx_merge = true := by native_decide

/-- X̄₁X̄₂X̄₃ is a genuine joint logical of the three-patch code. -/
theorem surface3_xxx_merge_target_is_logical :
    (surface3x3_qec.hz.all (fun r => ! gf2dot r supp_X1X2X3)
      && ! inRowspace surface3x3_qec.hx supp_X1X2X3) = true := by native_decide

end FormalRV.Corpus.SurgeryDemoMerge
