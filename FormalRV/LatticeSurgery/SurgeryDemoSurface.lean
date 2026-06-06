/-
  FormalRV.LatticeSurgery.SurgeryDemoSurface — a concrete LDPC lattice-surgery gadget
  on the SURFACE CODE [[13,1,3]] (Path A, John 2026-06-02).

  This is the first concrete surface-code instantiation of the code-general,
  axiom-free surgery-correctness theorem
  `SurgeryCorrect.surgery_implements_logical_measurement`.  It closes — for the
  surface code — the gap John flagged: "we don't know how to implement PPM with
  a code".  The surgery infrastructure was already proven CODE-GENERALLY; what
  was missing was a verified concrete surface-code `SurgeryGadget`.  This file
  supplies one (X-type, measuring the logical X̄) and connects it to the
  correctness engine, so "one logical Pauli-product measurement on the surface
  code is verified-correct".

  Construction (mirrors `Corpus/SurgeryDemoSteane.lean`):
    * Data code: surface3 = `surfaceHGP 3` = unrotated [[13,1,3]] surface code
      (6 X-checks, 6 Z-checks), wrapped as a `QECCode` with d = 3, k = 1.
    * Target: logical X̄ = X₆X₇X₈ (the bottom VV-row string), the standard
      distance-3 surface-code logical-X representative.  It commutes with every
      Z-stabiliser (even overlap) and is not a product of X-stabilisers (the
      CC qubits cannot cancel to leave {6,7,8}) — a genuine logical.
    * Ancilla: 1 qubit, 2 ancilla X-checks `H_X' = [[1],[1]]` — a 1-edge tree
      graph (dim ker H_X'ᵀ = 1), exactly as in the Steane demo.
    * Connection f_X': v₀ couples to the X̄ support {6,7,8}; v₁ is trivial.
    * τ_s = 2, giving 3·τ_s = 6 ≥ 2·d = 6.

  No Mathlib.  Pure Bool / Nat / List + decide + the PauliString algebra.
-/

import FormalRV.QEC.Instances
import FormalRV.QEC.CSSCode
import FormalRV.LatticeSurgery.SurgeryCorrect

namespace FormalRV.LatticeSurgery.SurgeryDemoSurface

open FormalRV.Framework
open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.Framework.SurgeryReadout
open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMUpdate
open FormalRV.Framework.PPMOp
open FormalRV.QEC
open FormalRV.QEC.Instances

/-! ## surface3 as a flat `QECCode` -/

/-- surface3 ([[13,1,3]]) as the flat `QECCode` the surgery gadget consumes
    (k = 1, d = 3; hx/hz from the CSS construction). -/
def surface3_qec : QECCode := surface3.toQECCode 1 3

/-! ## The surface3 X-surgery gadget -/

/-- The logical X̄ support `{6,7,8}` as a length-13 Bool vector. -/
def supp678 : List Bool :=
  [false, false, false, false, false, false, true, true, true, false, false, false, false]

/-- Connection `f_X'`: 2 rows of length 13.  Row 0 couples ancilla vertex v₀ to
    the X̄ support {6,7,8}; row 1 is the trivial vertex v₁. -/
def surface3_x_surgery_conn_x : BoolMat :=
  [ supp678, List.replicate 13 false ]

/-- Connection `f_Z`: 6 rows (one per data Z-check) of length 1, all false
    (X-type surgery — the ancilla qubit isn't coupled into the data Z-checks). -/
def surface3_x_surgery_conn_z : BoolMat :=
  List.replicate 6 [false]

/-- Ancilla X-checks `H_X' = [[1],[1]]`: 2 checks on 1 ancilla qubit (tree edge). -/
def surface3_x_surgery_ancilla_hx : BoolMat := [ [true], [true] ]

/-- Ancilla Z-checks: empty (tree has no cycles). -/
def surface3_x_surgery_ancilla_hz : BoolMat := []

/-- The full surgery gadget measuring logical X̄ = X₆X₇X₈ on surface3. -/
def surface3_x_surgery : SurgeryGadget :=
  { data_code          := surface3_qec
    ancilla_n          := 1
    ancilla_hx         := surface3_x_surgery_ancilla_hx
    ancilla_hz         := surface3_x_surgery_ancilla_hz
    conn_x             := surface3_x_surgery_conn_x
    conn_z             := surface3_x_surgery_conn_z
    tau_s              := 2
    -- Target = X̄ on data ({6,7,8}) extended by 0 on the ancilla, length 14.
    target_pauli       := supp678 ++ [false]
    -- Witness selects the two ancilla X-checks (rows 6,7 of merged_hx); their
    -- XOR has ancilla side (1⊕1)=0 and data side (X̄⊕0)=X̄.
    span_witness       := List.replicate 6 false ++ [true, true]
    merged_qldpc_bound := 4 }

/-! ## Verifier closures -/

theorem surface3_x_surgery_dimensions :
    SurgeryGadget.dimensions_consistent surface3_x_surgery = true := by decide

theorem surface3_x_surgery_tau_s :
    SurgeryGadget.tau_s_sufficient surface3_x_surgery = true := by decide

theorem surface3_x_surgery_qldpc :
    SurgeryGadget.merged_is_qldpc surface3_x_surgery = true := by decide

theorem surface3_x_surgery_targets_correctly :
    SurgeryGadget.targets_logical_correctly surface3_x_surgery = true := by decide

/-- **Headline (structural):** the surface3 logical-X̄ surgery gadget passes the
    framework's complete structural verifier (dimensions + qLDPC + τ_s + the
    row-span kernel condition). -/
theorem surface3_x_surgery_verifies :
    SurgeryGadget.verify_surgery_gadget surface3_x_surgery = true := by decide

/-! ## Logical-measurement correctness (R ∧ N), the surface instance of the
    code-general, axiom-free theorem. -/

/-- **(R) readout headline: the surface3 surgery gadget MEASURES the logical
    X̄ = X₆X₇X₈.**  The product of the selected signed merged X-checks equals
    `target_pauli` (the logical X̄) signed by the XOR-parity of those checks'
    measurement outcomes — i.e. the surgery measures exactly X̄.  Axiom-free, via
    `SurgeryCorrect.surgery_eigenvalue` instantiated at the verified gadget. -/
theorem surface3_x_surgery_measures_logicalX (signs : List Bool)
    (hsig : signs.length = surface3_x_surgery.merged_hx.length) :
    selectedSignedProduct surface3_x_surgery.span_witness surface3_x_surgery.merged_hx signs
      = signedXRow (selectedParity surface3_x_surgery.span_witness signs)
          surface3_x_surgery.target_pauli :=
  (surgery_implements_logical_measurement surface3_x_surgery 14 signs
    (by decide) (by decide) hsig surface3_x_surgery_verifies).1

/-- **(commuting family):** the measured merged X-checks form a valid
    simultaneously-measurable commuting family — the precondition for the merge
    to be a well-defined PPM step. -/
theorem surface3_x_surgery_checks_commute :
    ∀ p ∈ merged_stabilizers_X surface3_x_surgery,
    ∀ q ∈ merged_stabilizers_X surface3_x_surgery, p.commutes q = true :=
  merged_X_checks_commute surface3_x_surgery

/-! ## (L5) Detailed physical realization: the MERGED code is CSS, and its
    syndrome-extraction circuit implements the merged stabilizer group.

    The "lattice surgery" of this gadget IS the syndrome-measurement of its merged
    data+ancilla code.  That merged code is CSS — and it is CSS *because* the
    target {6,7,8} is a genuine logical (it commutes with every data Z-check, so
    the coupled ancilla X-checks commute with the data Z-checks).  Hence the
    standard CSS syndrome-extraction circuit (`CSSCode.syndrome_circuit_implements_code`,
    each stabiliser an ancilla+CNOT+measure circuit per `CliffordConj`) realises
    the merge.  This is the detailed physical circuit underneath the surgery. -/

/-- The merged surface3+ancilla code as a `CSSCode` (14 qubits). -/
def surface3_merged_css : CSSCode :=
  { n  := surface3_x_surgery.merged_n
    hx := surface3_x_surgery.merged_hx
    hz := surface3_x_surgery.merged_hz }

/-- The merged code is well-shaped and CSS (`H̃_X · H̃_Z^T = 0`).  CSS holds
    precisely because the surgery target is a logical (commutes with all Z-checks). -/
theorem surface3_merged_well_shaped : surface3_merged_css.well_shaped = true := by decide
theorem surface3_merged_is_CSS : surface3_merged_css.css_condition = true := by decide

/-- **The detailed syndrome-extraction circuit implements the merge.**  The
    lowered merged stabiliser group is a valid (well-sized, pairwise-commuting)
    stabilizer code — i.e. the physical CSS syndrome circuit of the merged code
    (one ancilla + CNOTs + measurement per merged check, `CliffordConj`-realised)
    implements the lattice-surgery merge, via
    `CSSCode.syndrome_circuit_implements_code`. -/
theorem surface3_merged_syndrome_circuit_implements :
    StabilizerState.valid surface3_merged_css.toStabilizers surface3_merged_css.n = true := by
  rw [CSSCode.syndrome_circuit_implements_code surface3_merged_css surface3_merged_well_shaped]
  exact surface3_merged_is_CSS

end FormalRV.LatticeSurgery.SurgeryDemoSurface
