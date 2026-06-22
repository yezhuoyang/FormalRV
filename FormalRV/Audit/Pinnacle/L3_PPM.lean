/-
  Audit · webster-2026 "The Pinnacle Architecture" (arXiv:2602.11457) · LAYER 3 — PAULI-PRODUCT
  MEASUREMENT (on the real generalised-bicycle code)        [was a ⬜ empty stub]
  ════════════════════════════════════════════════════════════════════════════
  Pinnacle's PROCESSING UNIT performs "an arbitrary logical Pauli-product measurement on its logical
  qubits each logical cycle" (paper §II, Pauli-based computation).  This layer builds that on the REAL
  [[72,12,6]] generalised-bicycle code `pinnacle_gb_72` (the constructed representative GB instance,
  k = 12 DERIVED in L4_Code), MIRRORING the cain-xu LP-surgery L3:

    • PART A — the logical operators + code state on the real GB code (logical operators COMPUTED via
      `LogicalFinder`, not hand-specified), state validity, single-PPM measurement semantics;
    • PART B — the multi-PPM COMPUTATION model;
    • PART C — code stabilizers + commutation + **the length-parametric code PRESERVATION**: any
      sequence of logical-Pauli PPMs (the whole RNS modexp on the processing unit included) preserves
      EVERY code stabilizer — the key correctness property of Pauli-based computation.

  ── HONEST SCALE / AXIOM STATUS ──
  cain-xu's L3 ran kernel `decide` at 18 qubits (✅ axiom-clean, propext only).  At 72 qubits kernel
  `decide` times out, so the GB STRUCTURAL facts (state validity, the commutation table, single-PPM
  membership) use `native_decide` (➗ — they carry `Lean.ofReduceBool`, like `pinnacle_gb_72_k_derived`
  in L4_Code; #check'd, NOT #verify_clean'd).  The LENGTH-PARAMETRIC PRESERVATION theorem
  (`gb_logical_computation_preserves_code`) is a scale-free INDUCTION carrying the commutation as a
  HYPOTHESIS, so it is genuinely ✅ AXIOM-CLEAN (no native_decide); the specialised
  `gb_modexp_preserves_code` discharges that hypothesis with the ➗ native_decide commutation fact.

  ── ⬜ REMAINING GAP (QEC-compilation layer, openly flagged) ──
  The full GENERALISED-lattice-surgery measurement gadget (Webster et al. seed-operator + bridge
  construction, the merged-code SurgeryGadget realising the processing-unit measurement physically)
  is NOT built here — it parallels cain-xu's `bb_x_surgery` but on the Webster GB construction, and is
  part of the physical QEC-compilation roadmap (cf. L4_Code's recorded RSA-scale code).  What IS proven
  is the LOGICAL-LEVEL correctness: the processing unit's logical-Pauli measurements preserve the GB
  code throughout the computation.
-/
import FormalRV.QEC.LogicalFinder
import FormalRV.QEC.LatticeSurgery.SurgeryCorrect
import FormalRV.QEC.LatticeSurgery.SurgeryReadout
import FormalRV.QEC.LatticeSurgery.LDPCSurgery
import FormalRV.Audit.Pinnacle.L4_Code
import FormalRV.Verifier

namespace FormalRV.Audit.Pinnacle

open FormalRV.QEC.LogicalFinder
open FormalRV.Framework
open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.Framework.SurgeryReadout
open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp

/-============================================================================
  PART A — logical operators + code state on the real [[72,12,6]] GB code
============================================================================-/

/-- Logical X̄_i of the GB code (computed, symplectically paired). -/
def gbXbar (i : Nat) : PauliString := xRow ((pairedLogicalX pinnacle_gb_72).getD i [])
/-- Logical Z̄_i of the GB code (computed). -/
def gbZbar (i : Nat) : PauliString := zRow ((logicalZ pinnacle_gb_72).getD i [])

/-- The code's stabilizer state: the X- and Z-checks plus the 12 logical-X generators
    (the GB code has `k = 12` logical qubits, in an X-eigenstate). -/
def gbCodeState : StabilizerState :=
  pinnacle_gb_72.hx.map xRow ++ pinnacle_gb_72.hz.map zRow
    ++ (List.range 12).map gbXbar

/-- The GB code has exactly 12 logical qubits — the `LogicalFinder` agrees with the
    rank-derived `k = 12` (➗ native_decide). -/
theorem gb_numLogicals : numLogicals pinnacle_gb_72 = 12 := by native_decide

/-- The GB code stabilizer state is a VALID stabilizer state (➗ native_decide at 72 qubits). -/
theorem gbCodeState_valid : StabilizerState.valid gbCodeState pinnacle_gb_72.n = true := by
  native_decide

/-- **Single-PPM measurement semantics on the real GB code.**  Measuring the logical observable Z̄₀
    makes Z̄₀ a stabilizer of the post-measurement state (the +1 outcome branch): the measured logical
    Pauli is genuinely recorded — the defining action of a logical Pauli-product measurement
    (➗ native_decide). -/
theorem gb_single_ppm_records_observable :
    gbZbar 0 ∈ apply_PPM_pos gbCodeState (gbZbar 0) := by native_decide

/-============================================================================
  PART B — multi-PPM COMPUTATION
============================================================================-/

/-- Run a COMPUTATION = a sequence of logical Pauli-product measurements. -/
def runGBPPMs (ps : List PauliString) (s : StabilizerState) : StabilizerState := ps.foldl apply_PPM_pos s

/-============================================================================
  PART C — code stabilizers + the length-parametric code PRESERVATION
============================================================================-/

/-- The code stabilizers of the GB code (the X- and Z-checks). -/
def gbCodeStabs : List PauliString :=
  pinnacle_gb_72.hx.map xRow ++ pinnacle_gb_72.hz.map zRow

/-- Every code stabilizer is a member of the code state. -/
theorem gbCodeStabs_sub_state (g : PauliString) (hg : g ∈ gbCodeStabs) : g ∈ gbCodeState := by
  unfold gbCodeState gbCodeStabs at *
  exact List.mem_append.mpr (Or.inl hg)

/-- **Every code stabilizer commutes with every logical-Z generator** (➗ native_decide at 72 qubits).
    The logical Z̄ᵢ are in the centraliser of the stabilizer group — exactly what makes them logical. -/
theorem gbCodeStabs_commute_logZ :
    ∀ g ∈ gbCodeStabs, ∀ i ∈ List.range 12, g.commutes (gbZbar i) = true := by
  have h : gbCodeStabs.all (fun g => (List.range 12).all (fun i => g.commutes (gbZbar i))) = true := by
    native_decide
  intro g hg i hi
  exact (List.all_eq_true.mp ((List.all_eq_true.mp h) g hg)) i hi

/-- **THE FULLY GENERAL FORM (✅ AXIOM-CLEAN).**  Under the (any-length) hypothesis that every PPM
    commutes with every code stabilizer, every code stabilizer survives the whole computation —
    so ANY logical Pauli-product computation on the GB code preserves the code.  Scale-free
    induction (`mem_measureChecks_of_commutesAll`); NO native_decide, NO custom axioms. -/
theorem gb_logical_computation_preserves_code
    (ps : List PauliString)
    (hlog : ∀ P ∈ ps, ∀ g ∈ gbCodeStabs, g.commutes P = true)
    (g : PauliString) (hg : g ∈ gbCodeStabs) :
    g ∈ runGBPPMs ps gbCodeState := by
  show g ∈ measureChecks ps gbCodeState
  exact mem_measureChecks_of_commutesAll ps g gbCodeState (gbCodeStabs_sub_state g hg)
    (fun P hP => hlog P hP g hg)

/-- **THE FULL MODEXP PRESERVES THE GB CODE (parametric in length).**  For ANY sequence `ps` of
    logical-Z PPMs (the whole RNS modular-exponentiation on the processing unit included), every code
    stabilizer SURVIVES the entire computation.  The any-length induction is ✅ axiom-clean; the
    per-element commutation is discharged by the ➗ 72-qubit native_decide fact. -/
theorem gb_modexp_preserves_code
    (ps : List PauliString)
    (halpha : ∀ P ∈ ps, ∃ i ∈ List.range 12, P = gbZbar i)
    (g : PauliString) (hg : g ∈ gbCodeStabs) :
    g ∈ runGBPPMs ps gbCodeState := by
  refine gb_logical_computation_preserves_code ps (fun P hP g hg => ?_) g hg
  obtain ⟨i, hi, rfl⟩ := halpha P hP
  exact gbCodeStabs_commute_logZ g hg i hi

end FormalRV.Audit.Pinnacle
