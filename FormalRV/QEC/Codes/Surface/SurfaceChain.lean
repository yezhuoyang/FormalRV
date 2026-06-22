/-
  FormalRV.QEC.Codes.Surface.SurfaceChain — the surface-code family's
  END-TO-END test case (see `../README.md` for the pipeline charter).

  The code: `surface3 = surfaceHGP 3` — the unrotated [[13,1,3]] surface
  code.  Most of this family's chain predates the test-case folders (it was
  the development exemplar); this file CONSOLIDATES it in pipeline order and
  closes two gaps: the logical operators are here COMPUTED (`LogicalFinder`)
  rather than declared (`supp678`), and the hand-rolled
  `surface3_x_surgery` is pinned to the GENERIC `canonicalXSurgery` builder.

  Distance-parametric surgery (`surface_d_x_surgery d`, verified d = 3,5,7)
  lives in `FormalRV/Shor/PPM/ShorEmitDistance.lean` — above this layer.

  No Mathlib.  No `sorry`; no project axioms (kernel `decide` throughout).
-/

import FormalRV.QEC.LatticeSurgery.XSurgeryBuilder
import FormalRV.QEC.Circuit.CircuitSemantics
import FormalRV.QEC.Circuit.ExtractionCount
import FormalRV.QEC.LogicalFinder
import FormalRV.QEC.StabilizerCode

set_option maxRecDepth 16384

namespace FormalRV.QEC.Codes.Surface

open FormalRV.QEC FormalRV.QEC.Circuit FormalRV.QEC.LogicalFinder
open FormalRV.QEC.Instances
open FormalRV.Framework FormalRV.Framework.LDPC FormalRV.Framework.PPMOp
open FormalRV.LatticeSurgery.SurgeryDemoSurface
open FormalRV.LatticeSurgery.SurfaceShorResourceCount

/-! ## 1. The code -/

theorem surface3_n : surface3.n = 13 := by decide
theorem surface3_well_shaped : surface3.well_shaped = true := by decide
theorem surface3_css : surface3.css_condition = true := by decide

/-- REUSED: definitionally the legacy capstone (cited, not re-derived). -/
theorem surface3_stabilizer_valid : surface3.toStabilizerCode.valid = true :=
  FormalRV.QEC.Algebraic.surfaceHGP3_circuit_implements

/-! ## 2. Logical operators, COMPUTED (not declared) -/

theorem surface3_k : numLogicals surface3 = 1 := by decide
theorem surface3_lx_genuine : logicalX_genuine surface3 = true := by decide
theorem surface3_lz_genuine : logicalZ_genuine surface3 = true := by decide

/-! ## 3. The logical operation — and the builder pin

    The corpus gadget `surface3_x_surgery` (declared support `{6,7,8}`)
    coincides with the generic builder's output on every load-bearing field
    pinned below (`merged_hx`, `merged_hz`, `target_pauli`, `span_witness`);
    re-pointing the demo defs to the builder is the tracked full dedup. -/

theorem surface3_x_surgery_is_canonical :
    SurgeryGadget.merged_hx
        (canonicalXSurgery surface3_qec
          [false, false, false, false, false, false, true, true, true,
           false, false, false, false] 2 4)
      = SurgeryGadget.merged_hx surface3_x_surgery := by decide

theorem surface3_x_surgery_canonical_fields :
    (SurgeryGadget.merged_hz
        (canonicalXSurgery surface3_qec
          [false, false, false, false, false, false, true, true, true,
           false, false, false, false] 2 4)
      = SurgeryGadget.merged_hz surface3_x_surgery)
    ∧ ((canonicalXSurgery surface3_qec
          [false, false, false, false, false, false, true, true, true,
           false, false, false, false] 2 4).target_pauli
      = surface3_x_surgery.target_pauli)
    ∧ ((canonicalXSurgery surface3_qec
          [false, false, false, false, false, false, true, true, true,
           false, false, false, false] 2 4).span_witness
      = surface3_x_surgery.span_witness) :=
  ⟨by decide, by decide, by decide⟩

/-- The verified logical operation (re-exposed from the corpus). -/
theorem surface3_gadget_verifies :
    SurgeryGadget.verify_surgery_gadget surface3_x_surgery = true :=
  surface3_x_surgery_verifies

/-! ## 4. The compiled physical circuit and its semantics
    (re-exposed: proven in `Circuit/CircuitSemantics.lean`) -/

theorem surface3_circuit_measures_merged :
    Round.measuredDataObs
        (surface3_x_surgery.merged_n + surface3_x_surgery.merged_hx.length
          + surface3_x_surgery.merged_hz.length)
        surface3_x_surgery.merged_n
        (SurgeryGadget.extractionRound surface3_x_surgery)
      = FormalRV.Framework.SurgeryReadout.merged_stabilizers_X surface3_x_surgery
        ++ FormalRV.Framework.SurgeryCorrect.merged_stabilizers_Z surface3_x_surgery :=
  (surface3_circuit_measures_merged_and_verifies).1

/-! ## 5. Independent resource counts
    (proven in `Circuit/ExtractionCount.lean`: 28 / 45 / 14, plus the Stim
    string pin `surface3_extraction_stim_eq`) -/

theorem surface3_circuit_width_28 :
    FormalRV.Resource.widthC
        (Round.ops (SurgeryGadget.extractionRound surface3_x_surgery)) = 28 := by
  rw [widthC_extractionRound surface3_x_surgery (by decide) (by decide) (by decide)]
  decide

/-! ## 6. Logical-cycle schedule
    (`Time/LogicalCycle.lean`: `twoPPMpar` — 2 cycles parallel vs 4
    sequential, 56 vs 28 virtual qubits) -/

theorem surface3_par_duration :
    FormalRV.QEC.Time.CycleSchedule.duration
      FormalRV.QEC.Time.CycleSchedule.twoPPMpar = 2 :=
  FormalRV.QEC.Time.CycleSchedule.twoPPMpar_duration

end FormalRV.QEC.Codes.Surface
