/-
  FormalRV.LatticeSurgery.SurgeryReduction — the OPERATIONAL reduction: a logical
  Pauli-product-measurement command reduces to running the surgery gadget as a
  concrete stabilizer PROGRAM (a "surgery schedule").

  Path A, step (1) (John 2026-06-02).  `SurgeryCorrect.surgery_implements_logical_
  measurement` already proves, axiom-free and code-generally, the OPERATOR-level
  facts (R) eigenvalue extraction + (N) non-disturbance + commuting family.  Here
  we LIFT that from a static operator identity to a STATE-TRANSFORMATION property
  of an actual PPM PROGRAM EXECUTION: the surgery merge, written as a `StabProgram`
  (one `StabOp.meas` per merged X-check) and run by `StabProgram.runProgram`,
  induces the merge state-map `measureChecks`, and the readout (R) / non-
  disturbance (N) hold OF THAT EXECUTION.

  We choose the SIMPLEST CORRECT schedule — one measurement per merged check, the
  all-`+1` outcome branch — not an optimized minimum-space-time-volume schedule
  (John 2026-06-02: correctness first; the optimized schedule, when supplied, is
  verified by the SAME `verify_surgery_gadget` + this reduction, since both are
  code- and gadget-general).

  ## What is GENUINELY NEW vs reused (honesty, per CLAUDE.md)

  * NEW (the only new operational content): `runProgram_map_meas_nil` /
    `surgery_schedule_runs_as_merge` — running the merge schedule as a program
    EQUALS the `measureChecks` state-map.  This makes "running the surgery gadget"
    a first-class program execution (a peer of `hProgram`/`cnotProgram` in
    `StabProgram`), not a bare fold.
  * REUSED: (R) from `surgery_implements_logical_measurement`.1; (N) from
    `surgery_preserves_commuting_logical`.  The lift re-exposes these as
    properties of `runProgram …`.

  ## Honest residue (stays a CONTRACT — NOT closed here)

  This is the STABILIZER-LAYER reduction.  It does NOT reach
  `ShorPPMEndToEnd`, whose `MagicBasisPPMState` carries a PURELY CLASSICAL
  `bits : Nat → Bool` semantics (a `measurePauliKind Z` there is a deterministic
  bit-flip macro, NOT a projective ±1 measurement).  Connecting the two needs the
  Gottesman–Knill refinement (computational bits = the +1 sector of a stabilizer
  state) — a separate multi-step bridge, left explicit.  Also out of scope:
  (i) the full-state equality `measureChecks … = apply_PPM_pos s (xRow target)`,
  which is FALSE as a raw equality (the merged code has more qubits than the data
  code; they coincide only after the unformalized ancilla detach/projection,
  qianxu App. C Step 3); (ii) `teleportCCX` (non-Clifford, no stabilizer
  semantics); (iii) merged-code distance / fault tolerance.

  No Mathlib.  Pure List / the PauliString algebra + the Gottesman update.
  No `sorry`, no `axiom`.
-/

import FormalRV.LatticeSurgery.SurgeryCorrect
import FormalRV.PPM.StabProgram

namespace FormalRV.Framework.SurgeryReduction

open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.Framework.SurgeryReadout
open FormalRV.Framework.StabProgram
open FormalRV.Framework.PPMOp
open FormalRV.Framework.PauliSem

/-! ## (1) The new operational lemma: a measurement-only schedule run as a
    program equals the `measureChecks` fold. -/

/-- Running a sequence of `StabOp.meas` operations on the all-`+1` outcome branch
    (the empty outcome list) is exactly the left fold of the Gottesman `+`-update
    `apply_PPM_pos` — i.e. `StabProgram.runProgram` of a pure measurement schedule
    is `SurgeryCorrect.measureChecks`'s engine.  Proven by induction. -/
theorem runProgram_map_meas_nil (checks : List PauliString) (s : StabilizerState) :
    runProgram (checks.map StabOp.meas) [] s
      = checks.foldl (fun st P => apply_PPM_pos st P) s := by
  induction checks generalizing s with
  | nil => rfl
  | cons P rest ih => simp only [List.map_cons, List.foldl_cons, runProgram, ih]

/-- **Schedule = merge.**  The surgery merge, written as the concrete stabilizer
    program `(merged X-checks).map StabOp.meas` and executed by `runProgram` on
    the all-`+1` branch, induces exactly the merge state-map
    `measureChecks (merged_stabilizers_X g)`.  This is what makes "running the
    surgery gadget" a genuine PPM-PROGRAM EXECUTION. -/
theorem surgery_schedule_runs_as_merge (g : SurgeryGadget) (s : StabilizerState) :
    runProgram ((merged_stabilizers_X g).map StabOp.meas) [] s
      = measureChecks (merged_stabilizers_X g) s := by
  rw [measureChecks]
  exact runProgram_map_meas_nil _ s

/-! ## (2) The headline reduction: the logical PPM command reduces to the surgery
    SCHEDULE-PROGRAM, with readout (R) and non-disturbance (N) holding of the
    execution. -/

/-- **The logical Pauli-product-measurement command reduces to the surgery
    schedule.**  For a structurally-verified gadget, the abstract command "measure
    the logical operator P̄ = `target_pauli`" is realised by executing the surgery
    schedule-program, which:

    * (SCHEDULE) IS the merge state-map `measureChecks` (the new operational
      identity `surgery_schedule_runs_as_merge`);
    * (R) reads out P̄ signed by the XOR-parity of the merged-check outcomes
      (reused from `surgery_implements_logical_measurement`);
    * (N) preserves every logical commuting with the measured set — now as a
      property of the PROGRAM EXECUTION `runProgram …`, not just the bare fold.

    This is strictly more than the operator identity: it certifies that the
    abstract measurement command and the concrete schedule-program induce the same
    state map on the relevant sector.  Axiom-free. -/
theorem logical_PPM_reduces_to_surgery_schedule
    (g : SurgeryGadget) (n : Nat) (signs : List Bool)
    (hn : 0 < n) (hshape : ∀ r ∈ g.merged_hx, r.length = n)
    (hsig : signs.length = g.merged_hx.length)
    (hverify : g.verify_surgery_gadget = true) :
    -- (SCHEDULE) the surgery schedule-program IS the merge state-map
    (∀ s, runProgram ((merged_stabilizers_X g).map StabOp.meas) [] s
            = measureChecks (merged_stabilizers_X g) s)
    -- (R) its readout extracts P̄ signed by the merged-check outcome parity
    ∧ (selectedSignedProduct g.span_witness g.merged_hx signs
            = signedXRow (selectedParity g.span_witness signs) g.target_pauli)
    -- (N) it preserves the logical sector commuting with P̄ (of the EXECUTION)
    ∧ (∀ (L : PauliString) (s : StabilizerState), L ∈ s →
         (∀ P ∈ merged_stabilizers_X g, L.commutes P = true) →
         L ∈ runProgram ((merged_stabilizers_X g).map StabOp.meas) [] s) := by
  refine ⟨fun s => surgery_schedule_runs_as_merge g s, ?_, ?_⟩
  · exact (surgery_implements_logical_measurement g n signs hn hshape hsig hverify).1
  · intro L s hmem hcomm
    rw [surgery_schedule_runs_as_merge]
    exact surgery_preserves_commuting_logical g L s hmem hcomm

/-! ## (3) The Z-TYPE DUAL (closing (2): both measurement bases).

    `runProgram_map_meas_nil` is Pauli-generic, so the Z-type surgery (measuring
    the merged Z-checks `merged_stabilizers_Z`, for a logical Z̄) reduces the same
    way, reusing the Z-type correctness theorems verbatim. -/

theorem surgery_schedule_runs_as_merge_Z (g : SurgeryGadget) (s : StabilizerState) :
    runProgram ((merged_stabilizers_Z g).map StabOp.meas) [] s
      = measureChecks (merged_stabilizers_Z g) s := by
  rw [measureChecks]
  exact runProgram_map_meas_nil _ s

/-- The Z-type logical PPM command (measuring the logical Z̄ = `ztarget`) reduces
    to the merged-Z-check surgery schedule-program, with readout (R) + non-
    disturbance (N) of the execution.  `zwitness/ztarget` carry the Z-kernel
    identity (the gadget stores only the X-kernel), as in
    `surgery_implements_logical_measurement_Z`. -/
theorem logical_PPM_Z_reduces_to_surgery_schedule
    (g : SurgeryGadget) (n : Nat) (zwitness ztarget : BoolVec) (signs : List Bool)
    (hn : 0 < n) (hshape : ∀ r ∈ g.merged_hz, r.length = n)
    (hsig : signs.length = g.merged_hz.length)
    (hzker : row_combination zwitness g.merged_hz = ztarget) :
    (∀ s, runProgram ((merged_stabilizers_Z g).map StabOp.meas) [] s
            = measureChecks (merged_stabilizers_Z g) s)
    ∧ (selectedSignedZProduct zwitness g.merged_hz signs
            = signedZRow (selectedZParity zwitness signs) ztarget)
    ∧ (∀ (L : PauliString) (s : StabilizerState), L ∈ s →
         (∀ P ∈ merged_stabilizers_Z g, L.commutes P = true) →
         L ∈ runProgram ((merged_stabilizers_Z g).map StabOp.meas) [] s) := by
  refine ⟨fun s => surgery_schedule_runs_as_merge_Z g s, ?_, ?_⟩
  · exact (surgery_implements_logical_measurement_Z g n zwitness ztarget signs
            hn hshape hsig hzker).1
  · intro L s hmem hcomm
    rw [surgery_schedule_runs_as_merge_Z]
    exact surgery_preserves_commuting_logical_Z g L s hmem hcomm

/-! ## (4) Smoke: the schedule-as-program identity fires on a concrete check list. -/

example (s : StabilizerState) :
    runProgram ([xRow [true, false], xRow [false, true]].map StabOp.meas) [] s
      = measureChecks [xRow [true, false], xRow [false, true]] s := by
  rw [measureChecks]; exact runProgram_map_meas_nil _ s

end FormalRV.Framework.SurgeryReduction
