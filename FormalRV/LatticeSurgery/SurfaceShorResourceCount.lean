/-
  FormalRV.LatticeSurgery.SurfaceShorResourceCount — RESOURCE COUNT of the surface-code
  lattice-surgery realisation of Shor, derived AFTER semantic verification.

  This file is governed by the project's hard rule "semantic correctness BEFORE
  resource counts" (CLAUDE.md, 2026-05-13).  The per-operation primitive counted
  here is `surface3_x_surgery` — the [[13,1,3]] surface code's logical X̄ measured
  by lattice surgery — which is PROVEN:
    * structurally valid           (`surface3_x_surgery_verifies`),
    * to MEASURE the logical X̄    (`surface3_x_surgery_measures_logicalX`,
                                    the readout of the axiom-free, code-general
                                    `surgery_implements_logical_measurement`),
    * realised by an explicit physical CSS syndrome circuit
                                   (`surface3_merged_syndrome_circuit_implements`,
                                    emitted gate-by-gate by `StimEmit.surgeryToStim`,
                                    Stim-flow cross-validated in PyCircuits/).
  ONLY THEN do we count its physical resources.

  ## Three parts
  * Part A  resource functions on ANY surgery gadget's emitted circuit
            (`StimEmit.surgeryToStim`): physical qubits, CNOTs, measurements,
            rounds.  Parametric — reusable for any verified gadget / any code.
  * Part B  the EXACT counts of the verified surface3 X̄ surgery (`by decide`).
  * Part C  the Shor-scale figure: plug the verified surface3 code into the
            reusable, rfl-verified `surfaceModel` cost model with a paper-cited
            Toffoli count.

  ## Honesty boundary
  Part A/B are exact counts of the VERIFIED primitive.  Part C is a PARAMETRIC
  estimate: it composes the verified primitive's per-patch area and the code
  distance with a Toffoli count through the verified cost-model derivation
  (`estimateWith_qubits/time`, proven `∀ model` by `rfl`).  It is NOT a claim
  that the whole Shor program is enumerated into one schedule — that enumeration
  is the deferred contract delimited in `SurfaceShorPPMEndToEnd`.  It IS a
  resource model whose every per-operation input is a verified quantity.

  No `sorry`, no new `axiom`.
-/

import FormalRV.LatticeSurgery.SurgeryDemoSurface
import FormalRV.LatticeSurgery.StimEmit
import FormalRV.Framework.CostModel
import FormalRV.Framework.PaperClaims

namespace FormalRV.LatticeSurgery.SurfaceShorResourceCount

open FormalRV.Framework FormalRV.Framework.LDPC
open FormalRV.Framework.Resource
open FormalRV.LatticeSurgery.SurgeryDemoSurface
open FormalRV.PaperClaims

/-! ## Part A — physical resource count of a verified surgery gadget's circuit

    These count the DETAILED physical syndrome-extraction circuit that
    `StimEmit.surgeryToStim g` emits for the merged code: data + surgery-ancilla
    qubits `0..merged_n−1`, one syndrome ancilla per merged check
    (`merged_n + i`), an `RX/CX…/MX` block per X-check and `R/CX…/M` per Z-check.
    Parametric over the gadget, hence reusable for any verified surgery / code. -/

/-- Hamming weight of a check row = number of CNOTs that check contributes. -/
def rowWeight (row : List Bool) : Nat := (row.filter (fun b => b)).length

/-- Physical qubits of the emitted circuit: `merged_n` (data + surgery ancilla)
    plus one syndrome ancilla per merged check (X-checks then Z-checks). -/
def surgeryPhysQubits (g : SurgeryGadget) : Nat :=
  g.merged_n + g.merged_hx.length + g.merged_hz.length

/-- Two-qubit gates (CNOTs) in one syndrome round = total check weight. -/
def surgeryCNOTs (g : SurgeryGadget) : Nat :=
  (g.merged_hx.map rowWeight).foldl (· + ·) 0 + (g.merged_hz.map rowWeight).foldl (· + ·) 0

/-- Measurements in one syndrome round = one per merged check. -/
def surgeryMeasPerRound (g : SurgeryGadget) : Nat :=
  g.merged_hx.length + g.merged_hz.length

/-- Syndrome rounds the merge runs for (the gadget's verified `tau_s`). -/
def surgeryRounds (g : SurgeryGadget) : Nat := g.tau_s

/-- Total measurements over the whole merge = per-round × rounds. -/
def surgeryTotalMeas (g : SurgeryGadget) : Nat :=
  surgeryMeasPerRound g * surgeryRounds g

/-! ## Part B — the VERIFIED surface3 X̄ surgery, counted exactly -/

/-- The counted primitive is the structurally-verified gadget.  Its full semantic
    correctness (it MEASURES the logical X̄) is `surface3_x_surgery_measures_logicalX`;
    we re-expose the structural verifier here as the gate that the resource count
    is allowed to proceed. -/
theorem counted_surgery_is_verified :
    SurgeryGadget.verify_surgery_gadget surface3_x_surgery = true :=
  surface3_x_surgery_verifies

/-- The [[13,1,3]] logical-X̄ lattice surgery uses **28 physical qubits**
    (14 data+ancilla + 8 X-syndrome + 6 Z-syndrome ancillas). -/
theorem surface3_phys_qubits : surgeryPhysQubits surface3_x_surgery = 28 := by decide

/-- …**45 CNOTs** per syndrome round (25 in the X-checks, 20 in the Z-checks). -/
theorem surface3_cnots : surgeryCNOTs surface3_x_surgery = 45 := by decide

/-- …**14 measurements** per round (8 X-checks + 6 Z-checks). -/
theorem surface3_meas_per_round : surgeryMeasPerRound surface3_x_surgery = 14 := by decide

/-- …over **2 syndrome rounds** (the verified `tau_s`). -/
theorem surface3_rounds : surgeryRounds surface3_x_surgery = 2 := by decide

/-- …for **28 measurements** total — matching the Stim-flow cross-validation in
    `PyCircuits/validate_surface3_stim.py` (28 qubits, 14 measurements/round). -/
theorem surface3_total_meas : surgeryTotalMeas surface3_x_surgery = 28 := by decide

/-! ## Part C — Shor-scale composition through the verified `surfaceModel`

    The reusable cost model (`estimateWith_qubits/time`, proven `∀ model` by `rfl`)
    is instantiated at the VERIFIED `surface3_qec` code.  Per logical patch the
    surface model charges `2·physPerLogical = 26` physical qubits (data + standing
    routing area); per logical Toffoli it charges `tauToff = d = 3` code cycles.
    (Note: the merge PRIMITIVE's verified `tau_s = 2` — `surface3_rounds` — is the
    duration of one X̄-measuring merge; the full FT logical Toffoli costs `d`
    cycles for error suppression.) -/

/-- A Shor workload: `T` logical Toffolis on `L` logical (data) qubits. -/
def shorWorkload (T L : Nat) : Workload := { n_toff := T, n_logical := L }

/-- physPerLogical of the verified [[13,1,3]] code is its data count, 13. -/
theorem surface3_physPerLogical : physPerLogical surface3_qec = 13 := by decide

/-- Code distance of the verified surface3 code is 3. -/
theorem surface3_distance : surface3_qec.d = 3 := by decide

/-- **Surface-code Shor physical qubits.**  Through the verified surface model:
    `L` logical patches of the verified [[13,1,3]] code (26 physical qubits each:
    data + routing) plus the magic-state factory. -/
theorem shor_surface_qubits (T L factory : Nat) (hw : Hardware) (ow p : Nat) :
    (estimateWith (surfaceModel factory) hw (shorWorkload T L) surface3_qec ow p).qubits
      = L * 26 + factory := by
  rw [estimateWith_qubits_tagged]
  simp only [surfaceModel, shorWorkload, Nat.add_zero]
  rw [surface3_physPerLogical]

/-- **Surface-code Shor runtime.**  `T` logical Toffolis, each `d = 3` code cycles,
    at the hardware cycle time. -/
theorem shor_surface_time (T L factory : Nat) (hw : Hardware) (ow p : Nat) :
    (estimateWith (surfaceModel factory) hw (shorWorkload T L) surface3_qec ow p).time_us_tenths
      = T * 3 * hw.cycle_time_us_tenths := by
  rw [estimateWith_time]
  simp only [surfaceModel, shorWorkload]
  rw [surface3_distance]

/-- **Worked small instance.**  A 4-bit controlled modular adder — 8 Toffolis
    (`ctl_adder_total_toffolis_n_bit 4`, qianxu p. 22) — on `L` logical patches
    with a factory of `f` qubits: physical qubits `= L·26 + f`, runtime
    `= 8·3·cycle = 24·cycle`. -/
theorem ctl_adder4_surface_qubits (L f : Nat) (hw : Hardware) :
    (estimateWith (surfaceModel f) hw
        (shorWorkload (ctl_adder_total_toffolis_n_bit 4) L) surface3_qec 0 0).qubits
      = L * 26 + f :=
  shor_surface_qubits _ L f hw 0 0

theorem ctl_adder4_surface_time (L f : Nat) (hw : Hardware) :
    (estimateWith (surfaceModel f) hw
        (shorWorkload (ctl_adder_total_toffolis_n_bit 4) L) surface3_qec 0 0).time_us_tenths
      = 8 * 3 * hw.cycle_time_us_tenths := by
  rw [shor_surface_time]; rfl

end FormalRV.LatticeSurgery.SurfaceShorResourceCount
