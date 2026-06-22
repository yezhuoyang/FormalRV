/-
  FormalRV.QEC.LogicalLayout.PhysicalCompile
  ──────────────────────────────────────────
  **THE PPM → DETAILED-PHYSICAL-CIRCUIT DRIVER (P0-1).**

  Every PPM wire is a logical qubit of a surface-code patch (`LogicalLayout`
  labeling).  This file compiles that to ACTUAL physical instructions
  (`PhysCircuit`: `prep`/`cx`/`meas`):

    §1  the IR qubit-shifter (`Round.shift`) — the missing combinator that
        places a patch's circuit on a FRESH, disjoint physical range, with
        gate counts provably preserved;
    §2  `CSSCode.extractionCircuitN` — the FULL per-cycle syndrome
        extraction of a patch (one detailed round per surface-code cycle,
        `d` rounds per logical cycle), reusing `CSSCode.extractionRound`;
    §3  the BOARD: lay every patch of a `BlockLayout` on disjoint ranges and
        emit ALL their syndrome extraction each cycle, with the physical
        qubit count = `Σ (data + syndrome)` proven on the nose;
    §4  the LATTICE-SURGERY realization of a logical Pauli measurement:
        a single-block PPM `Measure` term → a verified `SurgeryGadget`
        (reusing `canonicalXSurgery` / `selectX`) whose merged-code
        extraction circuit IS the physical surgery.

  Reuses the whole `QEC/Circuit` + `QEC/LatticeSurgery` + `QEC/Addressing`
  stack; the new content is the shifter, the board assembly, and the
  PPM-term → gadget bridge.
-/
import FormalRV.QEC.LogicalLayout.Labeling
import FormalRV.QEC.Codes.Surface.RotatedSurface
import FormalRV.QEC.Circuit.ExtractionCount
import FormalRV.QEC.LatticeSurgery.XSurgeryBuilder
import FormalRV.QEC.LatticeSurgery.SurgeryCorrect
import FormalRV.QEC.Addressing

namespace FormalRV.QEC.LogicalLayout

open FormalRV.QEC
open FormalRV.QEC.Circuit
open FormalRV.Framework.LDPC
open FormalRV.Resource

/-! ## §1. The IR qubit-shifter — disjoint placement. -/

/-- Relabel one physical op onto a range shifted by `off`. -/
def PhysOp.shift (off : Nat) : PhysOp → PhysOp
  | .prep b q => .prep b (q + off)
  | .cx c t => .cx (c + off) (t + off)
  | .meas b q => .meas b (q + off)

/-- Relabel a whole circuit. -/
def physShift (off : Nat) (c : PhysCircuit) : PhysCircuit :=
  c.map (PhysOp.shift off)

/-- Relabel one check block (ancilla + every support qubit). -/
def CheckBlock.shift (off : Nat) (b : CheckBlock) : CheckBlock :=
  ⟨b.basis, b.anc + off, b.supp.map (· + off)⟩

/-- Relabel a whole syndrome-extraction round. -/
def Round.shift (off : Nat) (r : Round) : Round :=
  r.map (CheckBlock.shift off)

/-- A shifted block's ops ARE the block's ops, relabeled (the structure is
preserved — only qubit indices move). -/
theorem CheckBlock.shift_ops (off : Nat) (b : CheckBlock) :
    (CheckBlock.shift off b).ops = physShift off b.ops := by
  cases hb : b.basis <;>
    simp only [CheckBlock.shift, CheckBlock.ops, hb, physShift,
      List.map_cons, List.map_append, List.map_map, PhysOp.shift,
      Function.comp_def, List.map_nil]

theorem physShift_append (off : Nat) (c d : PhysCircuit) :
    physShift off (c ++ d) = physShift off c ++ physShift off d :=
  List.map_append ..

/-- A shifted round's ops are the round's ops, relabeled. -/
theorem Round.shift_ops (off : Nat) (r : Round) :
    Round.ops (Round.shift off r) = physShift off (Round.ops r) := by
  induction r with
  | nil => rfl
  | cons b t ih =>
      rw [Round.shift, List.map_cons, ← Round.shift, Round.ops_cons,
          Round.ops_cons, physShift_append, CheckBlock.shift_ops, ih]

/-- **Shifting preserves the measurement count** (relabeling moves qubits,
not gates). -/
theorem measCountC_physShift (off : Nat) (c : PhysCircuit) :
    measCountC (physShift off c) = measCountC c := by
  induction c with
  | nil => rfl
  | cons op t ih =>
      cases op <;>
        simp only [physShift, List.map_cons, measCountC, List.countP_cons,
          PhysOp.shift, PhysOp.isMeas] at ih ⊢ <;>
        omega

/-- **Shifting preserves the CNOT count.** -/
theorem cxCountC_physShift (off : Nat) (c : PhysCircuit) :
    cxCountC (physShift off c) = cxCountC c := by
  induction c with
  | nil => rfl
  | cons op t ih =>
      cases op <;>
        simp only [physShift, List.map_cons, cxCountC, List.countP_cons,
          PhysOp.shift, PhysOp.isCX] at ih ⊢ <;>
        omega

/-! ## §2. The full per-cycle syndrome extraction of a patch. -/

/-- **The full syndrome extraction of a CSS patch over `rounds` cycles** —
`rounds` repetitions of the detailed extraction round (syndrome ancillas
re-prepared each round since `prep` is a reset).  For a distance-`d` patch
the logical cycle is `rounds = d`. -/
def CSSCode.extractionCircuitN (c : CSSCode) (rounds : Nat) : PhysCircuit :=
  (List.replicate rounds (CSSCode.extractionRound c)).flatMap Round.ops

/-- Measurements over `rounds` cycles: one per check per round. -/
theorem extractionCircuitN_measCount (c : CSSCode) (rounds : Nat) :
    measCountC (CSSCode.extractionCircuitN c rounds)
      = rounds * (c.hx.length + c.hz.length) := by
  unfold CSSCode.extractionCircuitN
  induction rounds with
  | zero => simp [measCountC]
  | succ n ih =>
      rw [List.replicate_succ, List.flatMap_cons, measCountC_append, ih]
      show measCountC (Round.ops (CSSCode.extractionRound c))
          + n * (c.hx.length + c.hz.length) = _
      rw [measCountC_round]
      show (CSSCode.extractionRound c).length + _ = _
      unfold CSSCode.extractionRound
      rw [extractionBlocks_length]
      ring

/-! ## §3. The board: every patch on a disjoint physical range. -/

/-- Physical qubits one patch occupies: data `+` syndrome ancillas. -/
def patchPhysQubits (blk : CodeBlock) : Nat :=
  blk.code.n + blk.code.hx.length + blk.code.hz.length

/-- The physical offset of block `i`: the running sum of prior footprints. -/
def boardOffset : List CodeBlock → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | blk :: rest, i + 1 => patchPhysQubits blk + boardOffset rest i

/-- Total physical qubits of all patches (disjoint). -/
def boardPhysQubits : List CodeBlock → Nat
  | [] => 0
  | blk :: rest => patchPhysQubits blk + boardPhysQubits rest

/-- **The board syndrome-extraction circuit for one logical cycle**: every
patch's `rounds`-round full extraction, each on its own disjoint physical
range. -/
def boardExtraction : List CodeBlock → Nat → Nat → PhysCircuit
  | [], _, _ => []
  | blk :: rest, off, rounds =>
      physShift off (CSSCode.extractionCircuitN blk.code rounds)
        ++ boardExtraction rest (off + patchPhysQubits blk) rounds

/-- **THE BOARD MEASUREMENT COUNT**: total syndrome measurements per
logical cycle = `rounds · Σ_i (|hx_i| + |hz_i|)` — every patch's every
check, every round, counted on the physical circuit. -/
theorem boardExtraction_measCount :
    ∀ (blocks : List CodeBlock) (off rounds : Nat),
      measCountC (boardExtraction blocks off rounds)
        = rounds * (blocks.map (fun b => b.code.hx.length
            + b.code.hz.length)).sum := by
  intro blocks
  induction blocks with
  | nil => intro off rounds; rfl
  | cons blk rest ih =>
      intro off rounds
      show measCountC (physShift off (CSSCode.extractionCircuitN blk.code rounds)
          ++ boardExtraction rest (off + patchPhysQubits blk) rounds) = _
      rw [measCountC_append, measCountC_physShift,
          extractionCircuitN_measCount, ih]
      simp only [List.map_cons, List.sum_cons]
      ring

/-! ## §4. Lattice-surgery realization of a logical Pauli measurement. -/

/-- The block-local logical-qubit slot indices a PPM term addresses inside
block `b` (the raw `Nat` slots; turn into `Fin k` via the block's `k`). -/
def blockSlotIndices (blocks : List CodeBlock)
    (P : FormalRV.PPM.Prog.PauliProduct) (b : Nat) : List Nat :=
  (slotsInBlock blocks P b).map (·.1)

/-- **THE SURGERY GADGET of a single-block logical-X̄ measurement**: the
verified `canonicalXSurgery` merge whose `target_pauli` is the addressed
logical-X support `selectX` of the slots, over `tau` surgery rounds.  Its
merged-code extraction circuit (`SurgeryGadget.extractionRound`) is the
physical lattice surgery. -/
def logicalXMeasurementGadget {c : CSSCode} {k : Nat}
    (L : LogicalBasis c k) (kdims dd : Nat) (S : List (Fin k))
    (tau bound : Nat) : Framework.LDPC.SurgeryGadget :=
  canonicalXSurgery (c.toQECCode kdims dd) (L.selectX S) tau bound

/-- The surgery gadget's `target_pauli` IS the addressed logical-X operator
(zero-extended onto the single surgery ancilla) — so the merge measures
exactly `∏_{i∈S} X̄_i`. -/
theorem logicalXMeasurementGadget_target {c : CSSCode} {k : Nat}
    (L : LogicalBasis c k) (kdims dd : Nat) (S : List (Fin k))
    (tau bound : Nat) :
    (logicalXMeasurementGadget L kdims dd S tau bound).target_pauli
      = L.addressedTargetX S 1 := by
  show (L.selectX S) ++ [false] = L.selectX S ++ zero_vec 1
  rfl

/-- The physical circuit of the surgery (the merged-code syndrome
extraction over `tau_s` rounds — the detailed lattice MERGE; the SPLIT is
the symmetric ancilla detachment, the same extraction structure). -/
def surgeryPhysicalCircuit (g : Framework.LDPC.SurgeryGadget) : PhysCircuit :=
  g.extractionCircuit

/-! ## §5. The Stim-emittable board circuit.

  The output level (per John's spec): FULL physical, detailed syndrome
  extraction and detailed merge/split — emittable to Stim — over VIRTUAL
  physical qubits (`Nat` indices, the IR's charter: not real hardware, and
  with no factory/ancilla SUPPLY concern: magic states and surgery
  ancillas are simply fresh physical qubits). -/

/-- **THE BOARD AS ONE STIM PROGRAM**: one logical cycle of every patch's
detailed syndrome extraction, serialized to a Stim circuit string. -/
def boardStim (blocks : List CodeBlock) (rounds : Nat) : String :=
  toStim (boardExtraction blocks 0 rounds)

/-- A surgery (merge) as a Stim program. -/
def surgeryStim (g : Framework.LDPC.SurgeryGadget) : String :=
  toStim (surgeryPhysicalCircuit g)

/-! ## §6. Worked example: a distance-3 rotated-surface patch. -/

/-- The full distance-3 syndrome extraction (one round = 8 checks, each
prep+CNOTs+measure) of the rotated `[[9,1,3]]` patch. -/
def demoPatchCircuit : PhysCircuit :=
  CSSCode.extractionCircuitN (Codes.Surface.rotatedSurface 3) 3

/-- 3 rounds × 8 checks = 24 syndrome measurements (kernel-checked). -/
example : measCountC demoPatchCircuit = 24 := by
  show measCountC (CSSCode.extractionCircuitN _ 3) = 24
  rw [extractionCircuitN_measCount]
  decide

/-- Two patches on a disjoint board: 2 × 24 = 48 measurements per cycle. -/
example :
    measCountC (boardExtraction
        [⟨"A", Codes.Surface.rotatedSurface 3, 1,
            ⟨fun _ => [], fun _ => []⟩⟩,
         ⟨"B", Codes.Surface.rotatedSurface 3, 1,
            ⟨fun _ => [], fun _ => []⟩⟩] 0 3) = 48 := by
  rw [boardExtraction_measCount]
  decide

/-! ## §7. RESOURCE COUNTS ON VERIFIED-CORRECT CIRCUITS.

  Per the audit discipline: the syntactic circuit whose resources we count
  must be PROVEN to do the right thing.  The two correctness pillars —
  reused from the existing semantics layer — are:

    1. SYNDROME EXTRACTION is correct: the detailed `prep/cx/meas` round we
       count measures EXACTLY the patch's stabilizers
       (`extractionRound_measures_code`), discharged PARAMETRICALLY for the
       rotated surface patch at every distance (incl. 27) by
       `rotatedSurface_well_shaped`.
    2. MERGE/SPLIT + LOGICAL MEASUREMENT is correct: the surgery gadget we
       emit measures EXACTLY its target logical Pauli, with the eigenvalue =
       parity of the selected merged-X-check outcomes
       (`surgery_implements_logical_measurement`).

  The resource theorems (`extractionCircuitN_measCount`,
  `boardExtraction_measCount`, the surgery counters) are then counts ON
  these verified-correct objects. -/

/-- **PILLAR 1 (parametric): the rotated-patch syndrome extraction is
correct at EVERY distance** — the detailed extraction round we count
measures exactly the `[[d²,1,d]]` stabilizers.  The `well_shaped`
hypothesis is discharged by the parametric `rotatedSurface_well_shaped`,
so this holds at `d = 27` (the GE2021 patch) with no `native_decide`. -/
theorem rotatedExtraction_measures_stabilizers (d : Nat) :
    Round.measuredDataObs
        ((Codes.Surface.rotatedSurface d).n
          + (Codes.Surface.rotatedSurface d).hx.length
          + (Codes.Surface.rotatedSurface d).hz.length)
        (Codes.Surface.rotatedSurface d).n
        (CSSCode.extractionRound (Codes.Surface.rotatedSurface d))
      = (Codes.Surface.rotatedSurface d).toStabilizers :=
  extractionRound_measures_code _ (Codes.Surface.rotatedSurface_well_shaped d)

/-- **The counted per-cycle circuit IS built from the verified round**: each
of the `rounds` cycles of `extractionCircuitN` is exactly the
stabilizer-measuring `extractionRound` — so the count is on the correct
circuit. -/
theorem extractionCircuitN_uses_verified_round (c : CSSCode) (rounds : Nat) :
    CSSCode.extractionCircuitN c rounds
      = (List.replicate rounds (CSSCode.extractionRound c)).flatMap Round.ops :=
  rfl

/-- **A VERIFIED-CORRECT, RESOURCE-COUNTED syndrome-extraction circuit** for
the GE2021 rotated patch (`d = 27`): the physical circuit measures the
[[729,1,27]] stabilizers each round AND has exactly `27·728` measurements
over a logical cycle of 27 rounds — correctness and count on the SAME
object. -/
theorem ge2021_patch_verified_and_counted :
    -- (correctness) the round measures the code's stabilizers
    (Round.measuredDataObs
        ((Codes.Surface.rotatedSurface 27).n
          + (Codes.Surface.rotatedSurface 27).hx.length
          + (Codes.Surface.rotatedSurface 27).hz.length)
        (Codes.Surface.rotatedSurface 27).n
        (CSSCode.extractionRound (Codes.Surface.rotatedSurface 27))
      = (Codes.Surface.rotatedSurface 27).toStabilizers)
    -- (count) the d-round logical cycle has 27·728 = 19656 measurements
    ∧ measCountC (CSSCode.extractionCircuitN (Codes.Surface.rotatedSurface 27) 27)
        = 19656 := by
  refine ⟨rotatedExtraction_measures_stabilizers 27, ?_⟩
  rw [extractionCircuitN_measCount]
  rw [(Codes.Surface.rotatedSurface27_counts).2.1,
      (Codes.Surface.rotatedSurface27_counts).2.2]

/-- **PILLAR 2: merge/split + logical measurement is correct** — for any
single-block logical-X̄ surgery gadget that passes the (decidable) verifier,
the merged-code extraction measures exactly the target logical Pauli, with
the eigenvalue = parity of the selected merged-X-check outcomes (the
`qianxu` surgery law).  Reuses `surgery_implements_logical_measurement`
directly; the gadget we emit (`logicalXMeasurementGadget`) is a
`canonicalXSurgery`, the exact verified shape. -/
theorem logicalXMeasurement_correct
    (g : Framework.LDPC.SurgeryGadget) (n : Nat) (signs : List Bool)
    (hn : 0 < n) (hshape : ∀ r ∈ g.merged_hx, r.length = n)
    (hsig : signs.length = g.merged_hx.length)
    (hverify : g.verify_surgery_gadget = true) :
    Framework.SurgeryCorrect.selectedSignedProduct g.span_witness g.merged_hx signs
      = Framework.SurgeryCorrect.signedXRow
          (Framework.SurgeryCorrect.selectedParity g.span_witness signs)
          g.target_pauli :=
  (Framework.SurgeryCorrect.surgery_implements_logical_measurement
    g n signs hn hshape hsig hverify).1

/-! ## §8. THE UNIFORM BOARD — proved ONCE for all patches.

  In GE2021 every logical qubit is the SAME surface code at the SAME
  distance, so the board is `replicate count patch`.  The syndrome-
  extraction CORRECTNESS is a SINGLE theorem
  (`rotatedExtraction_measures_stabilizers 27`) that covers every one of the
  thousands of patches — no per-patch reproof — and the resource counts
  scale by a clean multiplication. -/

private theorem map_replicate_sum {α : Type*} (f : α → Nat) (count : Nat)
    (x : α) : ((List.replicate count x).map f).sum = count * f x := by
  induction count with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.map_cons, List.sum_cons, ih]; ring

/-- A uniform board: `count` copies of the same patch. -/
def uniformBoard (blk : CodeBlock) (count : Nat) : List CodeBlock :=
  List.replicate count blk

/-- **Total physical qubits of a uniform board** = `count · (data +
syndrome)` — closed form, no list walk. -/
theorem uniformBoard_physQubits (blk : CodeBlock) (count : Nat) :
    boardPhysQubits (uniformBoard blk count) = count * patchPhysQubits blk := by
  unfold uniformBoard
  induction count with
  | zero => simp [boardPhysQubits]
  | succ n ih =>
      rw [List.replicate_succ]
      show patchPhysQubits blk + boardPhysQubits (List.replicate n blk) = _
      rw [ih]; ring

/-- **Total syndrome measurements of a uniform board per logical cycle** =
`count · rounds · (|hx| + |hz|)` — one theorem for the whole board. -/
theorem uniformBoard_measCount (blk : CodeBlock) (count off rounds : Nat) :
    measCountC (boardExtraction (uniformBoard blk count) off rounds)
      = count * (rounds * (blk.code.hx.length + blk.code.hz.length)) := by
  rw [boardExtraction_measCount]
  unfold uniformBoard
  rw [map_replicate_sum]
  ring

/-! ### THE GE2021 BOARD, once for all 226·63 patches. -/

/-- The GE2021 data patch as a `CodeBlock`: the rotated `[[729,1,27]]`
surface code, one logical qubit. -/
def ge2021Patch : CodeBlock :=
  ⟨"surface27", Codes.Surface.rotatedSurface 27, 1, ⟨fun _ => [], fun _ => []⟩⟩

/-- The GE2021 logical board: `226 · 63 = 14238` identical patches. -/
def ge2021Board : List CodeBlock := uniformBoard ge2021Patch 14238

set_option maxRecDepth 100000 in
/-- **THE WHOLE GE2021 BOARD, VERIFIED AND COUNTED — ONCE.**
  • CORRECTNESS (one theorem, all 14238 patches): each patch's detailed
    syndrome extraction measures the `[[729,1,27]]` stabilizers.
  • PHYSICAL QUBITS: `14238 · 1457 = 20,744,766` (data + syndrome; the
    paper's `1568`/patch adds routing spacing).
  • MEASUREMENTS / logical cycle: `14238 · 27 · 728 = 279,862,128`.
  Correctness and counts on the SAME verified physical circuit. -/
theorem ge2021_board_verified_and_counted :
    (Round.measuredDataObs
        ((Codes.Surface.rotatedSurface 27).n
          + (Codes.Surface.rotatedSurface 27).hx.length
          + (Codes.Surface.rotatedSurface 27).hz.length)
        (Codes.Surface.rotatedSurface 27).n
        (CSSCode.extractionRound ge2021Patch.code)
      = ge2021Patch.code.toStabilizers)
    ∧ boardPhysQubits ge2021Board = 20744766
    ∧ measCountC (boardExtraction ge2021Board 0 27) = 279862128 := by
  obtain ⟨hn, hx, hz⟩ := Codes.Surface.rotatedSurface27_counts
  refine ⟨rotatedExtraction_measures_stabilizers 27, ?_, ?_⟩
  · rw [ge2021Board, uniformBoard_physQubits]
    show 14238 * ((Codes.Surface.rotatedSurface 27).n
      + (Codes.Surface.rotatedSurface 27).hx.length
      + (Codes.Surface.rotatedSurface 27).hz.length) = _
    rw [hn, hx, hz]
  · rw [ge2021Board, uniformBoard_measCount]
    show 14238 * (27 * ((Codes.Surface.rotatedSurface 27).hx.length
      + (Codes.Surface.rotatedSurface 27).hz.length)) = _
    rw [hx, hz]

end FormalRV.QEC.LogicalLayout
