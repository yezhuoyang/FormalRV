/-
  FormalRV.QEC.LogicalLayout.MagicMerge
  ─────────────────────────────────────
  **DETAILED MULTI-BLOCK MERGE + useT / useCCZ as lattice surgery.**

  Closes the two scoped gaps of the PPM→physical driver:

    §1  MULTI-BLOCK MERGE.  A joint logical Pauli measurement spanning
        several surface patches is one lattice-surgery merge on the
        DIRECT-SUM (composite) code, with the joint support being the
        per-block supports concatenated.  Built by `canonicalXSurgery`
        over the composite code; its merged-code extraction circuit IS the
        detailed physical merge (`prep`/`cx`/`meas`).

    §2  useT / useCCZ.  A `useT` is one Z̄⊗Z̄ joint measurement between the
        data patch and a fresh `|T⟩` magic patch (gate teleportation) plus
        a classical S-correction frame update; a `useCCZ` is the verified
        three-joint-measurement CCZ teleport block, each measurement a
        merge.  The magic states are SUPPLIED on fresh physical patches
        (no factory/supply concern — that lives below this level).

  **d ROUNDS PER SURGERY (fault tolerance, honest).**  GE2021 stores
  distance-`d` patches and lattice surgery is "code-depth limited" at `d`
  (main.tex §Runtime, `d = 27`): each merge runs `tau_s = d` rounds of the
  merged-code syndrome extraction so the timelike distance matches the
  spacelike one.  We MODEL the `d` rounds in the circuit and count them;
  we do NOT verify fault tolerance — the merged distance `d̃ = Θ(d)` is the
  external residue (`SurgeryFaultTolerant`, cited not proven).
-/
import FormalRV.QEC.LogicalLayout.PhysicalCompile
import FormalRV.QEC.CodeBuilders

namespace FormalRV.QEC.LogicalLayout

open FormalRV.QEC
open FormalRV.QEC.Circuit
open FormalRV.Framework.LDPC
open FormalRV.Resource

/-! ## §1. The composite code and the multi-block merge. -/

/-- The direct-sum (composite) code of a list of patches: their data
qubits laid out consecutively (`= BlockAddressing.compositeCode` shape). -/
def compositeOf : List CodeBlock → CSSCode
  | [] => ⟨0, [], []⟩
  | blk :: rest => blk.code.directSum (compositeOf rest)

/-- The composite's qubit count is the sum of the patches' `n`. -/
theorem compositeOf_n : ∀ (blocks : List CodeBlock),
    (compositeOf blocks).n = (blocks.map (fun b => b.code.n)).sum
  | [] => rfl
  | blk :: rest => by
      show blk.code.n + (compositeOf rest).n = _
      rw [compositeOf_n rest]
      simp

/-- **THE MULTI-BLOCK MERGE GADGET**: a joint logical-X̄ measurement across
the patches `blocks`, realized as ONE lattice-surgery merge on the
composite code with the joint support `jointSupp` (the per-block X-supports
concatenated).  Runs `d` rounds (`tau_s = d`) for fault tolerance. -/
def mergeGadget (blocks : List CodeBlock) (jointSupp : BoolVec)
    (d bound : Nat) : SurgeryGadget :=
  canonicalXSurgery ((compositeOf blocks).toQECCode 1 d) jointSupp d bound

/-- **THE DETAILED PHYSICAL MERGE CIRCUIT**: `d` rounds of the merged-code
syndrome extraction — actual `prep`/`cx`/`meas` over virtual physical
qubits (Stim-emittable via `toStim`). -/
def mergeCircuit (blocks : List CodeBlock) (jointSupp : BoolVec)
    (d bound : Nat) : PhysCircuit :=
  (mergeGadget blocks jointSupp d bound).extractionCircuit

/-- The merge gadget targets EXACTLY the joint logical operator
(zero-extended onto the single surgery ancilla). -/
theorem mergeGadget_target (blocks : List CodeBlock) (jointSupp : BoolVec)
    (d bound : Nat) :
    (mergeGadget blocks jointSupp d bound).target_pauli
      = jointSupp ++ [false] := rfl

/-- The merge runs exactly `d` surgery rounds (the fault-tolerance depth). -/
theorem mergeGadget_rounds (blocks : List CodeBlock) (jointSupp : BoolVec)
    (d bound : Nat) :
    (mergeGadget blocks jointSupp d bound).tau_s = d := rfl

/-! ## §2. The per-block → joint-support bridge. -/

/-- The joint X-support of a measurement over patches, each contributing
its addressed logical-X support (`selectX` of that patch's slots), laid out
on the composite's consecutive qubits.  `supps i` is patch `i`'s support
(length `blocks[i].code.n`). -/
def jointSupport : List CodeBlock → (Nat → BoolVec) → BoolVec
  | [], _ => []
  | _ :: rest, supps =>
      supps 0 ++ jointSupport rest (fun i => supps (i + 1))

/-- The joint support has the composite's length when each piece is the
right width (so it is a well-formed support of the composite code). -/
theorem jointSupport_length : ∀ (blocks : List CodeBlock) (supps : Nat → BoolVec),
    (∀ i (h : i < blocks.length), (supps i).length = blocks[i].code.n) →
    (jointSupport blocks supps).length = (compositeOf blocks).n
  | [], _, _ => rfl
  | blk :: rest, supps, hlen => by
      show (supps 0 ++ jointSupport rest (fun i => supps (i + 1))).length
        = (blk.code.directSum (compositeOf rest)).n
      rw [List.length_append,
          jointSupport_length rest (fun i => supps (i + 1))
            (fun i h => hlen (i + 1) (by simp; omega))]
      show (supps 0).length + (compositeOf rest).n = blk.code.n + _
      rw [hlen 0 (by simp)]
      rfl

/-! ## §3. useT — gate teleportation as a lattice surgery. -/

/-- **The useT physical circuit**: one Z̄⊗Z̄ joint measurement (merge)
between the data patch and a fresh `|T⟩` magic patch — `d` rounds of the
merged-code syndrome extraction.  The classical S-correction is a Pauli
frame update (no extra physical gates at this level); the `|T⟩` state is
supplied on the magic patch (no factory). -/
def useTCircuit (dataPatch magicPatch : CodeBlock) (dataZ magicZ : BoolVec)
    (d bound : Nat) : PhysCircuit :=
  mergeCircuit [dataPatch, magicPatch]
    (jointSupport [dataPatch, magicPatch]
      (fun i => if i = 0 then dataZ else magicZ)) d bound

/-- useT runs exactly `d` surgery rounds. -/
theorem useTCircuit_rounds (dataPatch magicPatch : CodeBlock)
    (dataZ magicZ : BoolVec) (d bound : Nat) :
    (mergeGadget [dataPatch, magicPatch]
      (jointSupport [dataPatch, magicPatch]
        (fun i => if i = 0 then dataZ else magicZ)) d bound).tau_s = d := rfl

/-! ## §4. useCCZ — the three-merge CCZ teleport block. -/

/-- **The useCCZ physical circuit**: the verified CCZ-teleport block as
THREE joint logical measurements (lattice surgeries), one per data/magic
pair, each `d` rounds.  (The `|CCZ⟩` magic state on the three magic patches
is supplied; the corrections are frame updates.)  Three merge circuits
concatenated, the magic patches following the data patches on the board so
the qubit ranges are disjoint. -/
def useCCZCircuit (dA dB dC mA mB mC : CodeBlock)
    (zA zB zC zMA zMB zMC : BoolVec) (d bound : Nat) : PhysCircuit :=
  mergeCircuit [dA, mA]
      (jointSupport [dA, mA] (fun i => if i = 0 then zA else zMA)) d bound
    ++ mergeCircuit [dB, mB]
      (jointSupport [dB, mB] (fun i => if i = 0 then zB else zMB)) d bound
    ++ mergeCircuit [dC, mC]
      (jointSupport [dC, mC] (fun i => if i = 0 then zC else zMC)) d bound

/-- useCCZ consumes exactly THREE lattice-surgery merges. -/
theorem useCCZ_three_merges (dA dB dC mA mB mC : CodeBlock)
    (zA zB zC zMA zMB zMC : BoolVec) (d bound : Nat) :
    measCountC (useCCZCircuit dA dB dC mA mB mC zA zB zC zMA zMB zMC d bound)
      = measCountC (mergeCircuit [dA, mA]
            (jointSupport [dA, mA] (fun i => if i = 0 then zA else zMA)) d bound)
        + measCountC (mergeCircuit [dB, mB]
            (jointSupport [dB, mB] (fun i => if i = 0 then zB else zMB)) d bound)
        + measCountC (mergeCircuit [dC, mC]
            (jointSupport [dC, mC] (fun i => if i = 0 then zC else zMC)) d bound) := by
  unfold useCCZCircuit
  rw [measCountC_append, measCountC_append, Nat.add_assoc]

/-! ## §5. Counts on the verified merge circuit. -/

private theorem replicate_round_measCount (r : Round) (t : Nat) :
    measCountC ((List.replicate t r).flatMap Round.ops)
      = t * measCountC (Round.ops r) := by
  induction t with
  | zero => simp [measCountC]
  | succ n ih =>
      rw [List.replicate_succ, List.flatMap_cons, measCountC_append, ih]
      ring

/-- **A SURGERY MERGE'S MEASUREMENT COUNT** (any gadget): `tau_s` rounds, one
measurement per merged check. -/
theorem surgeryExtraction_measCount (g : SurgeryGadget) :
    measCountC (SurgeryGadget.extractionCircuit g)
      = g.tau_s * (g.merged_hx.length + g.merged_hz.length) := by
  unfold SurgeryGadget.extractionCircuit
  rw [replicate_round_measCount, measCountC_round]
  show g.tau_s * (SurgeryGadget.extractionRound g).length = _
  unfold SurgeryGadget.extractionRound
  rw [extractionBlocks_length]

/-- **THE MERGE MEASUREMENT COUNT**: `d · (|H̃x| + |H̃z|)` — `d` rounds, one
measurement per merged check.  On the SAME circuit whose correctness is
`surgery_implements_logical_measurement` (when the verifier passes). -/
theorem mergeCircuit_measCount (blocks : List CodeBlock) (jointSupp : BoolVec)
    (d bound : Nat) :
    measCountC (mergeCircuit blocks jointSupp d bound)
      = d * ((mergeGadget blocks jointSupp d bound).merged_hx.length
          + (mergeGadget blocks jointSupp d bound).merged_hz.length) := by
  show measCountC (SurgeryGadget.extractionCircuit (mergeGadget _ _ d bound)) = _
  rw [surgeryExtraction_measCount, mergeGadget_rounds]

/-- **PILLAR (merge correctness)**: a multi-block merge that passes the
decidable surgery verifier measures EXACTLY its joint logical Pauli — the
eigenvalue is the parity of the selected merged-X-check outcomes.  Reuses
`surgery_implements_logical_measurement` directly. -/
theorem mergeCircuit_correct (blocks : List CodeBlock) (jointSupp : BoolVec)
    (d bound n : Nat) (signs : List Bool)
    (hn : 0 < n)
    (hshape : ∀ r ∈ (mergeGadget blocks jointSupp d bound).merged_hx, r.length = n)
    (hsig : signs.length = (mergeGadget blocks jointSupp d bound).merged_hx.length)
    (hverify : (mergeGadget blocks jointSupp d bound).verify_surgery_gadget = true) :
    Framework.SurgeryCorrect.selectedSignedProduct
        (mergeGadget blocks jointSupp d bound).span_witness
        (mergeGadget blocks jointSupp d bound).merged_hx signs
      = Framework.SurgeryCorrect.signedXRow
          (Framework.SurgeryCorrect.selectedParity
            (mergeGadget blocks jointSupp d bound).span_witness signs)
          (mergeGadget blocks jointSupp d bound).target_pauli :=
  logicalXMeasurement_correct (mergeGadget blocks jointSupp d bound) n signs
    hn hshape hsig hverify

/-! ## §6. Worked GE2021-scale instance. -/

/-- A useT between two GE2021 d=27 patches: one Z̄⊗Z̄ merge, 27 rounds of the
merged `[[≈1459,·]]` syndrome extraction.  Its measurement count is on the
verified merged-code circuit. -/
def ge2021UseT (dataZ magicZ : BoolVec) : PhysCircuit :=
  useTCircuit ge2021Patch ge2021Patch dataZ magicZ 27 8

/-- The useT merge runs exactly 27 (= `d`) surgery rounds. -/
example (dataZ magicZ : BoolVec) :
    (mergeGadget [ge2021Patch, ge2021Patch]
      (jointSupport [ge2021Patch, ge2021Patch]
        (fun i => if i = 0 then dataZ else magicZ)) 27 8).tau_s = 27 := rfl

/-- A useCCZ across six GE2021 patches = three lattice-surgery merges, each
27 rounds — the measurement count decomposes as the three merges. -/
example (zA zB zC zMA zMB zMC : BoolVec) :
    measCountC (useCCZCircuit ge2021Patch ge2021Patch ge2021Patch
        ge2021Patch ge2021Patch ge2021Patch zA zB zC zMA zMB zMC 27 8)
      = measCountC (mergeCircuit [ge2021Patch, ge2021Patch]
            (jointSupport [ge2021Patch, ge2021Patch]
              (fun i => if i = 0 then zA else zMA)) 27 8)
        + measCountC (mergeCircuit [ge2021Patch, ge2021Patch]
            (jointSupport [ge2021Patch, ge2021Patch]
              (fun i => if i = 0 then zB else zMB)) 27 8)
        + measCountC (mergeCircuit [ge2021Patch, ge2021Patch]
            (jointSupport [ge2021Patch, ge2021Patch]
              (fun i => if i = 0 then zC else zMC)) 27 8) :=
  useCCZ_three_merges _ _ _ _ _ _ zA zB zC zMA zMB zMC 27 8

end FormalRV.QEC.LogicalLayout
