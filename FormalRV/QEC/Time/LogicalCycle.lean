/-
  FormalRV.QEC.Time.LogicalCycle — LOGICAL-CYCLE time for the QEC layer:
  parallel vs sequential composition of QEC operations, measured in logical
  cycles over virtual qubits.  NO hardware time anywhere.

  ## Charter (John, 2026-06-10)

  The QEC layer must "distinguish parallel operation / sequential operation,
  with a notion of time and logical cycle already — not necessarily detailed
  to hardware time, but able to differentiate parallel PPM, parallel syndrome
  extraction, and sequential ones."  Before this file, the repo had three
  incompatible time notions: per-gadget `tau_s` scalars (logical, but no
  composition), `scheduleTotalRounds` (logical, but strictly sequential), and
  the System layer's microsecond SysCall wallclock (hardware — out of bounds
  for QEC).  This file supplies the missing algebra.

  ## The model

  * `CycleOp` — one QEC-layer operation occupying a RANGE of virtual qubits
    for a number of logical cycles:
      - `ppmVia g base`       : a logical PPM realised by lattice surgery;
                                duration `g.tau_s` cycles; footprint = the
                                merged block + its syndrome ancillas placed
                                at `base` (the extraction-circuit width
                                proven by `ExtractionCount.widthC_*`).
      - `extractRound c base` : one syndrome-extraction round of a CSS code
                                block; duration 1 cycle.
    One logical cycle = one syndrome-measurement round, the standard
    convention (`tau_s` counts exactly these — `LDPCSurgery`).

  * `CycleSchedule` — `op | seq | par | rep` with
      duration: op ↦ its cycles, seq ↦ sum, PAR ↦ MAX, rep k ↦ k·_
    (the cycle-valued analogue of the System layer's `CompressedSchedule`
    seq/par/rep shape, with µs replaced by logical cycles and zone capacity
    replaced by virtual-qubit-range disjointness).

  * `wellFormed` — decidable: `par` branches must occupy DISJOINT virtual-
    qubit ranges.  Allocation is free (infinite virtual qubits), so demand-
    side parallelism is exactly "the operations touch different qubits".

  ## Honest residue

  Well-formedness is the SYNTACTIC guarantee for parallel composition.  The
  semantic interchange theorem (a parallel slot of footprint-disjoint PPMs
  equals every sequential interleaving at the stabilizer level) needs the
  parametric commutation-preservation laws that `PPMOperational`'s header
  lists as open; until they land, parallel slots get duration/footprint
  accounting and decidable well-formedness, with semantics per-op via
  `CircuitSemantics`.  The System layer remains responsible for whether the
  demanded parallelism FITS a machine (zones, decoders, routing) — that is
  deliberately not modeled here.

  No Mathlib.  No `sorry`, no `axiom`.
-/

import FormalRV.QEC.CSSCode
import FormalRV.QEC.LatticeSurgery.LDPCSurgery
import FormalRV.QEC.LatticeSurgery.SurgerySchedule
import FormalRV.QEC.LatticeSurgery.SurgeryDemoSurface

namespace FormalRV.QEC.Time

open FormalRV.Framework.LDPC

/-! ## Operations with footprint and duration -/

/-- One QEC-layer operation, placed at a base virtual qubit. -/
inductive CycleOp where
  /-- A logical PPM realised by the surgery gadget `g`, its merged block and
      syndrome ancillas occupying `base .. base + footprint`. -/
  | ppmVia (g : SurgeryGadget) (base : Nat)
  /-- One syndrome-extraction round of the CSS code block `c` at `base`. -/
  | extractRound (c : FormalRV.QEC.CSSCode) (base : Nat)

namespace CycleOp

/-- Footprint size: the width of the op's compiled extraction circuit
    (data + surgery ancilla + one syndrome ancilla per check — the
    `ExtractionCount.widthC_*` figure). -/
def size : CycleOp → Nat
  | .ppmVia g _       => g.merged_n + g.merged_hx.length + g.merged_hz.length
  | .extractRound c _ => c.n + c.hx.length + c.hz.length

def base : CycleOp → Nat
  | .ppmVia _ b       => b
  | .extractRound _ b => b

/-- Duration in logical cycles: a surgery PPM runs `tau_s` syndrome rounds;
    one extraction round is one cycle. -/
def cycles : CycleOp → Nat
  | .ppmVia g _       => g.tau_s
  | .extractRound _ _ => 1

/-- Virtual-qubit range `[lo, hi)`. -/
def lo (o : CycleOp) : Nat := o.base
def hi (o : CycleOp) : Nat := o.base + o.size

/-- Two ops occupy disjoint virtual-qubit ranges. -/
def disjoint (o₁ o₂ : CycleOp) : Bool :=
  o₁.hi ≤ o₂.lo || o₂.hi ≤ o₁.lo

theorem disjoint_comm (o₁ o₂ : CycleOp) : disjoint o₁ o₂ = disjoint o₂ o₁ := by
  simp [disjoint, Bool.or_comm]

end CycleOp

/-! ## The schedule algebra -/

/-- A logical-cycle schedule: a single op, sequential composition, PARALLEL
    composition, or `k`-fold sequential repetition. -/
inductive CycleSchedule where
  | op  (o : CycleOp)
  | seq (a b : CycleSchedule)
  | par (a b : CycleSchedule)
  | rep (k : Nat) (a : CycleSchedule)

namespace CycleSchedule

/-- Duration in logical cycles: `seq` adds, `par` takes the max (the slot
    ends when its slowest member ends), `rep` scales. -/
def duration : CycleSchedule → Nat
  | .op o    => o.cycles
  | .seq a b => duration a + duration b
  | .par a b => max (duration a) (duration b)
  | .rep k a => k * duration a

@[simp] theorem duration_op (o : CycleOp) : duration (.op o) = o.cycles := rfl
@[simp] theorem duration_seq (a b : CycleSchedule) :
    duration (.seq a b) = duration a + duration b := rfl
@[simp] theorem duration_par (a b : CycleSchedule) :
    duration (.par a b) = max (duration a) (duration b) := rfl
@[simp] theorem duration_rep (k : Nat) (a : CycleSchedule) :
    duration (.rep k a) = k * duration a := rfl

/-- All ops of a schedule. -/
def opsOf : CycleSchedule → List CycleOp
  | .op o    => [o]
  | .seq a b => opsOf a ++ opsOf b
  | .par a b => opsOf a ++ opsOf b
  | .rep _ a => opsOf a

/-- Total footprint demand: the highest virtual qubit touched (+1).  This is
    the SPACE figure handed to the System layer (how many qubits the demand
    needs if everything is laid out as placed). -/
def widthDemand (s : CycleSchedule) : Nat :=
  (s.opsOf.map CycleOp.hi).foldl max 0

/-- Decidable well-formedness: every `par` junction joins schedules whose op
    footprints are pairwise disjoint.  (Sequential composition may freely
    reuse qubits — `prep` is a reset.) -/
def wellFormed : CycleSchedule → Bool
  | .op _    => true
  | .seq a b => wellFormed a && wellFormed b
  | .par a b =>
      wellFormed a && wellFormed b &&
        (opsOf a).all (fun o₁ => (opsOf b).all (fun o₂ => o₁.disjoint o₂))
  | .rep _ a => wellFormed a

/-! ## Sequential schedules of surgery gadgets: the bridge to
    `SurgerySchedule.scheduleTotalRounds` -/

/-- The strictly sequential schedule running each gadget's merge in turn on
    the same placed block (sequential merges reuse the patch). -/
def seqGadgets (base : Nat) : List SurgeryGadget → CycleSchedule
  | []      => .rep 0 (.op (.extractRound ⟨0, [], []⟩ base))   -- 0-cycle idle
  | [g]     => .op (.ppmVia g base)
  | g :: gs => .seq (.op (.ppmVia g base)) (seqGadgets base gs)

private theorem foldl_add_init (l : List Nat) :
    ∀ (n : Nat), l.foldl (· + ·) n = n + l.foldl (· + ·) 0 := by
  induction l with
  | nil => intro n; simp
  | cons x rest ih =>
    intro n
    simp only [List.foldl_cons]
    rw [ih (n + x), ih (0 + x)]
    omega

private theorem scheduleTotalRounds_cons (g : SurgeryGadget) (gs : List SurgeryGadget) :
    FormalRV.Framework.SurgerySchedule.scheduleTotalRounds (g :: gs)
      = g.tau_s + FormalRV.Framework.SurgerySchedule.scheduleTotalRounds gs := by
  unfold FormalRV.Framework.SurgerySchedule.scheduleTotalRounds
  simp only [List.map_cons, List.foldl_cons]
  rw [foldl_add_init]
  omega

/-- **Bridge.**  The sequential cycle schedule's duration is EXACTLY the
    legacy `scheduleTotalRounds` (Σ `tau_s`) of `SurgerySchedule` — the
    existing sequential semantics embeds as the all-`seq` corner of the new
    algebra. -/
theorem seqGadgets_duration (base : Nat) (gs : List SurgeryGadget) :
    duration (seqGadgets base gs)
      = FormalRV.Framework.SurgerySchedule.scheduleTotalRounds gs := by
  induction gs with
  | nil => rfl
  | cons g rest ih =>
    cases rest with
    | nil =>
      simp [seqGadgets, CycleOp.cycles,
            FormalRV.Framework.SurgerySchedule.scheduleTotalRounds]
    | cons g' rest' =>
      rw [scheduleTotalRounds_cons]
      show duration (.seq (.op (.ppmVia g base)) (seqGadgets base (g' :: rest'))) = _
      rw [duration_seq, duration_op, ih]
      rfl

/-! ## Parallel vs sequential: the general laws -/

/-- Two single-op schedules placed on disjoint ranges compose in parallel,
    well-formedly. -/
theorem par_ops_wellFormed (o₁ o₂ : CycleOp) (h : o₁.disjoint o₂ = true) :
    wellFormed (.par (.op o₁) (.op o₂)) = true := by
  simp [wellFormed, opsOf, h]

/-- Parallel duration never exceeds sequential duration. -/
theorem par_le_seq (a b : CycleSchedule) :
    duration (.par a b) ≤ duration (.seq a b) := by
  simp only [duration_par, duration_seq]
  omega

/-- For two ops of equal duration (e.g. two identical merges), the parallel
    slot HALVES the sequential cost. -/
theorem par_halves (a b : CycleSchedule) (h : duration a = duration b) :
    2 * duration (.par a b) = duration (.seq a b) := by
  simp only [duration_par, duration_seq, h]
  omega

/-! ## Corpus exemplars: parallel PPM and parallel syndrome extraction

    The verified surface3 X̄ surgery (merged footprint 28, `tau_s = 2`) and
    the [[13,1,3]] code block (extraction footprint 25), placed on disjoint
    virtual ranges.  These are the demand-side schedules the user asked the
    layer to be able to EXPRESS: parallel PPM ≠ sequential PPM, parallel
    extraction ≠ sequential extraction, with explicit cycle counts. -/

open FormalRV.LatticeSurgery.SurgeryDemoSurface

/-- Two surface3 X̄-surgery PPMs in PARALLEL on disjoint blocks: 2 cycles. -/
def twoPPMpar : CycleSchedule :=
  .par (.op (.ppmVia surface3_x_surgery 0))
       (.op (.ppmVia surface3_x_surgery 28))

/-- The same two PPMs SEQUENTIALLY (block reused): 4 cycles. -/
def twoPPMseq : CycleSchedule :=
  .seq (.op (.ppmVia surface3_x_surgery 0))
       (.op (.ppmVia surface3_x_surgery 0))

theorem twoPPMpar_wellFormed : twoPPMpar.wellFormed = true := by decide
theorem twoPPMpar_duration : twoPPMpar.duration = 2 := by decide
theorem twoPPMseq_duration : twoPPMseq.duration = 4 := by decide

/-- Parallel beats sequential by exactly 2× here (equal-duration members). -/
theorem twoPPM_par_halves : 2 * twoPPMpar.duration = twoPPMseq.duration := by decide

/-- The parallel demand costs more SPACE: 56 virtual qubits vs 28 — the
    space/time tradeoff the System layer must arbitrate, here made explicit
    on the demand side. -/
theorem twoPPMpar_width : twoPPMpar.widthDemand = 56 := by decide
theorem twoPPMseq_width : twoPPMseq.widthDemand = 28 := by decide

/-- Parallel syndrome extraction on two disjoint [[13,1,3]] blocks: ONE
    logical cycle for both blocks (vs two sequentially). -/
def twoExtractPar : CycleSchedule :=
  .par (.op (.extractRound FormalRV.QEC.Instances.surface3 0))
       (.op (.extractRound FormalRV.QEC.Instances.surface3 25))

theorem twoExtractPar_wellFormed : twoExtractPar.wellFormed = true := by decide
theorem twoExtractPar_duration : twoExtractPar.duration = 1 := by decide

/-- `tau_s` rounds of code-block maintenance, expressed as repetition: the
    repeated extraction round of the surface3 block costs `k` cycles. -/
theorem rep_extract_duration (k : Nat) :
    duration (.rep k (.op (.extractRound FormalRV.QEC.Instances.surface3 0))) = k := by
  simp [duration, CycleOp.cycles]

end CycleSchedule

end FormalRV.QEC.Time
