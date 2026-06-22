/-
  FormalRV.QEC.Circuit.ExtractionCount — count theorems tying the legacy
  surgery resource counters to the SYNTACTIC extraction circuit.

  ## What this closes

  `SurfaceShorResourceCount` Part A defines `surgeryPhysQubits` / `surgeryCNOTs`
  / `surgeryMeasPerRound` / `surgeryTotalMeas` directly on `SurgeryGadget`
  FIELDS, with the comment-level claim that they count "the emitted circuit".
  That claim had no theorem — the documented gap "counts are defined on gadget
  fields with no theorem linking them to the emitted circuit".

  Here the independent tree-walk counters of `FormalRV/Resource/QECCircuitCount`
  are evaluated on the compiled `extractionRound`/`extractionCircuit` OBJECTS
  and proven, parametrically, to return exactly the legacy formulas:

    * `widthC      = surgeryPhysQubits g`   (data + surgery ancilla + one
                                             syndrome ancilla per merged check)
    * `cxCountC    = surgeryCNOTs g`        (Σ row weights, per round)
    * `measCountC  = surgeryMeasPerRound g` (one per merged check, per round)
    * over `tau_s` rounds: `measCountC = surgeryTotalMeas g`.

  The surface3 corpus instances are additionally pinned by `native_decide`
  directly on the objects (the skeptic's `#eval`-style cross-check; compiled
  evaluation — the legacy Part B field counts they mirror are kernel
  `decide`, and all parametric theorems here are kernel-checked).

  No Mathlib.  No `sorry`; no project axioms (`native_decide` pins carry the
  standard compiler-trust axiom).
-/

import FormalRV.QEC.Circuit.SyndromeExtraction
import FormalRV.Resource.QECCircuitCount
import FormalRV.QEC.LatticeSurgery.SurfaceShorResourceCount
import FormalRV.QEC.Time.LogicalCycle

namespace FormalRV.QEC.Circuit

open FormalRV.Framework.LDPC
open FormalRV.Resource
open FormalRV.LatticeSurgery.SurfaceShorResourceCount
open FormalRV.LatticeSurgery.SurgeryDemoSurface

/-! ## Per-block counters -/

private theorem cxCountC_map_ctrl (a : Nat) (supp : List Nat) :
    cxCountC (supp.map (fun s => PhysOp.cx a s)) = supp.length := by
  induction supp with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, cxCountC, List.countP_cons, List.length_cons] at *
    simp [PhysOp.isCX]

private theorem cxCountC_map_tgt (a : Nat) (supp : List Nat) :
    cxCountC (supp.map (fun s => PhysOp.cx s a)) = supp.length := by
  induction supp with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, cxCountC, List.countP_cons, List.length_cons] at *
    simp [PhysOp.isCX]

private theorem measCountC_map_ctrl (a : Nat) (supp : List Nat) :
    measCountC (supp.map (fun s => PhysOp.cx a s)) = 0 := by
  induction supp with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, measCountC, List.countP_cons] at *
    simp [PhysOp.isMeas]

private theorem measCountC_map_tgt (a : Nat) (supp : List Nat) :
    measCountC (supp.map (fun s => PhysOp.cx s a)) = 0 := by
  induction supp with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, measCountC, List.countP_cons] at *
    simp [PhysOp.isMeas]

/-- A check block contributes exactly `|supp|` CNOTs. -/
theorem cxCountC_block (b : CheckBlock) : cxCountC b.ops = b.supp.length := by
  cases hb : b.basis <;>
    simp [CheckBlock.ops, hb, cxCountC, List.countP_append, PhysOp.isCX]

/-- A check block contributes exactly one measurement. -/
theorem measCountC_block (b : CheckBlock) : measCountC b.ops = 1 := by
  cases hb : b.basis <;>
    simp [CheckBlock.ops, hb, measCountC, List.countP_append, PhysOp.isMeas]

/-! ## Per-round counters -/

/-- Measurements in a round = number of check blocks. -/
theorem measCountC_round (r : Round) : measCountC (Round.ops r) = r.length := by
  induction r with
  | nil => rfl
  | cons b rest ih =>
    rw [Round.ops_cons, measCountC_append, measCountC_block, ih, List.length_cons]
    omega

/-- CNOTs in a round = sum of the blocks' support sizes. -/
theorem cxCountC_round (r : Round) :
    cxCountC (Round.ops r) = (r.map (fun b => b.supp.length)).foldl (· + ·) 0 := by
  suffices h : ∀ (r : Round) (n : Nat),
      (r.map (fun b => b.supp.length)).foldl (· + ·) n = n + cxCountC (Round.ops r) by
    have := h r 0
    omega
  intro r
  induction r with
  | nil => intro n; simp [cxCountC]
  | cons b rest ih =>
    intro n
    rw [List.map_cons, List.foldl_cons, ih, Round.ops_cons, cxCountC_append,
        cxCountC_block]
    omega

/-! ## The extraction round of a code / gadget -/

/-- Row-weight sum, recursion form. -/
private def weightSum : BoolMat → Nat
  | []          => 0
  | row :: rest => rowWeight row + weightSum rest

private theorem foldl_add_init (l : List Nat) :
    ∀ (n : Nat), l.foldl (· + ·) n = n + l.foldl (· + ·) 0 := by
  induction l with
  | nil => intro n; simp
  | cons x rest ih =>
    intro n
    simp only [List.foldl_cons]
    rw [ih (n + x), ih (0 + x)]
    omega

private theorem map_rowWeight_foldl (rows : BoolMat) :
    (rows.map rowWeight).foldl (· + ·) 0 = weightSum rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_add_init, ih]
    simp only [weightSum]
    omega

private theorem cxCountC_xBlocksFrom (rows : BoolMat) :
    ∀ (a : Nat), cxCountC (Round.ops (xBlocksFrom rows a)) = weightSum rows := by
  induction rows with
  | nil => intro _; rfl
  | cons row rest ih =>
    intro a
    simp only [xBlocksFrom, Round.ops_cons, cxCountC_append, cxCountC_block,
               weightSum]
    rw [ih (a + 1), rowSupport_length]
    rfl

private theorem cxCountC_zBlocksFrom (rows : BoolMat) :
    ∀ (a : Nat), cxCountC (Round.ops (zBlocksFrom rows a)) = weightSum rows := by
  induction rows with
  | nil => intro _; rfl
  | cons row rest ih =>
    intro a
    simp only [zBlocksFrom, Round.ops_cons, cxCountC_append, cxCountC_block,
               weightSum]
    rw [ih (a + 1), rowSupport_length]
    rfl

/-- **CNOT count theorem.**  The independent counter, on the compiled
    extraction round of a surgery gadget, returns exactly the legacy
    `surgeryCNOTs` formula (Σ merged-check row weights). -/
theorem cxCountC_extractionRound (g : SurgeryGadget) :
    cxCountC (Round.ops (SurgeryGadget.extractionRound g)) = surgeryCNOTs g := by
  unfold SurgeryGadget.extractionRound extractionBlocks surgeryCNOTs
  rw [Round.ops_append, cxCountC_append, cxCountC_xBlocksFrom, cxCountC_zBlocksFrom,
      map_rowWeight_foldl, map_rowWeight_foldl]

/-- **Measurement count theorem.**  One measurement per merged check. -/
theorem measCountC_extractionRound (g : SurgeryGadget) :
    measCountC (Round.ops (SurgeryGadget.extractionRound g)) = surgeryMeasPerRound g := by
  rw [measCountC_round]
  unfold SurgeryGadget.extractionRound surgeryMeasPerRound
  rw [extractionBlocks_length]

/-! ## Width (SPACE) -/

private theorem widthC_map_ctrl (a : Nat) (supp : List Nat) (h : ∀ s ∈ supp, s ≤ a) :
    widthC (supp.map (fun s => PhysOp.cx a s)) ≤ a + 1 := by
  induction supp with
  | nil => simp
  | cons s rest ih =>
    simp only [List.map_cons, widthC_cons, opWidth]
    have hs : s ≤ a := h s (List.mem_cons_self ..)
    have hr := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    omega

private theorem widthC_map_tgt (a : Nat) (supp : List Nat) (h : ∀ s ∈ supp, s ≤ a) :
    widthC (supp.map (fun s => PhysOp.cx s a)) ≤ a + 1 := by
  induction supp with
  | nil => simp
  | cons s rest ih =>
    simp only [List.map_cons, widthC_cons, opWidth]
    have hs : s ≤ a := h s (List.mem_cons_self ..)
    have hr := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    omega

/-- A check block whose support stays at or below its ancilla spans exactly
    `anc + 1` virtual qubits. -/
theorem widthC_block (b : CheckBlock) (h : ∀ s ∈ b.supp, s ≤ b.anc) :
    widthC b.ops = b.anc + 1 := by
  cases hb : b.basis <;>
    · simp only [CheckBlock.ops, hb, widthC_cons, opWidth]
      rw [widthC_append]
      simp only [widthC_cons, widthC_nil, opWidth]
      first
        | (have := widthC_map_tgt b.anc b.supp h; omega)
        | (have := widthC_map_ctrl b.anc b.supp h; omega)

private theorem widthC_xBlocksFrom (rows : BoolMat) :
    ∀ (a : Nat), (∀ row ∈ rows, row.length ≤ a) → rows ≠ [] →
      widthC (Round.ops (xBlocksFrom rows a)) = a + rows.length := by
  induction rows with
  | nil => intro _ _ h; exact absurd rfl h
  | cons row rest ih =>
    intro a hrows _
    have hsupp : ∀ s ∈ rowSupport row, s ≤ a := by
      intro s hs
      have h1 := rowSupport_lt row s hs
      have h2 := hrows row (List.mem_cons_self ..)
      omega
    rw [xBlocksFrom, Round.ops_cons, widthC_append,
        widthC_block ⟨.x, a, rowSupport row⟩ hsupp]
    cases hrest : rest with
    | nil => simp [xBlocksFrom]
    | cons r' rest' =>
      rw [← hrest, ih (a + 1)
            (fun row' h' => Nat.le_succ_of_le (hrows row' (List.mem_cons_of_mem _ h')))
            (by simp [hrest])]
      simp only [List.length_cons]
      omega

private theorem widthC_zBlocksFrom (rows : BoolMat) :
    ∀ (a : Nat), (∀ row ∈ rows, row.length ≤ a) → rows ≠ [] →
      widthC (Round.ops (zBlocksFrom rows a)) = a + rows.length := by
  induction rows with
  | nil => intro _ _ h; exact absurd rfl h
  | cons row rest ih =>
    intro a hrows _
    have hsupp : ∀ s ∈ rowSupport row, s ≤ a := by
      intro s hs
      have h1 := rowSupport_lt row s hs
      have h2 := hrows row (List.mem_cons_self ..)
      omega
    rw [zBlocksFrom, Round.ops_cons, widthC_append,
        widthC_block ⟨.z, a, rowSupport row⟩ hsupp]
    cases hrest : rest with
    | nil => simp [zBlocksFrom]
    | cons r' rest' =>
      rw [← hrest, ih (a + 1)
            (fun row' h' => Nat.le_succ_of_le (hrows row' (List.mem_cons_of_mem _ h')))
            (by simp [hrest])]
      simp only [List.length_cons]
      omega

private theorem widthC_xBlocksFrom_le (rows : BoolMat) :
    ∀ (a : Nat), (∀ row ∈ rows, row.length ≤ a) →
      widthC (Round.ops (xBlocksFrom rows a)) ≤ a + rows.length := by
  intro a hrows
  cases hr : rows with
  | nil => simp [xBlocksFrom]
  | cons row rest =>
    rw [← hr, widthC_xBlocksFrom rows a hrows (by simp [hr])]

/-- **Width theorem.**  The compiled extraction round of `(n, hx, hz)` spans
    exactly `n + |hx| + |hz|` virtual qubits — every data/surgery qubit below
    `n` plus one syndrome ancilla per check, none hidden, none double-counted.
    (`hz ≠ []` because a CSS code with no Z-checks ends at the X-ancillas;
    the gadget corpus always has both.) -/
theorem widthC_extractionBlocks (n : Nat) (hx hz : BoolMat)
    (hxr : ∀ row ∈ hx, row.length ≤ n) (hzr : ∀ row ∈ hz, row.length ≤ n)
    (hnz : hz ≠ []) :
    widthC (Round.ops (extractionBlocks n hx hz)) = n + hx.length + hz.length := by
  unfold extractionBlocks
  rw [Round.ops_append, widthC_append,
      widthC_zBlocksFrom hz (n + hx.length)
        (fun row h => Nat.le_trans (hzr row h) (Nat.le_add_right ..)) hnz]
  have hxle := widthC_xBlocksFrom_le hx n hxr
  omega

/-- **Physical-qubit theorem.**  The independent width counter, on the
    compiled extraction round, returns exactly `surgeryPhysQubits g` —
    the syndrome-ancilla overhead the top layer neglects is IN the syntax
    tree and counted. -/
theorem widthC_extractionRound (g : SurgeryGadget)
    (hxr : ∀ row ∈ g.merged_hx, row.length ≤ g.merged_n)
    (hzr : ∀ row ∈ g.merged_hz, row.length ≤ g.merged_n)
    (hnz : g.merged_hz ≠ []) :
    widthC (Round.ops (SurgeryGadget.extractionRound g)) = surgeryPhysQubits g := by
  unfold SurgeryGadget.extractionRound surgeryPhysQubits
  exact widthC_extractionBlocks g.merged_n g.merged_hx g.merged_hz hxr hzr hnz

/-! ## The full merge circuit (`tau_s` rounds) -/

private theorem measCountC_replicate (r : Round) :
    ∀ (k : Nat),
      measCountC ((List.replicate k r).flatMap Round.ops) = k * measCountC (Round.ops r) := by
  intro k
  induction k with
  | zero => simp [measCountC]
  | succ k' ih =>
    rw [List.replicate_succ, List.flatMap_cons, measCountC_append, ih,
        Nat.succ_mul]
    omega

/-- **Total measurement theorem.**  Over the whole merge (`tau_s` rounds),
    the independent counter returns exactly `surgeryTotalMeas g`. -/
theorem measCountC_extractionCircuit (g : SurgeryGadget) :
    measCountC (SurgeryGadget.extractionCircuit g) = surgeryTotalMeas g := by
  unfold SurgeryGadget.extractionCircuit surgeryTotalMeas surgeryRounds
  rw [measCountC_replicate, measCountC_extractionRound]
  exact Nat.mul_comm ..

/-! ## Corpus cross-checks (`native_decide` directly on the objects —
    compiled-evaluation cross-checks of the kernel-checked parametric route)

    The surface3 X̄-surgery extraction round, counted by the independent
    tree-walk counters on the SYNTACTIC object, reproduces Part B of
    `SurfaceShorResourceCount` — 28 qubits / 45 CNOTs / 14 measurements. -/

theorem surface3_extraction_width :
    widthC (Round.ops (SurgeryGadget.extractionRound surface3_x_surgery)) = 28 := by
  native_decide

theorem surface3_extraction_cnots :
    cxCountC (Round.ops (SurgeryGadget.extractionRound surface3_x_surgery)) = 45 := by
  native_decide

theorem surface3_extraction_meas :
    measCountC (Round.ops (SurgeryGadget.extractionRound surface3_x_surgery)) = 14 := by
  native_decide

/-- The serialized surface3 extraction round reproduces the legacy Stim
    emitter — so the string that `PyCircuits/validate_surface3_stim.py`
    cross-validates is certified to be a view of THIS syntactic object. -/
theorem surface3_extraction_stim_eq :
    toStim (Round.ops (SurgeryGadget.extractionRound surface3_x_surgery))
      = FormalRV.LatticeSurgery.StimEmit.surgeryToStim surface3_x_surgery := by
  native_decide

/-! ## Pins to the logical-cycle time algebra

    The footprints `Time/LogicalCycle.lean` charges per op are definitionally
    the counted extraction-circuit figures (no silent desynchronization). -/

theorem cycleOp_ppmVia_size (g : SurgeryGadget) (b : Nat) :
    (FormalRV.QEC.Time.CycleOp.ppmVia g b).size = surgeryPhysQubits g := rfl

theorem cycleOp_extractRound_size (c : FormalRV.QEC.CSSCode) (b : Nat) :
    (FormalRV.QEC.Time.CycleOp.extractRound c b).size
      = c.n + c.hx.length + c.hz.length := rfl

end FormalRV.QEC.Circuit
