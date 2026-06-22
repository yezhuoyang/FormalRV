/-
  FormalRV.QEC.Circuit.CircuitSemantics — the SEMANTICS of the compiled
  syndrome-extraction circuit: the syntactic gate circuit MEASURES exactly the
  code's stabilizers, parametrically over any CSS code / surgery gadget.

  ## The theorem this provides

  Until this file, "the compiled gate circuit measures the code's
  stabilizers" existed only as the hardcoded [[4,2,2]] `decide` demo
  (`GateSyndromeWorkedExample`) and validity-only instances
  (`surface3_merged_syndrome_circuit_implements`).  Here it is parametric
  over every well-shaped CSS code, riding on `PPM/CliffordConj.lean`'s
  Heisenberg-conjugation characterizations.  (The separately recorded open
  obligations `specMatch` (`CircuitToPPMInterface` §22–24) and
  `MagicInjectionObligations.CCX_ok` are NOT discharged here — they concern
  the SysCall-lowering interface and magic injection respectively.)

    * `conjOps` interprets a `PhysCircuit` as backward Heisenberg conjugation
      (CNOTs conjugate via `cnotConj`; prep/meas are conjugation-neutral);
      for one check block this is DEFINITIONALLY `measGadgetConj` /
      `xMeasGadgetConj` (`conjOps_zBlock` / `conjOps_xBlock`).
    * `CheckBlock.measuredObs` — what the block's final ancilla measurement
      reads on the whole register, in the Heisenberg picture.
    * `measuredObs_zBlock` / `measuredObs_xBlock` — the data-register part of
      the measured observable is EXACTLY the check's Pauli lowering
      (`CSSCode.zStab` / `xStab`), parametric in the row, ancilla, width.
    * `extractionRound_measures_code` — **headline**: the compiled extraction
      round of any well-shaped CSS code measures exactly `c.toStabilizers`,
      generalizing `QEC/GateSyndromeWorkedExample.lean`'s [[4,2,2]] `decide`
      demo to every code at once.
    * `extractionRound_measures_merged` + `extraction_implements_merge` — the
      surgery-gadget instance: the compiled circuit of the MERGED code
      measures `merged_stabilizers_X ++ merged_stabilizers_Z`, so running its
      measured observables through the Gottesman update IS the lattice-surgery
      merge `measureChecks` fold of `SurgeryCorrect`.

  ## The full chain to "implements the PPM on logical qubits"

      PhysCircuit (this file: measures the merged checks)
        → `SurgeryCorrect.measureChecks`               (definitional fold)
        → `surgery_implements_logical_measurement(_Z)` (eigenvalue (R) +
           non-disturbance (N), code-general, axiom-free)
        → `LogicalMeasurementGeneral.full_modexp_preserves_code_general`
           (sequences of logical PPMs preserve any CSS code).

  Faithfulness of the symplectic Heisenberg picture to full Hilbert-space
  state action is the cited Gottesman–Knill bridge (same residue as
  `CliffordConj` / `GateSyndromeWorkedExample`).

  ## Per-block segmentation (honest accounting)

  `CheckBlock.measuredObs` conjugates the ancilla observable through the
  BLOCK'S OWN ops, not through the other blocks of the round — the same
  per-check segmentation `GateSyndromeWorkedExample` and the
  `toStabilizers → measureChecks` layering use.  Composing the per-block
  observables into a single full-round Heisenberg pass is NOT mere ancilla
  freshness: pushing a Z-block's data observable back through an earlier
  X-block's CNOT fan multiplies in that X-row iff their GF(2) overlap is
  odd — so full-round invariance of the measured list holds exactly when
  every X-row/Z-row pair overlaps evenly, i.e. the (merged) CSS condition.
  That is the physical reason the CSS condition is load-bearing; the
  full-round interchange theorem (under `css_condition`) is an open
  strengthening, tracked in `QEC/README.md`.

  No Mathlib.  No `sorry`; no project axioms (the corpus instance at the
  bottom uses kernel `decide` for its hypotheses; the cited theorems are
  axiom-clean).
-/

import FormalRV.QEC.Circuit.SyndromeExtraction
import FormalRV.PPM.Rules.CliffordConj
import FormalRV.QEC.LatticeSurgery.SurgeryCorrect
import FormalRV.QEC.LatticeSurgery.SurgeryDemoSurface

namespace FormalRV.QEC.Circuit

open FormalRV.Framework.PauliSem
open FormalRV.Framework.CliffordConj
open FormalRV.Framework.LDPC
open FormalRV.Framework.PPMOp

/-! ## Heisenberg interpretation of the IR -/

/-- Conjugate an observable through one operation (Heisenberg picture).
    CNOT conjugates by the symplectic rule; preparations and measurements are
    conjugation-neutral (they delimit, rather than transform, observables). -/
def conjOp : PhysOp → PauliString → PauliString
  | .cx c t,   p => cnotConj c t p
  | .prep _ _, p => p
  | .meas _ _, p => p

/-- Conjugate an observable through a circuit, folding in FORWARD op order.

    Convention note: textbook back-conjugation of a final observable through
    `g₁; …; g_k` applies `g_k` first; this forward fold agrees with it
    whenever the conjugating ops mutually commute — which holds for every
    `CheckBlock` (a CNOT fan sharing its ancilla as common control/target),
    and matches the legacy `measGadgetConj`/`xMeasGadgetConj` folds exactly.
    A future non-CSS extension with basis-change gates must revisit the
    order convention. -/
def conjOps (ops : PhysCircuit) (p : PauliString) : PauliString :=
  ops.foldl (fun q op => conjOp op q) p

/-- The single-qubit observable a basis measurement reads. -/
def MeasBasis.toPauli : MeasBasis → Pauli
  | .z => Pauli.Z
  | .x => Pauli.X

/-- The ancilla observable of a block's final measurement, as a length-`w`
    string: identity everywhere, the measurement basis' Pauli at `anc`. -/
def ancillaObs (b : MeasBasis) (w anc : Nat) : PauliString :=
  ⟨Phase.plus, (List.replicate w Pauli.I).set anc b.toPauli⟩

/-- What a check block MEASURES on the `w`-qubit register (Heisenberg
    picture): its ancilla observable conjugated back through its ops. -/
def CheckBlock.measuredObs (w : Nat) (b : CheckBlock) : PauliString :=
  conjOps b.ops (ancillaObs b.basis w b.anc)

/-- The data-register part of an observable (first `n` qubits). -/
def dataPart (n : Nat) (p : PauliString) : PauliString :=
  ⟨p.phase, p.ops.take n⟩

/-- The list of data observables a round measures, in block order. -/
def Round.measuredDataObs (w n : Nat) (r : Round) : List PauliString :=
  r.map (fun b => dataPart n (CheckBlock.measuredObs w b))

@[simp] theorem Round.measuredDataObs_nil (w n : Nat) :
    Round.measuredDataObs w n [] = [] := rfl

theorem Round.measuredDataObs_append (w n : Nat) (r s : Round) :
    Round.measuredDataObs w n (r ++ s)
      = Round.measuredDataObs w n r ++ Round.measuredDataObs w n s := by
  simp [Round.measuredDataObs]

/-! ## A block's interpretation IS the CliffordConj gadget -/

/-- The Z-check block conjugates exactly as `measGadgetConj` (the
    ancilla-in-`|0⟩`, `CX data→anc` gadget of `CliffordConj`). -/
theorem conjOps_zBlock (anc : Nat) (supp : List Nat) (p : PauliString) :
    conjOps (CheckBlock.ops ⟨.z, anc, supp⟩) p = measGadgetConj supp anc p := by
  simp only [CheckBlock.ops, conjOps, List.foldl_cons, List.foldl_append,
             List.foldl_map, List.foldl_nil, conjOp, measGadgetConj]

/-- The X-check block conjugates exactly as `xMeasGadgetConj` (the
    ancilla-in-`|+⟩`, `CX anc→data` gadget of `CliffordConj`). -/
theorem conjOps_xBlock (anc : Nat) (supp : List Nat) (p : PauliString) :
    conjOps (CheckBlock.ops ⟨.x, anc, supp⟩) p = xMeasGadgetConj supp anc p := by
  simp only [CheckBlock.ops, conjOps, List.foldl_cons, List.foldl_append,
             List.foldl_map, List.foldl_nil, conjOp, xMeasGadgetConj]

/-! ## Canonical-input reading facts -/

private theorem ancillaObs_len (b : MeasBasis) (w anc : Nat) :
    (ancillaObs b w anc).ops.length = w := by
  simp [ancillaObs]

private theorem ancillaObs_at_anc (b : MeasBasis) (w anc : Nat) (h : anc < w) :
    (ancillaObs b w anc).ops.getD anc .I = b.toPauli := by
  simp only [ancillaObs]
  rw [List.getD_eq_getElem?_getD,
      List.getElem?_set_self (by simp only [List.length_replicate]; omega)]
  rfl

private theorem ancillaObs_other (b : MeasBasis) (w anc j : Nat) (hj : j ≠ anc) :
    (ancillaObs b w anc).ops.getD j .I = Pauli.I := by
  simp only [ancillaObs]
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega)]
  by_cases hjw : j < w
  · simp [hjw]
  · simp [hjw]

/-! ## Positionwise helpers -/

private theorem pauliString_ext (p q : PauliString)
    (hphase : p.phase = q.phase) (hlen : p.ops.length = q.ops.length)
    (hpos : ∀ j, j < p.ops.length → p.ops.getD j .I = q.ops.getD j .I) :
    p = q := by
  cases p with | mk pph pops =>
  cases q with | mk qph qops =>
  simp only at hphase hlen hpos
  subst hphase
  have hops : pops = qops := by
    apply List.ext_getElem hlen
    intro i h1 h2
    have h := hpos i h1
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
         List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
         Option.getD_some, Option.getD_some] at h
  rw [hops]

private theorem getD_take_eq (l : List Pauli) (n j : Nat) (hj : j < n)
    (hl : j < l.length) :
    (l.take n).getD j .I = l.getD j .I := by
  have hjt : j < (l.take n).length := by
    simp only [List.length_take]
    omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hjt, List.getElem?_eq_getElem hl,
      Option.getD_some, Option.getD_some]
  exact List.getElem_take ..

private theorem map_bit_getD (f : Bool → Pauli) (row : List Bool) (j : Nat)
    (hjr : j < row.length) :
    (row.map f).getD j .I = f (row.getD j false) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hjr,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjr]
  rfl

/-! ## The per-block measurement theorems -/

/-- **Z-check block semantics.**  The data-register part of what the block
    `(prep |0⟩ anc; CX s→anc for s ∈ supp(row); meas Z anc)` measures is
    EXACTLY the check's Pauli lowering `zStab row` — parametric in the row,
    the ancilla position (at or above the data register), and the register
    width. -/
theorem measuredObs_zBlock (w n anc : Nat) (row : List Bool)
    (hrow : row.length = n) (hlo : n ≤ anc) (hhi : anc < w) :
    dataPart n (CheckBlock.measuredObs w ⟨.z, anc, rowSupport row⟩)
      = FormalRV.QEC.CSSCode.zStab row := by
  have hbridge : CheckBlock.measuredObs w ⟨.z, anc, rowSupport row⟩
      = measGadgetConj (rowSupport row) anc (ancillaObs .z w anc) :=
    conjOps_zBlock anc (rowSupport row) _
  have hanc_notin : anc ∉ rowSupport row := by
    intro h
    have := rowSupport_lt row anc h
    omega
  have hnd := rowSupport_nodup row
  have hca : (ancillaObs .z w anc).ops.getD anc .I = Pauli.Z :=
    ancillaObs_at_anc .z w anc hhi
  have hrange : ∀ i ∈ rowSupport row, i < (ancillaObs .z w anc).ops.length := by
    intro i hi
    have := rowSupport_lt row i hi
    rw [ancillaObs_len]
    omega
  have hctrl0 : ∀ i ∈ rowSupport row, (ancillaObs .z w anc).ops.getD i .I = Pauli.I := by
    intro i hi
    have := rowSupport_lt row i hi
    exact ancillaObs_other .z w anc i (by omega)
  obtain ⟨hZ, _, hother⟩ :=
    measGadget_characterization (rowSupport row) anc (ancillaObs .z w anc)
      (by rw [ancillaObs_len]; omega) hanc_notin hnd hca hrange hctrl0
  have hlen : (measGadgetConj (rowSupport row) anc (ancillaObs .z w anc)).ops.length = w := by
    rw [gadget_len, ancillaObs_len]
  have hphase : (measGadgetConj (rowSupport row) anc (ancillaObs .z w anc)).phase
      = Phase.plus := gadget_phase ..
  apply pauliString_ext
  · show (dataPart n (CheckBlock.measuredObs w ⟨.z, anc, rowSupport row⟩)).phase = _
    rw [dataPart, hbridge]
    exact hphase
  · simp only [dataPart, hbridge, FormalRV.QEC.CSSCode.zStab, List.length_take,
               List.length_map, hlen]
    omega
  · intro j hj
    simp only [dataPart, hbridge, List.length_take, hlen] at hj
    have hjn : j < n := by omega
    have hjlen : j < (measGadgetConj (rowSupport row) anc (ancillaObs .z w anc)).ops.length := by
      omega
    simp only [dataPart, hbridge]
    rw [getD_take_eq _ n j hjn hjlen,
        show (FormalRV.QEC.CSSCode.zStab row).ops = row.map FormalRV.QEC.CSSCode.zbit from rfl,
        map_bit_getD _ row j (by omega)]
    by_cases hbit : row.getD j false = true
    · have hmem : j ∈ rowSupport row := (mem_rowSupport row j).mpr ⟨by omega, hbit⟩
      rw [hZ j hmem, hbit]
      rfl
    · have hnotmem : j ∉ rowSupport row := by
        intro h
        exact hbit ((mem_rowSupport row j).mp h).2
      rw [hother j (by omega) hnotmem, ancillaObs_other .z w anc j (by omega)]
      simp only [Bool.not_eq_true] at hbit
      rw [hbit]
      rfl

/-- **X-check block semantics** — the exact dual. -/
theorem measuredObs_xBlock (w n anc : Nat) (row : List Bool)
    (hrow : row.length = n) (hlo : n ≤ anc) (hhi : anc < w) :
    dataPart n (CheckBlock.measuredObs w ⟨.x, anc, rowSupport row⟩)
      = FormalRV.QEC.CSSCode.xStab row := by
  have hbridge : CheckBlock.measuredObs w ⟨.x, anc, rowSupport row⟩
      = xMeasGadgetConj (rowSupport row) anc (ancillaObs .x w anc) :=
    conjOps_xBlock anc (rowSupport row) _
  have hanc_notin : anc ∉ rowSupport row := by
    intro h
    have := rowSupport_lt row anc h
    omega
  have hnd := rowSupport_nodup row
  have hca : (ancillaObs .x w anc).ops.getD anc .I = Pauli.X :=
    ancillaObs_at_anc .x w anc hhi
  have hrange : ∀ i ∈ rowSupport row, i < (ancillaObs .x w anc).ops.length := by
    intro i hi
    have := rowSupport_lt row i hi
    rw [ancillaObs_len]
    omega
  have hctrl0 : ∀ i ∈ rowSupport row, (ancillaObs .x w anc).ops.getD i .I = Pauli.I := by
    intro i hi
    have := rowSupport_lt row i hi
    exact ancillaObs_other .x w anc i (by omega)
  obtain ⟨hX, _, hother⟩ :=
    xMeasGadget_characterization (rowSupport row) anc (ancillaObs .x w anc)
      (by rw [ancillaObs_len]; omega) hanc_notin hnd hca hrange hctrl0
  have hlen : (xMeasGadgetConj (rowSupport row) anc (ancillaObs .x w anc)).ops.length = w := by
    rw [xgadget_len, ancillaObs_len]
  have hphase : (xMeasGadgetConj (rowSupport row) anc (ancillaObs .x w anc)).phase
      = Phase.plus := xgadget_phase ..
  apply pauliString_ext
  · show (dataPart n (CheckBlock.measuredObs w ⟨.x, anc, rowSupport row⟩)).phase = _
    rw [dataPart, hbridge]
    exact hphase
  · simp only [dataPart, hbridge, FormalRV.QEC.CSSCode.xStab, List.length_take,
               List.length_map, hlen]
    omega
  · intro j hj
    simp only [dataPart, hbridge, List.length_take, hlen] at hj
    have hjn : j < n := by omega
    have hjlen : j < (xMeasGadgetConj (rowSupport row) anc (ancillaObs .x w anc)).ops.length := by
      omega
    simp only [dataPart, hbridge]
    rw [getD_take_eq _ n j hjn hjlen,
        show (FormalRV.QEC.CSSCode.xStab row).ops = row.map FormalRV.QEC.CSSCode.xbit from rfl,
        map_bit_getD _ row j (by omega)]
    by_cases hbit : row.getD j false = true
    · have hmem : j ∈ rowSupport row := (mem_rowSupport row j).mpr ⟨by omega, hbit⟩
      rw [hX j hmem, hbit]
      rfl
    · have hnotmem : j ∉ rowSupport row := by
        intro h
        exact hbit ((mem_rowSupport row j).mp h).2
      rw [hother j (by omega) hnotmem, ancillaObs_other .x w anc j (by omega)]
      simp only [Bool.not_eq_true] at hbit
      rw [hbit]
      rfl

/-! ## Round-level: the compiled round measures the lowered check list -/

private theorem measuredDataObs_xBlocksFrom (n w : Nat) (rows : BoolMat) :
    ∀ (a : Nat), n ≤ a → a + rows.length ≤ w →
      (∀ row ∈ rows, row.length = n) →
      Round.measuredDataObs w n (xBlocksFrom rows a)
        = rows.map FormalRV.QEC.CSSCode.xStab := by
  induction rows with
  | nil => intro a _ _ _; rfl
  | cons row rest ih =>
    intro a hna haw hrows
    simp only [xBlocksFrom, Round.measuredDataObs, List.map_cons]
    rw [measuredObs_xBlock w n a row (hrows row (List.mem_cons_self ..)) hna
          (by simp only [List.length_cons] at haw; omega)]
    have := ih (a + 1) (by omega)
      (by simp only [List.length_cons] at haw; omega)
      (fun r hr => hrows r (List.mem_cons_of_mem _ hr))
    simpa [Round.measuredDataObs] using this

private theorem measuredDataObs_zBlocksFrom (n w : Nat) (rows : BoolMat) :
    ∀ (a : Nat), n ≤ a → a + rows.length ≤ w →
      (∀ row ∈ rows, row.length = n) →
      Round.measuredDataObs w n (zBlocksFrom rows a)
        = rows.map FormalRV.QEC.CSSCode.zStab := by
  induction rows with
  | nil => intro a _ _ _; rfl
  | cons row rest ih =>
    intro a hna haw hrows
    simp only [zBlocksFrom, Round.measuredDataObs, List.map_cons]
    rw [measuredObs_zBlock w n a row (hrows row (List.mem_cons_self ..)) hna
          (by simp only [List.length_cons] at haw; omega)]
    have := ih (a + 1) (by omega)
      (by simp only [List.length_cons] at haw; omega)
      (fun r hr => hrows r (List.mem_cons_of_mem _ hr))
    simpa [Round.measuredDataObs] using this

/-- **HEADLINE.**  The compiled syndrome-extraction round of ANY well-shaped
    CSS code measures, on the data register, exactly the code's lowered
    stabilizer list `c.toStabilizers` — the parametric generalization of the
    `GateSyndromeWorkedExample` [[4,2,2]] `decide` demo.  Combined with
    `CSSCode.syndrome_circuit_implements_code`, the measured set is a valid
    stabilizer code iff the CSS condition holds. -/
theorem extractionRound_measures_code (c : FormalRV.QEC.CSSCode)
    (hws : c.well_shaped = true) :
    Round.measuredDataObs (c.n + c.hx.length + c.hz.length) c.n
        (FormalRV.QEC.CSSCode.extractionRound c)
      = c.toStabilizers := by
  rw [FormalRV.QEC.CSSCode.well_shaped, Bool.and_eq_true, matrix_has_n_cols,
      matrix_has_n_cols, List.all_eq_true, List.all_eq_true] at hws
  obtain ⟨hwx, hwz⟩ := hws
  have hxlen : ∀ row ∈ c.hx, row.length = c.n := by
    intro row hr
    have := hwx row hr
    simpa using this
  have hzlen : ∀ row ∈ c.hz, row.length = c.n := by
    intro row hr
    have := hwz row hr
    simpa using this
  unfold FormalRV.QEC.CSSCode.extractionRound extractionBlocks
  rw [Round.measuredDataObs_append,
      measuredDataObs_xBlocksFrom c.n _ c.hx c.n (Nat.le_refl _) (by omega) hxlen,
      measuredDataObs_zBlocksFrom c.n _ c.hz (c.n + c.hx.length) (by omega) (by omega) hzlen]
  rfl

/-! ## Surgery-gadget instance: the compiled circuit implements the merge -/

/-- `xRow` (the surgery-side lowering) coincides with `xStab` (the code-side
    lowering) — the duplication flagged in `CSSCode.lean`'s header, pinned. -/
theorem xRow_eq_xStab (l : List Bool) :
    FormalRV.Framework.SurgeryReadout.xRow l = FormalRV.QEC.CSSCode.xStab l := rfl

theorem zRow_eq_zStab (l : List Bool) :
    FormalRV.Framework.SurgeryCorrect.zRow l = FormalRV.QEC.CSSCode.zStab l := rfl

/-- The compiled extraction round of a surgery gadget's MERGED code measures
    exactly the merged stabilizers (X-checks then Z-checks) — the operators
    whose `measureChecks` fold is the verified lattice-surgery merge. -/
theorem extractionRound_measures_merged (g : SurgeryGadget)
    (hxr : ∀ row ∈ g.merged_hx, row.length = g.merged_n)
    (hzr : ∀ row ∈ g.merged_hz, row.length = g.merged_n) :
    Round.measuredDataObs (g.merged_n + g.merged_hx.length + g.merged_hz.length)
        g.merged_n (SurgeryGadget.extractionRound g)
      = FormalRV.Framework.SurgeryReadout.merged_stabilizers_X g
        ++ FormalRV.Framework.SurgeryCorrect.merged_stabilizers_Z g := by
  unfold SurgeryGadget.extractionRound extractionBlocks
  rw [Round.measuredDataObs_append,
      measuredDataObs_xBlocksFrom g.merged_n _ g.merged_hx g.merged_n
        (Nat.le_refl _) (by omega) hxr,
      measuredDataObs_zBlocksFrom g.merged_n _ g.merged_hz
        (g.merged_n + g.merged_hx.length) (by omega) (by omega) hzr]
  unfold FormalRV.Framework.SurgeryReadout.merged_stabilizers_X
         FormalRV.Framework.SurgeryCorrect.merged_stabilizers_Z
  rw [List.map_congr_left (fun l _ => xRow_eq_xStab l),
      List.map_congr_left (fun l _ => zRow_eq_zStab l)]

/-- **The chain-capstone.**  Running the measured data observables of the
    compiled circuit through the Gottesman PPM update IS the lattice-surgery
    merge: `measureChecks` of the merged X-checks then the merged Z-checks —
    the state-map whose single-type stages are the subjects of
    `SurgeryCorrect`'s (R)-readout identity and (N)-preservation theorems.
    The COMPOSED (N) for this full fold is `extraction_preserves_commuting`
    below; the (R) identity applies to the circuit's X-prefix via
    `extraction_measures_readout`. -/
theorem extraction_implements_merge (g : SurgeryGadget)
    (hxr : ∀ row ∈ g.merged_hx, row.length = g.merged_n)
    (hzr : ∀ row ∈ g.merged_hz, row.length = g.merged_n)
    (s : StabilizerState) :
    FormalRV.Framework.SurgeryCorrect.measureChecks
        (Round.measuredDataObs (g.merged_n + g.merged_hx.length + g.merged_hz.length)
          g.merged_n (SurgeryGadget.extractionRound g)) s
      = FormalRV.Framework.SurgeryCorrect.measureChecks
          (FormalRV.Framework.SurgeryCorrect.merged_stabilizers_Z g)
          (FormalRV.Framework.SurgeryCorrect.measureChecks
            (FormalRV.Framework.SurgeryReadout.merged_stabilizers_X g) s) := by
  rw [extractionRound_measures_merged g hxr hzr]
  unfold FormalRV.Framework.SurgeryCorrect.measureChecks
  exact List.foldl_append ..

/-- **Composed non-disturbance (N) for the COMPILED CIRCUIT.**  Any operator
    of the pre-merge stabilizer state that commutes with every observable the
    compiled circuit measures is preserved through the circuit's whole
    state-map — `mem_measureChecks_of_commutesAll` applied to the measured
    list, made a statement about the SYNTACTIC object via
    `extractionRound_measures_merged`. -/
theorem extraction_preserves_commuting (g : SurgeryGadget)
    (hxr : ∀ row ∈ g.merged_hx, row.length = g.merged_n)
    (hzr : ∀ row ∈ g.merged_hz, row.length = g.merged_n)
    (s : StabilizerState) (L : PauliString) (hmem : L ∈ s)
    (hcomm : ∀ P ∈ FormalRV.Framework.SurgeryReadout.merged_stabilizers_X g
                ++ FormalRV.Framework.SurgeryCorrect.merged_stabilizers_Z g,
        L.commutes P = true) :
    L ∈ FormalRV.Framework.SurgeryCorrect.measureChecks
          (Round.measuredDataObs
            (g.merged_n + g.merged_hx.length + g.merged_hz.length)
            g.merged_n (SurgeryGadget.extractionRound g)) s := by
  rw [extractionRound_measures_merged g hxr hzr]
  exact FormalRV.Framework.SurgeryCorrect.mem_measureChecks_of_commutesAll
    _ L s hmem hcomm

/-- **Readout (R) on the COMPILED CIRCUIT.**  The first `|merged_hx|`
    observables the compiled circuit measures are exactly the merged
    X-checks (a syntactic prefix identity), and the span-witness-selected
    signed product of those checks reads the target logical Pauli — the
    `surgery_eigenvalue` identity, now anchored to the circuit object.
    (Binding the `signs` argument to the circuit's actual measurement
    records needs outcome semantics in the IR — tracked residue.) -/
theorem extraction_measures_readout (g : SurgeryGadget) (hn : 0 < g.merged_n)
    (signs : List Bool)
    (hxr : ∀ row ∈ g.merged_hx, row.length = g.merged_n)
    (hzr : ∀ row ∈ g.merged_hz, row.length = g.merged_n)
    (hsig : signs.length = g.merged_hx.length)
    (hker : g.targets_logical_correctly = true) :
    ((Round.measuredDataObs
        (g.merged_n + g.merged_hx.length + g.merged_hz.length)
        g.merged_n (SurgeryGadget.extractionRound g)).take g.merged_hx.length
      = FormalRV.Framework.SurgeryReadout.merged_stabilizers_X g)
    ∧ FormalRV.Framework.SurgeryCorrect.selectedSignedProduct
        g.span_witness g.merged_hx signs
      = FormalRV.Framework.SurgeryCorrect.signedXRow
          (FormalRV.Framework.SurgeryCorrect.selectedParity g.span_witness signs)
          g.target_pauli := by
  constructor
  · rw [extractionRound_measures_merged g hxr hzr]
    have hlen : g.merged_hx.length
        = (FormalRV.Framework.SurgeryReadout.merged_stabilizers_X g).length := by
      simp [FormalRV.Framework.SurgeryReadout.merged_stabilizers_X]
    rw [hlen]
    exact List.take_left ..
  · exact FormalRV.Framework.SurgeryCorrect.surgery_eigenvalue
      g g.merged_n hn signs hxr hsig hker

/-! ## Corpus instance: the verified surface3 X̄ surgery -/

/-- The compiled 28-qubit circuit (14 data+surgery-ancilla qubits, 8+6
    syndrome ancillas) of the verified [[13,1,3]] X̄ surgery measures exactly
    its merged stabilizers, and the gadget passes the structural verifier.
    Together with `extraction_preserves_commuting` (composed (N)) and
    `extraction_measures_readout` (the (R) identity on the circuit's
    X-prefix, with `surface3_x_surgery_measures_logicalX` as its corpus
    instance), this anchors the logical-X̄-PPM chain to the compiled
    physical circuit; the remaining un-formalized step is binding outcome
    `signs` to measurement records (no outcome semantics in the IR yet). -/
theorem surface3_circuit_measures_merged_and_verifies :
    (Round.measuredDataObs
        (FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery.merged_n
          + FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery.merged_hx.length
          + FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery.merged_hz.length)
        FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery.merged_n
        (SurgeryGadget.extractionRound
          FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery)
      = FormalRV.Framework.SurgeryReadout.merged_stabilizers_X
          FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery
        ++ FormalRV.Framework.SurgeryCorrect.merged_stabilizers_Z
          FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery)
    ∧ SurgeryGadget.verify_surgery_gadget
        FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery = true := by
  constructor
  · exact extractionRound_measures_merged
      FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery
      (by decide) (by decide)
  · exact FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery_verifies

end FormalRV.QEC.Circuit
