/-
  FormalRV.QEC.Gidney21.SplitDetach
  ─────────────────────────────────
  **(completeness) SPLIT / DETACH — the inverse of merge, freeing the surgery
  ancilla.**

  After a merge has measured its joint logical (over `tau_s` rounds of merged
  syndrome extraction), the patches are SPLIT back apart: the surgery ancilla
  qubits are measured OUT (single-qubit `Z` measurements — the standard
  X-merge detach), decoupling them, and the data patches resume their OWN
  syndrome extraction.  The post-split code is EXACTLY the original
  `data_code`, so the patches are restored.

  Two correctness facts, both reusing existing machinery:
    • the detach MEASURES every surgery-ancilla qubit (one `Z`-measurement
      each — the ancilla is freed);
    • the RESTORED patches' syndrome extraction measures `data_code`'s
      stabilizers (`extractionRound_measures_code`, parametric, kernel-pure).

  The merge→split round trip thus returns to the original patches, with the
  detach measurements counted on the real circuit.
-/
import FormalRV.QEC.Gidney21.RotatedMerge
import FormalRV.QEC.Gidney21.SurgerySemantics
import FormalRV.QEC.LogicalLayout.PhysicalCompile

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC FormalRV.QEC.Circuit
open FormalRV.QEC.LogicalLayout
open FormalRV.Framework.LDPC
open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp
open FormalRV.Framework.SurgeryCorrect
open FormalRV.LatticeSurgery
open FormalRV.Resource

/-! ## §1. The detach circuit (measure the surgery ancilla out). -/

/-- **The DETACH circuit**: measure each surgery-ancilla qubit (indices
`data_code.n .. data_code.n + ancilla_n − 1`) in the `Z` basis, freeing them
and splitting the merged patch back apart. -/
def detachCircuit (g : SurgeryGadget) : PhysCircuit :=
  (List.range g.ancilla_n).map
    (fun i => PhysOp.meas MeasBasis.z (g.data_code.n + i))

/-- **The detach measures exactly the `ancilla_n` surgery-ancilla qubits** —
the freed ancilla count, walked from the circuit. -/
theorem detachCircuit_measCount (g : SurgeryGadget) :
    measCountC (detachCircuit g) = g.ancilla_n := by
  show ((List.range g.ancilla_n).map
      (fun i => PhysOp.meas MeasBasis.z (g.data_code.n + i))).countP
      (fun op => op.isMeas) = g.ancilla_n
  rw [List.countP_map]
  trans (List.range g.ancilla_n).length
  · apply List.countP_eq_length.mpr; intro a _; rfl
  · exact List.length_range

/-! ## §2. The restored patches (post-split = data_code). -/

/-- **The post-split code IS the original `data_code`** — the patches as they
were before the merge. -/
def postSplitCSS (g : SurgeryGadget) : CSSCode :=
  ⟨g.data_code.n, g.data_code.hx, g.data_code.hz⟩

/-- **SPLIT RESTORES THE PATCHES**: after the detach, the resumed syndrome
extraction of the data patches measures EXACTLY `data_code`'s stabilizers —
the original code, recovered (parametric, kernel-pure). -/
theorem split_restores_patches (g : SurgeryGadget)
    (hws : (postSplitCSS g).well_shaped = true) :
    Round.measuredDataObs
        ((postSplitCSS g).n + (postSplitCSS g).hx.length + (postSplitCSS g).hz.length)
        (postSplitCSS g).n
        (CSSCode.extractionRound (postSplitCSS g))
      = (postSplitCSS g).toStabilizers :=
  extractionRound_measures_code (postSplitCSS g) hws

/-! ## §3. The full split circuit and its resource. -/

/-- **The SPLIT circuit**: detach the ancilla, then run `rounds` cycles of the
restored patches' syndrome extraction. -/
def splitCircuit (g : SurgeryGadget) (rounds : Nat) : PhysCircuit :=
  detachCircuit g ++ CSSCode.extractionCircuitN (postSplitCSS g) rounds

/-- **The split's measurement count, walked from the circuit**: the
`ancilla_n` detach measurements plus `rounds · (|hx|+|hz|)` restored-patch
syndrome measurements. -/
theorem splitCircuit_measCount (g : SurgeryGadget) (rounds : Nat) :
    measCountC (splitCircuit g rounds)
      = g.ancilla_n
        + rounds * ((postSplitCSS g).hx.length + (postSplitCSS g).hz.length) := by
  rw [splitCircuit, measCountC_append, detachCircuit_measCount,
      extractionCircuitN_measCount]

/-- **A split is STRUCTURALLY CORRECT** when its detach frees all the surgery
ancilla AND the restored patches' syndrome extraction is correct. -/
def SplitFullyCorrect (g : SurgeryGadget) : Prop :=
  measCountC (detachCircuit g) = g.ancilla_n
    ∧ ((postSplitCSS g).well_shaped = true →
        Round.measuredDataObs
          ((postSplitCSS g).n + (postSplitCSS g).hx.length
            + (postSplitCSS g).hz.length)
          (postSplitCSS g).n (CSSCode.extractionRound (postSplitCSS g))
        = (postSplitCSS g).toStabilizers)

/-- Every split is structurally correct (both facts from the reused lemmas). -/
theorem splitFullyCorrect_of (g : SurgeryGadget) : SplitFullyCorrect g :=
  ⟨detachCircuit_measCount g, fun hws => split_restores_patches g hws⟩

/-! ## §4. Concrete: the rotated-surface merge→split round trip at d=27. -/

/-- The d=27 X-merge's split frees its single surgery ancilla. -/
theorem rotatedXMerge27_detach_count :
    measCountC (detachCircuit (rotatedXMerge 27 18 40)) = 1 :=
  detachCircuit_measCount (rotatedXMerge 27 18 40)

/-- **The d=27 X-merge's split is structurally correct** — detach + restored
patches. -/
theorem rotatedXMerge27_split_correct : SplitFullyCorrect (rotatedXMerge 27 18 40) :=
  splitFullyCorrect_of (rotatedXMerge 27 18 40)

/-- **The split restores the genuine rotated `[[729,1,27]]` patch**: the
post-split code's syndrome extraction measures the rotated-surface
stabilizers (via the d=27 well-shapedness). -/
theorem rotatedXMerge27_split_restores :
    Round.measuredDataObs
        ((postSplitCSS (rotatedXMerge 27 18 40)).n
          + (postSplitCSS (rotatedXMerge 27 18 40)).hx.length
          + (postSplitCSS (rotatedXMerge 27 18 40)).hz.length)
        (postSplitCSS (rotatedXMerge 27 18 40)).n
        (CSSCode.extractionRound (postSplitCSS (rotatedXMerge 27 18 40)))
      = (postSplitCSS (rotatedXMerge 27 18 40)).toStabilizers :=
  split_restores_patches (rotatedXMerge 27 18 40) (by native_decide)

/-! ## §5. SPLIT NON-DISTURBANCE — the data logicals survive the detach. -/

/-- **The detach's measured observables**: a single-qubit `Z` on each surgery-
ancilla qubit (`data_code.n + i`), as a `PauliString` of width `merged_n`. -/
def detachObservables (g : SurgeryGadget) : List PauliString :=
  (List.range g.ancilla_n).map (fun i =>
    zRow ((List.range g.merged_n).map (fun j => decide (j = g.data_code.n + i))))

/-- **SPLIT NON-DISTURBANCE (general).**  Any logical operator `L ∈ s` that
COMMUTES with every detach observable SURVIVES the split — it stays in the
post-detach stabilizer group.  This is the (N) half for the split, exactly
parallel to the merge's `surgery_preserves_commuting_logical`, reusing the
same fold-preservation lemma. -/
theorem split_preserves_commuting_logical (g : SurgeryGadget) (L : PauliString)
    (s : StabilizerState) (hmem : L ∈ s)
    (hcomm : ∀ P ∈ detachObservables g, L.commutes P = true) :
    L ∈ measureChecks (detachObservables g) s :=
  mem_measureChecks_of_commutesAll (detachObservables g) L s hmem hcomm

/-- **Every detach observable is a `Z`-row** (a single `Z`, the rest `I`). -/
theorem detachObservables_zRow (g : SurgeryGadget) :
    ∀ P ∈ detachObservables g, ∃ v : BoolVec, P = zRow v := by
  intro P hP
  rw [detachObservables, List.mem_map] at hP
  obtain ⟨i, _, rfl⟩ := hP
  exact ⟨_, rfl⟩

/-- **Z-TYPE DATA LOGICALS SURVIVE THE SPLIT.**  Any `Z`-type operator
(`zRow a`) in the stabilizer group is preserved through the detach — since
all `Z`/`I` strings commute (`zRow_commutes`), it commutes with every detach
`Z`-observable and stays in the post-split group. -/
theorem split_preserves_zRow_logical (g : SurgeryGadget) (a : BoolVec)
    (s : StabilizerState) (hmem : zRow a ∈ s) :
    zRow a ∈ measureChecks (detachObservables g) s := by
  apply split_preserves_commuting_logical g (zRow a) s hmem
  intro P hP
  obtain ⟨v, rfl⟩ := detachObservables_zRow g P hP
  exact zRow_commutes a v

/-! ### Non-disturbance for ALL logical types (X, Z, Y, mixed). -/

/-- **Pointwise ⇒ global commutation**: if a Pauli string commutes with
another at EVERY position, the strings commute. -/
theorem commutes_of_all_pos (L obs : PauliString)
    (h : ∀ p ∈ L.ops.zip obs.ops, Pauli.commutes p.1 p.2 = true) :
    L.commutes obs = true := by
  have hz : (L.ops.zip obs.ops).countP
      (fun p => ! Pauli.commutes p.1 p.2) = 0 := by
    rw [List.countP_eq_zero]
    intro p hp
    simp [h p hp]
  unfold PauliString.commutes
  simp only [hz, Nat.zero_mod, beq_self_eq_true]

/-- **A single-`Z` detach observable commutes with ANY operator that is
identity at that ancilla position.**  Holds for X-, Z-, Y-, or mixed-type
`L` — the only place the observable could anticommute is the lone `Z`, and
there `L` is `I`. -/
theorem detachObs_commutes_of_I (L : PauliString) (q n : Nat)
    (hlen : L.ops.length = n) (hq : q < n)
    (hI : L.ops[q]'(by omega) = Pauli.I) :
    L.commutes (zRow ((List.range n).map (fun j => decide (j = q)))) = true := by
  apply commutes_of_all_pos
  intro p hp
  rw [List.mem_iff_getElem] at hp
  obtain ⟨j, hj, hpj⟩ := hp
  rw [List.length_zip] at hj
  rw [List.getElem_zip] at hpj
  subst hpj
  simp only [zRow, List.getElem_map, List.getElem_range]
  by_cases hjq : j = q
  · subst hjq
    simp only [decide_true]
    rw [hI]
    decide
  · simp only [hjq, decide_false]
    cases L.ops[j] <;> decide

/-- **ALL DATA LOGICALS SURVIVE THE SPLIT.**  Any operator `L ∈ s` of width
`merged_n` that is IDENTITY on the surgery-ancilla qubits (`data_code.n ≤ q`)
— X-type, Z-type, Y-type, or mixed — is preserved through the detach: it
commutes with every detach observable (each a single `Z` on an ancilla
qubit, where `L` is `I`).  So the split disturbs no logical of any type. -/
theorem split_preserves_data_logical (g : SurgeryGadget) (L : PauliString)
    (s : StabilizerState) (hmem : L ∈ s)
    (hlen : L.ops.length = g.merged_n)
    (hI : ∀ (q : Nat) (hq : q < g.merged_n), g.data_code.n ≤ q →
            L.ops[q]'(by rw [hlen]; exact hq) = Pauli.I) :
    L ∈ measureChecks (detachObservables g) s := by
  apply split_preserves_commuting_logical g L s hmem
  intro P hP
  rw [detachObservables, List.mem_map] at hP
  obtain ⟨i, hi, rfl⟩ := hP
  rw [List.mem_range] at hi
  have hqlt : g.data_code.n + i < g.merged_n := by
    show g.data_code.n + i < g.data_code.n + g.ancilla_n; omega
  exact detachObs_commutes_of_I L (g.data_code.n + i) g.merged_n hlen hqlt
    (hI (g.data_code.n + i) hqlt (Nat.le_add_right _ _))

end FormalRV.QEC.Gidney21
