/-
  FormalRV.QEC.Circuit.SyndromeExtraction — the syndrome-extraction COMPILER:
  from a CSS code's check matrices (or a surgery gadget's merged code) to the
  standard extraction circuit as a syntactic `PhysCircuit` object.

  ## What this closes

  Until this file, the detailed physical syndrome-extraction circuit existed
  only as emitted Stim STRINGS (`QEC/LatticeSurgery/StimEmit.lean`) — nothing
  in Lean could count it or attach semantics to it.  Here the same circuit is
  built as a `Round` of `CheckBlock`s over virtual qubits:

    * data (+ surgery-ancilla) qubits `0 .. n−1`;
    * one syndrome ancilla per check: X-check `i` uses ancilla `n + i`,
      Z-check `j` uses ancilla `n + |hx| + j` — same layout as `StimEmit`;
    * per X-check: prep `|+⟩`, `CX anc→s` for `s` in the row support, `MX`;
      per Z-check: prep `|0⟩`, `CX s→anc`, `M`.

  `toStim` of the compiled object reproduces `StimEmit.surgeryToStim` exactly
  (pinned on the Steane gadget below by `native_decide`; the legacy emitter is
  from now on a VIEW of this object).  The honest tree-walk counters live in
  `FormalRV/Resource/QECCircuitCount.lean`; the count theorems tying them to
  the legacy gadget-field counters (`surgeryPhysQubits` etc.) are in
  `ExtractionCount.lean`; the stabilizer semantics (the compiled circuit
  measures exactly the code's stabilizers) is in `CircuitSemantics.lean`.

  The block builders are RECURSIVE (not `zipIdx.map`) so that every downstream
  counting and semantics theorem is a clean structural induction.

  No Mathlib.  No `sorry`; no project axioms (the Stim pin below uses
  `native_decide`, which carries the standard compiler-trust axiom — the
  defs and structural lemmas are kernel-checked).
-/

import FormalRV.QEC.Circuit.PhysCircuit
import FormalRV.QEC.CSSCode
import FormalRV.QEC.LatticeSurgery.LDPCSurgery
import FormalRV.QEC.LatticeSurgery.StimEmit
import FormalRV.QEC.LatticeSurgery.SurgeryDemoSteane

namespace FormalRV.QEC.Circuit

open FormalRV.Framework.LDPC

/-! ## Block builders -/

/-- X-check blocks for the given rows, with ancillas `a, a+1, …`. -/
def xBlocksFrom : BoolMat → Nat → Round
  | [],          _ => []
  | row :: rest, a => ⟨.x, a, rowSupport row⟩ :: xBlocksFrom rest (a + 1)

/-- Z-check blocks for the given rows, with ancillas `a, a+1, …`. -/
def zBlocksFrom : BoolMat → Nat → Round
  | [],          _ => []
  | row :: rest, a => ⟨.z, a, rowSupport row⟩ :: zBlocksFrom rest (a + 1)

/-- One full syndrome-extraction round of the code `(n, hx, hz)`:
    X-check blocks first (ancillas `n .. n+|hx|−1`), then Z-check blocks
    (ancillas `n+|hx| .. n+|hx|+|hz|−1`) — the `StimEmit` layout. -/
def extractionBlocks (n : Nat) (hx hz : BoolMat) : Round :=
  xBlocksFrom hx n ++ zBlocksFrom hz (n + hx.length)

@[simp] theorem xBlocksFrom_length (rows : BoolMat) :
    ∀ (a : Nat), (xBlocksFrom rows a).length = rows.length := by
  induction rows with
  | nil => intro _; rfl
  | cons row rest ih => intro a; simp [xBlocksFrom, ih (a + 1)]

@[simp] theorem zBlocksFrom_length (rows : BoolMat) :
    ∀ (a : Nat), (zBlocksFrom rows a).length = rows.length := by
  induction rows with
  | nil => intro _; rfl
  | cons row rest ih => intro a; simp [zBlocksFrom, ih (a + 1)]

/-- One block per check. -/
theorem extractionBlocks_length (n : Nat) (hx hz : BoolMat) :
    (extractionBlocks n hx hz).length = hx.length + hz.length := by
  simp [extractionBlocks]

/-! ## The compiled objects -/

/-- The standard syndrome-extraction round of a CSS code, as a syntactic
    circuit object. -/
def _root_.FormalRV.QEC.CSSCode.extractionRound (c : FormalRV.QEC.CSSCode) : Round :=
  extractionBlocks c.n c.hx c.hz

/-- The extraction round of a surgery gadget's MERGED code — the per-round
    physical circuit of the lattice-surgery merge (data + surgery ancilla
    `0..merged_n−1`, one syndrome ancilla per merged check). -/
def _root_.FormalRV.Framework.LDPC.SurgeryGadget.extractionRound
    (g : SurgeryGadget) : Round :=
  extractionBlocks g.merged_n g.merged_hx g.merged_hz

/-- The full merge circuit: `tau_s` repetitions of the extraction round
    (syndrome ancillas are re-prepared each round — `prep` is a reset). -/
def _root_.FormalRV.Framework.LDPC.SurgeryGadget.extractionCircuit
    (g : SurgeryGadget) : PhysCircuit :=
  (List.replicate g.tau_s (SurgeryGadget.extractionRound g)).flatMap Round.ops

/-! ## Stim bridge

    The serialized IR object reproduces the legacy string emitter exactly.
    Pinned on the smallest verified gadget (Steane [[7,1,3]] X̄ surgery:
    5 merged X-checks + 3 merged Z-checks over `merged_n = 8` data+surgery
    qubits, syndrome ancillas `8..15`); the surface3 pin lives in
    `ExtractionCount.lean` next to its count cross-checks.  The parametric
    string-level identity is a documented residue (string-lemma plumbing, no
    mathematical content).  From these theorems on, `StimEmit.surgeryToStim`
    output is certified to be a VIEW of the syntactic `extractionRound`
    object for the pinned corpus. -/

theorem steane_extraction_stim_eq :
    toStim (Round.ops
        (SurgeryGadget.extractionRound
          FormalRV.LatticeSurgery.SurgeryDemoSteane.steane_x_surgery))
      = FormalRV.LatticeSurgery.StimEmit.surgeryToStim
          FormalRV.LatticeSurgery.SurgeryDemoSteane.steane_x_surgery := by
  native_decide

end FormalRV.QEC.Circuit
