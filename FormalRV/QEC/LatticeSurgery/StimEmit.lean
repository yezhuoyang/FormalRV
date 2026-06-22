/-
  FormalRV.LatticeSurgery.StimEmit — emit a verified surgery gadget's merged-code
  stabilizer-measurement circuit as a Stim program (the framework producing the
  actual compiled surface-code circuit), for cross-validation against Stim
  (the reference Gottesman–Knill simulator) and downstream TQEC tooling.

  Path A tooling (John 2026-06-02): debug/validate the surgery construction with
  Stim, and make the framework emit Stim/TQEC code.  The emitted circuit is the
  DETAILED physical syndrome extraction of the merged code: for each merged
  X-check (support S) an ancilla in |+⟩, `CX anc→s` for s∈S, measure X; for each
  merged Z-check an ancilla in |0⟩, `CX s→anc`, measure Z.  Measurement records
  appear in order: X-checks first (rec 0..|hx|−1), then Z-checks.  A Stim FLOW
  check (in `PyCircuits/`) then confirms the span_witness-selected X-check records
  read the logical X̄ — independently reproducing `surface3_x_surgery_measures_logicalX`.

  No Mathlib.  Pure String emission.  (No theorems here — this is the codegen
  bridge; the SEMANTICS are proven in `SurgeryDemoSurface` / `SurgeryCorrect`.)
-/

import FormalRV.QEC.LatticeSurgery.LDPCSurgery
namespace FormalRV.LatticeSurgery.StimEmit

open FormalRV.Framework FormalRV.Framework.LDPC

/-- The support (list of qubit indices where the row is `true`) of a check row. -/
def rowSupport (row : List Bool) : List Nat :=
  (row.zipIdx.filter (fun p => p.1)).map (fun p => p.2)

private def nl : String := "\n"

/-- One X-check measurement block: ancilla `anc` in |+⟩, `CX anc→s` for each
    support qubit `s`, measure ancilla in X. -/
def xCheckBlock (anc : Nat) (support : List Nat) : String :=
  "RX " ++ toString anc ++ nl
    ++ String.join (support.map (fun s => "CX " ++ toString anc ++ " " ++ toString s ++ nl))
    ++ "MX " ++ toString anc ++ nl

/-- One Z-check measurement block: ancilla `anc` in |0⟩, `CX s→anc` for each
    support qubit `s`, measure ancilla in Z. -/
def zCheckBlock (anc : Nat) (support : List Nat) : String :=
  "R " ++ toString anc ++ nl
    ++ String.join (support.map (fun s => "CX " ++ toString s ++ " " ++ toString anc ++ nl))
    ++ "M " ++ toString anc ++ nl

/-- Emit the merged-code stabilizer-measurement circuit of a surgery gadget as a
    Stim program.  Data + surgery-ancilla qubits are `0..merged_n−1`; the
    syndrome-measurement ancillas are `merged_n + i`.  X-checks are emitted first
    (records `0..|hx|−1`), then Z-checks. -/
def surgeryToStim (g : SurgeryGadget) : String :=
  let mn := g.merged_n
  let hx := g.merged_hx
  let hz := g.merged_hz
  let xBlocks := hx.zipIdx.map (fun p => xCheckBlock (mn + p.2) (rowSupport p.1))
  let zBlocks := hz.zipIdx.map (fun p => zCheckBlock (mn + hx.length + p.2) (rowSupport p.1))
  String.join xBlocks ++ String.join zBlocks

end FormalRV.LatticeSurgery.StimEmit
