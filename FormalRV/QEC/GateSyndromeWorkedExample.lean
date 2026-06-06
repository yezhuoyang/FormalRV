/-
  FormalRV.QEC.GateSyndrome — GATE-LEVEL WORKED INSTANCE.

  The physical syndrome-extraction circuit of the [[4,2,2]] code —
  explicit ancilla+CNOT+measure gates — measures exactly the code's
  stabilizers {X₀X₁X₂X₃, Z₀Z₁Z₂Z₃} (each check via CliffordConj's
  `measGadgetConj`/`xMeasGadgetConj`, the set valid by
  `CSSCode.syndrome_circuit_implements_code`), and its resource count
  (physical qubits 6, CNOTs 8, cycles 2) follows from the per-check
  costs.  This is the bottom rung of the physical→PPM→logical→Shor
  stack, made concrete and resource-counted; the full-Hilbert
  faithfulness of the Heisenberg picture is the cited Gottesman–Knill
  bridge.

  No Mathlib.  Pure Bool / Nat / List + decide.
-/
import FormalRV.PPM.CliffordConj
import FormalRV.QEC.Instances

namespace FormalRV.QEC.GateSyndrome

open FormalRV.Framework.PauliSem FormalRV.Framework.CliffordConj FormalRV.QEC
open FormalRV.QEC.Instances FormalRV.Framework.LDPC FormalRV.Framework.PPMOp

/-! ## (2a) Gate-level measurement of each check (ancilla at index 4)

    The data register is qubits 0–3; the syndrome ancilla is qubit 4. -/

/-- The Z-check `ZZZZ` is measured by CNOT(0→4),CNOT(1→4),CNOT(2→4),
    CNOT(3→4); measure Z₄.  Heisenberg picture: Z₄ ↦ Z₀Z₁Z₂Z₃Z₄. -/
example : measGadgetConj [0, 1, 2, 3] 4
      ⟨Phase.plus, [Pauli.I, Pauli.I, Pauli.I, Pauli.I, Pauli.Z]⟩
    = ⟨Phase.plus, [Pauli.Z, Pauli.Z, Pauli.Z, Pauli.Z, Pauli.Z]⟩ := by decide

/-- The X-check `XXXX` is measured by CNOT(4→0),…,CNOT(4→3); measure X₄.
    Heisenberg picture: X₄ ↦ X₀X₁X₂X₃X₄. -/
example : xMeasGadgetConj [0, 1, 2, 3] 4
      ⟨Phase.plus, [Pauli.I, Pauli.I, Pauli.I, Pauli.I, Pauli.X]⟩
    = ⟨Phase.plus, [Pauli.X, Pauli.X, Pauli.X, Pauli.X, Pauli.X]⟩ := by decide

/-! ## (2b) The measured data operators ARE code422's stabilizers

    Dropping the ancilla position, the data-qubit operators measured by
    the two gadgets above are exactly `code422.toStabilizers`. -/

/-- `code422.toStabilizers = [xStab [T,T,T,T], zStab [T,T,T,T]]
    = [X₀X₁X₂X₃, Z₀Z₁Z₂Z₃]`. -/
example : code422.toStabilizers
    = [⟨Phase.plus, [Pauli.X, Pauli.X, Pauli.X, Pauli.X]⟩,
       ⟨Phase.plus, [Pauli.Z, Pauli.Z, Pauli.Z, Pauli.Z]⟩] := by decide

/-! ## (2c) The code is genuinely implemented (the group is valid) -/

/-- The lowered stabilizer group of `code422` is a valid (pairwise-
    commuting, well-sized) stabilizer code — the syndrome circuit
    implements it, since `code422` is CSS. -/
example : StabilizerState.valid code422.toStabilizers code422.n = true := by
  rw [CSSCode.syndrome_circuit_implements_code code422 (by decide)]; decide

/-- Named witness for the validity claim, for the axiom audit. -/
theorem code422_syndrome_circuit_valid :
    StabilizerState.valid code422.toStabilizers code422.n = true := by
  rw [CSSCode.syndrome_circuit_implements_code code422 (by decide)]; decide

/-! ## (2d) Resource count — the "resource count follows" deliverable -/

/-- Physical-layer resource tally of a gate-level syndrome circuit:
    data qubits, syndrome ancillae, CNOTs, and measurement cycles. -/
structure PhysResources where
  data_qubits    : Nat
  ancilla_qubits : Nat
  cnots          : Nat
  meas_cycles    : Nat
deriving Repr, DecidableEq

/-- Total physical qubits = data + ancilla. -/
def physQubits (r : PhysResources) : Nat := r.data_qubits + r.ancilla_qubits

/-- The weight of a check row = number of `true` (supported) entries. -/
def rowWeight (row : BoolVec) : Nat := (row.filter id).length

/-- Resource cost of the gate-level syndrome circuit of a CSS code: one
    ancilla per check, one CNOT per stabilizer-support entry
    (Σ row weights), one measurement cycle per check. -/
def syndromeCost (c : CSSCode) : PhysResources :=
  { data_qubits := c.n,
    ancilla_qubits := c.hx.length + c.hz.length,
    cnots := (c.hx.map rowWeight).sum + (c.hz.map rowWeight).sum,
    meas_cycles := c.hx.length + c.hz.length }

/-- code422: 4 data, 2 ancilla (1 per check), 8 CNOTs (4+4 = Σ weights),
    2 measurement cycles. -/
example : syndromeCost code422
    = { data_qubits := 4, ancilla_qubits := 2, cnots := 8, meas_cycles := 2 } := by decide

/-- The [[4,2,2]] syndrome circuit uses 6 physical qubits. -/
example : physQubits (syndromeCost code422) = 6 := by decide

end FormalRV.QEC.GateSyndrome
