/-
  FormalRV.PPM.PPMToQASM — emit OpenQASM 3 from the PPM (Pauli-product
  measurement) gadget IR.

  The executable backend of the verified compiler: the same measurement-based
  gadgets we prove correct (T teleportation in `TGadgetTeleport`, CCZ
  teleportation in `CCZGadgetTeleport`) are serialised to runnable OpenQASM 3,
  so the proof (`⟦·⟧`) and an independent numerical Qiskit simulation can be
  cross-checked (see `PyCircuits/ppm_qasm_verification.py`).

  Scope: the PPM-LEVEL logical circuit — magic-state prep, the entangling
  CNOTs, the Z-measurements, and the classically-controlled Clifford
  corrections (S for T, CZ for CCZ).  The physical surface-code / lattice-
  surgery layer is below this.  Pure syntax (no proof obligations).
-/

namespace FormalRV.PPM.PPMToQASM

/-- A minimal PPM-level QASM instruction set: Clifford+T gates, CNOT/CZ/CCZ,
    Z-measurement, and a classically-controlled (feed-forward) instruction. -/
inductive QasmOp where
  | opH    (q : Nat)
  | opT    (q : Nat)
  | opS    (q : Nat)
  | opX    (q : Nat)
  | opZ    (q : Nat)
  | opCX   (c t : Nat)
  | opCZ   (a b : Nat)
  | opCCZ  (a b c : Nat)
  | opMeas (q : Nat) (creg : Nat)
  | opIf   (creg : Nat) (op : QasmOp)          -- single-bit feed-forward
  | opIf2  (cr1 cr2 : Nat) (op : QasmOp)        -- AND-of-two-bits feed-forward
  deriving Repr

/-- One instruction → one OpenQASM 3 line. -/
def QasmOp.toLine : QasmOp → String
  | .opH q       => s!"h q[{q}];"
  | .opT q       => s!"t q[{q}];"
  | .opS q       => s!"s q[{q}];"
  | .opX q       => s!"x q[{q}];"
  | .opZ q       => s!"z q[{q}];"
  | .opCX c t    => s!"cx q[{c}], q[{t}];"
  | .opCZ a b    => s!"cz q[{a}], q[{b}];"
  -- CCZ is not in stdgates.inc; emit it as H·CCX·H (ccx, h ARE standard).
  | .opCCZ a b c => s!"h q[{c}]; ccx q[{a}], q[{b}], q[{c}]; h q[{c}];"
  | .opMeas q cr => s!"c[{cr}] = measure q[{q}];"
  | .opIf cr op  => s!"if (c[{cr}] == true) " ++ QasmOp.toLine op
  -- AND-of-two via nested if (OpenQASM 3 has no `&&` in qiskit's importer).
  | .opIf2 cr1 cr2 op =>
      s!"if (c[{cr1}] == true) if (c[{cr2}] == true) " ++ QasmOp.toLine op

/-- Emit a full OpenQASM 3 program: header + registers + the instruction list. -/
def toQASM (nq ncr : Nat) (ops : List QasmOp) : String :=
  "OPENQASM 3.0;\ninclude \"stdgates.inc\";\n"
    ++ s!"qubit[{nq}] q;\nbit[{ncr}] c;\n"
    ++ String.intercalate "\n" (ops.map QasmOp.toLine)
    ++ "\n"

/-! ## The T gate-teleportation gadget (matches `TGadgetTeleport`).

    q[0] = data, q[1] = magic ancilla.  Prepare `|T⟩ = T·H|0⟩` on the ancilla,
    CNOT (data→ancilla), Z-measure the ancilla, and apply the `S` correction to
    the data iff the outcome is 1 — exactly `t_gadget_with_feedback`. -/
def tGadgetOps : List QasmOp :=
  [ .opH 1, .opT 1,         -- prepare |T⟩ on the ancilla
    .opCX 0 1,              -- entangle: data controls ancilla
    .opMeas 1 0,            -- Z-measure the ancilla
    .opIf 0 (.opS 0) ]      -- classically-controlled S correction on the data

def tGadgetQASM : String := toQASM 2 1 tGadgetOps

/-! ## The CCZ state-teleportation gadget (matches `CCZGadgetTeleport`).

    q[0..2] = data, q[3..5] = magic ancillas.  Prepare `|CCZ⟩ = CCZ·H³|000⟩`,
    the transversal CNOT chain (data k → ancilla k), Z-measure the three
    ancillas, and the standard CZ feed-forward corrections (ancilla i = 1 ⇒ CZ
    on the other two data qubits). -/
def cczGadgetOps : List QasmOp :=
  [ .opH 3, .opH 4, .opH 5, .opCCZ 3 4 5,   -- prepare |CCZ⟩ on the ancillas
    .opCX 0 3, .opCX 1 4, .opCX 2 5,        -- transversal CNOT chain
    .opMeas 3 0, .opMeas 4 1, .opMeas 5 2,  -- Z-measure the three ancillas
    -- CCZ teleportation byproduct corrections (derived from the phase
    -- (-1)^{(m⊕x)₁(m⊕x)₂(m⊕x)₃}): CZ on the complementary pair per single
    -- outcome, plus Z on the third qubit per AND-of-two outcomes.
    .opIf 0 (.opCZ 1 2),                    -- m₁ ⇒ CZ₂₃
    .opIf 1 (.opCZ 0 2),                    -- m₂ ⇒ CZ₁₃
    .opIf 2 (.opCZ 0 1),                    -- m₃ ⇒ CZ₁₂
    .opIf2 0 1 (.opZ 2),                    -- m₁∧m₂ ⇒ Z₃
    .opIf2 0 2 (.opZ 1),                    -- m₁∧m₃ ⇒ Z₂
    .opIf2 1 2 (.opZ 0) ]                   -- m₂∧m₃ ⇒ Z₁

def cczGadgetQASM : String := toQASM 6 3 cczGadgetOps

-- Emitted programs (inspect via #eval, or `lake env lean --run`):
#eval IO.println tGadgetQASM
#eval IO.println cczGadgetQASM

end FormalRV.PPM.PPMToQASM
