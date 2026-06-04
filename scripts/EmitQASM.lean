/-
  Emit the ACTUAL verified Gate IR circuits as OpenQASM, and print the Lean-computed gate
  counts.  Run: `lake env lean --run scripts/EmitQASM.lean`.  A Qiskit script then loads
  each .qasm, counts gates, and confirms they equal these numbers — justifying the counting.
-/
import FormalRV.Core.GateQASM
import FormalRV.Arithmetic.SQIRModMult.Defs
import FormalRV.Shor.CliffordTControlledModExp

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.CliffordTControlledModExp

def emit (name : String) (g : FormalRV.Framework.Gate) : IO Unit := do
  IO.FS.writeFile s!"PyCircuits/qasm/{name}.qasm" (toQASM g)
  IO.println s!"{name}: qubits={maxQubit g + 1} numX={numX g} numCX={numCX g} numCCX={numCCX g} gcount={gcount g} tcount={tcount g}"

def main : IO Unit := do
  -- sanity: a bare Toffoli
  emit "toffoli" (Gate.CCX 0 1 2)
  -- the verified out-of-place modular multiplier (const_gate): tcount should be 56·bits²
  emit "modmult_const_2_15_7"  (sqir_modmult_const_gate 2 15 7)
  emit "modmult_const_3_21_5"  (sqir_modmult_const_gate 3 21 5)
  -- the ACTUAL verified Shor oracle term (in-place MCP gate): tcount should be 112·bits²
  --   (ainv of 7 mod 15 is 13, since 7·13 = 91 ≡ 1 mod 15)
  emit "modmult_MCP_2_15_7_13" (sqir_modmult_MCP_gate 2 15 7 13)
  -- FULLY Clifford+T controlled multipliers (control qubit 100, ancilla 101): magic should be
  --   numCX + 3·numCCX, and the QASM should contain ONLY x/cx/ccx (no rotations).
  emit "ctrl_const_2_15_7"     (ctrlGate 100 101 (sqir_modmult_const_gate 2 15 7))
  emit "ctrl_MCP_2_15_7_13"    (ctrlGate 100 101 (sqir_modmult_MCP_gate 2 15 7 13))
