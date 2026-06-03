/-
  FormalRV.Core.GateQASM — emit a `Gate` IR circuit as OpenQASM, and tie the per-gate-type
  counts to `tcount`.  This lets an external tool (Qiskit) load the EMITTED circuit, count
  its gates, and confirm the count equals the Lean-proved number — empirical justification
  that the counting is correct (no Lean-only bookkeeping trick).

  Proved consistency: `tcount g = 7 · numCCX g` (each Toffoli = 7 T) and
  `gcount g = numX g + numCX g + numCCX g` (total = sum of per-type).  So once Qiskit
  confirms `#ccx` in the emitted QASM equals `numCCX g`, it has confirmed `tcount/7`.
-/
import FormalRV.Core.Gate

namespace FormalRV.Framework.Gate

/-! ## Per-gate-type counts. -/

def numCCX : Gate → Nat
  | .CCX _ _ _ => 1
  | .seq a b => numCCX a + numCCX b
  | _ => 0

def numCX : Gate → Nat
  | .CX _ _ => 1
  | .seq a b => numCX a + numCX b
  | _ => 0

def numX : Gate → Nat
  | .X _ => 1
  | .seq a b => numX a + numX b
  | _ => 0

/-- `tcount = 7 · (#Toffoli)`: ties the QASM `ccx` count to the proved T-count. -/
theorem tcount_eq_seven_numCCX (g : Gate) : tcount g = 7 * numCCX g := by
  induction g with
  | I => rfl
  | X q => rfl
  | CX a b => rfl
  | CCX a b c => rfl
  | seq a b ih1 ih2 => simp only [tcount, numCCX, ih1, ih2]; omega

/-- `gcount = #X + #CX + #CCX`: the total gate count is the sum of the per-type counts. -/
theorem gcount_eq_sum (g : Gate) : gcount g = numX g + numCX g + numCCX g := by
  induction g with
  | I => rfl
  | X q => rfl
  | CX a b => rfl
  | CCX a b c => rfl
  | seq a b ih1 ih2 => simp only [gcount, numX, numCX, numCCX, ih1, ih2]; omega

/-! ## QASM emission. -/

/-- Highest qubit index the circuit touches. -/
def maxQubit : Gate → Nat
  | .I => 0
  | .X q => q
  | .CX a b => max a b
  | .CCX a b c => max a (max b c)
  | .seq x y => max (maxQubit x) (maxQubit y)

def toQASMBody : Gate → List String
  | .I => []
  | .X q => [s!"x q[{q}];"]
  | .CX a b => [s!"cx q[{a}], q[{b}];"]
  | .CCX a b c => [s!"ccx q[{a}], q[{b}], q[{c}];"]
  | .seq x y => toQASMBody x ++ toQASMBody y

/-- Emit the circuit as an OpenQASM 2.0 program (Qiskit-loadable; `ccx` is native). -/
def toQASM (g : Gate) : String :=
  let n := maxQubit g + 1
  "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[" ++ toString n ++ "];\n"
    ++ String.intercalate "\n" (toQASMBody g) ++ "\n"

end FormalRV.Framework.Gate
