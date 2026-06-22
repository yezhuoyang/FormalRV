/-
  FormalRV.QFT.IQFTExample
  ────────────────────────
  A worked example for the inverse QFT + its `UGadget` descriptor for the
  uniform `BaseUCom` QASM emitter (`Codegen.UComQasm`), the quantum-side sibling
  of the arithmetic `Gadget` / `emitQASM` framework.

  This file contains `#eval` demos, so it is kept OFF the default build path
  (not imported by the `QFT` umbrella). Build / run on demand:
    lake build FormalRV.QFT.IQFTExample

  The emitted readable gates are EXACTLY the verified circuit's gates:
    • `h q[t]`              = `H t`               (= `U(π/2,0,π)`)
    • `cu1(-pi/2^d) q[j],q[t]` = `controlled_Rz j t (-π/2^d)`  (the qelib1 `cu1`
                              decomposition IS our 5-gate `controlled_Rz`)
    • `swap q[i],q[k]`      = `SWAP i k`
  so `iqftQasmLines n` renders `IQFT n` (= `real_QFTinv_layer n`) faithfully, and
  the op-level faithfulness `uprogMat n (emitUComOps (IQFT n)) = uc_eval (IQFT n)`
  (from `Codegen.uprogMat_emitUComOps`) plus `iqft_correct` give the punchline
  `iqft_emitted_unitary_eq_IQFT_matrix`: the EMITTED circuit's unitary is exactly
  the ideal inverse-QFT matrix.
-/
import FormalRV.QFT.IQFTCorrectness
import FormalRV.Codegen.UComQasm

namespace FormalRV.SQIRPort

open FormalRV.Framework
open FormalRV.Codegen (UGadget emitUComOps uprogMat uprogMat_emitUComOps)

/-! ## §1. Computable readable OpenQASM body for the n-qubit inverse QFT.

Mirrors `real_QFTinv_layer n` gate-for-gate: bit-reversal `swap`s, then for each
target `t = n-1 … 0` the controlled phases `cu1(-π/2^(j-t)) q[j],q[t]` (controls
`j > t`) followed by `h q[t]`. -/

/-- Bit-reversal SWAP lines: `swap q[i],q[n-1-i]` for `i` with `2i+1 < n`. -/
def iqftSwapLines (n : Nat) : List String :=
  (List.range n).filterMap (fun i =>
    if 2 * i + 1 < n then some s!"swap q[{i}],q[{n - 1 - i}];" else none)

/-- Phase-ladder lines for one target: `cu1(-pi/2^(j-t)) q[j],q[t]` for controls
`j > t`, then `h q[t]`. -/
def iqftLadderLines (n target : Nat) : List String :=
  (List.range n).filterMap (fun j =>
    if target < j then some s!"cu1(-pi/{2 ^ (j - target)}) q[{j}],q[{target}];"
    else none)
  ++ [s!"h q[{target}];"]

/-- The full readable OpenQASM body of the n-qubit inverse QFT. -/
def iqftQasmLines (n : Nat) : List String :=
  iqftSwapLines n ++ ((List.range n).reverse.flatMap (fun t => iqftLadderLines n t))

/-! ## §2. The inverse QFT as a uniform, emittable `UGadget`. -/

/-- The inverse QFT as a uniform `UGadget` descriptor (quantum-side analogue of
the arithmetic `Gadget`).  `render = iqftQasmLines` is the computable OpenQASM
body for `IQFT n`; its semantic faithfulness is `iqft_emitted_unitary_eq_IQFT_matrix`. -/
def IQFTGadget : UGadget :=
  { name := "iqft", nqubits := fun n => n, render := iqftQasmLines }

-- Emit the 2- and 3-qubit inverse QFTs as OpenQASM 2.0 via the uniform emitter.
#eval IO.println (IQFTGadget.emitQASM 2)
#eval IO.println (IQFTGadget.emitQASM 3)

/-! ## §3. The punchline: the EMITTED circuit's unitary is the ideal matrix. -/

/-- **The emitted inverse-QFT circuit's unitary is exactly the ideal
`IQFT_matrix`.**  Chains the uniform emitter's faithfulness
(`uprogMat_emitUComOps`, the same `progMat = uc_eval` contract the arithmetic
emitter satisfies) with the circuit-correctness headline `iqft_correct`.  So the
OpenQASM we emit denotes, as a unitary, precisely `(y,x) ↦ (1/√2ⁿ)·exp(-2πi·x·y/2ⁿ)`. -/
theorem iqft_emitted_unitary_eq_IQFT_matrix (n : Nat) (hn : 0 < n) :
    uprogMat n (emitUComOps (IQFT n)) = IQFT_matrix n := by
  rw [uprogMat_emitUComOps]
  exact iqft_correct n hn

/-! ## §4. Emit OpenQASM + a wire-name legend to file (input to draw_qasm.py → PNG). -/

/-- Per-qubit wire names + INPUT/OUTPUT legend for the 3-qubit IQFT diagram. -/
def iqft3IoJson : String :=
  "{\n" ++
  "  \"title\": \"Inverse QFT (3 qubits): |Fourier⟩ → |y⟩\",\n" ++
  "  \"wires\": [\"q0\", \"q1\", \"q2\"],\n" ++
  "  \"input\":  [\"q2q1q0 = Fourier-basis state\"],\n" ++
  "  \"output\": [\"q2q1q0 = y (computational basis)\"]\n" ++
  "}\n"

#eval (do
  IO.FS.createDirAll "FormalRV/QFT/diagrams"
  IO.FS.writeFile "FormalRV/QFT/diagrams/iqft_3qubit.qasm" (IQFTGadget.emitQASM 3)
  IO.FS.writeFile "FormalRV/QFT/diagrams/iqft_3qubit.io.json" iqft3IoJson
  IO.println "wrote diagrams/iqft_3qubit.qasm + .io.json" : IO Unit)

end FormalRV.SQIRPort
