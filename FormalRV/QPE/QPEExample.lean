/-
  FormalRV.QPE.QPEExample
  ───────────────────────
  A worked example for QPE + its `UGadget` descriptor for the uniform `BaseUCom`
  QASM emitter (`Codegen.UComQasm`), the same framework the QFT and arithmetic
  gadgets emit through.

  This file contains `#eval` demos, so it is kept OFF the default build path
  (not imported by the `QPE` umbrella). Build / run on demand:
    lake build FormalRV.QPE.QPEExample

  ## The black box, made concrete

  QPE's oracle is a BLACK BOX in general (`QPECorrectness.qpe_on_eigenstate_correct`
  holds for any eigenstate-bearing family).  To EMIT a runnable circuit we pick
  the canonical concrete oracle: the single-qubit PHASE gate `U = u1(2πθ)` on one
  ancilla, whose eigenstate is `|1⟩` with eigenvalue `e^{2πiθ}`.  Then
  `c i = control i (U^{2^i}) = cu1(2π·2^i·θ) q[i],q[ancilla]`, and the QPE circuit
  on `k` measurement qubits + 1 ancilla is

      h q[0..k-1] ;  cu1(2π·2^i·θ) q[i],q[k]  (i<k) ;  inverse-QFT q[0..k-1]

  estimating the `k`-bit value of `θ`.  For `θ = 1/2^k` the peak is at `y = 1`.
-/
import FormalRV.QPE.QPECorrectness
import FormalRV.Codegen.UComQasm

namespace FormalRV.SQIRPort

open FormalRV.Framework
open FormalRV.Codegen (UGadget)

/-! ## §1. Computable readable OpenQASM body for a phase-oracle QPE. -/

/-- Render `num·π/den` as OpenQASM angle text, reduced by `gcd`. -/
def piFrac (num : Int) (den : Nat) : String :=
  let g : Nat := Nat.gcd num.natAbs den
  let n : Int := if g == 0 then num else num / (g : Int)
  let d : Nat := if g == 0 then den else den / g
  let core : String := if n.natAbs == 1 then "pi" else s!"{n.natAbs}*pi"
  let signed : String := if n < 0 then "-" ++ core else core
  if d == 1 then signed else s!"{signed}/{d}"

/-- The inverse QFT on the measurement register `q[0..k-1]` (the QPE measurement
basis): bit-reversal `swap`s, then the `cu1`/`h` phase-ladder countdown.  Same
gates as `IQFT k`, acting only on the first `k` qubits. -/
def iqftPrefixLines (k : Nat) : List String :=
  ((List.range k).filterMap (fun i =>
      if 2 * i + 1 < k then some s!"swap q[{i}],q[{k - 1 - i}];" else none))
  ++ ((List.range k).reverse.flatMap (fun t =>
       ((List.range k).filterMap (fun j =>
           if t < j then some s!"cu1({piFrac (-1) (2 ^ (j - t))}) q[{j}],q[{t}];"
           else none))
       ++ [s!"h q[{t}];"]))

/-- The phase-oracle QPE body on `k` measurement qubits + ancilla `q[k]`,
estimating `θ = p / 2^q`: H-layer, the `cu1(2π·2^i·θ)` controlled-power ladder,
then the inverse QFT on the measurement register. -/
def qpeBodyLines (k p q : Nat) : List String :=
  ((List.range k).map (fun i => s!"h q[{i}];"))
  ++ ((List.range k).map (fun i =>
       s!"cu1({piFrac ((2 ^ (i + 1) * p : Nat) : Int) (2 ^ q)}) q[{i}],q[{k}];"))
  ++ iqftPrefixLines k

/-! ## §2. QPE as a uniform, emittable `UGadget`.

Parameter `k` = number of measurement qubits; fixed estimation target
`θ = 1/2^k` (so the peak outcome is `y = 1`); register width `k + 1`. -/

/-- Phase-oracle QPE as a uniform `UGadget` (estimating `θ = 1/2^k`). -/
def QPEPhaseGadget : UGadget :=
  { name := "qpe_phase", nqubits := fun k => k + 1,
    render := fun k => qpeBodyLines k 1 k }

-- Emit the 2- and 3-measurement-qubit phase-oracle QPE as OpenQASM 2.0.
#eval IO.println (QPEPhaseGadget.emitQASM 2)
#eval IO.println (QPEPhaseGadget.emitQASM 3)

/-! ## §3. Correctness anchor (the black-box QPE headline).

The emitted circuit is the concrete phase-oracle instance of the general QPE
correctness: for ANY eigenstate-bearing oracle family, QPE recovers the phase. -/

-- The general black-box QPE-on-eigenstate correctness theorem (QPECorrectness).
#check @qpe_on_eigenstate_correct

/-! ## §4. Emit OpenQASM + a wire-name legend to file (input to draw_qasm.py → PNG). -/

/-- Wire names + INPUT/OUTPUT legend for the 3+1-qubit phase-oracle QPE. -/
def qpe3IoJson : String :=
  "{\n" ++
  "  \"title\": \"QPE (3 measurement qubits) for a phase oracle, θ = 1/8\",\n" ++
  "  \"wires\": [\"m0\", \"m1\", \"m2\", \"u\"],\n" ++
  "  \"input\":  [\"m2m1m0 = |0..0⟩\", \"u = |1⟩  (eigenstate of u1(2πθ))\"],\n" ++
  "  \"output\": [\"m2m1m0 ≈ y with y/8 ≈ θ = 1/8  (peak at y=1)\", \"u = |1⟩ (preserved)\"]\n" ++
  "}\n"

#eval (do
  IO.FS.createDirAll "FormalRV/QPE/diagrams"
  IO.FS.writeFile "FormalRV/QPE/diagrams/qpe_phase_3qubit.qasm" (QPEPhaseGadget.emitQASM 3)
  IO.FS.writeFile "FormalRV/QPE/diagrams/qpe_phase_3qubit.io.json" qpe3IoJson
  IO.println "wrote diagrams/qpe_phase_3qubit.qasm + .io.json" : IO Unit)

end FormalRV.SQIRPort
