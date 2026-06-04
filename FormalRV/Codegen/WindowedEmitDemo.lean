/-
  FormalRV.Codegen.WindowedEmitDemo — END-TO-END demonstration (logical level):

    1. COUNT  — evaluate the structurally-proven resource counts of the windowed
                multiplier and the babbush unary-iteration QROM, and the RSA-2048
                cost-model Toffoli total, confirming they match Gidney–Ekerå.
    2. EMIT   — write runnable OpenQASM 2.0 for the full windowed multiplier
                (`Gate` IR) and the babbush QROM (`EGate` IR, with measurement-uncompute).

  Run:  lake env lean FormalRV/Codegen/WindowedEmitDemo.lean
  (writes C:/tmp/qasm_demo/{windowed_mul_w2,babbush_qrom_w2}.qasm and prints the QROM).

  SEMANTICS are verified separately by `native_decide` in `FormalRV.Shor.WindowedCircuitExec`
  (the multiplier computes a·y) and `FormalRV.Shor.MeasUncomputeExec` (the QROM reads T[a]);
  the emitted QASM is additionally checked in Qiskit by `verify_emitted_qrom.py`.
  Counts are PROVEN by `windowedMulCircuit_toffoli`, `width_windowedMulCircuit`,
  `toffoli_unaryQROM`, `toffoli_babbushLookupAdd`, `toffoliCount_rsa2048`; the emitter is
  PROVEN faithful by `GateQasm.emitOps_applyNat` and `EGateQasm.emitEOps_applyNat`.
-/
import FormalRV.Codegen.EGateQasm
import FormalRV.Shor.WindowedCostModel
import FormalRV.Shor.WindowedWidth
import FormalRV.Shor.WindowedComposed
import FormalRV.Shor.WindowedComposedCost

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Codegen FormalRV.Shor.WindowedCircuit FormalRV.Shor.MeasUncompute
open FormalRV.Shor.WindowedComposed

/-! ### 1. COUNTS (each `#eval` matches its proven closed form) -/

#eval s!"windowed-mult Toffoli (w=2,bits=4,numWin=2) = {toffoliCount (windowedMulCircuit 2 4 3 2)}  [proven = numWin*(4w*2^w+2bits) = 2*(32+8) = 80]"
#eval s!"windowed-mult qubit width                  = {width (windowedMulCircuit 2 4 3 2)}  [proven = 2w+2bits+numWin*w+2 = 18]"
#eval s!"babbush QROM Toffoli (w=2)                 = {EGate.toffoli (unaryQROM 3 (fun v => v) 1 3 5 2 0 0)}  [proven = 2^w-1 = 3]"
#eval s!"  emitted ccx lines (text cross-check)      = {emittedCcxCount (unaryQROM 3 (fun v => v) 1 3 5 2 0 0)}"
#eval s!"babbushLookupAdd Toffoli (w=2,bits=4)      = {EGate.toffoli (babbushLookupAdd 2 3 (fun v => v) 4 1 3 5 8)}  [proven = (2^w-1)+2bits = 11 = Gidney 2^(c_mul+c_exp)]"
#eval s!"RSA-2048 cost-model Toffoli                = {(FormalRV.Shor.WindowedCostModel.toffoliCount 2048 3072 11 : Rat)}  [proven = 2,622,824,448 <= paper 0.3 n^3 + 0.0005 n^3 lg n]"

/-! ### 2. EMIT runnable OpenQASM 2.0 -/

#eval show IO Unit from do
  let dir := "C:/tmp/qasm_demo/"
  IO.FS.createDirAll dir
  let mul  := toQasm (windowedMulCircuit 2 4 3 2) false 0
  let qrom := toQasmE (unaryQROM 3 (fun v => v) 1 3 5 2 0 0)
  IO.FS.writeFile (dir ++ "windowed_mul_w2.qasm") mul
  IO.FS.writeFile (dir ++ "babbush_qrom_w2.qasm") qrom
  IO.println s!"[emitted] {dir}windowed_mul_w2.qasm  ({(mul.splitOn "\n").length} lines)"
  IO.println s!"[emitted] {dir}babbush_qrom_w2.qasm"
  IO.println "\n=== babbush_qrom_w2.qasm (unary-iteration QROM with measurement-uncompute) ===\n"
  IO.println qrom

/-! ### 3. COMPOSED full modular exponentiation (built from babbushLookupAdd) -/

-- A small composed mod-exp: numMults=2 multiplications × 2 multiply-adds × numWin=2 windows,
-- window w=2, adder width bits=4.  Structural Toffoli = numMults·2·numWin·((2^w−1)+2·bits).
#eval s!"composed modExp Toffoli (numMults=2,numWin=2,w=2,bits=4) = {EGate.toffoli (modExp 2 3 4 (fun v => v) 2 2)}  [proven = 2·2·2·((2^2-1)+2·4) = 8·11 = 88]"

#eval show IO Unit from do
  let dir := "C:/tmp/qasm_demo/"
  IO.FS.createDirAll dir
  let me := toQasmE (modExp 2 3 4 (fun v => v) 2 2)
  IO.FS.writeFile (dir ++ "composed_modexp.qasm") me
  IO.println s!"\n[emitted] {dir}composed_modexp.qasm  ({(me.splitOn "\n").length} lines, full mod-exp from babbushLookupAdd)"

/-! ### 4. RSA-2048 HEAD-TO-HEAD: composed structural count vs paper's reported count -/

#eval "── RSA-2048 (n=2048, n_e=3072, g_exp=g_mul=5, g_sep=1024, g_pad=43, w=10) ──"
#eval s!"per lookup-addition : structural (babbushLookupAdd) = {(FormalRV.Shor.WindowedComposedCost.structPerLookup 2048 : Rat)}   paper = {(FormalRV.Shor.WindowedCostModel.perLookupToffoli 2048 11 : Rat)}   gap = 87 (=1 rounding + 86 runway-fold)"
#eval s!"FULL mod-exp total  : structural = {(FormalRV.Shor.WindowedComposedCost.structToffoliCount 2048 3072 : Rat)}   paper = {(FormalRV.Shor.WindowedCostModel.toffoliCount 2048 3072 11 : Rat)}"
#eval s!"total gap           : {(FormalRV.Shor.WindowedCostModel.toffoliCount 2048 3072 11 - FormalRV.Shor.WindowedComposedCost.structToffoliCount 2048 3072 : Rat)}  (1.67%, fully attributed; all PROVEN in WindowedComposedCost)"
