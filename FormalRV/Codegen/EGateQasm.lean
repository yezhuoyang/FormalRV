/-
  FormalRV.Codegen.EGateQasm — emit OpenQASM 2.0 from the measurement-augmented `EGate` IR
  (base gates + `mz` measurement-reset), reusing the proven `Gate` emitter for base gates.

  `mz q` (measurement-based uncomputation's value-effect: measure and reset to |0⟩) emits the
  QASM `measure q -> c; reset q;` pair, whose computational-basis effect is `update f q false`
  — exactly `EGate.applyNat (mz q)`.  Base gates emit via `GateQasm.emitOps`.

  Faithfulness is PROVEN (`emitEOps_applyNat`): the emitted op-list's computational-basis action
  equals `EGate.applyNat`.  Rendering (ops → text) is then a syntactic serialization, and the text
  emitter `emitEGate`/`toQasmE` shares those exact ops.
-/
import FormalRV.Codegen.GateQasm
import FormalRV.Shor.MeasUncompute

namespace FormalRV.Codegen

open FormalRV.Framework
open FormalRV.Shor.MeasUncompute

/-- One emitted QASM op for the `EGate` IR: a native `QasmOp`, or a measure-and-reset. -/
inductive EQasmOp where
  | op   : QasmOp → EQasmOp
  | meas : Nat → EQasmOp
  deriving Repr

/-- Computational-basis action.  `meas q` (measure + reset to |0⟩) sets bit `q` to `false`. -/
def EQasmOp.applyNat : EQasmOp → (Nat → Bool) → (Nat → Bool)
  | EQasmOp.op o,   f => o.applyNat f
  | EQasmOp.meas q, f => Function.update f q false

/-- Run an emitted EGate program. -/
def applyEProg (prog : List EQasmOp) (f : Nat → Bool) : Nat → Bool :=
  prog.foldl (fun f o => o.applyNat f) f

theorem applyEProg_append (p q : List EQasmOp) (f : Nat → Bool) :
    applyEProg (p ++ q) f = applyEProg q (applyEProg p f) := by
  simp [applyEProg, List.foldl_append]

/-- A `QasmOp`-only program embeds into an `EQasmOp` program with the same action. -/
theorem applyEProg_map_op (l : List QasmOp) (f : Nat → Bool) :
    applyEProg (l.map EQasmOp.op) f = applyProg l f := by
  simp only [applyEProg, applyProg, List.foldl_map, EQasmOp.applyNat]

/-- **Structured EGate emitter.** -/
def emitEOps : EGate → List EQasmOp
  | EGate.base g  => (emitOps g).map EQasmOp.op
  | EGate.mz q    => [EQasmOp.meas q]
  | EGate.seq a b => emitEOps a ++ emitEOps b

/-- **★ EGate emitter faithfulness ★** — the emitted program's computational-basis action
    equals `EGate.applyNat`.  (Base gates via `emitOps_applyNat`; `mz` via measure-reset.) -/
theorem emitEOps_applyNat (g : EGate) (f : Nat → Bool) :
    applyEProg (emitEOps g) f = EGate.applyNat g f := by
  induction g generalizing f with
  | base g => simp [emitEOps, applyEProg_map_op, emitOps_applyNat, EGate.applyNat]
  | mz q => simp [emitEOps, applyEProg, EQasmOp.applyNat, EGate.applyNat]
  | seq a b iha ihb =>
      simp [emitEOps, applyEProg_append, iha, ihb, EGate.applyNat]

/-- Render one emitted op to QASM source line(s). -/
def EQasmOp.render : EQasmOp → List String
  | EQasmOp.op o   => [o.render]
  | EQasmOp.meas q => ["measure " ++ qref q ++ " -> c[" ++ toString q ++ "];",
                       "reset " ++ qref q ++ ";"]

/-- Emit an `EGate` as a list of QASM source lines (rendering the proven-faithful op-list). -/
def emitEGate (g : EGate) : List String :=
  ((emitEOps g).map EQasmOp.render).flatten

/-- Qubit width touched by an `EGate`. -/
def egateWidth : EGate → Nat
  | EGate.base g  => widthOf g
  | EGate.mz q    => q + 1
  | EGate.seq a b => max (egateWidth a) (egateWidth b)

/-- Full OpenQASM 2.0 program for an `EGate` (with a classical register for measurements). -/
def toQasmE (g : EGate) : String :=
  let n := egateWidth g
  String.intercalate "\n"
    ([ "OPENQASM 2.0;", "include \"qelib1.inc\";",
       "qreg q[" ++ toString n ++ "];", "creg c[" ++ toString n ++ "];" ] ++ emitEGate g)

/-- Number of emitted `ccx` op-lines — i.e. the emitted Toffoli count,
    cross-checking `EGate.toffoli` at the text level. -/
def emittedCcxCount (g : EGate) : Nat :=
  (emitEGate g).foldl (fun n s => if "ccx".isPrefixOf s then n + 1 else n) 0

end FormalRV.Codegen
