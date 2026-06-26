/-
  FormalRV.Shor.MeasUncomputeExec — executable verification that the babbush2018
  unary-iteration QROM (`MeasUncompute.unaryQROM`) is a SEMANTICALLY CORRECT lookup.

  Runs the actual `EGate` circuit (`EGate.applyNat`) on a qubit-encoded address `a` and
  checks the decoded output equals `T[a]`, over ALL `w=2` addresses and two distinct tables.
  Together with `MeasUncompute.toffoli_unaryQROM` (the proven `2^w − 1` Toffoli count), this
  confirms the QROM-read is a real, emittable circuit — no black box.

  (`native_decide` ⇒ these carry `Lean.ofReduceBool`; standalone / on-demand, not in the
  routine aggregator.) -/
import FormalRV.Shor.MeasUncompute

set_option maxRecDepth 8000

namespace FormalRV.Shor.MeasUncomputeExec

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute

/-- Input: control qubit `0` set, address `a` encoded in qubits `1,2` (w = 2). -/
def inp (a : Nat) : Nat → Bool := fun p =>
  if p = 0 then true
  else if p = 1 then a.testBit 0
  else if p = 2 then a.testBit 1
  else false

/-- Decode the 3-bit output register (qubits 5,6,7). -/
def decOut (f : Nat → Bool) : Nat :=
  (List.range 3).foldl (fun acc j => acc + if f (5 + j) then 2 ^ j else 0) 0

/-- Run the QROM read for table `T` on address `a`. -/
def runQROM (T : Nat → Nat) (a : Nat) : Nat :=
  decOut (EGate.applyNat (unaryQROM 3 T 1 3 5 2 0 0) (inp a))

-- The unary-iteration QROM reads `T[a]` for every `w=2` address (table `T = id`):
example : runQROM (fun v => v) 0 = 0 := by decide
example : runQROM (fun v => v) 1 = 1 := by decide
example : runQROM (fun v => v) 2 = 2 := by decide
example : runQROM (fun v => v) 3 = 3 := by decide
-- and for a different table `T v = 5v mod 8`:
example : runQROM (fun v => 5 * v % 8) 3 = 15 % 8 := by decide

end FormalRV.Shor.MeasUncomputeExec
