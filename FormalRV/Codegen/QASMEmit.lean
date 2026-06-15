/-
  FormalRV.Codegen.QASMEmit — a UNIFORM OpenQASM emission framework.

  A `Gadget` bundles a name with a width-parametric `Gate`-IR circuit.
  `emitQASM` turns ANY gadget, at ANY width `n`, into an OpenQASM 2.0 program
  via the faithful `toQasm` emitter. Every arithmetic gadget exposes one
  `Gadget` descriptor and emits uniformly:

      #eval IO.println (emitQASM CuccaroAdder 3)

  The same interface is intended for every `Gate`-IR circuit in the project
  (arithmetic gadgets, and QFT/QPE once exposed as `Gate`), so emission code
  is written once, here, not per gadget.
-/
import FormalRV.Codegen.GateQasm

namespace FormalRV.Codegen

open FormalRV.Framework

/-- A named, width-parametric quantum circuit gadget that can be emitted to
OpenQASM. `circuit n` is the gadget at register width `n`, placed at qubit
offset 0. Every arithmetic/logic gadget should expose one of these. -/
structure Gadget where
  /-- A short identifier used for file/labeling. -/
  name : String
  /-- The concrete `Gate`-IR circuit at register width `n`. -/
  circuit : Nat → Gate

namespace Gadget

/-- The emitted OpenQASM 2.0 program for gadget `g` at width `n`
(Clifford+T basis). -/
def toQASM (g : Gadget) (n : Nat) : String :=
  FormalRV.Codegen.toQasm (g.circuit n)

/-- The emitted program in the native (CX/CCX/X) basis instead of Clifford+T. -/
def toQASMNative (g : Gadget) (n : Nat) : String :=
  FormalRV.Codegen.toQasm (g.circuit n) (cliffT := false)

/-! ### Exact resource readouts.

These are the SAME structural counters used in every gadget's resource
theorem — computed directly from `g.circuit n`, so the count is **exact by
construction** (it accumulates from the atomic gates: `tcount (CCX) = 7`,
`tcount (seq a b) = tcount a + tcount b`). For a fixed `n` they reduce to a
concrete integer; the gadget's `…Resource.lean` proves the closed form. -/

/-- Exact T-count of the gadget at register width `n`. -/
def tcount (g : Gadget) (n : Nat) : Nat := FormalRV.Framework.Gate.tcount (g.circuit n)

/-- Exact total gate count of the gadget at register width `n`. -/
def gateCount (g : Gadget) (n : Nat) : Nat := FormalRV.Framework.Gate.gcount (g.circuit n)

/-- A human-readable exact resource line. -/
def resourceReport (g : Gadget) (n : Nat) : String :=
  s!"{g.name} (n={n}): gates={g.gateCount n}, T={g.tcount n}"

end Gadget

/-- **Uniform QASM emitter.** `emitQASM g n` is the OpenQASM 2.0 program for
gadget `g` at register width `n`. Works for every `Gadget` — e.g.
`emitQASM CuccaroAdder 3`. -/
def emitQASM (g : Gadget) (n : Nat) : String := g.toQASM n

end FormalRV.Codegen
