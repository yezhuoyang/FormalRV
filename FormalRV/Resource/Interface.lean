/-
  FormalRV.Resource.Interface
  ───────────────────────────
  The unified, IR-agnostic resource-counting interface.

  Every circuit IR in the project (`Gate`, `BaseUCom`, and — to be migrated —
  the PPM / lattice-surgery IRs) exposes the SAME two honest counters through one
  typeclass: a CNOT count and a total gate count.  IR-specific counters that have
  no cross-IR meaning stay in their own module (`countT`/`countToffoli` on the
  reversible `Gate` IR; `oneQCountU` on the unitary `BaseUCom` IR).

  This is the single, separate "resource system": it depends only on the IRs,
  never on the circuit builders or the correctness proofs, so a count cannot be
  influenced by a proof.
-/
import FormalRV.Resource.GateCount
import FormalRV.Resource.UComCount

namespace FormalRV.Resource

open FormalRV.Framework

/-- An IR whose syntactic objects carry honest resource counters, split into the
two physical resources: TIME (gate counts) and SPACE (qubit count). -/
class HasResourceCount (α : Type _) where
  /-- TIME — CNOT (entangling 2-qubit) gate count. -/
  cnot   : α → Nat
  /-- TIME — total primitive-gate count. -/
  gates  : α → Nat
  /-- SPACE — qubit count (register width). -/
  qubits : α → Nat

/-- The reversible `Gate` IR. -/
instance : HasResourceCount Gate where
  cnot   := countCNOT
  gates  := gateCount
  qubits := width

/-- The unitary `BaseUCom` IR. -/
instance {dim : Nat} : HasResourceCount (BaseUCom dim) where
  cnot   := cnotCountU
  gates  := gateCountU
  qubits := widthU

/-! ## Smoke: the uniform interface resolves to each IR's honest walker. -/

example : HasResourceCount.gates  (Gate.CCX 0 1 2) = 1 := by decide   -- TIME
example : HasResourceCount.qubits (Gate.CCX 0 1 2) = 3 := by decide   -- SPACE
example : HasResourceCount.cnot (Gate.seq (Gate.CX 0 1) (Gate.CX 1 2)) = 2 := by decide
example {dim} (c t : Nat) :
    HasResourceCount.cnot (BaseUCom.CNOT c t : BaseUCom dim) = 1 := rfl

end FormalRV.Resource
