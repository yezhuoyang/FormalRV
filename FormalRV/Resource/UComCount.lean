/-
  FormalRV.Resource.UComCount
  ───────────────────────────
  The canonical, INDEPENDENT resource counters for the `BaseUCom` UNITARY IR
  (Hadamards, rotations, CNOT, SWAP, …) — the genuinely-quantum circuits (QFT,
  QPE) that the reversible `Gate` IR cannot express.

  CLOSES THE GAP: before this file, `BaseUCom` had NO gate counter at all — QFT/QPE
  "resource" was only an `IsCliffordT` predicate plus a real-valued approximation
  ERROR budget, neither of which is a gate count.  Here are honest counters.

  Each counter is a structural recursion over the `UCom` syntax tree.  It matches
  ONLY the shape (`app1` = 1-qubit gate, `app2` = CNOT, `seq` = compose) and never
  inspects the rotation angles, so it is a pure, computable tree-walk independent
  of the gate parameters — the same uncheatable discipline as `GateCount.lean`,
  now over the unitary IR.  (`BaseUnitary 1 = {R}`, `BaseUnitary 2 = {CNOT}`,
  `BaseUnitary 3` is empty — so these three shapes cover every `BaseUCom`.)

  Imports ONLY the IR (`Core.QuantumGate`).  The per-gadget count THEOREMS
  (`countCNOT (IQFT n) = …`) live with their gadget (e.g. `QFT/IQFTResource.lean`).
-/
import FormalRV.Core.QuantumGate

namespace FormalRV.Resource

open FormalRV.Framework

/-! ## §1. The BaseUCom counters (honest structural tree-walks). -/

/-- **1-qubit-gate count** of a `BaseUCom` circuit (each `app1`: H, Rz, T, X, …). -/
def oneQCountU {dim : Nat} : BaseUCom dim → Nat
  | UCom.seq a b      => oneQCountU a + oneQCountU b
  | UCom.app1 _ _     => 1
  | UCom.app2 _ _ _   => 0
  | UCom.app3 _ _ _ _ => 0

/-- **CNOT count** of a `BaseUCom` circuit (`app2` is CNOT — the only 2-qubit
primitive in `BaseUnitary`). -/
def cnotCountU {dim : Nat} : BaseUCom dim → Nat
  | UCom.seq a b      => cnotCountU a + cnotCountU b
  | UCom.app1 _ _     => 0
  | UCom.app2 _ _ _   => 1
  | UCom.app3 _ _ _ _ => 0

/-- **Total primitive-gate count** of a `BaseUCom` circuit. -/
def gateCountU {dim : Nat} : BaseUCom dim → Nat
  | UCom.seq a b      => gateCountU a + gateCountU b
  | UCom.app1 _ _     => 1
  | UCom.app2 _ _ _   => 1
  | UCom.app3 _ _ _ _ => 0

/-! ### Space resource: the qubit count.

The gate counters above are TIME resources.  `widthU` is the SPACE resource. -/

/-- **Qubit count (register width)** of a `BaseUCom` circuit: the largest qubit
index touched, plus one — the SPACE resource, dual to the gate counts (TIME). -/
def widthU {dim : Nat} : BaseUCom dim → Nat
  | UCom.seq a b      => max (widthU a) (widthU b)
  | UCom.app1 _ n     => n + 1
  | UCom.app2 _ m n   => max (m + 1) (n + 1)
  | UCom.app3 _ a b c => max (max (a + 1) (b + 1)) (c + 1)

/-! ## §2. Compositional laws + the gate-count split. -/

@[simp] theorem oneQCountU_seq {dim} (a b : BaseUCom dim) :
    oneQCountU (UCom.seq a b) = oneQCountU a + oneQCountU b := rfl
@[simp] theorem cnotCountU_seq {dim} (a b : BaseUCom dim) :
    cnotCountU (UCom.seq a b) = cnotCountU a + cnotCountU b := rfl
@[simp] theorem gateCountU_seq {dim} (a b : BaseUCom dim) :
    gateCountU (UCom.seq a b) = gateCountU a + gateCountU b := rfl

/-- The total gate count is exactly the 1-qubit gates plus the CNOTs (two
independent counters, reconciled from the same tree). -/
theorem gateCountU_eq_oneQ_add_cnot {dim} (c : BaseUCom dim) :
    gateCountU c = oneQCountU c + cnotCountU c := by
  induction c with
  | seq a b iha ihb => simp only [gateCountU, oneQCountU, cnotCountU, iha, ihb]; omega
  | app1 _ _ => rfl
  | app2 _ _ _ => rfl
  | app3 _ _ _ _ => rfl

/-! ## §3. Counts of the named shorthands (the building blocks of QFT/QPE).

`H`, `Rz`, `X`, … are `app1` (one 1-qubit gate); `CNOT` is `app2`; `SWAP` is three
CNOTs; the controlled-phase `controlled_Rz` decomposes into 3 `Rz` + 2 CNOT. -/

@[simp] theorem oneQCountU_H {dim} (n : Nat) : oneQCountU (BaseUCom.H n : BaseUCom dim) = 1 := rfl
@[simp] theorem cnotCountU_H {dim} (n : Nat) : cnotCountU (BaseUCom.H n : BaseUCom dim) = 0 := rfl
@[simp] theorem oneQCountU_Rz {dim} (lam : ℝ) (n : Nat) :
    oneQCountU (BaseUCom.Rz lam n : BaseUCom dim) = 1 := rfl
@[simp] theorem cnotCountU_CNOT {dim} (c t : Nat) :
    cnotCountU (BaseUCom.CNOT c t : BaseUCom dim) = 1 := rfl

/-- A `SWAP` is three CNOTs (and no 1-qubit gates). -/
@[simp] theorem cnotCountU_SWAP {dim} (m n : Nat) :
    cnotCountU (BaseUCom.SWAP m n : BaseUCom dim) = 3 := rfl
@[simp] theorem oneQCountU_SWAP {dim} (m n : Nat) :
    oneQCountU (BaseUCom.SWAP m n : BaseUCom dim) = 0 := rfl

/-! ## §4. Smoke checks. -/

example {dim} (c t : Nat) : gateCountU (BaseUCom.CNOT c t : BaseUCom dim) = 1 := rfl
example {dim} (m n : Nat) : gateCountU (BaseUCom.SWAP m n : BaseUCom dim) = 3 := rfl
example {dim} (n : Nat) :
    gateCountU (UCom.seq (BaseUCom.H n) (BaseUCom.CNOT 0 1) : BaseUCom dim) = 2 := rfl

end FormalRV.Resource
