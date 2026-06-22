/-
  FormalRV.Codegen.UComQasm — a UNIFORM, faithful OpenQASM emitter for the
  FULL `BaseUCom` unitary IR (rotations included), generalizing the Gate-IR
  emitter (`GateQasm`) onto the SAME semantic-faithfulness contract:

      progMat (emit c) = uc_eval c.

  ## Why this exists

  The reversible `Gate` IR (`I`/`X`/`CX`/`CCX`) underlying `Codegen.QASMEmit`
  cannot express continuous rotations, so genuinely-quantum gadgets — the
  (inverse) QFT, QPE — live in `BaseUCom` (`H`/`Rz`/`CNOT`/…).  Rather than a
  bespoke per-gadget emitter, this module emits ANY `BaseUCom` faithfully and
  proves the emitted op program's unitary (`uprogMat`, built from `uc_eval`
  matrices) equals the circuit's `uc_eval` — the exact contract the Clifford+T
  arithmetic emitter (`GateQasm.progMat` / `emitCliffT_acts_on_basis`) already
  satisfies.  Arithmetic gadgets factor through this emitter via `Gate.toUCom`
  (`uprogMat_emitUComOps_toUCom`), so emission is one framework, two op-sets.

  `BaseUnitary` has exactly two primitives — `R θ φ λ` (1-qubit) and `CNOT`
  (2-qubit) — and `BaseUnitary 3` is empty, so a two-op IR (`UOp.u`/`UOp.cx`)
  represents every `BaseUCom` with no gaps.  The op `UOp.u θ φ λ n` is exactly
  the OpenQASM 2.0 built-in `U(θ,φ,λ) q[n]` (whose matrix is the framework's
  `rotation θ φ λ`), so the emission is a literal, faithful translation.

  Machine-checked: `uprogMat_emitUComOps` is `uc_eval`-equality by structural
  induction (each op's matrix is DEFINED as the corresponding `uc_eval`).
-/
import FormalRV.Core.UnitarySem
import FormalRV.Arithmetic.GateToUCom

namespace FormalRV.Codegen

open FormalRV.Framework

/-! ## §1. The op IR for a `BaseUCom` program.

Two ops mirror the two `BaseUnitary` primitives:
* `UOp.u θ φ λ n`  — the general 1-qubit `U(θ,φ,λ)` on qubit `n` (= `app1 (R θ φ λ) n`);
* `UOp.cx c t`     — `CX` (= `app2 CNOT c t`).
This is complete for `BaseUCom` because `BaseUnitary 1 = {R}`, `BaseUnitary 2 =
{CNOT}`, and `BaseUnitary 3` is uninhabited. -/

/-- A single emitted `BaseUCom` op: a general 1-qubit rotation `U(θ,φ,λ)` or a
`CX`.  (`θ,φ,λ : ℝ`, so the op carries exact rotation data; text rendering of
arbitrary reals is non-computable and handled separately for circuits whose
angles are dyadic multiples of `π`.) -/
inductive UOp where
  | u  : ℝ → ℝ → ℝ → Nat → UOp
  | cx : Nat → Nat → UOp

namespace UOp

/-- The `BaseUCom` unitary of one op at dimension `dim`.  DEFINED to be the
`uc_eval` of the corresponding primitive, so faithfulness is structural. -/
noncomputable def mat (dim : Nat) : UOp → Square dim
  | UOp.u θ φ lam n => ueval_r dim n (BaseUnitary.R θ φ lam)
  | UOp.cx c t      => ueval_cnot dim c t

end UOp

/-- Unitary realised by an op program: circuit order left-to-right = matrix
product right-to-left, starting from the identity (mirrors `GateQasm.progMat`). -/
noncomputable def uprogMat (dim : Nat) : List UOp → Square dim
  | []      => 1
  | op :: l => uprogMat dim l * op.mat dim

theorem uprogMat_append (dim : Nat) (l1 l2 : List UOp) :
    uprogMat dim (l1 ++ l2) = uprogMat dim l2 * uprogMat dim l1 := by
  induction l1 with
  | nil => simp [uprogMat]
  | cons op l ih =>
    show uprogMat dim (op :: (l ++ l2)) = uprogMat dim l2 * uprogMat dim (op :: l)
    simp only [uprogMat, ih, Matrix.mul_assoc]

/-! ## §2. The faithful emitter. -/

/-- **The faithful `BaseUCom` emitter.**  `seq` concatenates; `app1 (R …)` and
`app2 CNOT` map to the two ops; `app3` is unreachable (`BaseUnitary 3` empty). -/
def emitUComOps {dim : Nat} : BaseUCom dim → List UOp
  | UCom.seq a b                       => emitUComOps a ++ emitUComOps b
  | UCom.app1 (BaseUnitary.R θ φ lam) n => [UOp.u θ φ lam n]
  | UCom.app2 BaseUnitary.CNOT m n      => [UOp.cx m n]
  | UCom.app3 u _ _ _                   => nomatch u

/-- **★ Faithfulness ★** — the emitted op program's unitary equals the
circuit's `uc_eval`, for EVERY `BaseUCom`.  The same `progMat = uc_eval`
contract the Clifford+T arithmetic emitter satisfies, now over the full
unitary IR. -/
theorem uprogMat_emitUComOps {dim : Nat} (c : BaseUCom dim) :
    uprogMat dim (emitUComOps c) = uc_eval c := by
  induction c with
  | seq a b iha ihb =>
    show uprogMat dim (emitUComOps a ++ emitUComOps b) = uc_eval b * uc_eval a
    rw [uprogMat_append, iha, ihb]
  | app1 U n =>
    cases U with
    | R θ φ lam =>
      show uprogMat dim [UOp.u θ φ lam n] = ueval_r dim n (BaseUnitary.R θ φ lam)
      simp [uprogMat, UOp.mat]
  | app2 U m n =>
    cases U with
    | CNOT =>
      show uprogMat dim [UOp.cx m n] = ueval_cnot dim m n
      simp [uprogMat, UOp.mat]
  | app3 U _ _ _ => cases U

/-! ## §3. Unification with the arithmetic (Gate-IR) emitter.

Every reversible-classical `Gate` gadget maps to a `BaseUCom` via
`Gate.toUCom`, so it emits through the SAME faithful emitter as the quantum
gadgets — the unification this module is for. -/

/-- A reversible `Gate` circuit, embedded into `BaseUCom` via `Gate.toUCom`,
emits faithfully through `emitUComOps`: the emitted op program's unitary equals
the gate's `uc_eval`.  This is the same `uc_eval` the arithmetic Clifford+T
emitter (`GateQasm`) targets, so arithmetic gadgets and quantum gadgets share
one emission framework. -/
theorem uprogMat_emitUComOps_toUCom (dim : Nat) (g : FormalRV.Framework.Gate) :
    uprogMat dim (emitUComOps (FormalRV.BQAlgo.Gate.toUCom dim g))
      = uc_eval (FormalRV.BQAlgo.Gate.toUCom dim g) :=
  uprogMat_emitUComOps _

/-! ## §4. A uniform descriptor for quantum (`BaseUCom`) gadgets.

The sibling of `Codegen.Gadget` (the Gate-IR descriptor in `QASMEmit.lean`).
A `UGadget` bundles a name, a width function, and a COMPUTABLE OpenQASM body
`render`.  (The arithmetic `Gadget` can carry its `Gate` circuit because that
IR is computable; the quantum circuit `BaseUCom` carries real rotation data and
is non-computable, so the emittable descriptor carries the computable rendering
and the SEMANTIC tie to `uc_eval` is the separate `uprogMat_emitUComOps`
theorem — proved per gadget, e.g. `iqft_emitted_unitary_eq_IQFT_matrix`.)  Both
descriptors emit OpenQASM 2.0 against the same `progMat/uprogMat = uc_eval`
faithfulness contract. -/
structure UGadget where
  /-- A short identifier (file/labeling). -/
  name    : String
  /-- Register width at parameter `n`. -/
  nqubits : Nat → Nat
  /-- Computable OpenQASM 2.0 body (one gate per line) at parameter `n`. -/
  render  : Nat → List String

/-- **Uniform QASM emitter for quantum gadgets.**  `emitQASM g n` is the
OpenQASM 2.0 program for quantum gadget `g` at parameter `n` (e.g.
`IQFTGadget.emitQASM 3`) — the `BaseUCom` analogue of `Codegen.emitQASM`. -/
def UGadget.emitQASM (g : UGadget) (n : Nat) : String :=
  String.intercalate "\n"
    ([ "OPENQASM 2.0;", "include \"qelib1.inc\";",
       "qreg q[" ++ toString (g.nqubits n) ++ "];" ] ++ g.render n) ++ "\n"

end FormalRV.Codegen
