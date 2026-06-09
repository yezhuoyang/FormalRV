/-
  FormalRV.Arithmetic.Adder
  ─────────────────────────
  An ADDER INTERFACE: a layout-parametric, reversible, in-place binary adder over
  the `Gate` IR. The point is to let higher gadgets (windowed multiplication, …)
  compose ANY adder without knowing its internal qubit layout — the interface
  exposes index functions saying WHERE each operand lives relative to a base
  offset, plus a decode-level correctness contract.

  Encoding is unified by the index functions `augendIdx`/`addendIdx`, not by a
  global re-layout: a consumer places its data at `addendIdx`, runs `circuit`, and
  reads the result at `augendIdx`. Both the Gidney patched ripple adder and the
  Cuccaro adder instantiate this (see `Arithmetic/Adder/*`).

  The `ancClean` precondition (the adder's internal carry block is 0) is what lets
  both adders qualify; it is preserved by `ancRestored`, so it is maintained
  inductively when an adder is run many times (e.g. once per window).
-/
import FormalRV.Arithmetic.Correctness

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- Decode the `n`-bit register sitting at positions `idx 0 … idx (n-1)`,
    LSB-first: bit `i` (at qubit `idx i`) carries weight `2^i`. -/
def decodeReg (idx : Nat → Nat) (n : Nat) (f : Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc i => acc + if f (idx i) then 2 ^ i else 0) 0

/-- `p` lies in the adder block `[q, q + span)`. -/
def inBlock (q span p : Nat) : Prop := q ≤ p ∧ p < q + span

/-- **The adder interface.** At base offset `q` and width `n`, `circuit n q` runs
    on the qubit block `[q, q + span n)` and, given the ancilla block clean,
    computes `augend ← (augend + addend) mod 2^n` in place, restoring the addend
    register and the ancillas and leaving everything outside the block untouched. -/
structure Adder where
  /-- Qubits used by an `n`-bit add (block `[q, q + span n)`). -/
  span      : Nat → Nat
  /-- Qubit holding augend / running-sum bit `i` (modified in place). -/
  augendIdx : Nat → Nat → Nat
  /-- Qubit holding addend bit `i` (the value added in; restored). -/
  addendIdx : Nat → Nat → Nat
  /-- The adder's internal carry / ancilla block is clean (0) in `f`. -/
  ancClean  : (Nat → Bool) → Nat → Nat → Prop
  /-- The adder circuit at width `n`, base offset `q`. -/
  circuit   : Nat → Nat → Gate
  /-- Decode-level correctness: the augend register decodes to `(augend+addend) mod 2^n`. -/
  sumCorrect : ∀ n q f, ancClean f n q →
      decodeReg (augendIdx q) n (Gate.applyNat (circuit n q) f)
        = (decodeReg (augendIdx q) n f + decodeReg (addendIdx q) n f) % 2 ^ n
  /-- The addend register is restored bit-for-bit. -/
  addendRestored : ∀ n q f, ancClean f n q → ∀ i, i < n →
      Gate.applyNat (circuit n q) f (addendIdx q i) = f (addendIdx q i)
  /-- The ancilla block is returned clean (so repeated adds stay in-contract). -/
  ancRestored : ∀ n q f, ancClean f n q → ancClean (Gate.applyNat (circuit n q) f) n q
  /-- Anything outside the block `[q, q + span n)` is untouched (frame). -/
  frame : ∀ n q f p, ¬ inBlock q (span n) p →
      Gate.applyNat (circuit n q) f p = f p
  /-- The circuit is well-typed at dimension `q + span n`. -/
  wellTyped : ∀ n q, Gate.WellTyped (q + span n) (circuit n q)

/-- `decodeReg` depends only on the values of `f` at the index positions. -/
theorem decodeReg_ext (idx : Nat → Nat) (n : Nat) (f g : Nat → Bool)
    (h : ∀ i, i < n → f (idx i) = g (idx i)) :
    decodeReg idx n f = decodeReg idx n g := by
  unfold decodeReg
  have : ∀ (m : Nat) (init : Nat), m ≤ n →
      (List.range m).foldl (fun acc i => acc + if f (idx i) then 2 ^ i else 0) init
        = (List.range m).foldl (fun acc i => acc + if g (idx i) then 2 ^ i else 0) init := by
    intro m
    induction m with
    | zero => intro init _; simp
    | succ k ih =>
        intro init hk
        rw [List.range_succ, List.foldl_append, List.foldl_append, ih init (by omega)]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [h k (by omega)]
  exact this n 0 (le_refl n)

end FormalRV.BQAlgo
