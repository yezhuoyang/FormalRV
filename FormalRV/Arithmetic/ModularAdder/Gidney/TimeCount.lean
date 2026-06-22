/-
  FormalRV.Arithmetic.ModularAdder.Gidney.TimeCount
  ─────────────────────────────────────────────────
  THE time-resource (T-count) theorems for the Gidney-style modular adder —
  closing the audit gap "ModularAdder semantics + space are anchored, but the
  closed-form TIME counts are missing" (arithmetic-gadget audit, 2026-06-10).

  Every theorem is ANCHORED: `Gate.tcount` (the independent tree-walker,
  = `Resource.countT`) applied to THE SAME syntactic objects the correctness
  theorems in `ForwardFaithfulness.lean` / `Correctness.lean` verify.

  The missing prerequisite proven here first: the carry-clearing PATCHED Gidney
  adder has the same `14·bits` T-count as the base adder (the patch is a
  T-free CX per reverse step).

  Closed forms (the pipelines run at internal width `bits + 1`; stated at
  `n + 2 = bits + 1`, i.e. data width `bits = n + 1`, so the patched adder's
  nontrivial case applies):

    gidney patched adder (n+2)                       14·(n+2)
    prepareConstRead / prepareMaskedConstRead         0
    addConstGate / subConstGate (n+2)                14·(n+2)
    conditionalAddConstGate (n+2)                    14·(n+2)
    copyTargetHighBitToFlag                           0
    modAddConstGate_dirtyFlag (n+1)                  42·(n+2)
    flagUncomputeGate (n+1)                          28·(n+2)
    modAddConstGate (n+1)        (THE clean gate)    70·(n+2)
    controlledModAddConstGate (n+1)                  70·(n+2) + 14
-/
import FormalRV.Arithmetic.ModularAdder.Gidney.Def
import FormalRV.Arithmetic.RippleCarryAdder.ForwardAndCost.FaithfulBackbone
import FormalRV.Arithmetic.RippleCarryAdder.ForwardAndCost.SkeletonCost

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## §1. The patched (carry-clearing) adder is still `14·bits`.

Each patched reverse step = the faithful reverse step (one CCX = 7 T) plus one
T-free carry-clearing CX. -/

@[simp] theorem tcount_gidney_adder_bit_step_faithful_first_reverse_patched :
    tcount gidney_adder_bit_step_faithful_first_reverse_patched = 7 := rfl

@[simp] theorem tcount_gidney_adder_bit_step_faithful_interior_reverse_patched (i : Nat) :
    tcount (gidney_adder_bit_step_faithful_interior_reverse_patched i) = 7 := rfl

@[simp] theorem tcount_gidney_adder_bit_step_faithful_last_reverse_patched (i : Nat) :
    tcount (gidney_adder_bit_step_faithful_last_reverse_patched i) = 7 := rfl

theorem tcount_gidney_adder_forward_with_propagation_reverse_patched :
    ∀ n, tcount (gidney_adder_forward_with_propagation_reverse_patched n) = 7 * n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    show tcount (Gate.seq (gidney_adder_bit_step_faithful_interior_reverse_patched (n + 1))
                          (gidney_adder_forward_with_propagation_reverse_patched (n + 1)))
        = 7 * (n + 2)
    rw [tcount, tcount_gidney_adder_bit_step_faithful_interior_reverse_patched,
        tcount_gidney_adder_forward_with_propagation_reverse_patched (n + 1)]
    omega

theorem tcount_gidney_adder_forward_faithful_full_reverse_patched (n : Nat) :
    tcount (gidney_adder_forward_faithful_full_reverse_patched (n + 2)) = 7 * (n + 2) := by
  show tcount (Gate.seq (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1))
                        (gidney_adder_forward_with_propagation_reverse_patched (n + 1)))
      = 7 * (n + 2)
  rw [tcount, tcount_gidney_adder_bit_step_faithful_last_reverse_patched,
      tcount_gidney_adder_forward_with_propagation_reverse_patched (n + 1)]
  omega

/-- **The carry-clean PATCHED Gidney adder has T-count `14·bits`** — the same
syntactic object verified by `gidney_adder_correct_full` (the reusable
modular-adder primitive). -/
theorem tcount_gidney_adder_full_faithful_no_measurement_patched (n : Nat) :
    tcount (gidney_adder_full_faithful_no_measurement_patched (n + 2)) = 14 * (n + 2) := by
  show tcount (Gate.seq
                 (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                           (gidney_final_cx_cascade (n + 2)))
                 (gidney_adder_forward_faithful_full_reverse_patched (n + 2)))
      = 14 * (n + 2)
  rw [tcount, tcount, tcount_gidney_adder_forward_faithful_full,
      tcount_gidney_final_cx_cascade,
      tcount_gidney_adder_forward_faithful_full_reverse_patched]
  omega

/-! ## §2. Preparations are T-free. -/

@[simp] theorem tcount_prepareConstRead (k c : Nat) :
    tcount (prepareConstRead k c) = 0 := by
  induction k with
  | zero => rfl
  | succ m ih =>
    show tcount (Gate.seq (prepareConstRead m c)
                          (if c.testBit m then Gate.X (read_idx m) else Gate.I)) = 0
    by_cases h : c.testBit m <;> simp [tcount, ih, h]

@[simp] theorem tcount_prepareMaskedConstRead (k N flagIdx : Nat) :
    tcount (prepareMaskedConstRead k N flagIdx) = 0 := by
  induction k with
  | zero => rfl
  | succ m ih =>
    show tcount (Gate.seq (prepareMaskedConstRead m N flagIdx)
                          (if N.testBit m then Gate.CX flagIdx (read_idx m) else Gate.I)) = 0
    by_cases h : N.testBit m <;> simp [tcount, ih, h]

/-! ## §3. Constant add / sub and the conditional variant: `14·bits`. -/

/-- **Add-constant T-count = 14·bits** — the object verified by the
`addConstGate` correctness chain. -/
theorem tcount_addConstGate (n c : Nat) :
    tcount (addConstGate (n + 2) c) = 14 * (n + 2) := by
  show tcount (Gate.seq (prepareConstRead (n + 2) c)
                 (Gate.seq (gidney_adder_full_faithful_no_measurement_patched (n + 2))
                           (prepareConstRead (n + 2) c))) = 14 * (n + 2)
  simp only [tcount, tcount_prepareConstRead,
      tcount_gidney_adder_full_faithful_no_measurement_patched]
  omega

theorem tcount_subConstGate (n N : Nat) :
    tcount (subConstGate (n + 2) N) = 14 * (n + 2) :=
  tcount_addConstGate n (2 ^ (n + 2) - N)

/-- **Conditional (flag-masked) add-constant T-count = 14·bits**. -/
theorem tcount_conditionalAddConstGate (n N flagIdx : Nat) :
    tcount (conditionalAddConstGate (n + 2) N flagIdx) = 14 * (n + 2) := by
  show tcount (Gate.seq (prepareMaskedConstRead (n + 2) N flagIdx)
                 (Gate.seq (gidney_adder_full_faithful_no_measurement_patched (n + 2))
                           (prepareMaskedConstRead (n + 2) N flagIdx))) = 14 * (n + 2)
  simp only [tcount, tcount_prepareMaskedConstRead,
      tcount_gidney_adder_full_faithful_no_measurement_patched]
  omega

@[simp] theorem tcount_copyTargetHighBitToFlag (bits flagIdx : Nat) :
    tcount (copyTargetHighBitToFlag bits flagIdx) = 0 := rfl

/-! ## §4. The modular-add pipelines (internal width `bits + 1 = n + 2`). -/

/-- Dirty-flag pipeline (add ; sub ; flag-copy ; conditional add-back):
`42·(bits+1)` — the object verified by the dirty-flag correctness chain. -/
theorem tcount_modAddConstGate_dirtyFlag (n N c flagIdx : Nat) :
    tcount (modAddConstGate_dirtyFlag (n + 1) N c flagIdx) = 42 * (n + 2) := by
  show tcount (Gate.seq (addConstGate (n + 2) c)
                 (Gate.seq (subConstGate (n + 2) N)
                   (Gate.seq (copyTargetHighBitToFlag (n + 1) flagIdx)
                             (conditionalAddConstGate (n + 2) N flagIdx)))) = 42 * (n + 2)
  rw [tcount, tcount, tcount, tcount_addConstGate, tcount_subConstGate,
      tcount_copyTargetHighBitToFlag, tcount_conditionalAddConstGate]
  omega

/-- Flag-uncompute (sub ; CX ; X ; add): `28·(bits+1)`. -/
theorem tcount_flagUncomputeGate (n c flagIdx : Nat) :
    tcount (flagUncomputeGate (n + 1) c flagIdx) = 28 * (n + 2) := by
  show tcount (Gate.seq (subConstGate (n + 2) c)
                 (Gate.seq (Gate.CX (target_idx (n + 1)) flagIdx)
                   (Gate.seq (Gate.X flagIdx)
                             (addConstGate (n + 2) c)))) = 28 * (n + 2)
  simp only [tcount, tcount_subConstGate, tcount_addConstGate]
  omega

/-- **THE clean Gidney modular add-constant gate: T-count = 70·(bits+1)** —
the object verified by `modAddConstGate`'s correctness bundle
(dirty-flag pipeline + flag uncompute). -/
theorem tcount_modAddConstGate (n N c : Nat) :
    tcount (modAddConstGate (n + 1) N c) = 70 * (n + 2) := by
  show tcount (Gate.seq
                 (modAddConstGate_dirtyFlag (n + 1) N c (adder_n_qubits (n + 2)))
                 (flagUncomputeGate (n + 1) c (adder_n_qubits (n + 2)))) = 70 * (n + 2)
  rw [tcount, tcount_modAddConstGate_dirtyFlag, tcount_flagUncomputeGate]
  omega

/-- **The CONTROLLED Gidney modular add-constant gate:
T-count = 70·(bits+1) + 14** (five conditional adds + two Toffolis). -/
theorem tcount_controlledModAddConstGate (n N c controlIdx flagIdx : Nat) :
    tcount (controlledModAddConstGate (n + 1) N c controlIdx flagIdx)
      = 70 * (n + 2) + 14 := by
  show tcount (Gate.seq (conditionalAddConstGate (n + 2) c controlIdx)
                 (Gate.seq (conditionalAddConstGate (n + 2) (2 ^ (n + 2) - N) controlIdx)
                   (Gate.seq (Gate.CCX controlIdx (target_idx (n + 1)) flagIdx)
                     (Gate.seq (conditionalAddConstGate (n + 2) N flagIdx)
                       (Gate.seq (conditionalAddConstGate (n + 2) (2 ^ (n + 2) - c) controlIdx)
                         (Gate.seq (Gate.CCX controlIdx (target_idx (n + 1)) flagIdx)
                           (Gate.seq (Gate.CX controlIdx flagIdx)
                                     (conditionalAddConstGate (n + 2) c controlIdx))))))))
      = 70 * (n + 2) + 14
  simp only [tcount, tcount_conditionalAddConstGate]
  omega

/-! ## §5. Smoke instances (third-party `#eval`-testable closed forms). -/

example : tcount (addConstGate 3 5) = 42 := by decide
example : tcount (modAddConstGate 2 5 3) = 210 := by decide

end FormalRV.BQAlgo
