/-
  FormalRV.Arithmetic.SQIRModMult.ToffoliCount — a proved Toffoli (T-count) bound on the
  SAME Gate IR term that the SQIR port proves computes modular multiplication.

  The verified modular multiplier `sqir_modmult_const_gate bits N a` is proved to write
  `(a · m) % N` into the accumulator (`sqir_modmult_const_gate_target_decode`).  Here we
  derive a closed-form UPPER BOUND on its T-count by structural induction over its Gate IR
  — `tcount ≤ 56·bits²` (i.e. ≤ 8·bits² Toffolis) — so for the first time a modular-
  arithmetic building block has count AND semantics on one verified circuit term.

  Layer counts (each derived, not asserted):
    prepare-reads            tcount 0        (only X / CX / cond)
    cuccaro_maj_chain_inv    tcount 7·n
    conditional add / sub    tcount 14·bits  (one Cuccaro adder, 14·bits)
    compare / ctrl-compare   tcount 14·bits  (two maj-chains, 7·bits each)
    controlled mod-add       tcount 56·bits  (four 14·bits sub-blocks)
    modmult prefix (k steps) tcount ≤ k·56·bits
    modmult const (bits)     tcount ≤ 56·bits²

  No `sorry`, no new `axiom`.
-/
import FormalRV.Arithmetic.SQIRModMult.Defs
import FormalRV.Arithmetic.Cuccaro.CuccaroFull

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## §1. Zero-Toffoli leaves: the masked/const read preparations. -/

@[simp] theorem tcount_cond_X_I (b : Bool) (q : Nat) :
    tcount (cond b (Gate.X q) Gate.I) = 0 := by cases b <;> rfl
@[simp] theorem tcount_cond_CX_I (b : Bool) (a c : Nat) :
    tcount (cond b (Gate.CX a c) Gate.I) = 0 := by cases b <;> rfl

theorem tcount_cuccaro_prepareConstRead (n q c : Nat) :
    tcount (cuccaro_prepareConstRead n q c) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [cuccaro_prepareConstRead, tcount, ih]

theorem tcount_sqir_prepareMaskedConstRead (n q N f : Nat) :
    tcount (sqir_prepareMaskedConstRead n q N f) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sqir_prepareMaskedConstRead, tcount, ih]

/-! ## §2. The inverse MAJ chain: `7·n` (mirrors the forward `tcount_cuccaro_maj_chain`). -/

theorem tcount_cuccaro_MAJ_inv (a b c : Nat) : tcount (cuccaro_MAJ_inv a b c) = 7 := by
  simp [cuccaro_MAJ_inv, tcount]

theorem tcount_cuccaro_maj_chain_inv (n q : Nat) :
    tcount (cuccaro_maj_chain_inv n q) = 7 * n := by
  induction n generalizing q with
  | zero => rfl
  | succ k ih =>
      simp [cuccaro_maj_chain_inv, tcount, ih, tcount_cuccaro_MAJ_inv]
      omega

/-! ## §3. The four `14·bits` sub-blocks of the controlled modular addition. -/

theorem tcount_sqir_conditionalAddConstGate (bits q N f : Nat) :
    tcount (sqir_conditionalAddConstGate bits q N f) = 14 * bits := by
  simp [sqir_conditionalAddConstGate, tcount, tcount_sqir_prepareMaskedConstRead,
        tcount_cuccaro_n_bit_adder_full]

theorem tcount_sqir_conditionalSubConstGate (bits q N f : Nat) :
    tcount (sqir_conditionalSubConstGate bits q N f) = 14 * bits := by
  simp [sqir_conditionalSubConstGate, tcount_sqir_conditionalAddConstGate]

theorem tcount_sqir_style_compareConst_candidate (bits q N f : Nat) :
    tcount (sqir_style_compareConst_candidate bits q N f) = 14 * bits := by
  simp [sqir_style_compareConst_candidate, tcount, tcount_cuccaro_prepareConstRead,
        tcount_cuccaro_maj_chain, tcount_cuccaro_maj_chain_inv]
  omega

theorem tcount_sqir_controlledCompareConst (bits q c ci f : Nat) :
    tcount (sqir_controlledCompareConst bits q c ci f) = 14 * bits := by
  simp [sqir_controlledCompareConst, tcount, tcount_sqir_prepareMaskedConstRead,
        tcount_cuccaro_maj_chain, tcount_cuccaro_maj_chain_inv]
  omega

/-! ## §4. The controlled modular addition: `56·bits`; the wrapped gate: `≤ 56·bits`. -/

theorem tcount_sqir_style_controlledModAddConst_candidate (bits q N c ci f : Nat) :
    tcount (sqir_style_controlledModAddConst_candidate bits q N c ci f) = 56 * bits := by
  simp [sqir_style_controlledModAddConst_candidate, tcount,
        tcount_sqir_conditionalAddConstGate, tcount_sqir_style_compareConst_candidate,
        tcount_sqir_conditionalSubConstGate, tcount_sqir_controlledCompareConst]
  omega

theorem tcount_sqir_style_controlledModAddConst_gate_le (bits q N c ci f : Nat) :
    tcount (sqir_style_controlledModAddConst_gate bits q N c ci f) ≤ 56 * bits := by
  unfold sqir_style_controlledModAddConst_gate
  split
  · simp [tcount]
  · rw [tcount_sqir_style_controlledModAddConst_candidate]

/-! ## §5. The modular multiplier: prefix `≤ k·56·bits`, const `≤ 56·bits²`. -/

theorem tcount_sqir_modmult_step_gate_le (bits N a j : Nat) :
    tcount (sqir_modmult_step_gate bits N a j) ≤ 56 * bits := by
  unfold sqir_modmult_step_gate
  exact tcount_sqir_style_controlledModAddConst_gate_le _ _ _ _ _ _

theorem tcount_sqir_modmult_prefix_gate_le (bits N a k : Nat) :
    tcount (sqir_modmult_prefix_gate bits N a k) ≤ k * (56 * bits) := by
  induction k with
  | zero => simp [sqir_modmult_prefix_gate, tcount]
  | succ m ih =>
      simp only [sqir_modmult_prefix_gate, tcount]
      calc tcount (sqir_modmult_prefix_gate bits N a m)
              + tcount (sqir_modmult_step_gate bits N a m)
            ≤ m * (56 * bits) + 56 * bits :=
              Nat.add_le_add ih (tcount_sqir_modmult_step_gate_le _ _ _ _)
        _ = (m + 1) * (56 * bits) := by ring

/-- **T-count UPPER BOUND on the verified modular multiplier.**  The SAME Gate term
    `sqir_modmult_const_gate bits N a` that `sqir_modmult_const_gate_target_decode` proves
    computes `(a · m) % N` costs at most `56·bits²` T-gates (≤ 8·bits² Toffolis). -/
theorem tcount_sqir_modmult_const_gate_le (bits N a : Nat) :
    tcount (sqir_modmult_const_gate bits N a) ≤ 56 * bits ^ 2 := by
  unfold sqir_modmult_const_gate
  calc tcount (sqir_modmult_prefix_gate bits N a bits)
        ≤ bits * (56 * bits) := tcount_sqir_modmult_prefix_gate_le _ _ _ _
    _ = 56 * bits ^ 2 := by ring

end FormalRV.BQAlgo
