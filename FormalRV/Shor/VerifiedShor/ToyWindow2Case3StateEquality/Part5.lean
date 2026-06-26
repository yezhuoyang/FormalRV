/- ToyWindow2Case3StateEquality — Part5 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.ToyWindow2Case3StateEquality.Part4

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ### R7d^ix: above-layout helper for case-3 gate

For positions `q ≥ 2 + 2*bits + 1` distinct from `b0Idx`, `b1Idx`,
`flagIdx`, the case-3 gate leaves `q` at `false` (its input value).

Proof strategy mirrors the ModMult `modmult_step_at_untouched_pos`
trick: at q the input is `false`, so `update input q false = input` (no-op).
By the SQIR commute lemma, the mod-add commutes with this trivial update,
yielding `applyNat mod-add input q = false` directly.

The CCX layers also commute with the q-update (q ∉ {b0Idx, b1Idx, flagIdx}),
so the full gate's output at q equals the input's value at q, which is
false by `cuccaro_input_F_above_eq_false`. -/

/-- The case-3 gate's output is `false` at any position `q` above the
SQIR/Cuccaro layout (`q ≥ 2 + 2*bits + 1`) that is distinct from the
window bits `b0Idx`/`b1Idx` and the lookup equality flag `flagIdx`. -/
theorem toyWindow2Case3Gate_aboveLayoutFalse
    (bits N a k acc flagIdx b0Idx b1Idx q : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (hq_above : 2 + 2 * bits + 1 ≤ q)
    (hq_ne_b0 : q ≠ b0Idx) (hq_ne_b1 : q ≠ b1Idx) (hq_ne_flag : q ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) q = false := by
  -- Auxiliary facts.
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_q_ne_one : q ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  -- Convert the gate to SQIR-form.
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) q
      = false
  simp only [Gate.applyNat_seq]
  -- Step 1: peel the outer CCX (q ≠ flagIdx).
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_flag]
  -- Step 2: peel the inner CCX.
  rw [Gate.applyNat_CCX]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_F0_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F0_b0, h_F0_b1, h_F0_flag]
  simp only [Bool.and_self, Bool.false_xor]
  -- Step 3: reorder updates to bring flagIdx innermost.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Step 4: push b1Idx, b0Idx updates outside the mod-add and read through.
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b1]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b0]
  -- Goal: Gate.applyNat (mod-add) (update F flagIdx true) q = false.
  -- Use the commute trick: input at q is false, so mod-add output at q is false.
  have h_input_q :
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true) q = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_flag]
    exact cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt
  have h_in_eq :
      update (update (cuccaro_input_F 2 false 0 acc) flagIdx true) q false
        = update (cuccaro_input_F 2 false 0 acc) flagIdx true := by
    -- Cannot use `rw [show false = (...) q from h_input_q.symm]` here because
    -- `cuccaro_input_F 2 false 0 acc` contains a `false` literal that would
    -- be hit by the rewrite.  Use funext instead.
    funext p
    by_cases hpq : p = q
    · subst hpq
      rw [FormalRV.Framework.update_eq]
      exact h_input_q.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hpq]
  have h_commute :=
    style_controlledModAddConst_gate_commute_update_outside_fun bits N
      (tableValue a N 2 k 3) flagIdx q false
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true)
      h_q_out h_q_ne_one hq_ne_flag
  rw [h_in_eq] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q


end Windowed
end VerifiedShor
