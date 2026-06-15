/-
  FormalRV.Arithmetic.RippleCarryAdder.UncomputeCascade.FrameLemmas
  Patched-adder uncompute cascade — frame lemmas (part 1/3). The
  "patched = unpatched at non-carry positions" cascade theorems plus the
  unpatched commute / input-independence helpers. Supporting lemmas only; the
  backbone (`gidney_adder_patched_primitive`) is in `WellTypedBackbone`.
-/
import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Framework.PaperClaims
import FormalRV.PPM.GidneyAND
import Mathlib.Tactic.IntervalCases
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderDef
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderPropagationReverse

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-- Unpatched full reverse cascade commutes with update at `c[j]` (`j > n+1`). -/
theorem unpatched_full_reverse_commute_update_at_c_above
    (n : Nat) (g : Nat → Bool) (v : Bool) (j : Nat) (hj : j > n + 1) :
    Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2)) (update g (carry_idx j) v)
      = update (Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2)) g)
          (carry_idx j) v := by
  show Gate.applyNat (gidney_adder_forward_with_propagation_reverse (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1))
          (update g (carry_idx j) v))
    = update (Gate.applyNat (gidney_adder_forward_with_propagation_reverse (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1)) g))
        (carry_idx j) v
  rw [unpatched_last_reverse_commute_update_at_c_above (n + 1) (by omega) g j (by omega) v]
  rw [unpatched_propagation_reverse_commute_update_at_c_above n _ v j (by omega)]

/-- **Input-independence of the unpatched propagation cascade** (Deliverable A):
changing the input at `carry_idx (m+1)` (above the cascade's range)
does not affect the output at any other position. -/
theorem unpatched_propagation_reverse_indep_input_at_c_above
    (m : Nat) (g : Nat → Bool) (v : Bool) (k : Nat) (h_k : k ≠ carry_idx (m + 1)) :
    Gate.applyNat (gidney_adder_forward_with_propagation_reverse (m + 1))
      (update g (carry_idx (m + 1)) v) k
    = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (m + 1)) g k := by
  rw [unpatched_propagation_reverse_commute_update_at_c_above m g v (m + 1) (by omega)]
  rw [update_neq _ _ _ _ h_k]

/-- Input-independence of the unpatched full reverse cascade at `c[n+2]`. -/
theorem unpatched_full_reverse_indep_input_at_c_above
    (n : Nat) (g : Nat → Bool) (v : Bool) (k : Nat) (h_k : k ≠ carry_idx (n + 2)) :
    Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2))
      (update g (carry_idx (n + 2)) v) k
    = Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2)) g k := by
  rw [unpatched_full_reverse_commute_update_at_c_above n g v (n + 2) (by omega)]
  rw [update_neq _ _ _ _ h_k]

/-! ## Cascade-level "patched = unpatched at non-carry" theorems (Deliverable B) -/

/-- Patched propagation cascade equals unpatched at `target_idx i`. -/
theorem patched_unpatched_propagation_reverse_eq_at_target (m : Nat) :
    ∀ (g : Nat → Bool) (i : Nat),
      Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (m + 1)) g
        (target_idx i)
        = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (m + 1)) g
            (target_idx i) := by
  induction m with
  | zero =>
      intro g i
      apply patched_first_reverse_eq_unpatched_at_non_c0
      unfold target_idx carry_idx; omega
  | succ k' ih =>
      intro g i
      show Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (k' + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched (k' + 1)) g)
            (target_idx i)
        = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (k' + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (k' + 1)) g)
            (target_idx i)
      set s_p := Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched (k' + 1)) g
      set s_u := Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (k' + 1)) g
      rw [ih s_p i]
      have h_sp_form : s_p = update s_u (carry_idx (k' + 1)) (s_p (carry_idx (k' + 1))) := by
        funext k
        by_cases h_k : k = carry_idx (k' + 1)
        · subst h_k; rw [update_eq]
        · rw [update_neq _ _ _ _ h_k]
          exact patched_interior_reverse_eq_unpatched_at_non_ci (k' + 1) g k h_k
      rw [h_sp_form]
      apply unpatched_propagation_reverse_indep_input_at_c_above k' s_u _ (target_idx i)
      unfold target_idx carry_idx; omega

/-- Patched propagation cascade equals unpatched at `read_idx i`. -/
theorem patched_unpatched_propagation_reverse_eq_at_read (m : Nat) :
    ∀ (g : Nat → Bool) (i : Nat),
      Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (m + 1)) g
        (read_idx i)
        = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (m + 1)) g
            (read_idx i) := by
  induction m with
  | zero =>
      intro g i
      apply patched_first_reverse_eq_unpatched_at_non_c0
      unfold read_idx carry_idx; omega
  | succ k' ih =>
      intro g i
      show Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (k' + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched (k' + 1)) g)
            (read_idx i)
        = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (k' + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (k' + 1)) g)
            (read_idx i)
      set s_p := Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched (k' + 1)) g
      set s_u := Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (k' + 1)) g
      rw [ih s_p i]
      have h_sp_form : s_p = update s_u (carry_idx (k' + 1)) (s_p (carry_idx (k' + 1))) := by
        funext k
        by_cases h_k : k = carry_idx (k' + 1)
        · subst h_k; rw [update_eq]
        · rw [update_neq _ _ _ _ h_k]
          exact patched_interior_reverse_eq_unpatched_at_non_ci (k' + 1) g k h_k
      rw [h_sp_form]
      apply unpatched_propagation_reverse_indep_input_at_c_above k' s_u _ (read_idx i)
      unfold read_idx carry_idx; omega

/-- Patched full reverse cascade equals unpatched at `target_idx i`. -/
theorem patched_full_reverse_eq_unpatched_at_target
    (n : Nat) (g : Nat → Bool) (i : Nat) :
    Gate.applyNat (gidney_adder_forward_faithful_full_reverse_patched (n + 2)) g (target_idx i)
      = Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2)) g (target_idx i) := by
  show Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1)) g)
        (target_idx i)
    = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1)) g)
        (target_idx i)
  set s_p := Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1)) g
  set s_u := Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1)) g
  rw [patched_unpatched_propagation_reverse_eq_at_target n s_p i]
  have h_sp_form : s_p = update s_u (carry_idx (n + 1)) (s_p (carry_idx (n + 1))) := by
    funext k
    by_cases h_k : k = carry_idx (n + 1)
    · subst h_k; rw [update_eq]
    · rw [update_neq _ _ _ _ h_k]
      exact patched_last_reverse_eq_unpatched_at_non_ci (n + 1) g k h_k
  rw [h_sp_form]
  apply unpatched_propagation_reverse_indep_input_at_c_above n s_u _ (target_idx i)
  unfold target_idx carry_idx; omega

/-- Patched full reverse cascade equals unpatched at `read_idx i`. -/
theorem patched_full_reverse_eq_unpatched_at_read
    (n : Nat) (g : Nat → Bool) (i : Nat) :
    Gate.applyNat (gidney_adder_forward_faithful_full_reverse_patched (n + 2)) g (read_idx i)
      = Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2)) g (read_idx i) := by
  show Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1)) g)
        (read_idx i)
    = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1)) g)
        (read_idx i)
  set s_p := Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1)) g
  set s_u := Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1)) g
  rw [patched_unpatched_propagation_reverse_eq_at_read n s_p i]
  have h_sp_form : s_p = update s_u (carry_idx (n + 1)) (s_p (carry_idx (n + 1))) := by
    funext k
    by_cases h_k : k = carry_idx (n + 1)
    · subst h_k; rw [update_eq]
    · rw [update_neq _ _ _ _ h_k]
      exact patched_last_reverse_eq_unpatched_at_non_ci (n + 1) g k h_k
  rw [h_sp_form]
  apply unpatched_propagation_reverse_indep_input_at_c_above n s_u _ (read_idx i)
  unfold read_idx carry_idx; omega

end FormalRV.BQAlgo
