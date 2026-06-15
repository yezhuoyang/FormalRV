/-
  FormalRV.Arithmetic.RippleCarryAdder.PropagationReverse.CarryClearanceBackbone
  BACKBONE (part 4/4): the arbitrary-n cascade carry-clearance inductions and the
  headline `gidney_adder_full_faithful_no_measurement_patched_clears_carries`,
  plus the trailing patched=unpatched / unpatched-frame / update-commute helpers.
  Builds on `PatchedCarryLemmas`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.PropagationReverse.PatchedCarryLemmas

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-! ## Arbitrary-`n` cascade carry-clearance theorems

Three induction-based theorems for the patched reverse cascade:
1. Propagation cascade (length `m+1`) clears `carry_idx i` for `i ≤ m`.
2. Full reverse cascade (length `n+2`) clears `carry_idx i` for `i ≤ n+1`.
3. Full faithful no-measurement patched adder clears all carries
   when applied to the standard `adder_input_F n a b` input.

All three are proved by structural induction on the recursion of the
gate definitions, using the per-step lemmas + frame conditions above.
No `decide` / `native_decide` / `interval_cases` in the main proof. -/

/-- **Arbitrary-`m` propagation-cascade carry-clearance.**  Under the
post-forward-final-CX invariant at positions `0..m`, the patched
propagation cascade `gidney_adder_forward_with_propagation_reverse_patched
(m+1)` makes every `carry_idx i` (for `i ≤ m`) `false`.

Proof: induction on `m`.  Base case is the first-reverse step (using
the minimal-hypothesis version).  Inductive step uses
`patched_interior_reverse_clears_carry_under_invariant` for the
high-bit case, `propagation_reverse_patched_preserves_carry_above`
to preserve the high carry across the rest of the cascade, and the
inductive hypothesis for lower bits — with `patched_interior_reverse_preserves_outside`
showing the invariant survives the interior step. -/
theorem patched_propagation_reverse_cascade_clears_carries
    (m a b : Nat) :
    ∀ (f : Nat → Bool),
      (∀ j, j ≤ m →
        f (carry_idx j)   = Adder.carry false (j + 1) a.testBit b.testBit
        ∧ f (read_idx j)  = xor (a.testBit j) (Adder.carry false j a.testBit b.testBit)
        ∧ f (target_idx j) = xor (a.testBit j) (b.testBit j)) →
      ∀ i, i ≤ m →
        Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (m + 1)) f
          (carry_idx i) = false := by
  induction m with
  | zero =>
      intro f h_inv i hi
      have hi_eq : i = 0 := Nat.le_zero.mp hi
      rw [hi_eq]
      obtain ⟨h_c0, h_r0, h_t0⟩ := h_inv 0 (by omega)
      have h_carry0 : Adder.carry false 0 a.testBit b.testBit = false := rfl
      rw [h_carry0, Bool.xor_false] at h_r0
      exact patched_first_reverse_clears_carry_minimal a b f h_r0 h_t0 h_c0
  | succ k ih =>
      intro f h_inv i hi
      show Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (k + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched (k + 1)) f)
            (carry_idx i) = false
      set f' := Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched (k + 1)) f
        with hf'_def
      obtain ⟨h_c_k1, h_r_k1, h_t_k1⟩ := h_inv (k + 1) (by omega)
      obtain ⟨h_c_k, _, _⟩ := h_inv k (by omega)
      have h_cm1_k1 : f (carry_idx ((k + 1) - 1)) = Adder.carry false (k + 1) a.testBit b.testBit := by
        have : (k + 1) - 1 = k := by omega
        rw [this]; exact h_c_k
      by_cases h_i_eq : i = k + 1
      · rw [h_i_eq, propagation_reverse_patched_preserves_carry_above k f' (k + 1) (by omega),
            hf'_def]
        exact patched_interior_reverse_clears_carry_under_invariant
                (k + 1) a b f h_c_k1 h_cm1_k1 h_r_k1 h_t_k1
      · have hi_le_k : i ≤ k := by omega
        apply ih f'
        · intro j hjk
          obtain ⟨h_cj, h_rj, h_tj⟩ := h_inv j (by omega)
          refine ⟨?_, ?_, ?_⟩
          · rw [hf'_def, patched_interior_reverse_preserves_outside (k + 1) f (carry_idx j)
                  (by unfold carry_idx; omega)
                  (by unfold carry_idx read_idx; omega)
                  (by unfold carry_idx target_idx; omega)]
            exact h_cj
          · rw [hf'_def, patched_interior_reverse_preserves_outside (k + 1) f (read_idx j)
                  (by unfold read_idx carry_idx; omega)
                  (by unfold read_idx; omega)
                  (by unfold read_idx target_idx; omega)]
            exact h_rj
          · rw [hf'_def, patched_interior_reverse_preserves_outside (k + 1) f (target_idx j)
                  (by unfold target_idx carry_idx; omega)
                  (by unfold target_idx read_idx; omega)
                  (by unfold target_idx; omega)]
            exact h_tj
        · exact hi_le_k

/-- **Arbitrary-`n` full-reverse-cascade carry-clearance.**  Under the
post-forward-final-CX invariant at positions `0..n+1`, the patched
full reverse cascade `gidney_adder_forward_faithful_full_reverse_patched
(n+2)` makes every `carry_idx i` (for `i ≤ n+1`) `false`. -/
theorem patched_full_reverse_cascade_clears_carries
    (n a b : Nat) (f : Nat → Bool)
    (h_inv : ∀ j, j ≤ n + 1 →
      f (carry_idx j)   = Adder.carry false (j + 1) a.testBit b.testBit
      ∧ f (read_idx j)  = xor (a.testBit j) (Adder.carry false j a.testBit b.testBit)
      ∧ f (target_idx j) = xor (a.testBit j) (b.testBit j)) :
    ∀ i, i ≤ n + 1 →
      Gate.applyNat (gidney_adder_forward_faithful_full_reverse_patched (n + 2)) f
        (carry_idx i) = false := by
  intro i hi
  show Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1)) f)
        (carry_idx i) = false
  set f' := Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1)) f
    with hf'_def
  obtain ⟨h_c_k1, h_r_k1, h_t_k1⟩ := h_inv (n + 1) (by omega)
  obtain ⟨h_c_k, _, _⟩ := h_inv n (by omega)
  have h_cm1_k1 : f (carry_idx ((n + 1) - 1)) = Adder.carry false (n + 1) a.testBit b.testBit := by
    have : (n + 1) - 1 = n := by omega
    rw [this]; exact h_c_k
  by_cases h_i_eq : i = n + 1
  · rw [h_i_eq, propagation_reverse_patched_preserves_carry_above n f' (n + 1) (by omega),
        hf'_def]
    exact patched_last_reverse_clears_carry_under_invariant
            (n + 1) a b f h_c_k1 h_cm1_k1 h_r_k1 h_t_k1
  · have hi_le_n : i ≤ n := by omega
    apply patched_propagation_reverse_cascade_clears_carries n a b f'
    · intro j hjn
      obtain ⟨h_cj, h_rj, h_tj⟩ := h_inv j (by omega)
      refine ⟨?_, ?_, ?_⟩
      · rw [hf'_def, patched_last_reverse_preserves_non_carry (n + 1) f (carry_idx j)
              (by unfold carry_idx; omega)]
        exact h_cj
      · rw [hf'_def, patched_last_reverse_preserves_non_carry (n + 1) f (read_idx j)
              (by unfold read_idx carry_idx; omega)]
        exact h_rj
      · rw [hf'_def, patched_last_reverse_preserves_non_carry (n + 1) f (target_idx j)
              (by unfold target_idx carry_idx; omega)]
        exact h_tj
    · exact hi_le_n

/-- **Arbitrary-`n` patched-adder carry-clearance on `adder_input_F`.**
The patched full faithful no-measurement Gidney adder, applied to the
standard two-operand input `adder_input_F (n+2) a b`, leaves every
carry position `carry_idx i` (for `i ≤ n+1`) cleared to `false`.

Proof: combine the Tick C wrappers (forward + final_cx applyNat
identities), the existing `Gidney.post_forward_final_cx_invariant_holds`
(Iter 188 + Iter 189), and the new
`patched_full_reverse_cascade_clears_carries` cascade theorem above. -/
theorem gidney_adder_full_faithful_no_measurement_patched_clears_carries
    (n a b : Nat) (ha : a < 2^(n + 2)) (hb : b < 2^(n + 2)) :
    ∀ i, i ≤ n + 1 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched (n + 2))
        (adder_input_F (n + 2) a b) (carry_idx i) = false := by
  intro i hi
  show Gate.applyNat (gidney_adder_forward_faithful_full_reverse_patched (n + 2))
        (Gate.applyNat (gidney_final_cx_cascade (n + 2))
          (Gate.applyNat (gidney_adder_forward_faithful_full (n + 2))
            (adder_input_F (n + 2) a b)))
        (carry_idx i) = false
  rw [gidney_adder_forward_faithful_full_applyNat,
      gidney_final_cx_cascade_applyNat]
  apply patched_full_reverse_cascade_clears_carries n a b _
  · intro j hj
    exact Gidney.post_forward_final_cx_invariant_holds (n + 2) a b
            (by omega) ha hb j (by omega)
  · exact hi

/-! ## Per-step "patched = unpatched at non-carry" frame lemmas

These show that each patched reverse step agrees with its unpatched
counterpart on every position OTHER than the patched carry. -/

theorem patched_first_reverse_eq_unpatched_at_non_c0
    (f : Nat → Bool) (k : Nat) (h_k : k ≠ carry_idx 0) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse_patched f k
      = Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f k := by
  show Gate.applyNat (Gate.CX (read_idx 0) (carry_idx 0))
        (Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f) k
    = Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f k
  simp only [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ h_k]

theorem patched_interior_reverse_eq_unpatched_at_non_ci
    (i : Nat) (f : Nat → Bool) (k : Nat) (h_k : k ≠ carry_idx i) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched i) f k
      = Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f k := by
  show Gate.applyNat (Gate.CX (read_idx i) (carry_idx i))
        (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f) k
    = Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f k
  simp only [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ h_k]

theorem patched_last_reverse_eq_unpatched_at_non_ci
    (i : Nat) (f : Nat → Bool) (k : Nat) (h_k : k ≠ carry_idx i) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched i) f k
      = Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f k := by
  show Gate.applyNat (Gate.CX (read_idx i) (carry_idx i))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f) k
    = Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f k
  simp only [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ h_k]

/-! ## Frame lemmas for the unpatched reverse cascade steps (mirror of the patched versions)

These are needed for the cascade-level "patched = unpatched at
non-carry" induction. -/

theorem unpatched_interior_reverse_preserves_outside
    (i : Nat) (f : Nat → Bool) (k : Nat)
    (h_k_c   : k ≠ carry_idx i)
    (h_k_ri1 : k ≠ read_idx (i + 1))
    (h_k_ti1 : k ≠ target_idx (i + 1)) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f k = f k := by
  unfold gidney_adder_bit_step_faithful_interior_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX,
             update_neq _ _ _ _ h_k_c, update_neq _ _ _ _ h_k_ri1,
             update_neq _ _ _ _ h_k_ti1]

theorem unpatched_first_reverse_preserves_outside
    (f : Nat → Bool) (k : Nat)
    (h_k_c0 : k ≠ carry_idx 0) (h_k_r1 : k ≠ read_idx 1) (h_k_t1 : k ≠ target_idx 1) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f k = f k := by
  unfold gidney_adder_bit_step_faithful_first_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX,
             update_neq _ _ _ _ h_k_c0, update_neq _ _ _ _ h_k_r1,
             update_neq _ _ _ _ h_k_t1]

theorem unpatched_last_reverse_preserves_non_carry
    (i : Nat) (f : Nat → Bool) (k : Nat) (h_k : k ≠ carry_idx i) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f k = f k := by
  unfold gidney_adder_bit_step_faithful_last_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX,
             update_neq _ _ _ _ h_k]

/-! ## Input-independence of the unpatched cascade at carries above its range.

This is the auxiliary frame lemma required to lift the per-step
"patched = unpatched at non-carry" identities to the cascade level.

Proof structure: each gate in the unpatched cascade reads/writes
only positions outside `{carry_idx j | j > m}`, so the gate's
applyNat **commutes** with `update _ (carry_idx j) v`.  By
composition (CX/CCX commute → seq commute → per-step commute →
cascade commute), the entire cascade commutes with the update.
Specializing at the position being queried (≠ `carry_idx (m+1)`)
gives the input independence statement. -/

/-- Two `update`s at different positions commute. -/
theorem update_update_comm (f : Nat → Bool) (a b : Nat) (u w : Bool) (h : a ≠ b) :
    update (update f a u) b w = update (update f b w) a u := by
  funext k
  by_cases h_ka : k = a
  · subst h_ka; rw [update_neq _ _ _ _ h, update_eq, update_eq]
  · by_cases h_kb : k = b
    · subst h_kb; rw [update_eq, update_neq _ _ _ _ (Ne.symm h), update_eq]
    · rw [update_neq _ _ _ _ h_kb, update_neq _ _ _ _ h_ka,
          update_neq _ _ _ _ h_ka, update_neq _ _ _ _ h_kb]

/-- `applyNat (CX c t)` commutes with `update _ p v` when `p` is
disjoint from both `c` and `t`. -/
theorem applyNat_CX_commute_update_disjoint
    (c t : Nat) (f : Nat → Bool) (p : Nat) (v : Bool)
    (h_p_c : p ≠ c) (h_p_t : p ≠ t) :
    Gate.applyNat (Gate.CX c t) (update f p v)
      = update (Gate.applyNat (Gate.CX c t) f) p v := by
  simp only [Gate.applyNat_CX, update_neq _ _ _ _ h_p_t.symm,
             update_neq _ _ _ _ h_p_c.symm]
  exact update_update_comm f p t v _ h_p_t

/-- `applyNat (CCX a b c)` commutes with `update _ p v` when `p` is
disjoint from `a`, `b`, and `c`. -/
theorem applyNat_CCX_commute_update_disjoint
    (a b c : Nat) (f : Nat → Bool) (p : Nat) (v : Bool)
    (h_p_a : p ≠ a) (h_p_b : p ≠ b) (h_p_c : p ≠ c) :
    Gate.applyNat (Gate.CCX a b c) (update f p v)
      = update (Gate.applyNat (Gate.CCX a b c) f) p v := by
  simp only [Gate.applyNat_CCX, update_neq _ _ _ _ h_p_a.symm,
             update_neq _ _ _ _ h_p_b.symm, update_neq _ _ _ _ h_p_c.symm]
  exact update_update_comm f p c v _ h_p_c

/-- Sequential composition of gates commutes with `update _ p v`
when each constituent gate does. -/
theorem applyNat_seq_commute_update
    (g₁ g₂ : Gate) (f : Nat → Bool) (p : Nat) (v : Bool)
    (h₁ : ∀ f', Gate.applyNat g₁ (update f' p v) = update (Gate.applyNat g₁ f') p v)
    (h₂ : ∀ f', Gate.applyNat g₂ (update f' p v) = update (Gate.applyNat g₂ f') p v) :
    Gate.applyNat (Gate.seq g₁ g₂) (update f p v)
      = update (Gate.applyNat (Gate.seq g₁ g₂) f) p v := by
  show Gate.applyNat g₂ (Gate.applyNat g₁ (update f p v))
    = update (Gate.applyNat g₂ (Gate.applyNat g₁ f)) p v
  rw [h₁ f, h₂ (Gate.applyNat g₁ f)]

/-- Unpatched first-reverse step commutes with update at `c[j]` (`j ≥ 1`). -/
theorem unpatched_first_reverse_commute_update_at_c_above
    (f : Nat → Bool) (j : Nat) (hj : j > 0) (v : Bool) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse (update f (carry_idx j) v)
      = update (Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f) (carry_idx j) v := by
  have h_cj_c0 : carry_idx j ≠ carry_idx 0 := by unfold carry_idx; omega
  have h_cj_t1 : carry_idx j ≠ target_idx 1 := by unfold carry_idx target_idx; omega
  have h_cj_r1 : carry_idx j ≠ read_idx 1 := by unfold carry_idx read_idx; omega
  have h_cj_r0 : carry_idx j ≠ read_idx 0 := by unfold carry_idx read_idx; omega
  have h_cj_t0 : carry_idx j ≠ target_idx 0 := by unfold carry_idx target_idx; omega
  unfold gidney_adder_bit_step_faithful_first_reverse
  apply applyNat_seq_commute_update _ _ _ _ _ ?_
    (fun _ => applyNat_CCX_commute_update_disjoint _ _ _ _ _ _ h_cj_r0 h_cj_t0 h_cj_c0)
  intro f'
  apply applyNat_seq_commute_update _ _ _ _ _
    (fun _ => applyNat_CX_commute_update_disjoint _ _ _ _ _ h_cj_c0 h_cj_t1)
    (fun _ => applyNat_CX_commute_update_disjoint _ _ _ _ _ h_cj_c0 h_cj_r1)

/-- Unpatched interior-reverse step commutes with update at `c[j]` (`j > i`). -/
theorem unpatched_interior_reverse_commute_update_at_c_above
    (i : Nat) (hi : 0 < i) (f : Nat → Bool) (j : Nat) (hj : j > i) (v : Bool) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i)
      (update f (carry_idx j) v)
      = update (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f)
          (carry_idx j) v := by
  have h_cj_ci : carry_idx j ≠ carry_idx i := by unfold carry_idx; omega
  have h_cj_ti1 : carry_idx j ≠ target_idx (i+1) := by unfold carry_idx target_idx; omega
  have h_cj_ri1 : carry_idx j ≠ read_idx (i+1) := by unfold carry_idx read_idx; omega
  have h_cj_cm1 : carry_idx j ≠ carry_idx (i-1) := by unfold carry_idx; omega
  have h_cj_ri : carry_idx j ≠ read_idx i := by unfold carry_idx read_idx; omega
  have h_cj_ti : carry_idx j ≠ target_idx i := by unfold carry_idx target_idx; omega
  unfold gidney_adder_bit_step_faithful_interior_reverse
  apply applyNat_seq_commute_update _ _ _ _ _ ?_
    (fun _ => applyNat_CCX_commute_update_disjoint _ _ _ _ _ _ h_cj_ri h_cj_ti h_cj_ci)
  intro f'
  apply applyNat_seq_commute_update _ _ _ _ _ ?_
    (fun _ => applyNat_CX_commute_update_disjoint _ _ _ _ _ h_cj_cm1 h_cj_ci)
  intro f''
  apply applyNat_seq_commute_update _ _ _ _ _
    (fun _ => applyNat_CX_commute_update_disjoint _ _ _ _ _ h_cj_ci h_cj_ti1)
    (fun _ => applyNat_CX_commute_update_disjoint _ _ _ _ _ h_cj_ci h_cj_ri1)

/-- Unpatched last-reverse step commutes with update at `c[j]` (`j > i`). -/
theorem unpatched_last_reverse_commute_update_at_c_above
    (i : Nat) (hi : 0 < i) (f : Nat → Bool) (j : Nat) (hj : j > i) (v : Bool) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) (update f (carry_idx j) v)
      = update (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f) (carry_idx j) v := by
  have h_cj_ci : carry_idx j ≠ carry_idx i := by unfold carry_idx; omega
  have h_cj_cm1 : carry_idx j ≠ carry_idx (i-1) := by unfold carry_idx; omega
  have h_cj_ri : carry_idx j ≠ read_idx i := by unfold carry_idx read_idx; omega
  have h_cj_ti : carry_idx j ≠ target_idx i := by unfold carry_idx target_idx; omega
  unfold gidney_adder_bit_step_faithful_last_reverse
  apply applyNat_seq_commute_update _ _ _ _ _
    (fun _ => applyNat_CX_commute_update_disjoint _ _ _ _ _ h_cj_cm1 h_cj_ci)
    (fun _ => applyNat_CCX_commute_update_disjoint _ _ _ _ _ _ h_cj_ri h_cj_ti h_cj_ci)

/-- Unpatched propagation cascade commutes with update at `c[j]` (`j > m`). -/
theorem unpatched_propagation_reverse_commute_update_at_c_above (m : Nat) :
    ∀ (g : Nat → Bool) (v : Bool) (j : Nat), j > m →
      Gate.applyNat (gidney_adder_forward_with_propagation_reverse (m + 1))
        (update g (carry_idx j) v)
        = update (Gate.applyNat (gidney_adder_forward_with_propagation_reverse (m + 1)) g)
            (carry_idx j) v := by
  induction m with
  | zero => intro g v j hj; exact unpatched_first_reverse_commute_update_at_c_above g j hj v
  | succ k' ih =>
      intro g v j hj
      show Gate.applyNat (gidney_adder_forward_with_propagation_reverse (k' + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (k' + 1))
              (update g (carry_idx j) v))
        = update (Gate.applyNat (gidney_adder_forward_with_propagation_reverse (k' + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (k' + 1)) g))
            (carry_idx j) v
      rw [unpatched_interior_reverse_commute_update_at_c_above (k' + 1) (by omega) g j (by omega) v]
      rw [ih _ v j (by omega)]

end FormalRV.BQAlgo
