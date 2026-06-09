/-
  FormalRV.Arithmetic.RippleCarryAdder.ForwardAndCost.LastBitAndSkeletonRev
  Faithful LAST bit-step + skeleton-reverse reversibility (part 4/5): last-bit
  correctness/cost/reversibility, the faithful-interior cascade correctness, and
  the simplified-bit-step reverse + proper-uncompute matrix involutions.
  Builds on `FirstBit`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.ForwardAndCost.FirstBit

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-- T-count of the last-bit step: 7 (1 Toffoli; CX is tcount-0). -/
theorem tcount_gidney_adder_bit_step_faithful_last (i : Nat) :
    tcount (gidney_adder_bit_step_faithful_last i) = 7 := by
  unfold gidney_adder_bit_step_faithful_last
  rfl

/-- Gate count of the last-bit step: **2** (vs interior's 4, first-
    bit's 3). The last bit drops both propagation CXs. -/
theorem gcount_gidney_adder_bit_step_faithful_last (i : Nat) :
    gcount (gidney_adder_bit_step_faithful_last i) = 2 := by
  unfold gidney_adder_bit_step_faithful_last
  rfl

/-- **Last-bit correctness on classical basis states** (Iter 67). -/
theorem gidney_adder_bit_step_faithful_last_correct
    (dim i : Nat) (f : Nat → Bool)
    (hri : read_idx i < dim) (hti : target_idx i < dim)
    (hci : carry_idx i < dim) (hcim1 : carry_idx (i - 1) < dim)
    (h_rt : read_idx i ≠ target_idx i)
    (h_rc : read_idx i ≠ carry_idx i)
    (h_tc : target_idx i ≠ carry_idx i)
    (h_cc : carry_idx (i - 1) ≠ carry_idx i) :
    uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_last i))
      * f_to_vec dim f
      = f_to_vec dim (gidney_last_bit_post_state i f) := by
  unfold gidney_adder_bit_step_faithful_last gidney_last_bit_post_state
  apply gate_seq_acts_on_basis dim _ _ f _ _
  · -- CCX: write (read ∧ target) into carry[i]
    exact gate_ccx_acts_on_basis dim _ _ _ hri hti hci h_rt h_rc h_tc f
  · -- CX (chain): write carry[i-1] into carry[i]
    exact gate_cx_acts_on_basis dim _ _ hcim1 hci h_cc _

/- Three-tier adder summary (regular comment, not docstring): per
   CLAUDE.md hard rules, the adder side now has Verified-tier
   coverage at all three boundary cases:
   - i = 0 (first bit): 3 gates (CCX + 2 propagation CXs), tcount=7,
     gcount=3. Iter 65 correctness.
   - i ≥ 1, not last (interior): 4 gates (CCX + chain + 2 prop),
     tcount=7, gcount=4. Iter 55-57 correctness.
   - i = last interior: 2 gates (CCX + chain), tcount=7, gcount=2.
     Iter 67 correctness (above).
   All three preserve the per-Toffoli figure (1 CCX = 7 T) but have
   different gate counts. The review's per-bit Toffoli count of q_A
   holds across all bit positions. -/

/-- **Forward · reverse (last-bit) = identity on basis states**.
    The two CX gates cancel (CX involution); the two CCX gates
    cancel (CCX involution). Composed correctly via the reusable
    framework. -/
theorem gidney_adder_bit_step_faithful_last_fwd_rev_id
    (dim i : Nat) (f : Nat → Bool)
    (hri : read_idx i < dim) (hti : target_idx i < dim)
    (hci : carry_idx i < dim) (hcim1 : carry_idx (i - 1) < dim)
    (h_rt : read_idx i ≠ target_idx i)
    (h_rc : read_idx i ≠ carry_idx i)
    (h_tc : target_idx i ≠ carry_idx i)
    (h_cc : carry_idx (i - 1) ≠ carry_idx i) :
    uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_bit_step_faithful_last i)
                        (gidney_adder_bit_step_faithful_last_reverse i)))
      * f_to_vec dim f
      = f_to_vec dim f := by
  -- The composition is (CCX; CX); (CX; CCX). uc_eval is right-to-
  -- left mul on seq, so the full matrix is uc_eval CCX * uc_eval CX
  -- * uc_eval CX * uc_eval CCX. Inner CX-pair = 1 (CNOT_CNOT_eq_one);
  -- outer CCX-pair = 1 (CCX_CCX_eq_one). Final matrix is 1; applied
  -- to f_to_vec gives f_to_vec.
  unfold gidney_adder_bit_step_faithful_last
         gidney_adder_bit_step_faithful_last_reverse
  -- Step 1: prove the composed matrix equals 1 (independent of v)
  have hM : uc_eval (Gate.toUCom dim
        (Gate.seq (Gate.seq
                    (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))
                    (Gate.CX (carry_idx (i - 1)) (carry_idx i)))
                  (Gate.seq
                    (Gate.CX (carry_idx (i - 1)) (carry_idx i))
                    (Gate.CCX (read_idx i) (target_idx i) (carry_idx i)))))
        = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
    -- Step a: collapse Gate.toUCom + uc_eval semantics. The outer seq
    -- evaluates as `uc_eval rev * uc_eval fwd`, etc.
    show (uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
          * uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i)))
          * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
             * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i))) = 1
    -- Step b: reassociate and use the seq-form involution lemmas
    -- (which are uc_eval (seq CNOT CNOT) = 1, etc., where uc_eval seq
    -- unfolds to right * left mul)
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (uc_eval (BaseUCom.CNOT _ _))
                            (uc_eval (BaseUCom.CNOT _ _))
                            (uc_eval (BaseUCom.CCX _ _ _))]
    -- `uc_eval CNOT * uc_eval CNOT` IS `uc_eval (seq CNOT CNOT)` by
    -- defeq; use `show` to align with CNOT_CNOT_eq_one's statement
    show uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
         * (uc_eval (UCom.seq (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
                              (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i)))
            * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)))
         = 1
    rw [CNOT_CNOT_eq_one dim (carry_idx (i - 1)) (carry_idx i) hcim1 hci h_cc]
    rw [Matrix.one_mul]
    -- Now: uc_eval CCX * uc_eval CCX = 1, again use seq form via show
    show uc_eval (UCom.seq (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
                           (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)))
         = 1
    exact CCX_CCX_eq_one dim _ _ _ hri hti hci h_rt h_rc h_tc
  -- Step 2: apply matrix · v = v when matrix = 1
  rw [hM, Matrix.one_mul]

/-- **Faithful n-bit cascade correctness**: given disjointness on each
    bit position 1..n, the cascade acts on `f_to_vec dim f` to produce
    `f_to_vec dim (gidney_cascade_post_state n f)`. Proof by induction
    on n. **First Verified-tier theorem for the n-bit Gidney
    adder forward cascade.** -/
theorem gidney_adder_forward_faithful_interior_correct
    (dim : Nat) (hdim : 0 < dim) (f : Nat → Bool) :
    ∀ n, (∀ i, 1 ≤ i → i ≤ n → BitDisjointness dim i) →
    uc_eval (Gate.toUCom dim (gidney_adder_forward_faithful_interior n))
      * f_to_vec dim f
      = f_to_vec dim (gidney_cascade_post_state n f)
  | 0    , _ => by
      show uc_eval (Gate.toUCom dim Gate.I) * f_to_vec dim f = f_to_vec dim f
      rw [Gate.toUCom_I]
      show uc_eval (BaseUCom.ID 0 : BaseUCom dim) * f_to_vec dim f
            = f_to_vec dim f
      rw [uc_eval_ID_eq_one hdim, Matrix.one_mul]
  | n + 1, hyp => by
      show uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_forward_faithful_interior n)
                        (gidney_adder_bit_step_faithful_interior (n + 1))))
            * f_to_vec dim f
            = f_to_vec dim (gidney_cascade_post_state (n + 1) f)
      apply gate_seq_acts_on_basis dim _ _ f (gidney_cascade_post_state n f) _
      · -- IH: cascade of n bits is correct
        exact gidney_adder_forward_faithful_interior_correct dim hdim f n
                (fun i h1 hn => hyp i h1 (Nat.le_succ_of_le hn))
      · -- Per-bit correctness at i = n+1, applied to the post-cascade state
        have d := hyp (n + 1) (Nat.le_add_left 1 n) (Nat.le_refl _)
        exact gidney_adder_bit_step_faithful_interior_correct
                dim (n + 1) _
                d.hri d.hti d.hci d.hcim1 d.hri1 d.hti1
                d.h_rt d.h_rc d.h_tc d.h_cc d.h_ci_ri1 d.h_ci_ti1

/-- Action of the simplified `gidney_adder_bit_step (i+1)` on basis
    states: XORs `(read[i+1] ∧ target[i+1]) ⊕ carry[i]` into `carry[i+1]`.
    **This is NOT Gidney's actual carry** (see review-gap note above);
    proving it here makes the discrepancy explicit. -/
theorem gidney_adder_bit_step_succ_simplified (dim i : Nat) (f : Nat → Bool)
    (hri : read_idx (i+1) < dim) (hti : target_idx (i+1) < dim)
    (hci : carry_idx (i+1) < dim) (hci' : carry_idx i < dim)
    (hrt : read_idx (i+1) ≠ target_idx (i+1))
    (hrc : read_idx (i+1) ≠ carry_idx (i+1))
    (htc : target_idx (i+1) ≠ carry_idx (i+1))
    (hcc : carry_idx i ≠ carry_idx (i+1)) :
    let f' := update f (carry_idx (i+1))
                (xor (f (carry_idx (i+1)))
                     (f (read_idx (i+1)) && f (target_idx (i+1))))
    uc_eval (Gate.toUCom dim (gidney_adder_bit_step (i+1))) * f_to_vec dim f
      = f_to_vec dim
          (update f' (carry_idx (i+1))
            (xor (f' (carry_idx (i+1))) (f' (carry_idx i)))) := by
  intro f'
  -- gidney_adder_bit_step (i+1) ↦ Gate.seq (CCX ...) (CX carry[i] carry[i+1])
  show uc_eval (Gate.toUCom dim
          (Gate.seq (Gate.CCX (read_idx (i+1)) (target_idx (i+1))
                              (carry_idx (i+1)))
                    (Gate.CX (carry_idx i) (carry_idx (i+1)))))
        * f_to_vec dim f = _
  apply gate_seq_acts_on_basis dim _ _ f f' _
  · -- First gate (CCX) acts: XOR (read ∧ target) into carry
    exact gate_ccx_acts_on_basis dim _ _ _ hri hti hci hrt hrc htc f
  · -- Second gate (CX) acts on the post-CCX state f': XOR f'(carry[i]) into f'(carry[i+1])
    exact gate_cx_acts_on_basis dim (carry_idx i) (carry_idx (i+1))
            hci' hci hcc f'

/-- T-count of the gate-reverse: same 7 as forward (same gates, swapped order). -/
theorem tcount_gidney_adder_bit_step_reverse (i : Nat) :
    tcount (gidney_adder_bit_step_reverse i) = 7 := by
  unfold gidney_adder_bit_step_reverse
  split <;> rfl

/-- Gate-count of the gate-reverse: 1 at i=0, 2 at i>0 (matches forward). -/
theorem gcount_gidney_adder_bit_step_reverse (i : Nat) :
    gcount (gidney_adder_bit_step_reverse i) = (if i = 0 then 1 else 2) := by
  unfold gidney_adder_bit_step_reverse
  split <;> rfl

/-- **Matrix-level per-bit involution**: `bit_step i · bit_step_reverse i = 1`.
    Proven for all `i` (both branches) under the standard bit-disjointness
    hypotheses. The i = 0 branch needs `read_idx 0 = 0, target_idx 0 = 1,
    carry_idx 0 = 2` (auto-derived from the `read_idx`/`target_idx`/`carry_idx`
    defs and the disjointness hypotheses); the i > 0 branch mirrors
    `gidney_adder_bit_step_faithful_last_fwd_rev_id` (Iter 69) structurally.

    **This is the per-bit collapse used in Iter 74's cascade induction**:
    `uc_eval (cascade (n+1) · uncompute (n+1))` re-associates to
    `uc_eval (cascade n) · uc_eval (bit_step n · bit_step_reverse n)
     · uc_eval (uncompute n)`, and the middle factor collapses to 1
    by this lemma. -/
theorem gidney_adder_bit_step_fwd_rev_eq_one (dim i : Nat)
    (hri : read_idx i < dim) (hti : target_idx i < dim)
    (hci : carry_idx i < dim)
    (h_rt : read_idx i ≠ target_idx i)
    (h_rc : read_idx i ≠ carry_idx i)
    (h_tc : target_idx i ≠ carry_idx i)
    (hcim1 : i ≠ 0 → carry_idx (i - 1) < dim)
    (h_cc : i ≠ 0 → carry_idx (i - 1) ≠ carry_idx i) :
    uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_bit_step i)
                        (gidney_adder_bit_step_reverse i)))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  by_cases hi0 : i = 0
  · -- i = 0: both reduce to the same single CCX; hcim1/h_cc not needed
    subst hi0
    have e1 : gidney_adder_bit_step 0
            = Gate.CCX (read_idx 0) (target_idx 0) (carry_idx 0) := by
      unfold gidney_adder_bit_step; rfl
    have e2 : gidney_adder_bit_step_reverse 0
            = Gate.CCX (read_idx 0) (target_idx 0) (carry_idx 0) := by
      unfold gidney_adder_bit_step_reverse; rfl
    rw [e1, e2, Gate.toUCom_seq, Gate.toUCom_CCX]
    show uc_eval (UCom.seq (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0)
                            : BaseUCom dim)
                           (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0))) = 1
    exact CCX_CCX_eq_one dim _ _ _ hri hti hci h_rt h_rc h_tc
  · -- i ≠ 0: (CCX·CX) · (CX·CCX) collapses via CNOT involution then CCX involution
    have hcim1' := hcim1 hi0
    have h_cc' := h_cc hi0
    have e1 : gidney_adder_bit_step i =
        Gate.seq (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))
                 (Gate.CX (carry_idx (i - 1)) (carry_idx i)) := by
      unfold gidney_adder_bit_step; rw [if_neg hi0]
    have e2 : gidney_adder_bit_step_reverse i =
        Gate.seq (Gate.CX (carry_idx (i - 1)) (carry_idx i))
                 (Gate.CCX (read_idx i) (target_idx i) (carry_idx i)) := by
      unfold gidney_adder_bit_step_reverse; rw [if_neg hi0]
    rw [e1, e2]
    -- Mirror Iter 69's proof structure (lines 908-945)
    show (uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
          * uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i)))
          * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
             * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i))) = 1
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (uc_eval (BaseUCom.CNOT _ _))
                            (uc_eval (BaseUCom.CNOT _ _))
                            (uc_eval (BaseUCom.CCX _ _ _))]
    show uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
         * (uc_eval (UCom.seq (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
                              (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i)))
            * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)))
         = 1
    rw [CNOT_CNOT_eq_one dim (carry_idx (i - 1)) (carry_idx i) hcim1' hci h_cc']
    rw [Matrix.one_mul]
    show uc_eval (UCom.seq (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)
                            : BaseUCom dim)
                           (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i))) = 1
    exact CCX_CCX_eq_one dim _ _ _ hri hti hci h_rt h_rc h_tc

/-- T-count of the proper reverse: 7n (same gates, reversed). -/
theorem tcount_gidney_adder_uncompute_proper (n : Nat) :
    tcount (gidney_adder_uncompute_proper n) = 7 * n := by
  induction n with
  | zero => decide
  | succ n ih =>
    show tcount (Gate.seq (gidney_adder_bit_step_reverse n)
                          (gidney_adder_uncompute_proper n))
           = 7 * (n + 1)
    simp [tcount, ih, tcount_gidney_adder_bit_step_reverse]
    omega

/-- **Matrix-level forward · proper-uncompute = identity**. The
    n-bit Gidney forward cascade composed with its proper
    (gate-reversed) uncomputation is the identity matrix. Proof
    by structural recursion on n, mirroring Iter 74's
    `prefix_and_cascade_uncompute_eq_one`.

    **Hypothesis**: a single `3 * n ≤ dim` bound suffices (the
    highest qubit touched at bit position k is `carry_idx k = 3k+2`,
    so all bits 0..n-1 fit when `3n ≤ dim`).

    **Fourth Verified-tier review chain** (adder side, mirror of
    Iter 74). Confirms that the simplified-bit-step forward cascade
    IS reversible by its proper inverse without measurement. -/
theorem gidney_adder_forward_uncompute_proper_eq_one
    (dim : Nat) (hdim : 0 < dim) :
    ∀ n, 3 * n ≤ dim →
    uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_forward n)
                        (gidney_adder_uncompute_proper n)))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ)
  | 0    , _ => by
      -- forward 0 = uncompute_proper 0 = Gate.I. uc_eval(seq I I) = 1·1 = 1.
      show uc_eval (Gate.toUCom dim (Gate.I : Gate)) *
             uc_eval (Gate.toUCom dim (Gate.I : Gate)) = 1
      rw [Gate.toUCom_I, uc_eval_ID_eq_one hdim, Matrix.one_mul]
  | n + 1, hbnd => by
      have ih : uc_eval (Gate.toUCom dim
                  (Gate.seq (gidney_adder_forward n)
                            (gidney_adder_uncompute_proper n))) = 1 := by
        apply gidney_adder_forward_uncompute_proper_eq_one dim hdim n
        omega
      -- Derive disjointness for bit position n from the cascade-dim bound.
      have hri  : read_idx n < dim := by unfold read_idx; omega
      have hti  : target_idx n < dim := by unfold target_idx; omega
      have hci  : carry_idx n < dim := by unfold carry_idx; omega
      have h_rt : read_idx n ≠ target_idx n := by
        unfold read_idx target_idx; omega
      have h_rc : read_idx n ≠ carry_idx n := by
        unfold read_idx carry_idx; omega
      have h_tc : target_idx n ≠ carry_idx n := by
        unfold target_idx carry_idx; omega
      have hcim1 : n ≠ 0 → carry_idx (n - 1) < dim := fun _ => by
        unfold carry_idx; omega
      have h_cc : n ≠ 0 → carry_idx (n - 1) ≠ carry_idx n := fun hne => by
        unfold carry_idx
        -- n ≠ 0 implies n ≥ 1, so 3*(n-1) + 2 = 3n - 1 ≠ 3n + 2
        have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hne
        omega
      have hstep := gidney_adder_bit_step_fwd_rev_eq_one dim n
                     hri hti hci h_rt h_rc h_tc hcim1 h_cc
      -- After pattern-match, the goal WHNF-reduces to the 4-factor form
      show (uc_eval (Gate.toUCom dim (gidney_adder_uncompute_proper n))
              * uc_eval (Gate.toUCom dim (gidney_adder_bit_step_reverse n)))
            * (uc_eval (Gate.toUCom dim (gidney_adder_bit_step n))
              * uc_eval (Gate.toUCom dim (gidney_adder_forward n))) = 1
      rw [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc
            (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_reverse n)))
            (uc_eval (Gate.toUCom dim (gidney_adder_bit_step n)))
            (uc_eval (Gate.toUCom dim (gidney_adder_forward n)))]
      -- Middle pair = uc_eval (toUCom (seq bit_step bit_step_reverse)) by defeq
      show uc_eval (Gate.toUCom dim (gidney_adder_uncompute_proper n)) *
            (uc_eval (Gate.toUCom dim
                       (Gate.seq (gidney_adder_bit_step n)
                                 (gidney_adder_bit_step_reverse n)))
              * uc_eval (Gate.toUCom dim (gidney_adder_forward n))) = 1
      rw [hstep, Matrix.one_mul]
      exact ih

end FormalRV.BQAlgo
