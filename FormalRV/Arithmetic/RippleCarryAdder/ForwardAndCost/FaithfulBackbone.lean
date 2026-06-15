/-
  FormalRV.Arithmetic.RippleCarryAdder.ForwardAndCost.FaithfulBackbone
  BACKBONE (part 5/5): the faithful full forward/reverse cascade — costs
  (`tcount_gidney_adder_full_faithful_no_measurement` = 14·(n+2)), basis-state
  correctness (`gidney_adder_forward_faithful_full_correct`), cascade-level
  reversibility (`..._fwd_rev_eq_one`), and the measurement-gap factor.
  Builds on `LastBitAndSkeletonRev`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.ForwardAndCost.LastBitAndSkeletonRev

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-- T-count of the propagation cascade: `7n` (each bit contributes
    1 Toffoli). -/
theorem tcount_gidney_adder_forward_with_propagation : ∀ n,
    tcount (gidney_adder_forward_with_propagation n) = 7 * n
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      show tcount (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                            (gidney_adder_bit_step_faithful_interior (n + 1)))
            = 7 * (n + 2)
      simp [tcount, tcount_gidney_adder_forward_with_propagation (n + 1),
            tcount_gidney_adder_bit_step_faithful_interior]
      omega

/-- Gate-count of the propagation cascade. Bit 0 contributes 3
    gates (1 CCX + 2 propagation CXs); each interior bit
    contributes 4 (1 CCX + 1 chain CX + 2 propagation CXs).
    Total: `3 + 4·(n-1) = 4n - 1` for `n ≥ 1`.

    Edge cases: `n=0` gives 0 gates; for n ≥ 1 the formula
    `4n - 1` holds. We state it as `4n + (if n = 0 then 0 else -1)`
    to handle both cleanly — but Nat doesn't support negative,
    so we split into two clauses. -/
theorem gcount_gidney_adder_forward_with_propagation : ∀ n,
    gcount (gidney_adder_forward_with_propagation n)
      = if n = 0 then 0 else 4 * n - 1
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      show gcount (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                            (gidney_adder_bit_step_faithful_interior (n + 1)))
            = if (n + 2) = 0 then 0 else 4 * (n + 2) - 1
      rw [if_neg (Nat.succ_ne_zero (n + 1))]
      have ih := gcount_gidney_adder_forward_with_propagation (n + 1)
      rw [if_neg (Nat.succ_ne_zero n)] at ih
      show gcount (gidney_adder_forward_with_propagation (n + 1))
            + gcount (gidney_adder_bit_step_faithful_interior (n + 1))
            = 4 * (n + 2) - 1
      rw [ih, gcount_gidney_adder_bit_step_faithful_interior]
      omega

/-- T-count of the faithful full forward cascade: `7n` for `n ≥ 2`.
    Matches qianxu Eq. E3's `q_A` Toffolis per adder (T-count =
    7 · q_A). -/
theorem tcount_gidney_adder_forward_faithful_full (n : Nat) :
    tcount (gidney_adder_forward_faithful_full (n + 2)) = 7 * (n + 2) := by
  show tcount (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                        (gidney_adder_bit_step_faithful_last (n + 1)))
        = 7 * (n + 2)
  simp [tcount, tcount_gidney_adder_forward_with_propagation,
        tcount_gidney_adder_bit_step_faithful_last]
  omega

/-- **Cost-equivalence (Iter 53 review-gap closure).** The COST-ONLY skeleton forward pass
    (`gidney_adder_forward`, which is *not* semantically the adder) and the semantically-correct
    faithful forward pass (`gidney_adder_forward_faithful_full`, proven on basis states) have the
    **same T-count**.  (The Shor cost model now binds *directly* to the faithful adder via
    `adderToff_eq`; this records that the deprecated skeleton was always cost-equivalent — the
    gates it omits are carry-propagation CXs, which are T-free.) -/
theorem gidney_cost_skeleton_eq_faithful (n : Nat) :
    tcount (gidney_adder_forward (n + 2))
      = tcount (gidney_adder_forward_faithful_full (n + 2)) := by
  rw [tcount_gidney_adder_forward, tcount_gidney_adder_forward_faithful_full]

/-- Gate-count of the faithful full forward cascade: `4n - 3` for
    `n ≥ 2`. Decomposes as 3 (first) + 4·(n-2) (interiors) + 2
    (last) = 4n - 3. -/
theorem gcount_gidney_adder_forward_faithful_full (n : Nat) :
    gcount (gidney_adder_forward_faithful_full (n + 2)) = 4 * (n + 2) - 3 := by
  show gcount (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                        (gidney_adder_bit_step_faithful_last (n + 1)))
        = 4 * (n + 2) - 3
  have hp := gcount_gidney_adder_forward_with_propagation (n + 1)
  rw [if_neg (Nat.succ_ne_zero n)] at hp
  show gcount (gidney_adder_forward_with_propagation (n + 1))
        + gcount (gidney_adder_bit_step_faithful_last (n + 1))
        = 4 * (n + 2) - 3
  rw [hp, gcount_gidney_adder_bit_step_faithful_last]
  omega

/-- Concrete: 4-bit faithful Gidney adder = 28 T-gates = 4 Toffolis.
    (Matches `qq_gidney_adder.py` for a 4-bit instance.) -/
example : tcount (gidney_adder_forward_faithful_full 4) = 28 :=
  tcount_gidney_adder_forward_faithful_full 2

/-- Concrete: 33-bit faithful Gidney adder (RSA-2048 q_A=33 block) =
    231 T-gates = 33 Toffolis. -/
example : tcount (gidney_adder_forward_faithful_full 33) = 7 * 33 :=
  tcount_gidney_adder_forward_faithful_full 31

/-- **Propagation cascade correctness**: given a single dim-bound
    `3 * n + 2 ≤ dim` (covering all qubits up through bit position
    n-1's propagation to bit n), the cascade acts on `f_to_vec dim f`
    to produce `f_to_vec dim (gidney_propagation_post_state n f)`.

    Proof by structural recursion on the three-clause def:
    - n=0: Gate.I, trivially preserves.
    - n=1: apply `gidney_adder_bit_step_faithful_first_correct` with
      first-bit disjointness derived from dim ≥ 5.
    - n+2: `gate_seq_acts_on_basis` + IH (propagation n+1) +
      per-bit interior correctness at position n+1 (via
      `bit_disjointness_of_dim_bound`). -/
theorem gidney_adder_forward_with_propagation_correct
    (dim : Nat) (hdim : 0 < dim) (f : Nat → Bool) :
    ∀ n, 3 * n + 2 ≤ dim →
    uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation n))
      * f_to_vec dim f
      = f_to_vec dim (gidney_propagation_post_state n f)
  | 0    , _ => by
      show uc_eval (Gate.toUCom dim (Gate.I : Gate)) * f_to_vec dim f = f_to_vec dim f
      rw [Gate.toUCom_I, uc_eval_ID_eq_one hdim, Matrix.one_mul]
  | 1    , hbd => by
      -- propagation 1 = first; apply first-bit correctness
      show uc_eval (Gate.toUCom dim gidney_adder_bit_step_faithful_first)
            * f_to_vec dim f = f_to_vec dim (gidney_first_bit_post_state f)
      have fb := first_bit_disjointness_of_dim_bound dim (by omega : 5 ≤ dim)
      obtain ⟨hr0, ht0, hc0, hr1, ht1, h_rt0, h_rc0, h_tc0, h_c_r1, h_c_t1⟩ := fb
      exact gidney_adder_bit_step_faithful_first_correct dim f
              hr0 ht0 hc0 hr1 ht1 h_rt0 h_rc0 h_tc0 h_c_r1 h_c_t1
  | n + 2, hbd => by
      show uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                        (gidney_adder_bit_step_faithful_interior (n + 1))))
            * f_to_vec dim f
            = f_to_vec dim (gidney_propagation_post_state (n + 2) f)
      apply gate_seq_acts_on_basis dim _ _ f
              (gidney_propagation_post_state (n + 1) f) _
      · exact gidney_adder_forward_with_propagation_correct dim hdim f (n + 1)
                (by omega)
      · have d := bit_disjointness_of_dim_bound dim (n + 1)
                    (by omega) (by omega)
        exact gidney_adder_bit_step_faithful_interior_correct
                dim (n + 1) _
                d.hri d.hti d.hci d.hcim1 d.hri1 d.hti1
                d.h_rt d.h_rc d.h_tc d.h_cc d.h_ci_ri1 d.h_ci_ti1

/-- **Faithful full forward cascade correctness** (Phase A review
    anchor at the basis-state level): on `(n+2)`-bit input `f`, the
    cascade `gidney_adder_forward_faithful_full (n+2)` acts as
    `gidney_forward_faithful_full_post_state (n+2)` on basis states.

    Combines `gidney_adder_forward_with_propagation_correct`
    (propagation, this iter) with `gidney_adder_bit_step_faithful_last_correct`
    (last bit, Iter 67). Single dim-bound hypothesis `3*(n+2) ≤ dim`
    covers all qubits including the (n+1)-th carry. -/
theorem gidney_adder_forward_faithful_full_correct
    (dim : Nat) (hdim : 0 < dim) (f : Nat → Bool) (n : Nat)
    (hbd : 3 * (n + 2) ≤ dim) :
    uc_eval (Gate.toUCom dim (gidney_adder_forward_faithful_full (n + 2)))
      * f_to_vec dim f
      = f_to_vec dim (gidney_forward_faithful_full_post_state (n + 2) f) := by
  show uc_eval (Gate.toUCom dim
          (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                    (gidney_adder_bit_step_faithful_last (n + 1))))
        * f_to_vec dim f
        = f_to_vec dim
            (gidney_last_bit_post_state (n + 1)
              (gidney_propagation_post_state (n + 1) f))
  apply gate_seq_acts_on_basis dim _ _ f
          (gidney_propagation_post_state (n + 1) f) _
  · -- Propagation cascade correctness (just proven above)
    exact gidney_adder_forward_with_propagation_correct dim hdim f (n + 1)
            (by omega)
  · -- Last-bit correctness at position n+1
    -- The propagation cascade's post-state has the same qubit layout as f
    -- (only modifies certain qubits, all of them < dim by the dim bound).
    -- last-bit needs: read_(n+1), target_(n+1), carry_(n+1), carry_n < dim
    --  + pairwise disjoint indices.
    exact gidney_adder_bit_step_faithful_last_correct dim (n + 1) _
            (by unfold read_idx; omega)
            (by unfold target_idx; omega)
            (by unfold carry_idx; omega)
            (by unfold carry_idx; omega)
            (by unfold read_idx target_idx; omega)
            (by unfold read_idx carry_idx; omega)
            (by unfold target_idx carry_idx; omega)
            (by unfold carry_idx; omega)

/-- **Final CX cascade correctness** on classical basis states.
    Single dim-bound hypothesis `3 * n ≤ dim` covers all qubits
    `target_idx (n-1) = 3n - 2 < dim` (for n ≥ 1).

    Proof by structural recursion on `n`:
    - n = 0: cascade is `Gate.I`; trivially preserves.
    - n + 1: `gate_seq_acts_on_basis` + IH + per-step
      `gate_cx_acts_on_basis` with disjointness via `omega`. -/
theorem gidney_final_cx_cascade_correct
    (dim : Nat) (hdim : 0 < dim) (f : Nat → Bool) :
    ∀ n, 3 * n ≤ dim →
    uc_eval (Gate.toUCom dim (gidney_final_cx_cascade n)) * f_to_vec dim f
      = f_to_vec dim (gidney_final_cx_cascade_post_state n f)
  | 0    , _   => by
      show uc_eval (Gate.toUCom dim (Gate.I : Gate)) * f_to_vec dim f = f_to_vec dim f
      rw [Gate.toUCom_I, uc_eval_ID_eq_one hdim, Matrix.one_mul]
  | n + 1, hbd => by
      show uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_final_cx_cascade n)
                        (Gate.CX (read_idx n) (target_idx n))))
            * f_to_vec dim f
            = f_to_vec dim (gidney_final_cx_cascade_post_state (n + 1) f)
      apply gate_seq_acts_on_basis dim _ _ f
              (gidney_final_cx_cascade_post_state n f) _
      · -- IH
        exact gidney_final_cx_cascade_correct dim hdim f n (by omega)
      · -- Per-step CX correctness
        exact gate_cx_acts_on_basis dim _ _
                (by unfold read_idx; omega)
                (by unfold target_idx; omega)
                (by unfold read_idx target_idx; omega)
                _

/-- T-count of the propagation reverse cascade: 7n (same gates as
    forward, reversed). -/
theorem tcount_gidney_adder_forward_with_propagation_reverse : ∀ n,
    tcount (gidney_adder_forward_with_propagation_reverse n) = 7 * n
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      show tcount (Gate.seq (gidney_adder_bit_step_faithful_interior_reverse (n + 1))
                            (gidney_adder_forward_with_propagation_reverse (n + 1)))
            = 7 * (n + 2)
      simp [tcount,
            tcount_gidney_adder_bit_step_faithful_interior_reverse,
            tcount_gidney_adder_forward_with_propagation_reverse (n + 1)]
      omega

/-- T-count of the faithful full reverse cascade: 7n for `n ≥ 2`. -/
theorem tcount_gidney_adder_forward_faithful_full_reverse (n : Nat) :
    tcount (gidney_adder_forward_faithful_full_reverse (n + 2)) = 7 * (n + 2) := by
  show tcount (Gate.seq (gidney_adder_bit_step_faithful_last_reverse (n + 1))
                        (gidney_adder_forward_with_propagation_reverse (n + 1)))
        = 7 * (n + 2)
  -- last_reverse i = seq (CX_chain) (CCX), so tcount = 7
  have h_last : tcount (gidney_adder_bit_step_faithful_last_reverse (n + 1)) = 7 := by
    unfold gidney_adder_bit_step_faithful_last_reverse
    rfl
  simp [tcount, h_last,
        tcount_gidney_adder_forward_with_propagation_reverse]
  omega

/-- **Cascade-level forward · reverse = identity** for the propagation
    cascade. By structural recursion on `n`: collapse the middle
    `interior fwd · interior rev` pair via Iter 82's
    `..._interior_fwd_rev_eq_one`, then apply IH.

    Base cases:
    - n = 0: both are Gate.I; product is ID·ID = 1.
    - n = 1: just first_fwd · first_rev = 1 by Iter 81's involution.

    Inductive step n+2: `(forward (n+1) ; interior (n+1)) ;
                         (interior_reverse (n+1) ; reverse (n+1))`.
    Reassociate matrix product, collapse middle interior pair via
    Iter 82, drop via Matrix.one_mul, apply IH on forward (n+1) ·
    reverse (n+1). -/
theorem gidney_adder_forward_with_propagation_fwd_rev_eq_one
    (dim : Nat) (hdim : 0 < dim) :
    ∀ n, 3 * n + 2 ≤ dim →
    uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_forward_with_propagation n)
                        (gidney_adder_forward_with_propagation_reverse n)))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ)
  | 0    , _ => by
      show uc_eval (Gate.toUCom dim (Gate.I : Gate)) *
             uc_eval (Gate.toUCom dim (Gate.I : Gate)) = 1
      rw [Gate.toUCom_I, uc_eval_ID_eq_one hdim, Matrix.one_mul]
  | 1    , hbd => by
      -- propagation 1 = first; apply Iter 81's first-bit involution.
      show uc_eval (Gate.toUCom dim
              (Gate.seq gidney_adder_bit_step_faithful_first
                        gidney_adder_bit_step_faithful_first_reverse)) = 1
      have fb := first_bit_disjointness_of_dim_bound dim (by omega : 5 ≤ dim)
      obtain ⟨hr0, ht0, hc0, hr1, ht1, h_rt, h_rc, h_tc, h_c_r1, h_c_t1⟩ := fb
      exact gidney_adder_bit_step_faithful_first_fwd_rev_eq_one dim
              hr0 ht0 hc0 hr1 ht1 h_rt h_rc h_tc h_c_r1 h_c_t1
  | n + 2, hbd => by
      have ih : uc_eval (Gate.toUCom dim
                  (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                            (gidney_adder_forward_with_propagation_reverse (n + 1)))) = 1 := by
        apply gidney_adder_forward_with_propagation_fwd_rev_eq_one dim hdim (n + 1)
        omega
      have d := bit_disjointness_of_dim_bound dim (n + 1) (by omega) (by omega)
      have hstep := gidney_adder_bit_step_faithful_interior_fwd_rev_eq_one
                      dim (n + 1) d.hri d.hti d.hci d.hcim1 d.hri1 d.hti1
                      d.h_rt d.h_rc d.h_tc d.h_cc d.h_ci_ri1 d.h_ci_ti1
      -- Goal after pattern-match:
      -- uc_eval (toUCom (seq (seq fwd_(n+1) interior_(n+1))
      --                      (seq interior_rev_(n+1) rev_(n+1)))) = 1
      -- Which is uc_eval(rev_(n+1)) * uc_eval(interior_rev_(n+1))
      --        * uc_eval(interior_(n+1)) * uc_eval(fwd_(n+1)) = 1.
      show (uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation_reverse (n + 1)))
              * uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_interior_reverse (n + 1))))
            * (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_interior (n + 1)))
              * uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation (n + 1)))) = 1
      rw [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc
            (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_interior_reverse (n + 1))))
            (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_interior (n + 1))))
            (uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation (n + 1))))]
      -- Middle pair = uc_eval (toUCom (seq interior interior_reverse)) by defeq.
      show uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation_reverse (n + 1)))
            * (uc_eval (Gate.toUCom dim
                         (Gate.seq (gidney_adder_bit_step_faithful_interior (n + 1))
                                   (gidney_adder_bit_step_faithful_interior_reverse (n + 1))))
              * uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation (n + 1)))) = 1
      rw [hstep, Matrix.one_mul]
      exact ih

/-- **Faithful full forward · reverse = identity (cascade level)**
    for the `(n+2)`-bit Gidney adder. Combines
    `..._with_propagation_fwd_rev_eq_one` (propagation cascade) +
    Iter 69's `..._last_fwd_rev_id` (last bit) via matrix reassociation. -/
theorem gidney_adder_forward_faithful_full_fwd_rev_eq_one
    (dim : Nat) (hdim : 0 < dim) (n : Nat)
    (hbd : 3 * (n + 2) ≤ dim) :
    uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                        (gidney_adder_forward_faithful_full_reverse (n + 2))))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  -- After pattern match, the full faithful's def expands to:
  --   seq (seq propagation_(n+1) last_(n+1)) (seq last_reverse_(n+1) propagation_reverse_(n+1))
  -- uc_eval = uc_eval(prop_rev_(n+1)) * uc_eval(last_rev_(n+1))
  --         * uc_eval(last_(n+1)) * uc_eval(prop_(n+1))
  have hprop : uc_eval (Gate.toUCom dim
                (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                          (gidney_adder_forward_with_propagation_reverse (n + 1)))) = 1 := by
    apply gidney_adder_forward_with_propagation_fwd_rev_eq_one dim hdim (n + 1)
    omega
  -- Iter 69's last-bit fwd·rev acts on f_to_vec; we need its matrix-level form.
  -- Iter 69's `..._faithful_last_fwd_rev_id` is f_to_vec form;
  -- We need to extract a matrix-level lemma. Let's use matrix_eq_of_basis_action.
  -- Actually, we have it from Iter 67 last-bit's f_to_vec correctness composed with
  -- the reverse direction. Let me use a direct approach:
  -- last_(n+1) followed by last_reverse_(n+1) at gate level is exactly CCX·CX·CX·CCX,
  -- which is uc_eval CCX * uc_eval CX * uc_eval CX * uc_eval CCX in matrix form.
  -- CX·CX = 1 and CCX·CCX = 1, so the product is 1.
  -- Construct this inline (like Iter 69 did at the f_to_vec level, but matrix-level):
  have hlast : uc_eval (Gate.toUCom dim
                (Gate.seq (gidney_adder_bit_step_faithful_last (n + 1))
                          (gidney_adder_bit_step_faithful_last_reverse (n + 1)))) = 1 := by
    unfold gidney_adder_bit_step_faithful_last
           gidney_adder_bit_step_faithful_last_reverse
    -- Forward: CCX ; CX(chain). Reverse: CX(chain) ; CCX.
    -- uc_eval(fwd) = CX_chain * CCX. uc_eval(rev) = CCX * CX_chain.
    -- Compose: (CCX * CX_chain) * (CX_chain * CCX) = CCX * (CX_chain * CX_chain) * CCX.
    show (uc_eval (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1))
                    : BaseUCom dim)
          * uc_eval (BaseUCom.CNOT (carry_idx (n + 1 - 1)) (carry_idx (n + 1))))
          * (uc_eval (BaseUCom.CNOT (carry_idx (n + 1 - 1)) (carry_idx (n + 1)))
            * uc_eval (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1)))) = 1
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc
          (uc_eval (BaseUCom.CNOT (carry_idx (n + 1 - 1)) (carry_idx (n + 1)) : BaseUCom dim))
          (uc_eval (BaseUCom.CNOT (carry_idx (n + 1 - 1)) (carry_idx (n + 1))))
          (uc_eval (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1))))]
    show uc_eval (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1))
                  : BaseUCom dim)
          * (uc_eval (UCom.seq (BaseUCom.CNOT (carry_idx (n + 1 - 1)) (carry_idx (n + 1))
                                : BaseUCom dim)
                               (BaseUCom.CNOT (carry_idx (n + 1 - 1)) (carry_idx (n + 1))))
            * uc_eval (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1)))) = 1
    rw [CNOT_CNOT_eq_one dim (carry_idx (n + 1 - 1)) (carry_idx (n + 1))
          (by unfold carry_idx; omega) (by unfold carry_idx; omega)
          (by unfold carry_idx; omega)]
    rw [Matrix.one_mul]
    show uc_eval (UCom.seq (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1))
                            : BaseUCom dim)
                           (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1)))) = 1
    exact CCX_CCX_eq_one dim _ _ _
            (by unfold read_idx; omega)
            (by unfold target_idx; omega)
            (by unfold carry_idx; omega)
            (by unfold read_idx target_idx; omega)
            (by unfold read_idx carry_idx; omega)
            (by unfold target_idx carry_idx; omega)
  -- Combine: full = seq (seq prop last) (seq last_rev prop_rev).
  show (uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation_reverse (n + 1)))
          * uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_last_reverse (n + 1))))
        * (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_last (n + 1)))
          * uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation (n + 1)))) = 1
  rw [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
        (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_last_reverse (n + 1))))
        (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_last (n + 1))))
        (uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation (n + 1))))]
  -- Middle pair = uc_eval(toUCom(seq last last_reverse)) by defeq
  show uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation_reverse (n + 1)))
        * (uc_eval (Gate.toUCom dim
                     (Gate.seq (gidney_adder_bit_step_faithful_last (n + 1))
                               (gidney_adder_bit_step_faithful_last_reverse (n + 1))))
          * uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation (n + 1)))) = 1
  rw [hlast, Matrix.one_mul]
  exact hprop

/-- T-count of the full no-measurement faithful adder for `(n+2)`
    bits: `14(n+2)`. Derived from the gate sequence:
    7(n+2) (forward) + 0 (final CX = pure CXs) + 7(n+2) (reverse). -/
theorem tcount_gidney_adder_full_faithful_no_measurement (n : Nat) :
    tcount (gidney_adder_full_faithful_no_measurement (n + 2)) = 14 * (n + 2) := by
  show tcount (Gate.seq
                (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                          (gidney_final_cx_cascade (n + 2)))
                (gidney_adder_forward_faithful_full_reverse (n + 2)))
        = 14 * (n + 2)
  simp [tcount, tcount_gidney_adder_forward_faithful_full,
        tcount_gidney_final_cx_cascade,
        tcount_gidney_adder_forward_faithful_full_reverse]
  omega

/-- Concrete: 4-bit full faithful adder = 56 T-gates = 8 Toffolis. -/
example : tcount (gidney_adder_full_faithful_no_measurement 4) = 56 :=
  tcount_gidney_adder_full_faithful_no_measurement 2

/-- Concrete: 33-bit full faithful adder (RSA-2048 q_A=33) =
    14 · 33 = 462 T-gates = 66 Toffolis. **No-measurement
    upper bound** (Gidney measurement trick would halve this to
    33 Toffolis = 231 T). -/
example : tcount (gidney_adder_full_faithful_no_measurement 33) = 14 * 33 :=
  tcount_gidney_adder_full_faithful_no_measurement 31

/-- **Gate-faithful no-measurement vs measurement-trick factor**
    (Iter 88). Strengthens `gidney_full_vs_measurement_uncompute_factor`
    (Iter 25, simplified bit-step) to the **gate-faithful** Gidney
    adder. The faithful encoding emits the same Toffoli count (14n
    T-gates), but is now backed by `qq_gidney_adder.py`'s full gate
    sequence and the Phase A semantic/structural correctness chain
    (Iter 65/57/67 per-bit + Iter 80 cascade forward + Iter 83
    matrix-level inverse + Iter 86 reverse correctness).

    The factor of 2 remains the **measurement-uncomputation review
    gap**: faithful no-measurement T-count = 14n = 2 · (measurement
    paper-claim count 7n). -/
theorem gidney_adder_full_faithful_no_measurement_vs_measurement_factor
    (n : Nat) :
    tcount (gidney_adder_full_faithful_no_measurement (n + 2))
      = 2 * gidney_adder_full_with_measurement_uncompute_tcount (n + 2) := by
  rw [tcount_gidney_adder_full_faithful_no_measurement,
      gidney_adder_full_with_measurement_uncompute_tcount_eq]
  omega

end FormalRV.BQAlgo
