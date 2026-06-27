/- IQFTCircuitCorrectness — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.QFT.IQFTCircuitCorrectness.CircuitActionColumns

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-! ### Countdown circuit + structural decomposition of `real_QFTinv_layer`

`real_QFTinv_layer n` consists of `bit_reversal_swaps n` followed by
`real_QFTinv_layer.countdown n`. The countdown applies inverse-QFT
phase ladders for target = n-1 down to 0 in that order. This section
exposes the countdown structure for reusable theorems. -/

/-- Unfolding: `countdown n 0 = SKIP`. -/
theorem countdown_zero (n : Nat) :
    real_QFTinv_layer.countdown n 0 = (SKIP : FormalRV.Framework.BaseUCom n) := by
  conv_lhs => unfold real_QFTinv_layer.countdown

/-- Unfolding: `countdown n (k+1) = ladder n k ; countdown n k`.

By the seq semantics, applying `countdown n (k+1)` to a state `v` first
applies the ladder for target `k`, then `countdown n k` (which processes
targets `k-1, k-2, ..., 0`). -/
theorem countdown_succ (n k : Nat) :
    real_QFTinv_layer.countdown n (k+1)
      = UCom.seq (inverse_qft_phase_ladder n k) (real_QFTinv_layer.countdown n k) := by
  conv_lhs => unfold real_QFTinv_layer.countdown

/-- **Structural decomposition of `real_QFTinv_layer`.** -/
theorem real_QFTinv_layer_decomp (n : Nat) :
    (real_QFTinv_layer n : FormalRV.Framework.BaseUCom n)
      = UCom.seq (bit_reversal_swaps n) (real_QFTinv_layer.countdown n n) := by
  unfold real_QFTinv_layer
  rfl

/-- **State-level decomposition**: applying `real_QFTinv_layer n` to a state
equals applying `bit_reversal_swaps n` first, then `countdown n n`. -/
theorem real_QFTinv_layer_acts (n : Nat) (v : Matrix (Fin (2^n)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval (real_QFTinv_layer n : FormalRV.Framework.BaseUCom n) * v
    = FormalRV.Framework.uc_eval
        (real_QFTinv_layer.countdown n n : FormalRV.Framework.BaseUCom n)
      * (FormalRV.Framework.uc_eval
          (bit_reversal_swaps n : FormalRV.Framework.BaseUCom n) * v) := by
  rw [real_QFTinv_layer_decomp]
  rw [uc_eval_seq_mul]

/-- **Countdown 0 acts as identity** (for positive `n`). -/
theorem countdown_zero_acts (n : Nat) (hn : 0 < n) (v : Matrix (Fin (2^n)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (real_QFTinv_layer.countdown n 0 : FormalRV.Framework.BaseUCom n) * v = v := by
  rw [countdown_zero]
  rw [show (SKIP : FormalRV.Framework.BaseUCom n) = ID 0 from rfl]
  rw [uc_eval_ID_eq_one hn]
  exact Matrix.one_mul _

/-- **Structural recursion for `countdown` action**: `countdown (k+1)` applied
to `v` equals `countdown k` applied to (`ladder k` applied to `v`). -/
theorem countdown_succ_acts (n k : Nat) (v : Matrix (Fin (2^n)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (real_QFTinv_layer.countdown n (k+1) : FormalRV.Framework.BaseUCom n) * v
    = FormalRV.Framework.uc_eval
        (real_QFTinv_layer.countdown n k : FormalRV.Framework.BaseUCom n)
      * (FormalRV.Framework.uc_eval
          (inverse_qft_phase_ladder n k : FormalRV.Framework.BaseUCom n) * v) := by
  rw [countdown_succ]
  rw [uc_eval_seq_mul]

/-- **SWAP gate action on `f_to_vec`.** Direct wrapper around
`f_to_vec_SWAP` using the framework's CNOT-CNOT-CNOT unfolding of `SWAP`. -/
theorem uc_eval_SWAP_on_f_to_vec {n : Nat} (a b : Nat)
    (ha : a < n) (hb : b < n) (hab : a ≠ b) (f : Nat → Bool) :
    FormalRV.Framework.uc_eval
        (FormalRV.Framework.BaseUCom.SWAP a b : FormalRV.Framework.BaseUCom n)
      * f_to_vec n f
    = f_to_vec n (swapBits f a b) := by
  rw [show (FormalRV.Framework.BaseUCom.SWAP a b : FormalRV.Framework.BaseUCom n)
        = UCom.seq (FormalRV.Framework.BaseUCom.CNOT a b)
            (UCom.seq (FormalRV.Framework.BaseUCom.CNOT b a)
              (FormalRV.Framework.BaseUCom.CNOT a b)) from rfl]
  rw [f_to_vec_SWAP n a b ha hb hab f]
  congr 1
  funext i
  unfold swapBits update
  by_cases hia : i = a
  · subst hia; simp [hab]
  · by_cases hib : i = b
    · subst hib; simp [Ne.symm hab]
    · simp [hia, hib]

theorem bit_reversal_loop_step (n i : Nat) (hi : i + i + 1 < n) :
    bit_reversal_swaps.loop n i
      = UCom.seq (FormalRV.Framework.BaseUCom.SWAP i (n - 1 - i))
          (bit_reversal_swaps.loop n (i + 1)) := by
  conv_lhs => unfold bit_reversal_swaps.loop
  rw [if_pos hi]

theorem bit_reversal_loop_base (n i : Nat) (hi : ¬ i + i + 1 < n) :
    bit_reversal_swaps.loop n i = (SKIP : FormalRV.Framework.BaseUCom n) := by
  conv_lhs => unfold bit_reversal_swaps.loop
  rw [if_neg hi]

theorem applySwapsFrom_step (n k : Nat) (f : Nat → Bool) (hk : 2 * k + 1 < n) :
    applySwapsFrom n k f = applySwapsFrom n (k+1) (swapBits f k (n-1-k)) := by
  conv_lhs => unfold applySwapsFrom
  rw [dif_pos hk]

theorem applySwapsFrom_base (n k : Nat) (f : Nat → Bool) (hk : ¬ 2 * k + 1 < n) :
    applySwapsFrom n k f = f := by
  conv_lhs => unfold applySwapsFrom
  rw [dif_neg hk]

/-- **Auxiliary recursion.** Action of the inner `bit_reversal_swaps.loop n k`
on `f_to_vec n f` equals `f_to_vec n (applySwapsFrom n k f)`. Proved by
strong induction on `n - 2*k`. -/
theorem bit_reversal_loop_acts_on_f_to_vec_aux
    (n : Nat) (hn : 0 < n) : ∀ (m : Nat), ∀ (k : Nat), ∀ (f : Nat → Bool),
    n - 2 * k = m →
    FormalRV.Framework.uc_eval
        (bit_reversal_swaps.loop n k : FormalRV.Framework.BaseUCom n)
      * f_to_vec n f
    = f_to_vec n (applySwapsFrom n k f) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k f hm
    by_cases hk_lt : 2 * k + 1 < n
    · have hk_lt2 : k + k + 1 < n := by omega
      have hkn : k < n := by omega
      have h_n_1_k : n - 1 - k < n := by omega
      have h_ne : k ≠ n - 1 - k := by omega
      rw [bit_reversal_loop_step n k hk_lt2]
      rw [uc_eval_seq_mul]
      rw [uc_eval_SWAP_on_f_to_vec k (n-1-k) hkn h_n_1_k h_ne f]
      rw [ih (n - 2 * (k+1)) (by omega) (k+1) (swapBits f k (n-1-k)) rfl]
      rw [← applySwapsFrom_step n k f hk_lt]
    · have hk_done2 : ¬ k + k + 1 < n := by omega
      rw [bit_reversal_loop_base n k hk_done2]
      rw [applySwapsFrom_base n k f hk_lt]
      rw [show (SKIP : FormalRV.Framework.BaseUCom n) = ID 0 from rfl]
      rw [uc_eval_ID_eq_one hn]
      exact Matrix.one_mul _

/-- **HEADLINE: Bit-reversal SWAPs basis action.** The full bit-reversal
cascade maps `f_to_vec n f` to `f_to_vec n (applySwapsFrom n 0 f)`. -/
theorem bit_reversal_swaps_acts_on_f_to_vec (n : Nat) (hn : 0 < n) (f : Nat → Bool) :
    FormalRV.Framework.uc_eval (bit_reversal_swaps n : FormalRV.Framework.BaseUCom n)
      * f_to_vec n f
    = f_to_vec n (applySwapsFrom n 0 f) := by
  rw [show (bit_reversal_swaps n : FormalRV.Framework.BaseUCom n)
        = bit_reversal_swaps.loop n 0 from by unfold bit_reversal_swaps; rfl]
  exact bit_reversal_loop_acts_on_f_to_vec_aux n hn (n - 0) 0 f rfl

/-- Recursive step for `inverse_qft_ladder_phase_from`. -/
theorem inverse_qft_ladder_phase_from_succ (n target : Nat) (f : Nat → Bool) (k : Nat)
    (hk : k < n) :
    inverse_qft_ladder_phase_from n target f k
    = (if f k ∧ f target then
         Complex.exp ((((-(Real.pi / 2 ^ (k - target))) : ℝ)) * Complex.I)
       else 1)
      * inverse_qft_ladder_phase_from n target f (k+1) := by
  unfold inverse_qft_ladder_phase_from
  rw [← Finset.insert_Ico_add_one_left_eq_Ico hk]
  rw [Finset.prod_insert]
  · intro h
    rw [Finset.mem_Ico] at h
    omega

/-- Base case for `inverse_qft_ladder_phase_from` at `k = n`. -/
theorem inverse_qft_ladder_phase_from_at_top (n target : Nat) (f : Nat → Bool) :
    inverse_qft_ladder_phase_from n target f n = 1 := by
  unfold inverse_qft_ladder_phase_from
  rw [show Finset.Ico n n = (∅ : Finset Nat) from Finset.Ico_self n]
  simp

/-- Step unfolding for `inverse_qft_phase_ladder.loop` at `j < n`. -/
theorem ladder_loop_step (n target j : Nat) (hj : j < n) :
    inverse_qft_phase_ladder.loop n target j
      = UCom.seq (controlled_Rz j target (-(Real.pi / (2 ^ (j - target) : ℝ))))
                 (inverse_qft_phase_ladder.loop n target (j + 1)) := by
  conv_lhs => unfold inverse_qft_phase_ladder.loop
  rw [if_pos hj]

/-- Base case unfolding: `inverse_qft_phase_ladder.loop n target n = H target`. -/
theorem ladder_loop_base (n target j : Nat) (hj : ¬ j < n) :
    inverse_qft_phase_ladder.loop n target j
      = (FormalRV.Framework.BaseUCom.H target : FormalRV.Framework.BaseUCom n) := by
  conv_lhs => unfold inverse_qft_phase_ladder.loop
  rw [if_neg hj]

/-- **Auxiliary recursion**: action of the inner `loop k` on `f_to_vec`.
For `target < k ≤ n`, applying `loop k` to a basis-state vector
produces a scalar `inverse_qft_ladder_phase_from n target f k` times
the H-applied state. -/
theorem ladder_loop_acts_on_f_to_vec_aux
    (n_arg : Nat) (target : Nat) (h_target : target < n_arg)
    (f : Nat → Bool) :
    ∀ m k, k ≤ n_arg → n_arg - k = m → target < k →
      FormalRV.Framework.uc_eval
          (inverse_qft_phase_ladder.loop n_arg target k :
            FormalRV.Framework.BaseUCom n_arg)
        * f_to_vec n_arg f
      = inverse_qft_ladder_phase_from n_arg target f k
        • (FormalRV.Framework.uc_eval
            (FormalRV.Framework.BaseUCom.H target : FormalRV.Framework.BaseUCom n_arg)
            * f_to_vec n_arg f) := by
  intro m
  induction m with
  | zero =>
    intro k hk hm htarget
    have hkn : k = n_arg := by omega
    subst hkn
    rw [ladder_loop_base k target k (by omega)]
    rw [inverse_qft_ladder_phase_from_at_top]
    rw [one_smul]
  | succ m ih =>
    intro k hk hm htarget
    have hk_lt : k < n_arg := by omega
    rw [ladder_loop_step n_arg target k hk_lt]
    rw [uc_eval_seq_mul]
    rw [controlled_Rz_acts_on_basis_correct n_arg k target hk_lt h_target (by omega) _ f]
    rw [Matrix.mul_smul]
    rw [ih (k+1) (by omega) (by omega) (by omega)]
    rw [smul_smul]
    rw [← inverse_qft_ladder_phase_from_succ n_arg target f k hk_lt]

/-- **HEADLINE: Ladder action on basis state.** The full
`inverse_qft_phase_ladder n target` applied to a basis state
`f_to_vec n f` equals `(ladder phase) • (H_target · f_to_vec n f)`,
where the ladder phase is the product of controlled-Rz contributions
from each control bit `j ∈ [target+1, n)`. -/
theorem inverse_qft_phase_ladder_acts_on_f_to_vec
    (n target : Nat) (h_target : target < n)
    (f : Nat → Bool) :
    FormalRV.Framework.uc_eval
        (inverse_qft_phase_ladder n target : FormalRV.Framework.BaseUCom n)
      * f_to_vec n f
    = inverse_qft_ladder_phase n target f
      • (FormalRV.Framework.uc_eval
          (FormalRV.Framework.BaseUCom.H target : FormalRV.Framework.BaseUCom n)
          * f_to_vec n f) := by
  show FormalRV.Framework.uc_eval
        (inverse_qft_phase_ladder.loop n target (target + 1) :
          FormalRV.Framework.BaseUCom n)
      * f_to_vec n f = _
  exact ladder_loop_acts_on_f_to_vec_aux n target h_target f
    (n - (target + 1)) (target + 1) (by omega) rfl (by omega)

/-- **HEADLINE: Successor entry decomposition for `IQFT_matrix`.**

For `n ≥ 1`, the `(y, x)` entry of `IQFT_matrix (n+1)` decomposes as

    (1/√(2^(n+1))) · (-1)^(x_h · y_l + x_l · y_h) · exp(-π · I · x_l · y_l / 2^n)

where `(x_h, x_l)` and `(y_h, y_l)` are the MSB/lower-bit splits of `x` and `y`.

This is the matrix-arithmetic foundation for the recursive IQFT
correctness proof.

**Note on the inner exponent**: it is `exp(-π · I · x_l y_l / 2^n)`,
which is **half** the `IQFT_matrix n y_l x_l` exponent
`exp(-2π · I · x_l y_l / 2^n)`. This means the natural IQFT recursion
is not a direct factoring `IQFT_(n+1) y x = ... · IQFT_n y_l x_l`.
The textbook QFT recursion accounts for this discrepancy via the
controlled-phase ladder that conjugates the inner IQFT_n on the
control register (not yet formalized here). -/
theorem IQFT_matrix_succ_entry_decomp
    (n : Nat) (hn : 1 ≤ n)
    (y x : Fin (2^(n+1))) :
    IQFT_matrix (n+1) y x
      = ((1 : ℂ) / Real.sqrt (2^(n+1) : ℝ))
        * ((-1 : ℂ) ^
            ((iqftHighBit n x).val * (iqftLowBits n y).val
              + (iqftLowBits n x).val * (iqftHighBit n y).val))
        * Complex.exp (-(Real.pi : ℂ) * Complex.I
            * (iqftLowBits n x).val * (iqftLowBits n y).val / (2^n : ℂ)) := by
  unfold IQFT_matrix iqftHighBit iqftLowBits
  set xH : ℕ := x.val / 2^n
  set xL : ℕ := x.val % 2^n
  set yH : ℕ := y.val / 2^n
  set yL : ℕ := y.val % 2^n
  have hx_split : (x.val : ℂ) = (xH : ℂ) * 2^n + (xL : ℂ) := by
    have h := Nat.div_add_mod' x.val (2^n)
    push_cast
    rw [show ((x.val / 2^n : Nat) : ℂ) * (2^n : ℂ) + ((x.val % 2^n : Nat) : ℂ)
          = ((x.val / 2^n * 2^n + x.val % 2^n : Nat) : ℂ) from by push_cast; ring]
    congr 1
    exact_mod_cast h.symm
  have hy_split : (y.val : ℂ) = (yH : ℂ) * 2^n + (yL : ℂ) := by
    have h := Nat.div_add_mod' y.val (2^n)
    push_cast
    rw [show ((y.val / 2^n : Nat) : ℂ) * (2^n : ℂ) + ((y.val % 2^n : Nat) : ℂ)
          = ((y.val / 2^n * 2^n + y.val % 2^n : Nat) : ℂ) from by push_cast; ring]
    congr 1
    exact_mod_cast h.symm
  rw [hx_split, hy_split]
  have hsplit := IQFT_index_split n hn xH yH xL yL
  rw [show -(2 * Real.pi * Complex.I) * ((xH : ℂ) * 2^n + xL) * ((yH : ℂ) * 2^n + yL) /
          (2^(n+1) : ℂ)
        = -(2 * Real.pi * Complex.I) *
            ((2^n * (xH : ℂ) + xL) * (2^n * (yH : ℂ) + yL) / (2^(n+1) : ℂ)) from by ring]
  rw [hsplit]
  rw [show -(2 * Real.pi * Complex.I) *
        ((2^(n-1) * (xH : ℂ) * (yH : ℂ))
          + ((xH : ℂ) * (yL : ℂ) + (xL : ℂ) * (yH : ℂ)) / 2
          + ((xL : ℂ) * (yL : ℂ)) / (2^(n+1) : ℂ))
      = (-2 * Real.pi * ((xH * yH * 2^(n-1) : Nat) : ℝ) : ℂ) * Complex.I
        + ((-Real.pi * ((xH * yL + xL * yH : Nat) : ℝ) : ℝ) : ℂ) * Complex.I
        + (-((Real.pi : ℂ) * Complex.I) * (xL : ℂ) * (yL : ℂ) / (2^n : ℂ))
       from by
       push_cast
       rw [show ((2 : ℂ)^(n+1)) = 2 * 2^n from by ring]
       field_simp
       ring]
  rw [Complex.exp_add, Complex.exp_add]
  rw [exp_neg_two_pi_I_mul_nat]
  rw [exp_neg_pi_I_mul_nat]
  conv_rhs => rw [show ((-1 : ℂ) ^ (xH * yL + xL * yH))
                  = (-1 : ℂ) ^ (xH * yL) * (-1 : ℂ) ^ (xL * yH) from pow_add _ _ _]
  -- LHS and RHS differ only by associativity of multiplication
  -- inside Complex.exp and outside.
  have h_exp_eq : Complex.exp (-((Real.pi : ℂ) * Complex.I) * (xL : ℂ) * (yL : ℂ) / (2^n : ℂ))
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * ((⟨xL, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ : Fin (2^n)).val : ℂ)
            * ((⟨yL, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ : Fin (2^n)).val : ℂ) / (2^n : ℂ)) := by
    congr 1
    ring
  rw [h_exp_eq]
  ring

/-- **HEADLINE: Full real-QPE eigenstate theorem assuming IQFT correctness.**
Given `h_IQFT : uc_eval (real_QFTinv_on m) = IQFT_matrix m`, the
real-QPE circuit applied to `|0^m⟩ ⊗ ψ` (where `ψ` is a QPE eigenstate
with phase θ) yields `kron_vec (qpe_phase_state m θ) ψ`. This is the
exact form needed to drive `QPE_MMI_correct`; the only remaining
obligation is proving `h_IQFT` for arbitrary `m`. -/
theorem real_QPE_on_eigenstate_from_IQFT_correct
    {m anc : Nat} (hmanc : 0 < m + anc) (hm : 0 < m)
    (f : Nat → BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ)
    (θ : ℝ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (h_eig_data : ∀ i, i < m →
      FormalRV.Framework.uc_eval (f i) * ψ =
        qpeEigenvalue m i θ • ψ)
    (h_wt_IQFT : UCom.WellTyped m (real_QFTinv_on m))
    (h_IQFT : FormalRV.Framework.uc_eval (real_QFTinv_on m : BaseUCom m)
                = IQFT_matrix m) :
    FormalRV.Framework.uc_eval (real_QPE m anc f)
      * kron_vec (FormalRV.Framework.kron_zeros m) ψ
    = kron_vec (qpe_phase_state m θ) ψ := by
  unfold real_QPE
  rw [uc_eval_seq_mul, uc_eval_seq_mul]
  rw [QPE_pre_QFT_on_eigenstate_fourier_form hmanc hm f ψ θ h_wt_all h_eig_data]
  exact real_QFTinv_on_fourier_weighted_kron_state_from_matrix_correct
    θ ψ h_wt_IQFT h_IQFT


end FormalRV.SQIRPort
