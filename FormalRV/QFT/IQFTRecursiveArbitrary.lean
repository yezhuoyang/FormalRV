import FormalRV.QPE.PhaseKickback
import FormalRV.QPE.QPEAmplitude
import FormalRV.QFT.IQFTDefinitions
import FormalRV.QFT.IQFTCircuitCorrectness

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-- **HEADLINE: Bit-reversal action.** For `i < n`,
`applySwapsFrom n 0 f i = f (n - 1 - i)`. -/
theorem applySwapsFrom_apply (n : Nat) (f : Nat → Bool) (i : Nat) (hi : i < n) :
    applySwapsFrom n 0 f i = f (n - 1 - i) := by
  rw [applySwapsFrom_apply_region n (n - 0) 0 rfl f i]
  rw [if_pos (by omega : (0 ≤ i ∧ i ≤ n - 1 - 0))]

/-- **Bit-reversal successor extra-bit lemma.** The value of
`bitReversedBasisFun (n+1) x` at the extra LSB position `n` equals
`iqftHighBit n x`. -/
theorem bitReversedBasisFun_succ_extra (n : Nat) (x : Fin (2^(n+1))) :
    bitReversedBasisFun (n+1) x n = decide ((iqftHighBit n x).val = 1) := by
  unfold bitReversedBasisFun basisFunOfIndex
  rw [applySwapsFrom_apply (n+1) (nat_to_funbool (n+1) x.val) n (by omega)]
  rw [show (n + 1) - 1 - n = 0 from by omega]
  unfold nat_to_funbool iqftHighBit
  rw [show (n + 1) - 1 - 0 = n from by omega]
  show decide (x.val / 2^n % 2 = 1) = decide (x.val / 2^n = 1)
  have hx : x.val < 2^(n+1) := x.isLt
  have hpow : (2^(n+1) : Nat) = 2 * 2^n := by ring
  have hx' : x.val < 2 * 2^n := hpow ▸ hx
  have h_div_lt : x.val / 2^n < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)]
    omega
  set c := x.val / 2^n
  congr 1
  interval_cases c <;> simp

/-! ### Congruence helpers for countdown_output

`countdown_output n k f` depends on `f` only through positions `< n`.
These congruence lemmas make this dependence formal and unlock the
substitution `bitReversedBasisFun (n+1) x ≡ bitReversedBasisFun n (iqftLowBits n x)`
inside `countdown_output n n` (needed for the successor entry decomposition). -/

/-- `f_to_vec n` depends on `f` only through positions `< n`. -/
theorem f_to_vec_congr (n : Nat) (f g : Nat → Bool)
    (hfg : ∀ i, i < n → f i = g i) :
    f_to_vec n f = f_to_vec n g := by
  unfold f_to_vec
  rw [FormalRV.Framework.funbool_to_nat_congr n f g hfg]

/-- Congruence for `inverse_qft_ladder_phase_from` when `target < n`. -/
theorem inverse_qft_ladder_phase_from_congr (n target : Nat) (htarget : target < n)
    (f g : Nat → Bool) (hfg : ∀ i, i < n → f i = g i) (k : Nat) :
    inverse_qft_ladder_phase_from n target f k
    = inverse_qft_ladder_phase_from n target g k := by
  unfold inverse_qft_ladder_phase_from
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [hfg j (by omega), hfg target htarget]

/-- Congruence for `inverse_qft_ladder_phase`. -/
theorem inverse_qft_ladder_phase_congr (n target : Nat) (htarget : target < n)
    (f g : Nat → Bool) (hfg : ∀ i, i < n → f i = g i) :
    inverse_qft_ladder_phase n target f
    = inverse_qft_ladder_phase n target g := by
  unfold inverse_qft_ladder_phase
  exact inverse_qft_ladder_phase_from_congr n target htarget f g hfg (target + 1)

/-- If `f` and `g` agree on positions `< n`, then `update f k b` and `update g k b`
do too. -/
theorem update_congr_lt (n k : Nat) (f g : Nat → Bool) (b : Bool)
    (hfg : ∀ i, i < n → f i = g i) :
    ∀ i, i < n → (update f k b) i = (update g k b) i := by
  intro i hi
  unfold update
  by_cases h : i = k
  · simp [h]
  · simp [h, hfg i hi]

/-- **HEADLINE: countdown_output congruence on lower n bits.** If `f` and `g`
agree on positions `< n`, then `countdown_output n k f = countdown_output n k g`
for `k ≤ n`. Proof by induction on k. -/
theorem countdown_output_congr_input (n : Nat) :
    ∀ k, k ≤ n → ∀ (f g : Nat → Bool), (∀ i, i < n → f i = g i) →
      countdown_output n k f = countdown_output n k g := by
  intro k
  induction k with
  | zero =>
    intro hk f g hfg
    rw [countdown_output_zero, countdown_output_zero]
    exact f_to_vec_congr n f g hfg
  | succ k ih =>
    intro hk f g hfg
    have hk_lt : k < n := by omega
    have hk_le : k ≤ n := by omega
    rw [countdown_output_succ, countdown_output_succ]
    rw [inverse_qft_ladder_phase_congr n k hk_lt f g hfg]
    rw [hfg k hk_lt]
    rw [ih hk_le (update f k false) (update g k false) (update_congr_lt n k f g false hfg)]
    rw [ih hk_le (update f k true) (update g k true) (update_congr_lt n k f g true hfg)]

/-- **Bit-reversal successor restrict lemma.** For `i < n`, the value of
`bitReversedBasisFun (n+1) x` at position `i` equals the value of
`bitReversedBasisFun n (iqftLowBits n x)` at position `i`. -/
theorem bitReversedBasisFun_succ_restrict (n : Nat) (x : Fin (2^(n+1))) :
    ∀ i, i < n →
      bitReversedBasisFun (n+1) x i = bitReversedBasisFun n (iqftLowBits n x) i := by
  intro i hi
  unfold bitReversedBasisFun basisFunOfIndex
  rw [applySwapsFrom_apply (n+1) (nat_to_funbool (n+1) x.val) i (by omega)]
  rw [applySwapsFrom_apply n (nat_to_funbool n (iqftLowBits n x).val) i hi]
  rw [show (n + 1) - 1 - i = n - i from by omega]
  unfold nat_to_funbool iqftLowBits
  rw [show (n + 1) - 1 - (n - i) = i from by omega]
  rw [show n - 1 - (n - 1 - i) = i from by omega]
  congr 1
  have h_lhs : (x.val % 2^n).testBit i = decide ((x.val % 2^n) / 2^i % 2 = 1) :=
    Nat.testBit_eq_decide_div_mod_eq
  have h_rhs : x.val.testBit i = decide (x.val / 2^i % 2 = 1) :=
    Nat.testBit_eq_decide_div_mod_eq
  have h_eq : (x.val % 2^n).testBit i = x.val.testBit i := by
    rw [Nat.testBit_mod_two_pow]; simp [hi]
  rw [h_lhs, h_rhs] at h_eq
  have h_dec := decide_eq_decide.mp h_eq
  set a := x.val / 2^i % 2
  set b := (x.val % 2^n) / 2^i % 2
  have ha_lt : a < 2 := Nat.mod_lt _ (by norm_num)
  have hb_lt : b < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases a <;> interval_cases b <;> simp_all

/-- **Entry formula for `embedWithExtraBit`.** The entry at row `y` is
the corresponding entry of the embedded vector at the high-n part,
gated by the LSB match condition. -/
theorem embedWithExtraBit_apply (n : Nat) (extra : Bool)
    (v : Matrix (Fin (2^n)) (Fin 1) ℂ) (y : Fin (2^(n+1))) :
    embedWithExtraBit n extra v y 0
    = (if (iqftLowBitLSB n y).val = (if extra then 1 else 0)
       then v (iqftHighBitsN n y) 0
       else 0) := by
  unfold embedWithExtraBit
  rw [kron_vec_apply]
  rw [basis_vector_apply]
  by_cases h : (kron_vec_low y : Fin (2^1)).val = (if extra then 1 else 0)
  · rw [if_pos h]
    have h' : (iqftLowBitLSB n y).val = (if extra then 1 else 0) := by
      unfold iqftLowBitLSB
      have := h
      unfold kron_vec_low at this
      exact this
    rw [if_pos h']
    rw [show (kron_vec_high y : Fin (2^n)) = iqftHighBitsN n y from by
      unfold kron_vec_high iqftHighBitsN
      ext; simp]
    ring
  · rw [if_neg h]
    have h' : ¬ (iqftLowBitLSB n y).val = (if extra then 1 else 0) := by
      unfold iqftLowBitLSB
      intro habs
      apply h
      unfold kron_vec_low
      exact habs
    rw [if_neg h']
    ring

/-! ### Successor entry decomposition for countdownColumn

The `(n+1)`-th ladder's target is qubit `n`, which has no controls
(its phase scalar is the empty product `= 1`). After this trivial
ladder, the (n+1)-qubit countdown splits into two branches via H on
qubit n, and `countdown_output_dim_split` factors each branch
through the n-qubit countdown.

The result expresses each entry of `countdownColumn (n+1) x` in terms
of the corresponding entry of `countdownColumn n (iqftLowBits n x)`. -/

/-- `cumulative_extra_phase` is `1` when the extra bit (`f n`) is `false`. -/
theorem cumulative_extra_phase_false_extra
    (n k : Nat) (f : Nat → Bool) (hfn : f n = false) :
    cumulative_extra_phase n k f = 1 := by
  unfold cumulative_extra_phase
  apply Finset.prod_eq_one
  intro t _
  rw [hfn]
  simp

/-- The `(n+1)`-th ladder (target = n) has no controls, so its phase is 1. -/
theorem inverse_qft_ladder_phase_top (n : Nat) (f : Nat → Bool) :
    inverse_qft_ladder_phase (n+1) n f = 1 := by
  unfold inverse_qft_ladder_phase inverse_qft_ladder_phase_from
  rw [show Finset.Ico (n + 1) (n + 1) = (∅ : Finset Nat) from Finset.Ico_self _]
  simp

/-- `update f n b` agrees with `f` on positions `< n`. -/
theorem update_n_lt_eq (n : Nat) (f : Nat → Bool) (b : Bool) (i : Nat) (hi : i < n) :
    (update f n b) i = f i := by
  unfold update
  rw [if_neg (by omega : i ≠ n)]

/-- `update f n b` evaluates to `b` at position `n`. -/
theorem update_n_eval_self (n : Nat) (f : Nat → Bool) (b : Bool) :
    (update f n b) n = b := by
  unfold update; rw [if_pos rfl]

/-- **HEADLINE: Corrected countdownColumn successor entry decomposition.**

For `n ≥ 1`, the `(y, 0)` entry of `countdownColumn (n+1) x` decomposes
based on the LSB of `y`:

- If `LSB(y) = 0`: `(√2/2) * countdownColumn n (iqftLowBits n x) (iqftHighBitsN n y) 0`.
- If `LSB(y) = 1`: `(if iqftHighBit n x = 1 then -(√2/2) else (√2/2))
                  * cumulative_extra_phase n n (update (bitReversedBasisFun (n+1) x) n true)
                  * countdownColumn n (iqftLowBits n x) (iqftHighBitsN n y) 0`.

Note the **update to `n true`** in the cumulative phase: this captures the
"true-branch cumulative phase" (the phase product assuming the extra LSB is `true`),
which is the correct factor regardless of the original value of
`bitReversedBasisFun (n+1) x n`. -/
theorem countdownColumn_succ_entry_decomp_corrected
    (n : Nat) (_hn : 0 < n)
    (x y : Fin (2^(n+1))) :
    countdownColumn (n+1) x y 0
    = if (iqftLowBitLSB n y).val = 0 then
        ((Real.sqrt 2 / 2 : ℂ)) *
          countdownColumn n (iqftLowBits n x) (iqftHighBitsN n y) 0
      else
        (if (iqftHighBit n x).val = 1
         then -(Real.sqrt 2 / 2 : ℂ)
         else  (Real.sqrt 2 / 2 : ℂ))
        *
        cumulative_extra_phase n n
          (update (bitReversedBasisFun (n+1) x) n true)
        *
        countdownColumn n (iqftLowBits n x) (iqftHighBitsN n y) 0 := by
  set f := bitReversedBasisFun (n+1) x with hf
  unfold countdownColumn
  rw [show countdown_output (n+1) (n+1) (bitReversedBasisFun (n+1) x)
        = countdown_output (n+1) (n+1) f from by rw [hf]]
  rw [countdown_output_succ]
  rw [inverse_qft_ladder_phase_top]
  rw [one_smul]
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
  rw [countdown_output_dim_split_full n (update f n false)]
  rw [countdown_output_dim_split_full n (update f n true)]
  rw [update_n_eval_self, update_n_eval_self]
  rw [cumulative_extra_phase_false_extra n n (update f n false) (update_n_eval_self n f false)]
  rw [one_smul]
  show (Real.sqrt 2 / 2 : ℂ) •
        (embedWithExtraBit n false (countdown_output n n (update f n false))) y 0
       + (if f n then -(Real.sqrt 2 / 2 : ℂ) else (Real.sqrt 2 / 2 : ℂ)) •
         (cumulative_extra_phase n n (update f n true) •
          embedWithExtraBit n true (countdown_output n n (update f n true))) y 0 = _
  rw [Matrix.smul_apply, embedWithExtraBit_apply n false _ y]
  rw [embedWithExtraBit_apply n true _ y]
  rw [countdown_output_congr_input n n (le_refl n) (update f n false) f
      (fun i hi => update_n_lt_eq n f false i hi)]
  rw [countdown_output_congr_input n n (le_refl n) (update f n true) f
      (fun i hi => update_n_lt_eq n f true i hi)]
  rw [show countdown_output n n f
        = countdown_output n n (bitReversedBasisFun n (iqftLowBits n x)) from
      hf ▸ countdown_output_congr_input n n (le_refl n)
        (bitReversedBasisFun (n+1) x)
        (bitReversedBasisFun n (iqftLowBits n x))
        (bitReversedBasisFun_succ_restrict n x)]
  rw [show f n = decide ((iqftHighBit n x).val = 1) from
      hf ▸ bitReversedBasisFun_succ_extra n x]
  show _ = if (iqftLowBitLSB n y).val = 0
      then (Real.sqrt 2 / 2 : ℂ) * (countdown_output n n
            (bitReversedBasisFun n (iqftLowBits n x))) (iqftHighBitsN n y) 0
      else (if (iqftHighBit n x).val = 1
            then -(Real.sqrt 2 / 2 : ℂ) else (Real.sqrt 2 / 2 : ℂ))
           * cumulative_extra_phase n n (update f n true)
           * (countdown_output n n
              (bitReversedBasisFun n (iqftLowBits n x))) (iqftHighBitsN n y) 0
  by_cases h_lsb : (iqftLowBitLSB n y).val = 0
  · rw [if_pos h_lsb]
    rw [if_pos (by simp [h_lsb] : (iqftLowBitLSB n y).val = (if false then 1 else 0))]
    rw [if_neg (by simp [h_lsb] : ¬ (iqftLowBitLSB n y).val = (if true then 1 else 0))]
    simp only [smul_eq_mul]
    ring
  · rw [if_neg h_lsb]
    have h_lsb_one : (iqftLowBitLSB n y).val = 1 := by
      have := (iqftLowBitLSB n y).isLt; omega
    rw [if_neg (by simp [h_lsb] : ¬ (iqftLowBitLSB n y).val = (if false then 1 else 0))]
    rw [if_pos (by simp [h_lsb_one] : (iqftLowBitLSB n y).val = (if true then 1 else 0))]
    simp only [smul_eq_mul]
    by_cases hh : (iqftHighBit n x).val = 1
    · simp [hh]; ring
    · simp [hh]; ring

/-! ### Scalar collapse: cumulative extra phase (true branch) = exp

The cumulative extra phase scalar appearing in the true branch of
`countdownColumn_succ_entry_decomp_corrected` collapses to a single
complex exponential, by:
  1. removing the `update ... n true` (positions `< n` are unaffected);
  2. restricting the bit-reversal to the n-qubit one (via
     `bitReversedBasisFun_succ_restrict`);
  3. collapsing the product of per-bit phases via `Complex.exp_add`
     and the arithmetic identity `1/2^(n-t) = 2^t/2^n`;
  4. reassembling the bit-weighted sum into `(iqftLowBits n x).val`
     via `binary_expansion_lsb`. -/

/-- **Helper 1**: `cumulative_extra_phase n k (update f n true)` reduces
to a clean product over positions `t < k` of the per-bit phase factor,
controlled only by `f t` (since the extra bit is `true` and `t < k ≤ n`
means the update at position `n` doesn't affect `f t`). -/
theorem cumulative_extra_phase_update_extra_true
    (n k : Nat) (hk : k ≤ n) (f : Nat → Bool) :
    cumulative_extra_phase n k (update f n true)
    = ∏ t ∈ Finset.range k,
      (if f t then
        Complex.exp ((((-(Real.pi / 2 ^ (n - t))) : ℝ)) * Complex.I)
       else 1) := by
  unfold cumulative_extra_phase
  apply Finset.prod_congr rfl
  intro t ht
  rw [Finset.mem_range] at ht
  have h_t_lt_n : t < n := by omega
  rw [update_n_eval_self, update_n_lt_eq n f true t h_t_lt_n]
  simp

/-- **Helper 2**: After bit-reversal, position `t < n` of
`bitReversedBasisFun n xl` equals the `t`-th LSB bit of `xl.val`. -/
theorem bitReversedBasisFun_eq_lsb_bit (n : Nat) (xl : Fin (2^n))
    (t : Nat) (ht : t < n) :
    bitReversedBasisFun n xl t = decide ((xl.val / 2^t) % 2 = 1) := by
  unfold bitReversedBasisFun basisFunOfIndex
  rw [applySwapsFrom_apply n (nat_to_funbool n xl.val) t ht]
  unfold nat_to_funbool
  rw [show n - 1 - (n - 1 - t) = t from by omega]

/-- **Helper 3** (product-of-exponentials collapse): For any boolean
function `b` and any `k ≤ n`, the product
`∏ t < k, if b t then exp(-π·I/2^(n-t)) else 1` collapses to
`exp(-π·I · S / 2^n)` where `S = ∑ t < k, b_t · 2^t` is the
bit-weighted sum. Proof by induction on `k`, using `Complex.exp_add`
and the arithmetic `1/2^(n-k) = 2^k/2^n` (valid since `k ≤ n`). -/
theorem prod_exp_bits_eq_exp_sum_aux
    (n : Nat) (b : Nat → Bool) :
    ∀ k, k ≤ n →
      (∏ t ∈ Finset.range k,
        (if b t then
          Complex.exp ((((-(Real.pi / 2 ^ (n - t))) : ℝ)) * Complex.I)
         else 1))
      = Complex.exp
          (((-Real.pi
            * (((∑ t ∈ Finset.range k,
                  (if b t then 1 else 0) * 2^t) : Nat) : ℝ)
            / (2^n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk_lt : k < n := hk
    have hk_le : k ≤ n := Nat.le_of_lt hk_lt
    rw [Finset.prod_range_succ, Finset.sum_range_succ, ih hk_le]
    by_cases hbk : b k
    · rw [if_pos hbk, if_pos hbk]
      rw [← Complex.exp_add]; push_cast; congr 1
      have h_pow_split : (2 : ℂ)^n = 2^(n-k) * 2^k := by
        rw [← pow_add]; congr 1; omega
      have h_pow_ne : (2 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
      have h_pow_nk_ne : (2 : ℂ)^(n-k) ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
      have h_pow_k_ne : (2 : ℂ)^k ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
      field_simp; rw [h_pow_split]; ring
    · rw [if_neg hbk, if_neg hbk]; simp

/-- **HEADLINE: Cumulative extra phase (true branch) = exp.** The
cumulative extra phase scalar in the true branch of
`countdownColumn_succ_entry_decomp_corrected` collapses to a single
complex exponential whose argument is `-π·I · (iqftLowBits n x) / 2^n`.

Combines:
  - `cumulative_extra_phase_update_extra_true` (remove the update),
  - `bitReversedBasisFun_succ_restrict` (restrict bit-reversal to n),
  - `prod_exp_bits_eq_exp_sum_aux` (collapse product to exp of sum),
  - `bitReversedBasisFun_eq_lsb_bit` + `binary_expansion_lsb`
    (reassemble bit-weighted sum into `(iqftLowBits n x).val`). -/
theorem cumulative_extra_phase_true_branch_eq_exp
    (n : Nat) (_hn : 0 < n) (x : Fin (2^(n+1))) :
    cumulative_extra_phase n n
      (update (bitReversedBasisFun (n+1) x) n true)
    = Complex.exp
        (((-Real.pi
            * ((iqftLowBits n x).val : ℝ)
            / (2^n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [cumulative_extra_phase_update_extra_true n n (le_refl n)]
  have h_prod_eq :
      (∏ t ∈ Finset.range n,
          (if bitReversedBasisFun (n+1) x t then
            Complex.exp ((((-(Real.pi / 2 ^ (n - t))) : ℝ)) * Complex.I)
           else 1))
      = (∏ t ∈ Finset.range n,
          (if bitReversedBasisFun n (iqftLowBits n x) t then
            Complex.exp ((((-(Real.pi / 2 ^ (n - t))) : ℝ)) * Complex.I)
           else 1)) := by
    apply Finset.prod_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    rw [bitReversedBasisFun_succ_restrict n x t ht]
  rw [h_prod_eq]
  rw [prod_exp_bits_eq_exp_sum_aux n (bitReversedBasisFun n (iqftLowBits n x))
        n (le_refl n)]
  have h_sum_eq :
      (∑ t ∈ Finset.range n,
          (if bitReversedBasisFun n (iqftLowBits n x) t then 1 else 0) * 2^t)
      = (iqftLowBits n x).val := by
    have h_xl_lt : (iqftLowBits n x).val < 2^n := (iqftLowBits n x).isLt
    conv_rhs => rw [binary_expansion_lsb n (iqftLowBits n x).val h_xl_lt]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    rw [bitReversedBasisFun_eq_lsb_bit n (iqftLowBits n x) t ht]
    by_cases hbit : (iqftLowBits n x).val / 2^t % 2 = 1
    · simp [hbit]
    · have h2 : (iqftLowBits n x).val / 2^t % 2 = 0 := by
        have hlt : (iqftLowBits n x).val / 2^t % 2 < 2 := Nat.mod_lt _ (by norm_num)
        omega
      simp [h2]
  rw [h_sum_eq]

/-! ### IQFT matrix in countdown's split convention

The ideal `IQFT_matrix (n+1)` column entry expressed with the same
LSB/rest output split + MSB/rest input split that the `countdown`
recursion uses. Combined with `countdownColumn_succ_entry_decomp_corrected`
and `cumulative_extra_phase_true_branch_eq_exp`, this yields the
induction step `countdownColumn_succ_entry_eq_IQFT_entry`. -/

/-- **Sqrt-2 identity**: `1/√2 = √2/2`. Needed to convert
`inv_sqrt_pow_two_succ_factor`'s leading factor into the form used
in `countdownColumn_succ_entry_decomp_corrected`. -/
theorem inv_sqrt_two_eq_sqrt_two_div_two :
    (1 : ℂ) / Real.sqrt 2 = (Real.sqrt 2 / 2 : ℂ) := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h_sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (le_of_lt h2_pos)
  have h_cast : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by exact_mod_cast h_sqrt2_sq
  have h_sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    have : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr h2_pos
    exact_mod_cast this
  field_simp; linear_combination -h_cast

/-- **HEADLINE: IQFT_matrix mixed successor entry decomposition.**
The ideal `IQFT_matrix (n+1)` column entry at `(y, 0)` decomposes
based on the LSB of `y`, into a leading `√2/2` scalar (with possible
sign flip from `iqftHighBit n x`) times the n-bit IQFT_matrix column
entry, plus (in the LSB=1 branch) a `Complex.exp(-π·xl/2^n · I)`
factor. Mirrors `countdownColumn_succ_entry_decomp_corrected` in
shape.

Proof strategy: rewrite both matrix-vector products via
`IQFT_matrix_mul_basis_apply`; unfold `IQFT_matrix`; expand the
exponent via the index decompositions `x.val = xH · 2^n + xL` and
`y.val = yH · 2 + yL`; case-split on `yL` and on `xH ∈ Fin 2`.
The integer piece `xH·yH` collapses via `exp_neg_two_pi_I_mul_nat`;
the half-integer piece `xH` collapses via `exp_neg_pi_I_mul_nat`;
the `1/√2^(n+1)` factor splits via `inv_sqrt_pow_two_succ_factor`
combined with `inv_sqrt_two_eq_sqrt_two_div_two`. -/
theorem IQFT_matrix_succ_entry_decomp_mixed
    (n : Nat) (_hn : 0 < n) (x y : Fin (2^(n+1))) :
    (IQFT_matrix (n+1) * FormalRV.Framework.basis_vector (2^(n+1)) x.val) y 0
    = if (iqftLowBitLSB n y).val = 0 then
        ((Real.sqrt 2 / 2 : ℂ)) *
          (IQFT_matrix n
            * FormalRV.Framework.basis_vector (2^n) (iqftLowBits n x).val)
            (iqftHighBitsN n y) 0
      else
        (if (iqftHighBit n x).val = 1
         then -(Real.sqrt 2 / 2 : ℂ)
         else  (Real.sqrt 2 / 2 : ℂ))
        *
        Complex.exp
          (((-Real.pi
              * ((iqftLowBits n x).val : ℝ)
              / (2^n : ℝ) : ℝ) : ℂ) * Complex.I)
        *
        (IQFT_matrix n
          * FormalRV.Framework.basis_vector (2^n) (iqftLowBits n x).val)
          (iqftHighBitsN n y) 0 := by
  rw [IQFT_matrix_mul_basis_apply (n+1) x y, IQFT_matrix_mul_basis_apply n
        (iqftLowBits n x) (iqftHighBitsN n y)]
  unfold IQFT_matrix
  set xH : ℕ := (iqftHighBit n x).val with hxH_def
  set xL : ℕ := (iqftLowBits n x).val with hxL_def
  set yH : ℕ := (iqftHighBitsN n y).val with hyH_def
  set yL : ℕ := (iqftLowBitLSB n y).val with hyL_def
  have hx : x.val = xH * 2^n + xL := iqft_index_reconstruct n x
  have hy : y.val = yH * 2 + yL := iqft_index_reconstruct_highN_low1 n y
  rw [hx, hy]
  rw [show (((xH * 2^n + xL : Nat) : ℂ)) = (xH : ℂ) * 2^n + (xL : ℂ) from by push_cast; ring]
  rw [show (((yH * 2 + yL : Nat) : ℂ)) = (yH : ℂ) * 2 + (yL : ℂ) from by push_cast; ring]
  by_cases h_lsb : yL = 0
  · rw [if_pos h_lsb]
    have h_yL_zero : (yL : ℂ) = 0 := by simp [h_lsb]
    rw [h_yL_zero]
    rw [show -(2 * (Real.pi : ℂ) * Complex.I) * ((xH : ℂ) * 2^n + (xL : ℂ))
          * ((yH : ℂ) * 2 + 0) / (2^(n+1) : ℂ)
          = (-2 * Real.pi * ((xH * yH : Nat) : ℝ) : ℂ) * Complex.I
            + -(2 * Real.pi * Complex.I) * (xL : ℂ) * (yH : ℂ) / (2^n : ℂ) from by
        push_cast
        rw [show ((2 : ℂ)^(n+1)) = 2 * 2^n from by ring]
        have h_pow_ne : (2 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
        field_simp; ring]
    rw [Complex.exp_add, exp_neg_two_pi_I_mul_nat, one_mul]
    rw [inv_sqrt_pow_two_succ_factor, inv_sqrt_two_eq_sqrt_two_div_two]; ring
  · rw [if_neg h_lsb]
    have h_yL_one : yL = 1 := by
      have h_lt : yL < 2 := (iqftLowBitLSB n y).isLt
      omega
    have h_yL_one_C : (yL : ℂ) = 1 := by rw [h_yL_one]; simp
    rw [h_yL_one_C]
    rw [show -(2 * (Real.pi : ℂ) * Complex.I) * ((xH : ℂ) * 2^n + (xL : ℂ))
          * ((yH : ℂ) * 2 + 1) / (2^(n+1) : ℂ)
          = (-2 * Real.pi * ((xH * yH : Nat) : ℝ) : ℂ) * Complex.I
            + ((-Real.pi * (xH : ℝ) : ℝ) : ℂ) * Complex.I
            + -(2 * Real.pi * Complex.I) * (xL : ℂ) * (yH : ℂ) / (2^n : ℂ)
            + (((-Real.pi * (xL : ℝ) / (2^n : ℝ)) : ℝ) : ℂ) * Complex.I from by
        push_cast
        rw [show ((2 : ℂ)^(n+1)) = 2 * 2^n from by ring]
        have h_pow_ne : (2 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
        field_simp; ring]
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]
    rw [exp_neg_two_pi_I_mul_nat, exp_neg_pi_I_mul_nat, one_mul]
    rw [inv_sqrt_pow_two_succ_factor, inv_sqrt_two_eq_sqrt_two_div_two]
    have h_xH_lt : xH < 2 := (iqftHighBit n x).isLt
    by_cases h_xH : xH = 1
    · rw [if_pos h_xH, h_xH]; simp; ring
    · have h_xH_zero : xH = 0 := by omega
      rw [if_neg h_xH, h_xH_zero]; simp; ring

/-- **HEADLINE: Induction step from countdown column to IQFT matrix entry.**
Assuming the IH that `countdownColumn n (iqftLowBits n x)` equals
`IQFT_matrix n · basis_vector (iqftLowBits n x).val`, the entry-level
column equality lifts from `n` to `n+1`. Proof: rewrite LHS via
`countdownColumn_succ_entry_decomp_corrected`, RHS via
`IQFT_matrix_succ_entry_decomp_mixed`; apply IH at the inner entry;
collapse the cumulative phase via `cumulative_extra_phase_true_branch_eq_exp`.
The two `if`-`then`-`else` decompositions match by construction. -/
theorem countdownColumn_succ_entry_eq_IQFT_entry
    (n : Nat) (hn : 0 < n)
    (x y : Fin (2^(n+1)))
    (IH :
      countdownColumn n (iqftLowBits n x)
        =
      IQFT_matrix n * FormalRV.Framework.basis_vector (2^n) (iqftLowBits n x).val) :
    countdownColumn (n+1) x y 0
      =
    (IQFT_matrix (n+1) * FormalRV.Framework.basis_vector (2^(n+1)) x.val) y 0 := by
  rw [countdownColumn_succ_entry_decomp_corrected n hn x y]
  rw [IQFT_matrix_succ_entry_decomp_mixed n hn x y]
  have h_IH_entry :
      countdownColumn n (iqftLowBits n x) (iqftHighBitsN n y) 0
      = (IQFT_matrix n
          * FormalRV.Framework.basis_vector (2^n) (iqftLowBits n x).val)
          (iqftHighBitsN n y) 0 := by rw [IH]
  rw [h_IH_entry]
  by_cases h_lsb : (iqftLowBitLSB n y).val = 0
  · rw [if_pos h_lsb, if_pos h_lsb]
  · rw [if_neg h_lsb, if_neg h_lsb]
    rw [cumulative_extra_phase_true_branch_eq_exp n hn x]

/-- **HEADLINE: Full column theorem.** For all `n ≥ 1` and
`x : Fin (2^n)`, the recursive `countdownColumn n x` equals the
ideal IQFT column `IQFT_matrix n · basis_vector (2^n) x.val`. Proof
by induction on `n`: base case `n = 1` via
`countdownColumn_eq_IQFT_column_one`; successor case via
`countdownColumn_succ_entry_eq_IQFT_entry` applied per entry. -/
theorem countdownColumn_eq_IQFT_column
    (n : Nat) (hn : 0 < n) (x : Fin (2^n)) :
    countdownColumn n x
      = IQFT_matrix n * FormalRV.Framework.basis_vector (2^n) x.val := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : 0 < k
    · ext y col
      have h_col : col = 0 := by ext; have h := col.isLt; omega
      rw [h_col]
      exact countdownColumn_succ_entry_eq_IQFT_entry k hk x y (ih hk (iqftLowBits k x))
    · have h_k_zero : k = 0 := by omega
      subst h_k_zero
      exact countdownColumn_eq_IQFT_column_one x

/-- **Equivalence of column equality and layer-matrix correctness.**
The column equality `countdownColumn n x = IQFT_matrix n · basis_vector x.val`
for all `x` is equivalent to `uc_eval (real_QFTinv_layer n) = IQFT_matrix n`
via `matrix_eq_of_basis_action`. -/
theorem layer_matrix_correctness_iff_countdownColumn (n : Nat) (hn : 0 < n) :
    (FormalRV.Framework.uc_eval (real_QFTinv_layer n : FormalRV.Framework.BaseUCom n)
      = IQFT_matrix n)
    ↔ (∀ x : Fin (2^n),
        countdownColumn n x
          = IQFT_matrix n * FormalRV.Framework.basis_vector (2^n) x.val) := by
  constructor
  · intro h x
    unfold countdownColumn bitReversedBasisFun basisFunOfIndex
    rw [← real_QFTinv_layer_output_on_f_to_vec n hn _]
    rw [h]
    rw [show f_to_vec n (nat_to_funbool n x.val)
        = FormalRV.Framework.basis_vector (2^n) x.val from
        (basis_vector_eq_f_to_vec_nat_to_funbool n x).symm]
  · intro h
    apply matrix_eq_of_basis_action
    intro x
    have hbf : FormalRV.Framework.basis_vector (2^n) x.val
          = f_to_vec n (nat_to_funbool n x.val) :=
      basis_vector_eq_f_to_vec_nat_to_funbool n x
    rw [hbf]
    rw [real_QFTinv_layer_output_on_f_to_vec n hn _]
    have := h x
    unfold countdownColumn bitReversedBasisFun basisFunOfIndex at this
    rw [this]
    rw [← hbf]

/-- **HEADLINE: Arbitrary-n layer matrix correctness.** For all `n ≥ 1`,
`uc_eval (real_QFTinv_layer n) = IQFT_matrix n`. Direct corollary of
`countdownColumn_eq_IQFT_column` via
`layer_matrix_correctness_iff_countdownColumn`. -/
theorem uc_eval_real_QFTinv_layer_eq_IQFT_matrix
    (n : Nat) (hn : 0 < n) :
    FormalRV.Framework.uc_eval
        (real_QFTinv_layer n : FormalRV.Framework.BaseUCom n)
      = IQFT_matrix n :=
  (layer_matrix_correctness_iff_countdownColumn n hn).mpr
    (fun x => countdownColumn_eq_IQFT_column n hn x)

/-! ### Well-typedness of `real_QFTinv_layer`

For the lifted-IQFT theorem to apply at `m + anc` qubits, the
`m`-qubit `real_QFTinv_layer m` must be well-typed. Proof: structural
induction on the three layer pieces — `bit_reversal_swaps`, the
`countdown` recursion, and the `inverse_qft_phase_ladder` loop. -/

/-- `controlled_Rz q t λ` is `WellTyped` when both qubits are in range
and distinct. Unfolds to a 5-gate seq: Rz q ; CNOT q t ; Rz t ; CNOT q t ; Rz t. -/
theorem controlled_Rz_well_typed {dim : Nat} (q t : Nat) (lam : ℝ)
    (hq : q < dim) (ht : t < dim) (hqt : q ≠ t) :
    UCom.WellTyped dim (controlled_Rz q t lam : FormalRV.Framework.BaseUCom dim) := by
  unfold controlled_Rz
  refine UCom.WellTyped.seq (Rz_well_typed _ q hq) ?_
  refine UCom.WellTyped.seq (CNOT_well_typed _ _ hq ht hqt) ?_
  refine UCom.WellTyped.seq (Rz_well_typed _ t ht) ?_
  refine UCom.WellTyped.seq (CNOT_well_typed _ _ hq ht hqt) ?_
  exact Rz_well_typed _ t ht

/-- The inner `inverse_qft_phase_ladder.loop n target j` recursion is
`WellTyped` for `target < n` and `target < j`. Proof by strong
induction on `n - j`. The hypothesis `target < j` is the loop
invariant (loop always starts at `target + 1`). -/
theorem inverse_qft_phase_ladder_loop_well_typed
    (n target : Nat) (h_target : target < n) :
    ∀ (m j : Nat), n - j = m → target < j →
      UCom.WellTyped n
          (inverse_qft_phase_ladder.loop n target j
            : FormalRV.Framework.BaseUCom n) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro j hm h_t_lt_j
    by_cases hj : j < n
    · rw [ladder_loop_step n target j hj]
      refine UCom.WellTyped.seq (controlled_Rz_well_typed _ _ _ hj h_target (by omega)) ?_
      exact ih (n - (j+1)) (by omega) (j+1) rfl (by omega)
    · rw [ladder_loop_base n target j hj]
      exact H_well_typed _ h_target

/-- `inverse_qft_phase_ladder n target` is `WellTyped` when
`target < n`. -/
theorem inverse_qft_phase_ladder_well_typed (n target : Nat) (h_target : target < n) :
    UCom.WellTyped n
        (inverse_qft_phase_ladder n target : FormalRV.Framework.BaseUCom n) :=
  inverse_qft_phase_ladder_loop_well_typed n target h_target
    (n - (target+1)) (target+1) rfl (by omega)

/-- The `real_QFTinv_layer.countdown n k` recursion is `WellTyped`
when `0 < n` and `k ≤ n`. Proof by induction on `k`. -/
theorem real_QFTinv_layer_countdown_well_typed (n : Nat) (hn : 0 < n) :
    ∀ k, k ≤ n →
      UCom.WellTyped n
          (real_QFTinv_layer.countdown n k : FormalRV.Framework.BaseUCom n) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [countdown_zero]
    exact ID_well_typed _ hn
  | succ k ih =>
    intro hk
    rw [countdown_succ]
    exact UCom.WellTyped.seq
      (inverse_qft_phase_ladder_well_typed n k (by omega)) (ih (by omega))

/-- The inner `bit_reversal_swaps.loop n k` recursion is `WellTyped`
when `0 < n`. Proof by strong induction on `n - 2 * k`. -/
theorem bit_reversal_swaps_loop_well_typed (n : Nat) (hn : 0 < n) :
    ∀ (m k : Nat), n - 2 * k = m →
      UCom.WellTyped n
          (bit_reversal_swaps.loop n k : FormalRV.Framework.BaseUCom n) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hm
    by_cases hk_lt : 2 * k + 1 < n
    · have hk_lt2 : k + k + 1 < n := by omega
      rw [bit_reversal_loop_step n k hk_lt2]
      refine UCom.WellTyped.seq
        (SWAP_well_typed _ _ (by omega) (by omega) (by omega)) ?_
      exact ih (n - 2 * (k+1)) (by omega) (k+1) rfl
    · have hk_done2 : ¬ k + k + 1 < n := by omega
      rw [bit_reversal_loop_base n k hk_done2]
      exact ID_well_typed _ hn

/-- `bit_reversal_swaps n` is `WellTyped` when `0 < n`. -/
theorem bit_reversal_swaps_well_typed (n : Nat) (hn : 0 < n) :
    UCom.WellTyped n (bit_reversal_swaps n : FormalRV.Framework.BaseUCom n) :=
  bit_reversal_swaps_loop_well_typed n hn (n - 0) 0 rfl

/-- **HEADLINE: `real_QFTinv_layer` is well-typed for all `n ≥ 1`.**
Combines bit-reversal well-typedness with countdown well-typedness
via `real_QFTinv_layer_decomp`. -/
theorem wellTyped_real_QFTinv_layer (n : Nat) (hn : 0 < n) :
    UCom.WellTyped n (real_QFTinv_layer n : FormalRV.Framework.BaseUCom n) := by
  rw [real_QFTinv_layer_decomp]
  exact UCom.WellTyped.seq (bit_reversal_swaps_well_typed n hn)
    (real_QFTinv_layer_countdown_well_typed n hn n (le_refl n))


/-! ### Bridge: SQIRPort vs Framework `real_QFTinv_layer`

The `SQIRPort.real_QFTinv_layer n : BaseUCom n` and
`Framework.BaseUCom.real_QFTinv_layer (dim := n) n : BaseUCom n`
are STRUCTURALLY identical (same gate sequence) but differ at the
auto-generated nested helpers (different namespaces). The bridge
lemmas below prove their UCom equality by structural induction,
allowing the SQIRPort correctness theorems to transfer to the
framework def — and hence to `Framework.QPE.QFTinv n`. -/

/-- Loop-level bridge for `bit_reversal_swaps`. -/
theorem bit_reversal_loop_bridge (n : Nat) :
    ∀ (m k : Nat), n - 2 * k = m →
      FormalRV.SQIRPort.bit_reversal_swaps.loop n k
      = (@FormalRV.Framework.BaseUCom.bit_reversal_swaps.loop n n k
          : FormalRV.Framework.BaseUCom n) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hm
    by_cases hk_lt : 2 * k + 1 < n
    · have hk_lt2 : k + k + 1 < n := by omega
      show FormalRV.SQIRPort.bit_reversal_swaps.loop n k = _
      conv_lhs => unfold FormalRV.SQIRPort.bit_reversal_swaps.loop
      conv_rhs => unfold FormalRV.Framework.BaseUCom.bit_reversal_swaps.loop
      rw [if_pos hk_lt2, if_pos hk_lt2]
      congr 1
      exact ih (n - 2 * (k+1)) (by omega) (k+1) rfl
    · show FormalRV.SQIRPort.bit_reversal_swaps.loop n k = _
      conv_lhs => unfold FormalRV.SQIRPort.bit_reversal_swaps.loop
      conv_rhs => unfold FormalRV.Framework.BaseUCom.bit_reversal_swaps.loop
      have : ¬ k + k + 1 < n := by omega
      rw [if_neg this, if_neg this]

/-- Top-level bridge for `bit_reversal_swaps`. -/
theorem bit_reversal_swaps_bridge (n : Nat) :
    (FormalRV.SQIRPort.bit_reversal_swaps n : FormalRV.Framework.BaseUCom n)
    = (@FormalRV.Framework.BaseUCom.bit_reversal_swaps n n) := by
  show FormalRV.SQIRPort.bit_reversal_swaps.loop n 0 = _
  exact bit_reversal_loop_bridge n n 0 rfl

/-- Loop-level bridge for `inverse_qft_phase_ladder`. -/
theorem inverse_qft_phase_ladder_loop_bridge (n target : Nat) :
    ∀ (m j : Nat), n - j = m →
      FormalRV.SQIRPort.inverse_qft_phase_ladder.loop n target j
      = (@FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder.loop n n target j
          : FormalRV.Framework.BaseUCom n) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro j hm
    by_cases hj : j < n
    · show FormalRV.SQIRPort.inverse_qft_phase_ladder.loop n target j = _
      conv_lhs => unfold FormalRV.SQIRPort.inverse_qft_phase_ladder.loop
      conv_rhs => unfold FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder.loop
      rw [if_pos hj, if_pos hj]
      congr 1
      exact ih (n - (j+1)) (by omega) (j+1) rfl
    · show FormalRV.SQIRPort.inverse_qft_phase_ladder.loop n target j = _
      conv_lhs => unfold FormalRV.SQIRPort.inverse_qft_phase_ladder.loop
      conv_rhs => unfold FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder.loop
      rw [if_neg hj, if_neg hj]

/-- Top-level bridge for `inverse_qft_phase_ladder`. -/
theorem inverse_qft_phase_ladder_bridge (n target : Nat) :
    (FormalRV.SQIRPort.inverse_qft_phase_ladder n target
      : FormalRV.Framework.BaseUCom n)
    = (@FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder n n target) :=
  inverse_qft_phase_ladder_loop_bridge n target (n - (target+1)) (target+1) rfl

/-- Countdown-level bridge for `real_QFTinv_layer.countdown`. -/
theorem real_QFTinv_layer_countdown_bridge (n : Nat) :
    ∀ k,
      FormalRV.SQIRPort.real_QFTinv_layer.countdown n k
      = (@FormalRV.Framework.BaseUCom.real_QFTinv_layer.countdown n n k
          : FormalRV.Framework.BaseUCom n) := by
  intro k
  induction k with
  | zero =>
    show FormalRV.SQIRPort.real_QFTinv_layer.countdown n 0 = _
    conv_lhs => unfold FormalRV.SQIRPort.real_QFTinv_layer.countdown
    conv_rhs => unfold FormalRV.Framework.BaseUCom.real_QFTinv_layer.countdown
  | succ k ih =>
    show FormalRV.SQIRPort.real_QFTinv_layer.countdown n (k+1) = _
    conv_lhs => unfold FormalRV.SQIRPort.real_QFTinv_layer.countdown
    conv_rhs => unfold FormalRV.Framework.BaseUCom.real_QFTinv_layer.countdown
    rw [inverse_qft_phase_ladder_bridge n k, ih]

/-- **HEADLINE: Top-level bridge for `real_QFTinv_layer`.** Proves
`SQIRPort.real_QFTinv_layer n = Framework.BaseUCom.real_QFTinv_layer n`
as a `BaseUCom n` equality. This is the key bridge: it lets the
SQIRPort correctness theorem transfer to the framework def, which
underlies `Framework.QPE.QFTinv`. -/
theorem real_QFTinv_layer_bridge (n : Nat) :
    (FormalRV.SQIRPort.real_QFTinv_layer n : FormalRV.Framework.BaseUCom n)
    = (@FormalRV.Framework.BaseUCom.real_QFTinv_layer n n) := by
  show UCom.seq (FormalRV.SQIRPort.bit_reversal_swaps n)
                (FormalRV.SQIRPort.real_QFTinv_layer.countdown n n) = _
  conv_rhs => unfold FormalRV.Framework.BaseUCom.real_QFTinv_layer
  rw [bit_reversal_swaps_bridge n, real_QFTinv_layer_countdown_bridge n n]

/-! ### Framework `QFTinv` wrappers (matrix correctness + well-typedness)

These are the headline corollaries that establish the correctness of
the `Framework.QPE.QFTinv` (now defined as `real_QFTinv_layer n`).
They use the bridge lemmas above together with the SQIRPort
correctness chain. -/

/-- **HEADLINE: Framework QFTinv matrix correctness.** For all `m ≥ 1`,
`uc_eval (QFTinv m : BaseUCom m) = IQFT_matrix m`. Direct corollary
of `real_QFTinv_layer_bridge` + `uc_eval_real_QFTinv_layer_eq_IQFT_matrix`. -/
theorem uc_eval_QFTinv_eq_IQFT_matrix (m : Nat) (hm : 0 < m) :
    FormalRV.Framework.uc_eval
        (FormalRV.Framework.BaseUCom.QFTinv m : FormalRV.Framework.BaseUCom m)
      = IQFT_matrix m := by
  show FormalRV.Framework.uc_eval
        (@FormalRV.Framework.BaseUCom.real_QFTinv_layer m m
          : FormalRV.Framework.BaseUCom m)
      = IQFT_matrix m
  rw [← real_QFTinv_layer_bridge m]
  exact uc_eval_real_QFTinv_layer_eq_IQFT_matrix m hm

/-- **Framework QFTinv well-typedness wrapper at `dim = m`.** Direct
corollary of `wellTyped_real_QFTinv_layer` + the bridge. -/
theorem wellTyped_QFTinv (m : Nat) (hm : 0 < m) :
    UCom.WellTyped m
        (FormalRV.Framework.BaseUCom.QFTinv m : FormalRV.Framework.BaseUCom m) := by
  show UCom.WellTyped m
        (@FormalRV.Framework.BaseUCom.real_QFTinv_layer m m
          : FormalRV.Framework.BaseUCom m)
  rw [← real_QFTinv_layer_bridge m]
  exact wellTyped_real_QFTinv_layer m hm

/-! ### Polymorphic-lift bridge for the framework IQFT components

The framework defs are `{dim}`-polymorphic. When the same circuit
(e.g. `real_QFTinv_layer m`) is constructed at a HIGHER ambient
dimension `m + anc`, it must equal the dim-`m` version lifted via
`map_qubits id` to `BaseUCom (m + anc)`. The bridge below establishes
this UCom equality by structural induction; it lets the existing
`real_QFTinv_layer_on_fourier_weighted_kron_state` (which uses the
SQIRPort def via `map_qubits id`) apply to the framework def
constructed directly at `m + anc`. -/

/-- Loop-level bridge for `bit_reversal_swaps`. -/
theorem bit_reversal_swaps_loop_map_id_bridge (m anc n : Nat) :
    ∀ (m_meas k : Nat), n - 2 * k = m_meas →
      (@FormalRV.Framework.BaseUCom.bit_reversal_swaps.loop (m + anc) n k
        : FormalRV.Framework.BaseUCom (m + anc))
      = map_qubits id
          (@FormalRV.Framework.BaseUCom.bit_reversal_swaps.loop m n k
            : FormalRV.Framework.BaseUCom m) := by
  intro m_meas
  induction m_meas using Nat.strong_induction_on with
  | _ m_meas ih =>
    intro k hm
    by_cases hk_lt : 2 * k + 1 < n
    · have hk_lt2 : k + k + 1 < n := by omega
      show FormalRV.Framework.BaseUCom.bit_reversal_swaps.loop n k = _
      conv_lhs => unfold FormalRV.Framework.BaseUCom.bit_reversal_swaps.loop
      conv_rhs => unfold FormalRV.Framework.BaseUCom.bit_reversal_swaps.loop
      rw [if_pos hk_lt2, if_pos hk_lt2]
      show UCom.seq _ _ = UCom.seq _ _
      congr 1
      exact ih (n - 2 * (k+1)) (by omega) (k+1) rfl
    · show FormalRV.Framework.BaseUCom.bit_reversal_swaps.loop n k = _
      conv_lhs => unfold FormalRV.Framework.BaseUCom.bit_reversal_swaps.loop
      conv_rhs => unfold FormalRV.Framework.BaseUCom.bit_reversal_swaps.loop
      have : ¬ k + k + 1 < n := by omega
      rw [if_neg this, if_neg this]
      rfl

/-- Top-level bridge for `bit_reversal_swaps`. -/
theorem bit_reversal_swaps_map_id_bridge (m anc n : Nat) :
    (@FormalRV.Framework.BaseUCom.bit_reversal_swaps (m + anc) n
      : FormalRV.Framework.BaseUCom (m + anc))
    = map_qubits id
        (@FormalRV.Framework.BaseUCom.bit_reversal_swaps m n
          : FormalRV.Framework.BaseUCom m) :=
  bit_reversal_swaps_loop_map_id_bridge m anc n n 0 rfl

/-- Loop-level bridge for `inverse_qft_phase_ladder`. -/
theorem inverse_qft_phase_ladder_loop_map_id_bridge (m anc n target : Nat) :
    ∀ (m_meas j : Nat), n - j = m_meas →
      (@FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder.loop (m + anc) n target j
        : FormalRV.Framework.BaseUCom (m + anc))
      = map_qubits id
          (@FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder.loop m n target j
            : FormalRV.Framework.BaseUCom m) := by
  intro m_meas
  induction m_meas using Nat.strong_induction_on with
  | _ m_meas ih =>
    intro j hm
    by_cases hj : j < n
    · show FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder.loop n target j = _
      conv_lhs => unfold FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder.loop
      conv_rhs => unfold FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder.loop
      rw [if_pos hj, if_pos hj]
      show UCom.seq _ _ = UCom.seq _ _
      congr 1
      exact ih (n - (j+1)) (by omega) (j+1) rfl
    · show FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder.loop n target j = _
      conv_lhs => unfold FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder.loop
      conv_rhs => unfold FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder.loop
      rw [if_neg hj, if_neg hj]
      rfl

/-- Top-level bridge for `inverse_qft_phase_ladder`. -/
theorem inverse_qft_phase_ladder_map_id_bridge (m anc n target : Nat) :
    (@FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder (m + anc) n target
      : FormalRV.Framework.BaseUCom (m + anc))
    = map_qubits id
        (@FormalRV.Framework.BaseUCom.inverse_qft_phase_ladder m n target
          : FormalRV.Framework.BaseUCom m) :=
  inverse_qft_phase_ladder_loop_map_id_bridge m anc n target
    (n - (target+1)) (target+1) rfl

/-- Countdown-level bridge for `real_QFTinv_layer.countdown`. -/
theorem real_QFTinv_layer_countdown_map_id_bridge (m anc n : Nat) :
    ∀ k,
      (@FormalRV.Framework.BaseUCom.real_QFTinv_layer.countdown (m + anc) n k
        : FormalRV.Framework.BaseUCom (m + anc))
      = map_qubits id
          (@FormalRV.Framework.BaseUCom.real_QFTinv_layer.countdown m n k
            : FormalRV.Framework.BaseUCom m) := by
  intro k
  induction k with
  | zero =>
    show FormalRV.Framework.BaseUCom.real_QFTinv_layer.countdown n 0 = _
    conv_lhs => unfold FormalRV.Framework.BaseUCom.real_QFTinv_layer.countdown
    conv_rhs => unfold FormalRV.Framework.BaseUCom.real_QFTinv_layer.countdown
    rfl
  | succ k ih =>
    show FormalRV.Framework.BaseUCom.real_QFTinv_layer.countdown n (k+1) = _
    conv_lhs => unfold FormalRV.Framework.BaseUCom.real_QFTinv_layer.countdown
    conv_rhs => unfold FormalRV.Framework.BaseUCom.real_QFTinv_layer.countdown
    show UCom.seq _ _ = UCom.seq _ _
    rw [ih]
    congr 1
    exact inverse_qft_phase_ladder_map_id_bridge m anc n k

/-- **HEADLINE: Polymorphic-lift bridge for `real_QFTinv_layer`.**
The framework `real_QFTinv_layer n` constructed at `dim = m + anc`
equals the dim-`m` version lifted via `map_qubits id`. Proved by
structural induction over the recursive structure. -/
theorem real_QFTinv_layer_map_id_bridge (m anc n : Nat) :
    (@FormalRV.Framework.BaseUCom.real_QFTinv_layer (m + anc) n
      : FormalRV.Framework.BaseUCom (m + anc))
    = map_qubits id
        (@FormalRV.Framework.BaseUCom.real_QFTinv_layer m n
          : FormalRV.Framework.BaseUCom m) := by
  conv_lhs => unfold FormalRV.Framework.BaseUCom.real_QFTinv_layer
  conv_rhs => unfold FormalRV.Framework.BaseUCom.real_QFTinv_layer
  show UCom.seq _ _ = UCom.seq _ _
  rw [bit_reversal_swaps_map_id_bridge m anc n]
  congr 1
  exact real_QFTinv_layer_countdown_map_id_bridge m anc n n

end FormalRV.SQIRPort
