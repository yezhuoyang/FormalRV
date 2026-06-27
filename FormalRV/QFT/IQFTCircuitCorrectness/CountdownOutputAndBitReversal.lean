/- IQFTCircuitCorrectness — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.QFT.IQFTCircuitCorrectness.CountdownDecomposition

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-! ### Recursive countdown output + composition with bit reversal

The countdown circuit produces an exponentially-growing superposition
(one Hadamard branch per target). Rather than expanding this into a
single sum, we define the expected output recursively, matching the
state-action recurrence `countdown_succ_acts`, and prove the action
theorem against that recursive form. -/

/-- **Explicit two-branch ladder action.** Combines
`inverse_qft_phase_ladder_acts_on_f_to_vec` with `f_to_vec_H_uc_eval`
to expose the Hadamard expansion as a sum of two `f_to_vec` terms. -/
theorem inverse_qft_phase_ladder_explicit_on_f_to_vec
    (n target : Nat) (h_target : target < n)
    (f : Nat → Bool) :
    FormalRV.Framework.uc_eval
        (inverse_qft_phase_ladder n target : FormalRV.Framework.BaseUCom n)
      * f_to_vec n f
    = inverse_qft_ladder_phase n target f •
      (((Real.sqrt 2 / 2 : ℂ) • f_to_vec n (update f target false))
        + ((if f target then -(Real.sqrt 2 / 2 : ℂ) else (Real.sqrt 2 / 2 : ℂ))
            • f_to_vec n (update f target true))) := by
  rw [inverse_qft_phase_ladder_acts_on_f_to_vec n target h_target f]
  rw [f_to_vec_H_uc_eval n target h_target]
  congr 1
  by_cases h : f target
  · rw [if_pos h, if_pos h]; simp
  · rw [if_neg h, if_neg h]; simp

theorem countdown_output_zero (n : Nat) (f : Nat → Bool) :
    countdown_output n 0 f = f_to_vec n f := rfl

theorem countdown_output_succ (n k : Nat) (f : Nat → Bool) :
    countdown_output n (k+1) f
      = inverse_qft_ladder_phase n k f •
          (((Real.sqrt 2 / 2 : ℂ) • countdown_output n k (update f k false))
            + ((if f k then -(Real.sqrt 2 / 2 : ℂ) else (Real.sqrt 2 / 2 : ℂ))
                • countdown_output n k (update f k true))) := rfl

/-- **HEADLINE: Countdown action on `f_to_vec`.** Applying `countdown n k`
to a basis vector `f_to_vec n f` produces `countdown_output n k f`,
the recursively-defined expected output. Proof by induction on k,
using `countdown_succ_acts` and the explicit ladder action. -/
theorem countdown_acts_on_f_to_vec (n : Nat) (hn : 0 < n) :
    ∀ k, k ≤ n → ∀ (f : Nat → Bool),
      FormalRV.Framework.uc_eval
          (real_QFTinv_layer.countdown n k : FormalRV.Framework.BaseUCom n)
        * f_to_vec n f
      = countdown_output n k f := by
  intro k
  induction k with
  | zero => intro hk f; rw [countdown_zero_acts n hn]; rfl
  | succ k ih =>
    intro hk f
    have hk_lt : k < n := by omega
    have hk_le : k ≤ n := by omega
    rw [countdown_succ_acts]
    rw [inverse_qft_phase_ladder_explicit_on_f_to_vec n k hk_lt f]
    rw [Matrix.mul_smul, Matrix.mul_add]
    rw [Matrix.mul_smul, Matrix.mul_smul]
    rw [ih hk_le (update f k false)]
    rw [ih hk_le (update f k true)]
    rfl

/-- **Full `real_QFTinv_layer` action on `f_to_vec`.** Combines bit-reversal
and countdown: the layer applied to `f_to_vec n f` equals
`countdown_output n n (applySwapsFrom n 0 f)`. -/
theorem real_QFTinv_layer_output_on_f_to_vec
    (n : Nat) (hn : 0 < n) (f : Nat → Bool) :
    FormalRV.Framework.uc_eval (real_QFTinv_layer n : FormalRV.Framework.BaseUCom n)
      * f_to_vec n f
    = countdown_output n n (applySwapsFrom n 0 f) := by
  rw [real_QFTinv_layer_acts]
  rw [bit_reversal_swaps_acts_on_f_to_vec n hn f]
  exact countdown_acts_on_f_to_vec n hn n (le_refl n) _

/-- **`n = 1`: recursive layer matches `IQFT_matrix 1`.** Trivial since
`bit_reversal_swaps 1 = SKIP`, `countdown 1 = H 0 ; SKIP`, and the
matrix theorem for `H 0` is already in place. -/
theorem uc_eval_real_QFTinv_layer_eq_IQFT_matrix_one :
    FormalRV.Framework.uc_eval (real_QFTinv_layer 1 : FormalRV.Framework.BaseUCom 1)
      = IQFT_matrix 1 := by
  rw [real_QFTinv_layer_decomp]
  show FormalRV.Framework.uc_eval
        (UCom.seq (bit_reversal_swaps 1) (real_QFTinv_layer.countdown 1 1)) = IQFT_matrix 1
  rw [show (bit_reversal_swaps 1 : FormalRV.Framework.BaseUCom 1) = SKIP from by
    unfold bit_reversal_swaps
    rw [bit_reversal_loop_base 1 0 (by omega)]]
  rw [countdown_succ]
  rw [show real_QFTinv_layer.countdown 1 0 = (SKIP : FormalRV.Framework.BaseUCom 1)
       from countdown_zero 1]
  rw [show (inverse_qft_phase_ladder 1 0 : FormalRV.Framework.BaseUCom 1)
        = FormalRV.Framework.BaseUCom.H 0 from by
    unfold inverse_qft_phase_ladder
    rw [ladder_loop_base 1 0 1 (by omega)]]
  show FormalRV.Framework.uc_eval (UCom.seq (SKIP : FormalRV.Framework.BaseUCom 1)
        (UCom.seq (FormalRV.Framework.BaseUCom.H 0) (SKIP))) = IQFT_matrix 1
  rw [show (SKIP : FormalRV.Framework.BaseUCom 1) = ID 0 from rfl]
  show FormalRV.Framework.uc_eval (UCom.seq (ID 0) (UCom.seq (BaseUCom.H 0) (ID 0)))
      = IQFT_matrix 1
  rw [show FormalRV.Framework.uc_eval (UCom.seq (ID 0)
        (UCom.seq (BaseUCom.H 0) (ID 0)) : FormalRV.Framework.BaseUCom 1)
        = FormalRV.Framework.uc_eval (UCom.seq (BaseUCom.H 0) (ID 0))
          * FormalRV.Framework.uc_eval (ID 0) from rfl]
  rw [uc_eval_ID_eq_one (show (0:Nat) < 1 from by omega), Matrix.mul_one]
  rw [show FormalRV.Framework.uc_eval (UCom.seq (BaseUCom.H 0) (ID 0) :
        FormalRV.Framework.BaseUCom 1)
        = FormalRV.Framework.uc_eval (ID 0)
          * FormalRV.Framework.uc_eval (BaseUCom.H 0) from rfl]
  rw [uc_eval_ID_eq_one (show (0:Nat) < 1 from by omega), Matrix.one_mul]
  exact uc_eval_real_QFTinv_eq_IQFT_matrix_one

/-! ### Matching countdown_output to IQFT_matrix column

The final semantic bridge: `countdown_output n n (applySwapsFrom n 0 ...)`
should equal `IQFT_matrix n · basis_vector x`. This section closes
small cases (n=1, n=2) and provides the entry-formula API for the
arbitrary-n induction. -/

/-- **Entry formula for IQFT_matrix · basis_vector.** Picks out the
`(y, x)` entry of `IQFT_matrix`. -/
theorem IQFT_matrix_mul_basis_apply (n : Nat) (x y : Fin (2^n)) :
    (IQFT_matrix n * FormalRV.Framework.basis_vector (2^n) x.val) y 0
    = IQFT_matrix n y x := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single x]
  · rw [show (FormalRV.Framework.basis_vector (2^n) x.val) x 0 = 1 from by
      rw [basis_vector_apply]; simp]
    ring
  · intro i _ hix
    rw [show (FormalRV.Framework.basis_vector (2^n) x.val) i 0 = 0 from by
      rw [basis_vector_apply]
      have : i.val ≠ x.val := fun h => hix (Fin.ext h)
      simp [this]]
    ring
  · simp

/-- **`n = 1` column equality**: derived from the n=1 layer matrix
correctness via the `real_QFTinv_layer_output_on_f_to_vec` bridge. -/
theorem countdown_output_eq_IQFT_column_one (x : Fin (2^1)) :
    countdown_output 1 1 (applySwapsFrom 1 0 (nat_to_funbool 1 x.val))
    = IQFT_matrix 1 * FormalRV.Framework.basis_vector (2^1) x.val := by
  rw [← real_QFTinv_layer_output_on_f_to_vec 1 (by omega) _]
  rw [uc_eval_real_QFTinv_layer_eq_IQFT_matrix_one]
  rw [show f_to_vec 1 (nat_to_funbool 1 x.val)
        = FormalRV.Framework.basis_vector (2^1) x.val from
      (basis_vector_eq_f_to_vec_nat_to_funbool 1 x).symm]

/-- **`n = 2` column equality**: derived from the n=2 layer matrix
correctness. -/
theorem countdown_output_eq_IQFT_column_two (x : Fin (2^2)) :
    countdown_output 2 2 (applySwapsFrom 2 0 (nat_to_funbool 2 x.val))
    = IQFT_matrix 2 * FormalRV.Framework.basis_vector (2^2) x.val := by
  rw [← real_QFTinv_layer_output_on_f_to_vec 2 (by omega) _]
  rw [uc_eval_real_QFTinv_layer_eq_IQFT_matrix_two]
  rw [show f_to_vec 2 (nat_to_funbool 2 x.val)
        = FormalRV.Framework.basis_vector (2^2) x.val from
      (basis_vector_eq_f_to_vec_nat_to_funbool 2 x).symm]

/-- **`n = 1` column equality** in `countdownColumn` form. -/
theorem countdownColumn_eq_IQFT_column_one (x : Fin (2^1)) :
    countdownColumn 1 x = IQFT_matrix 1 * FormalRV.Framework.basis_vector (2^1) x.val := by
  unfold countdownColumn bitReversedBasisFun basisFunOfIndex
  exact countdown_output_eq_IQFT_column_one x

/-- **`n = 2` column equality** in `countdownColumn` form. -/
theorem countdownColumn_eq_IQFT_column_two (x : Fin (2^2)) :
    countdownColumn 2 x = IQFT_matrix 2 * FormalRV.Framework.basis_vector (2^2) x.val := by
  unfold countdownColumn bitReversedBasisFun basisFunOfIndex
  exact countdown_output_eq_IQFT_column_two x

/-! ### Dimension-split lemmas: (n+1)-qubit ↔ n-qubit + extra qubit

**Convention** (established by inspecting `countdown_output` /
`inverse_qft_phase_ladder`):

- Qubit `n` (the LSB in MSB-first convention) is the "untouched" extra
  qubit when going from `(n+1)`-qubit to `n`-qubit systems.
- For `k ≤ n`, `countdown_output (n+1) k f` processes ladders for
  targets `0..k-1`. Qubit `n` is never a target (never Hadamard'd),
  but is a CONTROL for every target `< n`, contributing extra phase
  factors.
- The split is therefore NOT a clean tensor product — there's an
  extra phase from qubit `n`'s controlling role. -/

/-- **`f_to_vec` dimension split.** `f_to_vec (n+1) f` factors as the
kron product of `f_to_vec n f` (using the lower n bits) and a
1-qubit basis vector encoding `f n`. -/
theorem f_to_vec_dim_split (n : Nat) (f : Nat → Bool) :
    f_to_vec (n+1) f
    = kron_vec (f_to_vec n f)
        (FormalRV.Framework.basis_vector 2 (if f n then 1 else 0)) := by
  unfold f_to_vec
  have h_fb_ne_pow : funbool_to_nat n f < 2^n := funbool_to_nat_lt n f
  have h_bit_lt : (if f n then 1 else 0) < 2 := by split_ifs <;> omega
  rw [show (FormalRV.Framework.basis_vector (2^n) (funbool_to_nat n f)
        : Matrix (Fin (2^n)) (Fin 1) ℂ)
        = FormalRV.Framework.basis_vector (2^n)
            (⟨funbool_to_nat n f, h_fb_ne_pow⟩ : Fin (2^n)).val from rfl]
  rw [show (FormalRV.Framework.basis_vector 2 (if f n then 1 else 0)
        : Matrix (Fin 2) (Fin 1) ℂ)
        = FormalRV.Framework.basis_vector (2^1)
            (⟨if f n then 1 else 0, h_bit_lt⟩ : Fin (2^1)).val from by simp]
  rw [kron_vec_basis_eq_basis_combine n 1
        ⟨funbool_to_nat n f, h_fb_ne_pow⟩ ⟨if f n then 1 else 0, h_bit_lt⟩]
  unfold kron_vec_combine
  congr 1
  show funbool_to_nat (n+1) f = funbool_to_nat n f * 2^1 + (if f n then 1 else 0)
  rw [show funbool_to_nat (n+1) f
        = 2 * funbool_to_nat n f + (if f n then 1 else 0) from rfl]
  ring

/-- **Ladder phase dimension split.** For `target < n`, the
`(n+1)`-qubit ladder phase factors as `(extra factor from qubit n) ·
(n-qubit ladder phase)`. The extra factor is the controlled-Rz
contribution from the highest qubit `n` onto the target. -/
theorem inverse_qft_ladder_phase_dim_split
    (n target : Nat) (h_target : target < n)
    (f : Nat → Bool) :
    inverse_qft_ladder_phase (n+1) target f
    = (if f n ∧ f target then
         Complex.exp ((((-(Real.pi / 2 ^ (n - target))) : ℝ)) * Complex.I)
       else 1)
      * inverse_qft_ladder_phase n target f := by
  unfold inverse_qft_ladder_phase inverse_qft_ladder_phase_from
  rw [Nat.Ico_succ_right_eq_insert_Ico (by omega : target + 1 ≤ n)]
  rw [Finset.prod_insert]
  · intro h
    rw [Finset.mem_Ico] at h
    omega

/-- `embedWithExtraBit` commutes with scalar multiplication. -/
theorem embedWithExtraBit_smul (n : Nat) (extra : Bool) (c : ℂ)
    (v : Matrix (Fin (2^n)) (Fin 1) ℂ) :
    embedWithExtraBit n extra (c • v) = c • embedWithExtraBit n extra v := by
  unfold embedWithExtraBit; rw [kron_vec_smul_left]

/-- `embedWithExtraBit` commutes with addition. -/
theorem embedWithExtraBit_add (n : Nat) (extra : Bool)
    (v w : Matrix (Fin (2^n)) (Fin 1) ℂ) :
    embedWithExtraBit n extra (v + w)
    = embedWithExtraBit n extra v + embedWithExtraBit n extra w := by
  unfold embedWithExtraBit; rw [kron_vec_add_left]

theorem cumulative_extra_phase_zero (n : Nat) (f : Nat → Bool) :
    cumulative_extra_phase n 0 f = 1 := by
  unfold cumulative_extra_phase; simp

theorem cumulative_extra_phase_succ (n k : Nat) (f : Nat → Bool) :
    cumulative_extra_phase n (k+1) f
    = cumulative_extra_phase n k f *
      (if f n ∧ f k then
        Complex.exp ((((-(Real.pi / 2 ^ (n - k))) : ℝ)) * Complex.I)
      else 1) := by
  unfold cumulative_extra_phase
  rw [Finset.prod_range_succ]

/-- **Extra-bit update lemma**: updating position `k < n` doesn't change
the value at position `n`. -/
theorem extra_bit_update_lt (n k : Nat) (hk : k < n) (f : Nat → Bool) (b : Bool) :
    update f k b n = f n := by
  unfold update; rw [if_neg (by omega)]

/-- **Cumulative extra phase update-branch lemma**: updating position
`k < n` doesn't change the cumulative extra phase product over targets
`t ∈ [0, k)`. -/
theorem cumulative_extra_phase_update_branch
    (n k : Nat) (hk : k < n) (f : Nat → Bool) (b : Bool) :
    cumulative_extra_phase n k (update f k b)
    = cumulative_extra_phase n k f := by
  unfold cumulative_extra_phase
  apply Finset.prod_congr rfl
  intro t ht
  rw [Finset.mem_range] at ht
  have htk : t ≠ k := by omega
  rw [extra_bit_update_lt n k hk f b]
  rw [show update f k b t = f t from by unfold update; rw [if_neg htk]]

/-- **HEADLINE: Countdown output dimension split.** For `k ≤ n`, the
`(n+1)`-qubit countdown output factors as a cumulative-extra-phase
scalar times the n-qubit countdown output embedded with the
extra-bit `f n`. Proof by induction on k: base via
`f_to_vec_dim_split`; successor via `inverse_qft_ladder_phase_dim_split`
+ the update lemmas + bilinearity of `embedWithExtraBit`, closed by
`module`. -/
theorem countdown_output_dim_split (n : Nat) :
    ∀ k, k ≤ n → ∀ (f : Nat → Bool),
      countdown_output (n+1) k f
      = cumulative_extra_phase n k f •
        embedWithExtraBit n (f n) (countdown_output n k f) := by
  intro k
  induction k with
  | zero =>
    intro hk f
    rw [countdown_output_zero, countdown_output_zero]
    rw [cumulative_extra_phase_zero, one_smul]
    unfold embedWithExtraBit
    exact f_to_vec_dim_split n f
  | succ k ih =>
    intro hk f
    have hk_lt : k < n := by omega
    have hk_le : k ≤ n := by omega
    rw [countdown_output_succ, countdown_output_succ]
    rw [ih hk_le (update f k false), ih hk_le (update f k true)]
    rw [extra_bit_update_lt n k hk_lt f false, extra_bit_update_lt n k hk_lt f true]
    rw [cumulative_extra_phase_update_branch n k hk_lt f false]
    rw [cumulative_extra_phase_update_branch n k hk_lt f true]
    rw [inverse_qft_ladder_phase_dim_split n k hk_lt f]
    rw [cumulative_extra_phase_succ n k f]
    rw [embedWithExtraBit_smul, embedWithExtraBit_add,
        embedWithExtraBit_smul, embedWithExtraBit_smul]
    module

/-- **Full-k specialization** of `countdown_output_dim_split`: at `k = n`,
the (n+1)-qubit countdown output factors through the full n-qubit
countdown. -/
theorem countdown_output_dim_split_full (n : Nat) (f : Nat → Bool) :
    countdown_output (n+1) n f
    = cumulative_extra_phase n n f •
      embedWithExtraBit n (f n) (countdown_output n n f) :=
  countdown_output_dim_split n n (le_refl n) f

/-- **Index reconstruction**: `y.val = high_n.val · 2 + lsb.val`. -/
theorem iqft_index_reconstruct_highN_low1 (n : Nat) (y : Fin (2^(n+1))) :
    y.val = (iqftHighBitsN n y).val * 2 + (iqftLowBitLSB n y).val := by
  show y.val = (y.val / 2) * 2 + y.val % 2
  rw [Nat.div_add_mod' y.val 2]

/-! ### Bit-reversal action formula and successor split

The bit-reversal cascade `applySwapsFrom n 0 f` maps position `i` to
the value at position `n-1-i` of the original `f`, for `i < n`. This
unlocks the bit-reversal successor split lemmas that bridge the
(n+1)-qubit and n-qubit countdown columns. -/

/-- `swapBits f a b a = f b`. -/
theorem swapBits_left (f : Nat → Bool) (a b : Nat) :
    swapBits f a b a = f b := by unfold swapBits; simp

/-- `swapBits f a b b = f a` (when `a ≠ b`). -/
theorem swapBits_right (f : Nat → Bool) (a b : Nat) (hab : a ≠ b) :
    swapBits f a b b = f a := by
  unfold swapBits; rw [if_neg (Ne.symm hab), if_pos rfl]

/-- `swapBits f a b i = f i` when `i ∉ {a, b}`. -/
theorem swapBits_other (f : Nat → Bool) (a b i : Nat) (hia : i ≠ a) (hib : i ≠ b) :
    swapBits f a b i = f i := by
  unfold swapBits; rw [if_neg hia, if_neg hib]

/-- **Partial-reversal invariant.** Starting from index `k`,
`applySwapsFrom n k f` reverses positions in `[k, n-1-k]` (and leaves
positions outside this range unchanged). Proof by strong induction
on `n - 2*k`. -/
theorem applySwapsFrom_apply_region (n : Nat) :
    ∀ (m k : Nat), n - 2 * k = m → ∀ (f : Nat → Bool) (i : Nat),
      applySwapsFrom n k f i =
        if k ≤ i ∧ i ≤ n - 1 - k then f (n - 1 - i) else f i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hm f i
    by_cases hk_lt : 2 * k + 1 < n
    · rw [applySwapsFrom_step n k f hk_lt]
      rw [ih (n - 2 * (k+1)) (by omega) (k+1) rfl (swapBits f k (n-1-k)) i]
      by_cases hi_eq_k : i = k
      · rw [hi_eq_k, if_neg (by omega : ¬(k + 1 ≤ k ∧ k ≤ n - 1 - (k+1))),
            swapBits_left, if_pos (by omega : k ≤ k ∧ k ≤ n - 1 - k)]
      · by_cases hi_eq_nk : i = n - 1 - k
        · rw [hi_eq_nk, if_neg (by omega : ¬(k + 1 ≤ n - 1 - k ∧ n - 1 - k ≤ n - 1 - (k+1)))]
          rw [swapBits_right f k (n-1-k) (by omega : k ≠ n - 1 - k)]
          rw [if_pos (by omega : k ≤ n - 1 - k ∧ n - 1 - k ≤ n - 1 - k)]
          rw [show n - 1 - (n - 1 - k) = k from by omega]
        · by_cases hi_inner : k + 1 ≤ i ∧ i ≤ n - 1 - (k+1)
          · rw [if_pos hi_inner]
            rw [swapBits_other f k (n-1-k) (n-1-i) (by omega) (by omega)]
            rw [if_pos (by omega : k ≤ i ∧ i ≤ n - 1 - k)]
          · rw [if_neg hi_inner, swapBits_other f k (n-1-k) i hi_eq_k hi_eq_nk]
            rw [if_neg (by omega : ¬(k ≤ i ∧ i ≤ n - 1 - k))]
    · rw [applySwapsFrom_base n k f hk_lt]
      by_cases h_then : k ≤ i ∧ i ≤ n - 1 - k
      · rw [if_pos h_then, ← (show i = n - 1 - i from by omega)]
      · rw [if_neg h_then]


end FormalRV.SQIRPort
