/- PhaseKickback — Part5 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.QPE.PhaseKickback.UniformSuperpositionEigenstate

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-! ## Explicit phase-weighted form of `phase_projector_product`

Converts the abstract `phase_projector_product ζ m` matrix into an
explicit phase-weighted sum over basis-control states. This is the
state shape that QFTinv will consume in the next pass. -/

/-- **Control bit at position `i`.** Boolean indicator of whether the
`i`-th qubit of `x : Fin (2^m)` (viewed via the framework's `padEquiv`
decomposition) is 1. Defined via `padEquiv m i hi` so it aligns with
`pad_u_proj{0,1}_on_basis_vector_{zero,one}`. -/
noncomputable def controlBit (m i : Nat) (hi : i < m) (x : Fin (2^m)) : Bool :=
  (((padEquiv m i hi).symm x).1.2 : Fin 2) = 1

/-- **Control bit ↔ binary digit.** The `controlBit m i hi x` Boolean is
true exactly when the `(m-i-1)`-th bit of `x.val` is set; this is the
MSB-first convention coming from `padEquiv`. -/
theorem controlBit_eq_digit (m i : Nat) (hi : i < m) (x : Fin (2^m)) :
    controlBit m i hi x = ((x.val / 2^(m-i-1)) % 2 = 1) := by
  unfold controlBit
  obtain ⟨⟨⟨xH, xM⟩, xL⟩, hx⟩ : ∃ p, padEquiv m i hi p = x :=
    ⟨(padEquiv m i hi).symm x, (padEquiv m i hi).apply_symm_apply x⟩
  rw [← hx]
  rw [Equiv.symm_apply_apply]
  have h_padEqv : (padEquiv m i hi ((xH, xM), xL)).val
                = xL.val + 2^(m-i-1) * (xM.val + 2 * xH.val) := by
    unfold padEquiv finProdFinEquiv
    simp
  rw [h_padEqv]
  have hxL : xL.val < 2^(m-i-1) := xL.isLt
  have hxM : xM.val < 2 := xM.isLt
  have h_div : (xL.val + 2^(m-i-1) * (xM.val + 2 * xH.val)) / 2^(m-i-1)
              = xM.val + 2 * xH.val := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos (m-i-1))]
    rw [Nat.div_eq_of_lt hxL]
    omega
  rw [h_div]
  have h_mod : (xM.val + 2 * xH.val) % 2 = xM.val := by
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hxM
  rw [h_mod]
  simp [Fin.ext_iff]

/-- **Numeric form of `controlBit`.** Returns the actual `Nat` digit
(0 or 1) of `x` at position `i` under the MSB-first convention. -/
noncomputable def controlBitNat (m i : Nat) (hi : i < m) (x : Fin (2^m)) : Nat :=
  if controlBit m i hi x then 1 else 0

/-- **Numeric `controlBit` equals the binary digit.** -/
theorem controlBitNat_eq_digit (m i : Nat) (hi : i < m) (x : Fin (2^m)) :
    controlBitNat m i hi x = (x.val / 2^(m-i-1)) % 2 := by
  unfold controlBitNat
  have h_eq := controlBit_eq_digit m i hi x
  by_cases h : controlBit m i hi x
  · rw [if_pos h]
    rw [h_eq] at h
    omega
  · rw [if_neg h]
    rw [h_eq] at h
    have h2 : (x.val / 2^(m-i-1)) % 2 < 2 := Nat.mod_lt _ (by omega)
    omega

/-- **Recursive phase prefix.** The scalar accumulated by applying the
first `k` phase projectors to the basis-control state `|x⟩`. Matches
the order of `phase_projector_product`. -/
noncomputable def phase_prefix (ζ : Nat → ℂ) (m : Nat) (x : Fin (2^m)) :
    Nat → ℂ
  | 0 => 1
  | k+1 =>
    (if h : k < m then
       (if controlBit m k h x then ζ k else 1)
     else 1) * phase_prefix ζ m x k

/-- Unfolding equation for `phase_prefix` at the successor case when
`k < m`. -/
theorem phase_prefix_succ {ζ : Nat → ℂ} {m : Nat} (x : Fin (2^m)) (k : Nat)
    (hk : k < m) :
    phase_prefix ζ m x (k+1) =
      (if controlBit m k hk x then ζ k else 1) * phase_prefix ζ m x k := by
  show (if h : k < m then if controlBit m k h x then ζ k else 1 else 1)
        * phase_prefix ζ m x k = _
  rw [dif_pos hk]

/-- **Single phase projector on basis-control kron.** The phase
projector `P0_i + ζ_i · P1_i` lifted to the combined `(m + anc)`-qubit
register acts on `kron_vec (basis_vector x) ψ` by leaving the data
register `ψ` unchanged and multiplying by `ζ_i` (when bit `i` of `x`
is 1) or `1` (when it is 0). -/
theorem phase_projector_on_kron_basis
    {m anc i : Nat} (hi : i < m)
    (ζi : ℂ)
    (x : Fin (2^m))
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    @phase_projector (m + anc) i ζi
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = (if controlBit m i hi x then ζi else 1) •
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  unfold phase_projector
  rw [Matrix.add_mul]
  rw [Matrix.smul_mul ζi (pad_u (m+anc) i proj1)
        (kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)]
  rw [pad_u_control_kron_vec_factors hi proj0 _ ψ]
  rw [pad_u_control_kron_vec_factors hi proj1 _ ψ]
  obtain ⟨⟨⟨xH, xM⟩, xL⟩, hx⟩ : ∃ p, padEquiv m i hi p = x :=
    ⟨(padEquiv m i hi).symm x, (padEquiv m i hi).apply_symm_apply x⟩
  subst hx
  rcases Fin.exists_fin_two.mp ⟨xM, rfl⟩ with rfl | rfl
  · rw [pad_u_proj0_on_basis_vector_zero hi xH xL]
    rw [pad_u_proj1_on_basis_vector_zero hi xH xL]
    have h_ctrl : controlBit m i hi (padEquiv m i hi ((xH, 0), xL)) = false := by
      unfold controlBit; rw [Equiv.symm_apply_apply]; simp
    rw [h_ctrl]
    rw [show kron_vec (0 : Matrix (Fin (2^m)) (Fin 1) ℂ) ψ = 0 from
        kron_vec_zero_left ψ]
    rw [smul_zero, add_zero]
    simp
  · rw [pad_u_proj0_on_basis_vector_one hi xH xL]
    rw [pad_u_proj1_on_basis_vector_one hi xH xL]
    have h_ctrl : controlBit m i hi (padEquiv m i hi ((xH, 1), xL)) = true := by
      unfold controlBit; rw [Equiv.symm_apply_apply]; simp
    rw [h_ctrl]
    rw [show kron_vec (0 : Matrix (Fin (2^m)) (Fin 1) ℂ) ψ = 0 from
        kron_vec_zero_left ψ]
    rw [zero_add]
    simp

/-- **Phase-projector-product prefix on basis-control kron.** Induction
on the inner index `k` (with `m` fixed): the prefix of `k` phase
projectors applied to `kron_vec (basis_vector x) ψ` yields the
`phase_prefix ζ m x k` scalar acting on the same kron state. -/
theorem phase_projector_product_prefix_on_kron_basis
    {m anc : Nat}
    (ζ : Nat → ℂ)
    (x : Fin (2^m))
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    ∀ k, k ≤ m →
      @phase_projector_product (m + anc) ζ k
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = phase_prefix ζ m x k •
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  intro k
  induction k with
  | zero =>
      intro _
      show (1 : Matrix (Fin (2^(m+anc))) (Fin (2^(m+anc))) ℂ) *
            kron_vec _ ψ = _
      rw [Matrix.one_mul]
      show kron_vec _ _ = (1 : ℂ) • _
      rw [one_smul]
  | succ k ih =>
      intro hk
      have hk_lt_m : k < m := hk
      have hk_le_m : k ≤ m := Nat.le_of_lt hk_lt_m
      show phase_projector k (ζ k) *
            @phase_projector_product (m + anc) ζ k *
            kron_vec _ _ = _
      rw [Matrix.mul_assoc]
      rw [ih hk_le_m]
      rw [Matrix.mul_smul]
      rw [phase_projector_on_kron_basis hk_lt_m (ζ k) x ψ]
      rw [smul_smul]
      rw [phase_prefix_succ x k hk_lt_m]
      ring_nf

/-- **Full phase-projector product on basis-control kron**: specialization
of the prefix theorem at `k = m`. -/
theorem phase_projector_product_on_kron_basis
    {m anc : Nat}
    (ζ : Nat → ℂ)
    (x : Fin (2^m))
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    @phase_projector_product (m + anc) ζ m
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = phase_prefix ζ m x m •
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ :=
  phase_projector_product_prefix_on_kron_basis ζ x ψ m (le_refl m)

/-- **PHASE-WEIGHTED FORM OF THE UNIFORM CONTROL SUM.** Applying the
phase-projector product to the H-prepared uniform superposition yields
the phase-weighted sum over basis-control states. This is the state
shape that QFTinv will consume in the next pass.

Proof: `Matrix.mul_smul` pulls the prefactor through, `Matrix.mul_sum`
distributes over the sum, then `phase_projector_product_on_kron_basis`
gives the per-term phase weight. -/
theorem phase_projector_product_on_uniform_control_sum
    {m anc : Nat}
    (ζ : Nat → ℂ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    @phase_projector_product (m + anc) ζ m
      * (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
          ∑ x : Fin (2^m),
            kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
    = ((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
        ∑ x : Fin (2^m),
          phase_prefix ζ m x m •
            kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  rw [Matrix.mul_smul]
  rw [Matrix.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact phase_projector_product_on_kron_basis ζ x ψ

/-- **LSB-first binary expansion.** Any `n < 2^m` is the sum of its
binary digits times the corresponding powers of two, with index `i`
weighted by `2^i`. -/
lemma binary_expansion_lsb (m n : Nat) (hn : n < 2^m) :
    n = ∑ i ∈ Finset.range m, ((n / 2^i) % 2) * 2^i := by
  induction m generalizing n with
  | zero => simp at hn; simp [hn]
  | succ k ih =>
      rw [Finset.sum_range_succ']
      have h_half : n/2 < 2^k := by
        have : 2^(k+1) = 2 * 2^k := by ring
        rw [this] at hn; omega
      have h_rec := ih (n/2) h_half
      simp only [pow_zero, Nat.div_one, pow_succ]
      have h_sum_eq : (∑ i ∈ Finset.range k, n / (2^i * 2) % 2 * (2^i * 2)) =
             2 * ∑ i ∈ Finset.range k, (n/2) / 2^i % 2 * 2^i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        have hki : n / (2^i * 2) = n/2 / 2^i := by
          rw [mul_comm, ← Nat.div_div_eq_div_mul]
        rw [hki]; ring
      rw [h_sum_eq, ← h_rec]
      omega

/-- **MSB-first binary expansion.** Same as `binary_expansion_lsb`
but reindexed so the `i`-th term is weighted by `2^(m-i-1)`, i.e.
the most-significant bit comes first (matching `padEquiv`'s
MSB-first decomposition). -/
lemma binary_expansion_msb (m n : Nat) (hn : n < 2^m) :
    n = ∑ i ∈ Finset.range m, ((n / 2^(m-i-1)) % 2) * 2^(m-i-1) := by
  conv_lhs => rw [binary_expansion_lsb m n hn]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have h_eq : m - 1 - i = m - i - 1 := by omega
  rw [h_eq]

/-- **Weighted control index.** The integer reconstructed from the
control bits of `x` under the MSB-first weighting. -/
noncomputable def controlWeightedIndex (m : Nat) (x : Fin (2^m)) : Nat :=
  ∑ i ∈ Finset.range m,
    (if h : i < m then controlBitNat m i h x else 0) * 2^(m-i-1)

/-- **Weighted control index equals `x.val`.** The phase-kickback
"weighted index" is exactly the underlying natural number — the
abstract bit-by-bit accumulation reassembles the binary expansion. -/
theorem controlWeightedIndex_eq_val (m : Nat) (x : Fin (2^m)) :
    controlWeightedIndex m x = x.val := by
  unfold controlWeightedIndex
  rw [binary_expansion_msb m x.val x.isLt]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [dif_pos hi]
  rw [controlBitNat_eq_digit m i hi x]

/-! ### Bridge from `phase_prefix` to the standard QPE phase

Specialize the abstract phase-prefix scalar to the QPE-eigenstate setting:
when the per-qubit eigenvalue at position `i` is `exp(2πi · 2^(m-i-1) · θ)`
(MSB-first weight, matching `padEquiv`'s middle-slot convention),
the accumulated phase factor collapses to `exp(2πi · x.val · θ)`. -/

/-- **QPE eigenvalue at qubit `i`.** The eigenvalue that the `i`-th
controlled-power gadget would impart on a phase-`θ` eigenstate, under
the MSB-first weighting `2^(m-i-1)`. -/
noncomputable def qpeEigenvalue (m i : Nat) (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (2^(m-i-1) : ℂ) * (θ : ℂ))

/-- **Partial weighted index.** Sum of `controlBitNat · 2^(m-i-1)` over
the first `k` qubits. At `k = m` this equals `controlWeightedIndex` and
hence `x.val`. -/
noncomputable def partialWeightedIndex (m k : Nat) (x : Fin (2^m)) : Nat :=
  ∑ i ∈ Finset.range k,
    (if h : i < m then controlBitNat m i h x else 0) * 2^(m-i-1)

/-- At `k = m`, the partial weighted index recovers `x.val`. -/
theorem partialWeightedIndex_at_m (m : Nat) (x : Fin (2^m)) :
    partialWeightedIndex m m x = x.val := by
  unfold partialWeightedIndex
  show (∑ i ∈ Finset.range m,
    (if h : i < m then controlBitNat m i h x else 0) * 2^(m-i-1)) = x.val
  exact controlWeightedIndex_eq_val m x

/-- Successor unfolding for the partial weighted index. -/
theorem partialWeightedIndex_succ (m k : Nat) (hk : k < m) (x : Fin (2^m)) :
    partialWeightedIndex m (k+1) x
      = partialWeightedIndex m k x
        + controlBitNat m k hk x * 2^(m-k-1) := by
  unfold partialWeightedIndex
  rw [Finset.sum_range_succ]
  congr 1
  rw [dif_pos hk]

/-- **Phase-prefix on QPE eigenvalues equals exp of weighted partial index.**
The accumulating phase factor for the QPE-specific eigenvalues collapses
to a single complex exponential whose argument is `2πi · θ · (partial sum)`. -/
theorem phase_prefix_qpe_eq_exp_partial (m : Nat) (θ : ℝ) (x : Fin (2^m)) :
    ∀ k, k ≤ m →
      phase_prefix (qpeEigenvalue m · θ) m x k
        = Complex.exp (2 * Real.pi * Complex.I *
            (partialWeightedIndex m k x : ℂ) * (θ : ℂ)) := by
  intro k
  induction k with
  | zero =>
      intro _
      unfold phase_prefix partialWeightedIndex
      simp
  | succ k ih =>
      intro hk
      have hk_lt_m : k < m := hk
      have hk_le_m : k ≤ m := Nat.le_of_lt hk_lt_m
      rw [phase_prefix_succ x k hk_lt_m]
      rw [ih hk_le_m]
      rw [partialWeightedIndex_succ m k hk_lt_m x]
      by_cases h : controlBit m k hk_lt_m x
      · rw [if_pos h]
        unfold qpeEigenvalue controlBitNat
        rw [if_pos h]
        push_cast
        rw [← Complex.exp_add]
        congr 1
        ring
      · rw [if_neg h]
        unfold controlBitNat
        rw [if_neg h]
        simp

/-- **Phase-prefix at full length equals `exp(2πi · x.val · θ)`.**
Combines `phase_prefix_qpe_eq_exp_partial` at `k = m` with
`partialWeightedIndex_at_m`. This is the bridge from the abstract
phase-projector cascade to the standard QPE phase-weighted form. -/
theorem phase_prefix_qpe_eq_exp_val (m : Nat) (θ : ℝ) (x : Fin (2^m)) :
    phase_prefix (qpeEigenvalue m · θ) m x m
      = Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) := by
  rw [phase_prefix_qpe_eq_exp_partial m θ x m (le_refl m)]
  rw [partialWeightedIndex_at_m m x]

/-! ### Explicit Fourier-form pre-QFT QPE theorem

Bundles the previous infrastructure into a single statement: the pre-QFT
half of QPE on a phase-`θ` eigenstate produces the standard QPE
phase-weighted superposition `(1/√2^m) · ∑_x exp(2πi · x · θ) |x⟩ ⊗ |ψ⟩`. -/

/-- **Pre-QFT QPE eigenstate result in explicit Fourier form.**

Given a data-register `ψ` such that each oracle `f i` (`i < m`) acts on
`ψ` as the QPE eigenvalue `exp(2πi · 2^(m-i-1) · θ)` (MSB-first
weighting), the composition `H^⊗m ; controlled_powers (shifted f) m`
applied to `|0^m⟩ ⊗ |ψ⟩` produces the phase-weighted Fourier
superposition `(1/√2^m) · ∑_x exp(2πi · x · θ) · |x⟩ ⊗ |ψ⟩`.

This is the state shape that a *real* `QFTinv` would consume to produce
`qpe_phase_state m θ ⊗ ψ`. The current `QFTinv` in
`Framework/QPE.lean` is a stub (see `QFTinv_is_stub` below); closing
`QPE_MMI_correct` further requires either implementing the real QFTinv
circuit or porting a QFT semantic axiom. -/
theorem QPE_pre_QFT_on_eigenstate_fourier_form
    {m anc : Nat} (hmanc : 0 < m + anc) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ)
    (θ : ℝ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (h_eig_data : ∀ i, i < m →
      FormalRV.Framework.uc_eval (f i) * ψ =
        qpeEigenvalue m i θ • ψ) :
    FormalRV.Framework.uc_eval (controlled_powers
        (fun i => (map_qubits (fun q => m + q) (f i) :
          FormalRV.Framework.BaseUCom (m + anc))) m)
      * (FormalRV.Framework.uc_eval
            (npar_H m : FormalRV.Framework.BaseUCom (m + anc))
          * kron_vec (FormalRV.Framework.kron_zeros m) ψ)
    = ((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
        ∑ x : Fin (2^m),
          Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
            kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  rw [QPE_pre_QFT_on_eigenstate hmanc hm f ψ (qpeEigenvalue m · θ)
        h_wt_all h_eig_data]
  rw [phase_projector_product_on_uniform_control_sum (qpeEigenvalue m · θ) ψ]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [phase_prefix_qpe_eq_exp_val m θ x]

/-! ### Status of QFTinv: currently a stub

The `QFTinv` definition at `Framework/QPE.lean:36` is `invert (QFT n)`,
where `QFT n` is itself a stub equal to `npar_H n`. Consequently
`QFTinv n = invert (npar_H n)`, which is *not* the inverse quantum
Fourier transform — it is just inverted Hadamards.

The following two theorems document this honestly. Any post-QFT
theorem that pretended to convert the Fourier-weighted superposition
above into `qpe_phase_state m θ` would be unsound until `QFT`/`QFTinv`
are replaced with their real circuit definitions. -/

-- HISTORICAL: `QFTinv_is_stub` proved `QFTinv n = invert (npar_H n)`
-- when `QFTinv` was a stub. Replaced 2026-05-26: `QFTinv n :=
-- real_QFTinv_layer n`, the actual recursive inverse-QFT circuit. The
-- correctness theorem is now `uc_eval_real_QFTinv_layer_eq_IQFT_matrix`
-- in `PostQFT.lean`.


end FormalRV.SQIRPort
