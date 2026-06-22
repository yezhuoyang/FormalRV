/-
  FormalRV.QPE.QPECorrectness
  ───────────────────────────
  THE semantic-correctness theorems for Quantum Phase Estimation, on an
  ABSTRACT (black-box) oracle family `f : Nat → BaseUCom anc`.  These are the
  QPE-generic results — they make NO reference to modular exponentiation (that
  instantiation is Shor's job: `Shor/PostQFT/QPEModmultEigenstate.lean`).

  Relocated here (2026-06-10) out of `QFT/IQFTRecursiveArbitrary.lean`, where
  they had been developed alongside the inverse-QFT correctness but did not
  belong: they are QPE's semantics, not the QFT's.  The QFT file now holds only
  the inverse-QFT correctness + the SQIRPort↔Framework bridges they depend on,
  which this file imports.

  THE headline:
    • `QPE_var_on_eigenstate_from_real_QFTinv`  — MSB-first: for an eigenstate
      `ψ` of each oracle `f i` with eigenvalue `qpeEigenvalue m i θ`, running
      `QPE_var m anc f` on `|0^m⟩ ⊗ ψ` yields `qpe_phase_state m θ ⊗ ψ`.
    • `QPE_var_lsb_on_eigenstate_from_real_QFTinv` — the LSB-first analogue
      (eigenvalue `exp(2πi · 2^i · θ)`), the convention Shor uses.
  Both are UNCONDITIONAL (no `h_IQFT` hypothesis) — the inverse-QFT matrix
  correctness is now proven for arbitrary `n`.  The measurement peak bound
  `qpe_prob_peak_bound` (≥ 4/π²) lives in `QPEAmplitude.lean`.
-/
import FormalRV.QFT.IQFTRecursiveArbitrary

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom
/-! ### Lifted real-IQFT-layer post-QFT theorem

The arbitrary-n analogue of `real_QFTinv_on_fourier_weighted_kron_state_from_matrix_correct`,
unconditionally (no `h_IQFT` hypothesis needed — the matrix correctness is now
proven for arbitrary n). -/

/-- **Lifted real-IQFT-layer factors through `kron_vec`.** The
`real_QFTinv_layer m` lifted to `m + anc` qubits acts on `kron_vec ψc ψd`
by applying `IQFT_matrix m` to the control factor `ψc`. Combines
`uc_eval_control_register_circuit_kron_vec` with the arbitrary-n
layer matrix correctness. -/
theorem real_QFTinv_layer_lifted_on_kron
    {m anc : Nat} (hm : 0 < m)
    (ψc : Matrix (Fin (2^m)) (Fin 1) ℂ)
    (ψd : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => q) (real_QFTinv_layer m)
          : FormalRV.Framework.BaseUCom (m + anc))
      * kron_vec ψc ψd
    = kron_vec (IQFT_matrix m * ψc) ψd := by
  rw [uc_eval_control_register_circuit_kron_vec (real_QFTinv_layer m)
        (wellTyped_real_QFTinv_layer m hm) ψc ψd]
  rw [uc_eval_real_QFTinv_layer_eq_IQFT_matrix m hm]

/-- **HEADLINE: Lifted real-IQFT-layer on Fourier-weighted state.**
The arbitrary-n analogue of `real_QFTinv_on_fourier_weighted_kron_state_from_matrix_correct`,
NOW UNCONDITIONAL: the `h_IQFT` hypothesis is discharged by
`uc_eval_real_QFTinv_layer_eq_IQFT_matrix`. -/
theorem real_QFTinv_layer_on_fourier_weighted_kron_state
    {m anc : Nat} (hm : 0 < m) (θ : ℝ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => q) (real_QFTinv_layer m)
          : FormalRV.Framework.BaseUCom (m + anc))
      *
    (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
      ∑ x : Fin (2^m),
        Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
    = kron_vec (qpe_phase_state m θ) ψ := by
  rw [fourier_weighted_kron_sum_eq_kron_vec_fourier_state]
  rw [real_QFTinv_layer_lifted_on_kron hm _ ψ]
  rw [IQFT_matrix_on_fourier_weighted_state m θ]

/-- **HEADLINE: Unconditional real-QPE-layer single-eigenstate theorem.**
Given a data-register `ψ` that is a QPE eigenstate (i.e., each oracle
`f i` acts on `ψ` as `qpeEigenvalue m i θ`), the `real_QPE_layer m anc f`
applied to `|0^m⟩ ⊗ ψ` produces `kron_vec (qpe_phase_state m θ) ψ`.

UNLIKE `real_QPE_on_eigenstate_from_IQFT_correct`, this theorem has
NO `h_IQFT` hypothesis — the matrix correctness is now built into
`real_QFTinv_layer`'s definition via
`uc_eval_real_QFTinv_layer_eq_IQFT_matrix`. -/
theorem real_QPE_layer_on_eigenstate
    {m anc : Nat} (hmanc : 0 < m + anc) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) (θ : ℝ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (h_eig_data : ∀ i, i < m →
      FormalRV.Framework.uc_eval (f i) * ψ =
        qpeEigenvalue m i θ • ψ) :
    FormalRV.Framework.uc_eval (real_QPE_layer m anc f)
      * kron_vec (FormalRV.Framework.kron_zeros m) ψ
    = kron_vec (qpe_phase_state m θ) ψ := by
  unfold real_QPE_layer
  rw [uc_eval_seq_mul, uc_eval_seq_mul]
  rw [QPE_pre_QFT_on_eigenstate_fourier_form hmanc hm f ψ θ h_wt_all h_eig_data]
  exact real_QFTinv_layer_on_fourier_weighted_kron_state hm θ ψ

/-! ### Framework QFTinv on Fourier-weighted kron state + QPE_var eigenstate

These are the final wrappers: directly stated about the framework
`QFTinv` (at `dim = m + anc`) and `QPE_var`. The proofs go through
the polymorphic-lift bridge + the SQIRPort vs Framework bridge +
the existing `real_QFTinv_layer_on_fourier_weighted_kron_state`. -/

/-- **HEADLINE: Framework `QFTinv` (lifted) on Fourier-weighted kron state.**
Direct analogue of `real_QFTinv_layer_on_fourier_weighted_kron_state`,
stated for the framework `QFTinv m : BaseUCom (m + anc)` (rather than
the SQIRPort-lifted version). Proof: unfold `QFTinv`; apply the
polymorphic-lift bridge to convert to the dim-`m` version via
`map_qubits id`; apply the SQIRPort bridge to convert to
`SQIRPort.real_QFTinv_layer`; apply the existing fourier-weighted theorem. -/
theorem QFTinv_on_fourier_weighted_kron_state
    {m anc : Nat} (hm : 0 < m) (θ : ℝ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (FormalRV.Framework.BaseUCom.QFTinv m
          : FormalRV.Framework.BaseUCom (m + anc))
      *
    (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
      ∑ x : Fin (2^m),
        Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
    = kron_vec (qpe_phase_state m θ) ψ := by
  unfold FormalRV.Framework.BaseUCom.QFTinv
  rw [real_QFTinv_layer_map_id_bridge m anc m]
  rw [show (@FormalRV.Framework.BaseUCom.real_QFTinv_layer m m
              : FormalRV.Framework.BaseUCom m)
        = (FormalRV.SQIRPort.real_QFTinv_layer m
            : FormalRV.Framework.BaseUCom m) from
        (real_QFTinv_layer_bridge m).symm]
  exact real_QFTinv_layer_on_fourier_weighted_kron_state hm θ ψ

/-- **HEADLINE: `QPE_var` on QPE eigenstate (real IQFT).** The first
fully-unconditional QPE eigenstate theorem for the framework
`QPE_var` (which underlies `Shor_final_state`). Given a data-register
eigenstate `ψ` with the standard QPE eigenvalue data on each oracle,
`QPE_var m anc f` applied to `|0^m⟩ ⊗ ψ` yields `qpe_phase_state m θ ⊗ ψ`.

Proof: unfold `QPE_var` and `BaseUCom.QPE`; chain through
`QPE_pre_QFT_on_eigenstate_fourier_form` (existing); finish with
`QFTinv_on_fourier_weighted_kron_state`. -/
theorem QPE_var_on_eigenstate_from_real_QFTinv
    {m anc : Nat} (hmanc : 0 < m + anc) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) (θ : ℝ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (h_eig_data : ∀ i, i < m →
      FormalRV.Framework.uc_eval (f i) * ψ =
        qpeEigenvalue m i θ • ψ) :
    FormalRV.Framework.uc_eval (FormalRV.SQIRPort.QPE_var m anc f)
      * kron_vec (FormalRV.Framework.kron_zeros m) ψ
    = kron_vec (qpe_phase_state m θ) ψ := by
  unfold FormalRV.SQIRPort.QPE_var
  rw [FormalRV.Framework.BaseUCom.QPE_def_unfold]
  rw [uc_eval_seq_mul, uc_eval_seq_mul]
  rw [QPE_pre_QFT_on_eigenstate_fourier_form hmanc hm f ψ θ h_wt_all h_eig_data]
  exact QFTinv_on_fourier_weighted_kron_state hm θ ψ

/-! ### LSB-compatible QPE wrapper (convention bridge)

The framework's `qpeEigenvalue m i θ = exp(2π·I · 2^(m-i-1) · θ)` assumes
MSB-first weight at oracle index `i`. The `ModMulImpl`-style oracle family
`f i = U^{2^i}` instead gives LSB-first weight `2^i` at oracle index `i`.
The two conventions differ by an index reversal `i ↔ m - 1 - i`.

This section defines `QPE_var_lsb m anc f` — a wrapper that pre-reverses
the oracle family, so that the underlying MSB-first QPE machinery
(`QPE_var_on_eigenstate_from_real_QFTinv`) can be applied to an
LSB-first eigenvalue hypothesis. Together with the upcoming modular-
multiplier eigenstate eigenvalue theorem in LSB form, this is the
convention bridge that unblocks `QPE_MMI_correct`. -/

-- Note: `revIndex`, `revIndex_lt`, and `QPE_var_lsb` moved to
-- `Shor.lean` (2026-05-27) so `Shor_final_state` can be defined in
-- terms of `QPE_var_lsb`. They remain accessible here via the
-- `namespace FormalRV.SQIRPort` shared between files.

/-- **Eigenvalue bridge**: the framework's MSB-first `qpeEigenvalue m j θ`
at reversed index `j = m - 1 - i` equals the natural LSB-first eigenvalue
`exp(2π·I · 2^i · θ)`. Substitutes `m - (m-1-i) - 1 = i` to reduce the
weight in qpeEigenvalue from `2^(m-(m-1-i)-1) = 2^i`. -/
theorem qpeEigenvalue_reverse_index_eq_lsb
    (m i : Nat) (_hi : i < m) (θ : ℝ) :
    qpeEigenvalue m (m - 1 - i) θ
      = Complex.exp (((2 * Real.pi * ((2^i : Nat) : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
  unfold qpeEigenvalue
  congr 1
  have h_eq : m - (m - 1 - i) - 1 = i := by omega
  rw [h_eq]
  push_cast
  ring

/-- **HEADLINE: LSB-compatible QPE eigenstate theorem.** The natural
LSB-first analogue of `QPE_var_on_eigenstate_from_real_QFTinv`. Given a
data-register eigenstate `ψ` with LSB-first eigenvalue weights
(`uc_eval (f i) * ψ = exp(2π·I · 2^i · θ) • ψ` for each oracle index `i`),
the `QPE_var_lsb m anc f` circuit applied to `|0^m⟩ ⊗ ψ` produces
`kron_vec (qpe_phase_state m θ) ψ`.

Proof: unfold `QPE_var_lsb`; apply `QPE_var_on_eigenstate_from_real_QFTinv`
to the reversed family `fun j => f (revIndex m j)`; discharge the
well-typedness obligation via `revIndex_lt` + `h_wt_all`; discharge the
eigenvalue obligation by chaining `h_eig_lsb` at index `revIndex m j`
with the index-arithmetic identity `m - 1 - (m-1-j) = j` (equivalently
`m - (m-1-j) - 1 = j`, so the qpeEigenvalue weight `2^(m-(m-1-j)-1) = 2^j`
matches the LSB-first weight at the reversed index). -/
theorem QPE_var_lsb_on_eigenstate_from_real_QFTinv
    {m anc : Nat} (hmanc : 0 < m + anc) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) (θ : ℝ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (h_eig_lsb : ∀ i, i < m →
      FormalRV.Framework.uc_eval (f i) * ψ =
        Complex.exp (((2 * Real.pi * ((2^i : Nat) : ℝ) * θ : ℝ) : ℂ) * Complex.I) • ψ) :
    FormalRV.Framework.uc_eval (QPE_var_lsb m anc f)
      * kron_vec (FormalRV.Framework.kron_zeros m) ψ
    = kron_vec (qpe_phase_state m θ) ψ := by
  unfold QPE_var_lsb
  refine QPE_var_on_eigenstate_from_real_QFTinv hmanc hm
    (fun j => f (revIndex m j)) ψ θ ?_ ?_
  · intro j hj
    exact h_wt_all (revIndex m j) (revIndex_lt m j hj)
  · intro j hj
    have h_lsb := h_eig_lsb (revIndex m j) (revIndex_lt m j hj)
    rw [h_lsb]
    congr 1
    unfold qpeEigenvalue revIndex
    congr 1
    push_cast
    have h_eq : m - 1 - j = m - j - 1 := by omega
    rw [h_eq]
    ring
/-! ## Clean headline aliases (the QPE correctness to audit). -/

/-- **QPE — eigenstate correctness (THE headline, LSB-first).**  Running the
QPE circuit `QPE_var_lsb m anc f` on `|0^m⟩ ⊗ ψ`, where `ψ` is a common
eigenstate of the abstract oracle family with LSB-first eigenvalues
`exp(2πi · 2^i · θ)`, produces exactly `qpe_phase_state m θ ⊗ ψ` — the ideal
phase-register state.  The oracle `f` is a BLACK BOX (any `WellTyped` family
with the eigenvalue property); modular exponentiation is just one instance. -/
theorem qpe_on_eigenstate_correct
    {m anc : Nat} (hmanc : 0 < m + anc) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) (θ : ℝ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (h_eig_lsb : ∀ i, i < m →
      FormalRV.Framework.uc_eval (f i) * ψ =
        Complex.exp (((2 * Real.pi * ((2^i : Nat) : ℝ) * θ : ℝ) : ℂ) * Complex.I) • ψ) :
    FormalRV.Framework.uc_eval (QPE_var_lsb m anc f)
      * kron_vec (FormalRV.Framework.kron_zeros m) ψ
    = kron_vec (qpe_phase_state m θ) ψ :=
  QPE_var_lsb_on_eigenstate_from_real_QFTinv hmanc hm f ψ θ h_wt_all h_eig_lsb

end FormalRV.SQIRPort
