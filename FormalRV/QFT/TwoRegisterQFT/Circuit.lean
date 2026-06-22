/-
  FormalRV.QFT.TwoRegisterQFT.Circuit — the GATE-LEVEL two-register QFT as a verified `BaseUCom`.

  `Basic.lean` gives the amplitude / Born-probability MODEL of a two-control-register QFT
  (`qft2Amp`, `qft2MeasProb`).  This file supplies the missing half the model is *about*: an honest
  **gate circuit** `twoRegQFT a b : BaseUCom (a + b)`, built by composing the project's fully-verified
  single-register inverse-QFT circuit `IQFT` on the two disjoint sub-registers, together with the
  **unitary semantic proof** that its `uc_eval` is exactly the tensor product of the two `IQFT_matrix`
  factors.  This is the structural circuit-level counterpart of `qft2Amp_factor`.

  ## Construction
      twoRegQFT a b
        = (IQFT a  lifted onto qubits [0,a))            -- `map_qubits id`
        ; (IQFT b  lifted onto qubits [a,a+b))          -- `map_qubits (·+a)`

  ## Headline (`uc_eval_twoRegQFT_kron`)
      uc_eval (twoRegQFT a b) * kron_vec ψc ψd
        = kron_vec (IQFT_matrix a * ψc) (IQFT_matrix b * ψd)

  i.e. the two-register QFT circuit acts as `IQFT ⊗ IQFT` on the two registers — the same tensor law
  the amplitude model `qft2Amp` postulates, now discharged on the genuine gate circuit and reusing
  `iqft_correct` per register.  `twoRegQFT_wellTyped` makes it pluggable into the `BaseUCom` /
  `prob_partial_meas` pipeline.

  ## Convention note
  `IQFT_matrix m y x = (1/√2^m)·e^{-2πi·xy/2^m}` is the INVERSE (measurement-basis) QFT — the transform
  QPE / Shor actually apply before measuring.  `Basic.qft2Amp` uses the forward kernel `e^{+2πi·xy}`;
  the two agree up to `x ↦ −x` (complex conjugation), which leaves every Born probability `‖·‖²`
  invariant.  So this circuit realizes the EH measurement distribution; the per-fibre amplitude readout
  `twoRegQFT_fiberAmp_factor` exposes the realized (inverse-kernel) amplitudes explicitly.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.

  Layering: this file depends on `FormalRV.QPE.PhaseKickback` (the `map_qubits` kron-factorization
  lemmas), which imports `Shor.MainAlgorithm`.  It is therefore kept OUT of the Shor-agnostic
  `FormalRV.QFT` umbrella and imported directly where the circuit is used (the Ekerå–Håstad audit).
-/
import FormalRV.QFT.IQFTCorrectness
import FormalRV.QFT.TwoRegisterQFT.Basic
import FormalRV.QPE.PhaseKickback
import FormalRV.Verifier.ProofGate

namespace FormalRV.QFT.TwoRegisterQFT

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.Framework

/-! ## §1. General control factor on the shifted (data) register

`PhaseKickback.uc_eval_map_qubits_shift_kron_basis_control_vec` proves the data-register
factorization only for a *basis* control factor.  We lift it to an arbitrary control factor `χ` by
linearity (`vec_eq_sum_basis`), exactly as `pad_u_control_kron_vec_factors` lifts its per-gate basis
lemma.  This is the data-register dual of `uc_eval_control_register_circuit_kron_vec`. -/

/-- **Shifted (data-register) circuit factorization, general control factor.**
For any well-typed `c : BaseUCom anc`, the lift `map_qubits (·+m) c` onto qubits `[m, m+anc)` leaves an
arbitrary control factor `χ` untouched and applies `uc_eval c` to the data factor. -/
theorem uc_eval_map_qubits_shift_kron_vec {m anc : Nat}
    (c : FormalRV.Framework.BaseUCom anc) (h_wt : UCom.WellTyped anc c)
    (χ : Matrix (Fin (2 ^ m)) (Fin 1) ℂ) (ψ : Matrix (Fin (2 ^ anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => m + q) c : FormalRV.Framework.BaseUCom (m + anc)) * kron_vec χ ψ
      = kron_vec χ (FormalRV.Framework.uc_eval c * ψ) := by
  conv_lhs => rw [vec_eq_sum_basis (2 ^ m) χ]
  conv_rhs => rw [vec_eq_sum_basis (2 ^ m) χ]
  rw [kron_vec_sum_left, Matrix.mul_sum, kron_vec_sum_left]
  apply Finset.sum_congr rfl
  intro x _
  rw [kron_vec_smul_left (χ x 0) _ _]
  rw [Matrix.mul_smul]
  rw [uc_eval_map_qubits_shift_kron_basis_control_vec c h_wt x ψ]
  rw [kron_vec_smul_left]

/-- **Identity-embed well-typedness.** A circuit well-typed on `dim` qubits, embedded by the identity
qubit map into a wider register `dim' ≥ dim`, stays well-typed (every index `< dim ≤ dim'`). -/
theorem wellTyped_map_qubits_id_embed {dim dim' : Nat} (hle : dim ≤ dim')
    (c : FormalRV.Framework.BaseUCom dim) (h_wt : UCom.WellTyped dim c) :
    UCom.WellTyped dim' (map_qubits (fun q => q) c : FormalRV.Framework.BaseUCom dim') := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
      cases h_wt with
      | seq h₁ h₂ => exact UCom.WellTyped.seq (ih₁ h₁) (ih₂ h₂)
  | app1 _ n =>
      cases h_wt with
      | app1 hn => exact UCom.WellTyped.app1 (show n < dim' by omega)
  | app2 _ a b =>
      cases h_wt with
      | app2 ha hb hab =>
        exact UCom.WellTyped.app2
          (show a < dim' by omega) (show b < dim' by omega) hab
  | app3 _ a b d =>
      cases h_wt with
      | app3 ha hb hd hab hbd had =>
        exact UCom.WellTyped.app3
          (show a < dim' by omega) (show b < dim' by omega) (show d < dim' by omega)
          hab hbd had

/-! ## §2. The gate-level two-register QFT circuit -/

/-- **The two-register QFT gate circuit.** `IQFT a` on the high register `[0,a)` followed by `IQFT b`
on the low register `[a,a+b)` — a genuine `BaseUCom (a+b)` built from the verified single-register
inverse-QFT circuit. -/
noncomputable def twoRegQFT (a b : Nat) : FormalRV.Framework.BaseUCom (a + b) :=
  UCom.seq
    (map_qubits (fun q => q) (IQFT a) : FormalRV.Framework.BaseUCom (a + b))
    (map_qubits (fun q => a + q) (IQFT b) : FormalRV.Framework.BaseUCom (a + b))

/-- **`twoRegQFT` is well-typed** — it touches only qubits `< a + b`, so it plugs into the
`BaseUCom` / `prob_partial_meas` pipeline. -/
theorem twoRegQFT_wellTyped (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    UCom.WellTyped (a + b) (twoRegQFT a b) := by
  unfold twoRegQFT
  refine UCom.WellTyped.seq ?_ ?_
  · exact wellTyped_map_qubits_id_embed (Nat.le_add_right a b) (IQFT a) (iqft_wellTyped a ha)
  · exact wellTyped_map_qubits_shift (IQFT b) (iqft_wellTyped b hb)

/-- **★ The two-register QFT circuit acts as `IQFT ⊗ IQFT`. ★**
`uc_eval (twoRegQFT a b) * kron_vec ψc ψd = kron_vec (IQFT_matrix a * ψc) (IQFT_matrix b * ψd)`.
The gate-level unitary semantic proof: the circuit realizes the tensor of the two verified
single-register inverse-QFT matrices (`iqft_correct` per register). -/
theorem uc_eval_twoRegQFT_kron (a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (ψc : Matrix (Fin (2 ^ a)) (Fin 1) ℂ) (ψd : Matrix (Fin (2 ^ b)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval (twoRegQFT a b) * kron_vec ψc ψd
      = kron_vec (IQFT_matrix a * ψc) (IQFT_matrix b * ψd) := by
  unfold twoRegQFT
  rw [uc_eval_seq_mul]
  rw [uc_eval_control_register_circuit_kron_vec (IQFT a) (iqft_wellTyped a ha) ψc ψd]
  rw [iqft_correct a ha]
  rw [uc_eval_map_qubits_shift_kron_vec (IQFT b) (iqft_wellTyped b hb) (IQFT_matrix a * ψc) ψd]
  rw [iqft_correct b hb]

/-! ## §3. Amplitude readout — connecting the circuit to the `Basic.lean` amplitude model -/

/-- **Single-register inverse-QFT amplitude readout.** The realized amplitude at output `j` is the
inverse-QFT of the input: `(1/√2^a) ∑_x e^{-2πi·xj/2^a} ψ_x`.  This is the gate-level counterpart of
`Basic.qftAmp` (forward kernel `e^{+2πi·xj}`; the two are complex conjugates, equal under `‖·‖²`). -/
theorem iqft_matrix_mulVec_apply (a : Nat) (ψ : Matrix (Fin (2 ^ a)) (Fin 1) ℂ) (j : Fin (2 ^ a)) :
    (IQFT_matrix a * ψ) j 0
      = (1 / (Real.sqrt (2 ^ a : ℝ) : ℂ))
          * ∑ x : Fin (2 ^ a),
              Complex.exp (-(2 * Real.pi * Complex.I) * (x.val : ℂ) * (j.val : ℂ) / (2 ^ a : ℂ))
                * ψ x 0 := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  unfold IQFT_matrix
  ring

/-- **★ Joint output-amplitude factorization (circuit-level `qft2Amp_factor`). ★**
The two-register QFT circuit's output amplitude at the joint control outcome `(j,k)` is the product of
the two single-register inverse-QFT amplitudes — the genuine gate realization of the tensor law that
`Basic.qft2Amp_factor` states for the amplitude model. -/
theorem twoRegQFT_out_apply (a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (ψc : Matrix (Fin (2 ^ a)) (Fin 1) ℂ) (ψd : Matrix (Fin (2 ^ b)) (Fin 1) ℂ)
    (j : Fin (2 ^ a)) (k : Fin (2 ^ b)) :
    (FormalRV.Framework.uc_eval (twoRegQFT a b) * kron_vec ψc ψd) (kron_vec_combine j k) 0
      = (IQFT_matrix a * ψc) j 0 * (IQFT_matrix b * ψd) k 0 := by
  rw [uc_eval_twoRegQFT_kron a b ha hb ψc ψd]
  exact kron_vec_apply_combine _ _ j k

end FormalRV.QFT.TwoRegisterQFT

/-! ## §4. Verifier gates -/
#verify_clean FormalRV.QFT.TwoRegisterQFT.uc_eval_map_qubits_shift_kron_vec
#verify_clean FormalRV.QFT.TwoRegisterQFT.wellTyped_map_qubits_id_embed
#verify_clean FormalRV.QFT.TwoRegisterQFT.twoRegQFT_wellTyped
#verify_clean FormalRV.QFT.TwoRegisterQFT.uc_eval_twoRegQFT_kron
#verify_clean FormalRV.QFT.TwoRegisterQFT.iqft_matrix_mulVec_apply
#verify_clean FormalRV.QFT.TwoRegisterQFT.twoRegQFT_out_apply
