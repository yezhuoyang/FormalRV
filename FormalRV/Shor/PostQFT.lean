import FormalRV.Shor.PhaseKickback
import FormalRV.Shor.QPEAmplitude

/-!
# Post-QFT QPE infrastructure

`Framework/QPE.lean`'s `QFTinv` is currently a stub (`invert (npar_H n)`,
NOT a real inverse QFT — see `FormalRV.SQIRPort.QFTinv_is_stub` in
`PhaseKickback.lean`). This file provides the *real* mathematical and
circuit infrastructure for the post-QFT step of QPE, in parallel with
the stub, without replacing the stub yet.

## Contents

- `IQFT_matrix m`: the ideal inverse-QFT matrix
  `(1/√2^m) · exp(-2πi · x · y / 2^m)`.
- `IQFT_matrix_on_fourier_weighted_state`: the **pure math theorem**
  that `IQFT_matrix` maps the Fourier-weighted superposition
  `(1/√2^m) · ∑_x exp(+2πi · x · θ) · |x⟩` to `qpe_phase_state m θ`.
- `real_QFTinv_on n`: the *real* inverse-QFT circuit (currently just
  the 1-qubit base case; recursive definition can be added later).
- `real_QFTinv_one_on_fourier_state`: the 1-qubit semantic theorem.
- `uc_eval_real_QFTinv_eq_IQFT_matrix_one`: the m=1 instance of the
  eventual full circuit-correctness theorem.

The global `QFTinv` in `Framework/QPE.lean` is **NOT** modified here;
it remains a stub. Replacement will happen only after the real circuit
is proved correct for general `m`. -/

open FormalRV.Framework
open FormalRV.Framework.BaseUCom

namespace FormalRV.SQIRPort

/-! ## §1. Ideal inverse-QFT matrix and its action on Fourier-weighted states

This section is pure linear algebra — the matrix-level target that
any honest `QFTinv` circuit must reproduce. -/

/-- **Ideal inverse-QFT matrix.** `IQFT_matrix m y x = (1/√2^m) ·
exp(-2πi · x · y / 2^m)`. This is the matrix-level target for any
correct `QFTinv m` circuit. -/
noncomputable def IQFT_matrix (m : Nat) :
    Matrix (Fin (2^m)) (Fin (2^m)) ℂ :=
  fun y x =>
    ((1 : ℂ) / Real.sqrt (2^m : ℝ)) *
      Complex.exp (-(2 * Real.pi * Complex.I) * (x.val : ℂ) * (y.val : ℂ) / (2^m : ℂ))

/-- Pointwise: the Fourier-weighted superposition evaluated at index `k`
gives the single non-zero term `(1/√2^m) · exp(2πi · k · θ)`. -/
lemma fourier_weighted_state_apply (m : Nat) (θ : ℝ) (k : Fin (2^m)) :
    (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
        ∑ x : Fin (2^m),
          Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
            FormalRV.Framework.basis_vector (2^m) x.val) k 0
    = ((1 : ℂ) / Real.sqrt (2^m : ℝ)) *
        Complex.exp (2 * Real.pi * Complex.I * (k.val : ℂ) * (θ : ℂ)) := by
  rw [Matrix.smul_apply, Matrix.sum_apply]
  rw [Finset.sum_eq_single k]
  · rw [Matrix.smul_apply, basis_vector_apply]
    simp [smul_eq_mul]
  · intro x _ hx
    rw [Matrix.smul_apply, basis_vector_apply]
    simp [smul_eq_mul]
    intro h_eq
    exact (hx (Fin.ext h_eq.symm)).elim
  · simp

/-- `(1/√2^m)² = 1/2^m` in ℂ. -/
lemma inv_sqrt_two_pow_sq (m : Nat) :
    ((1 : ℂ) / Real.sqrt (2^m : ℝ)) * ((1 : ℂ) / Real.sqrt (2^m : ℝ))
      = 1 / (2^m : ℂ) := by
  have h_pos : (0 : ℝ) < 2^m := by positivity
  have h_sqrt_sq_real : Real.sqrt (2^m : ℝ) * Real.sqrt (2^m : ℝ) = (2^m : ℝ) :=
    Real.mul_self_sqrt (le_of_lt h_pos)
  rw [show ((1 : ℂ) / Real.sqrt (2^m : ℝ)) * ((1 : ℂ) / Real.sqrt (2^m : ℝ))
        = 1 / ((Real.sqrt (2^m : ℝ) : ℂ) * Real.sqrt (2^m : ℝ)) from by ring]
  rw [show ((Real.sqrt (2^m : ℝ) : ℂ) * Real.sqrt (2^m : ℝ))
        = ((Real.sqrt (2^m : ℝ) * Real.sqrt (2^m : ℝ) : ℝ) : ℂ) from by push_cast; ring]
  rw [h_sqrt_sq_real]
  push_cast
  rfl

/-- **HEADLINE MATH THEOREM.** The ideal inverse-QFT matrix maps the
Fourier-weighted superposition `(1/√2^m) · ∑_x exp(+2πi · x · θ) · |x⟩`
to `qpe_phase_state m θ`. This is a pure linear-algebra fact,
independent of any specific circuit realization. -/
theorem IQFT_matrix_on_fourier_weighted_state
    (m : Nat) (θ : ℝ) :
    IQFT_matrix m *
      (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
        ∑ x : Fin (2^m),
          Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
            FormalRV.Framework.basis_vector (2^m) x.val)
    = qpe_phase_state m θ := by
  ext y j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  rw [Matrix.mul_apply]
  rw [show ∑ x : Fin (2^m), IQFT_matrix m y x *
            (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
              ∑ x' : Fin (2^m),
                Complex.exp (2 * Real.pi * Complex.I * (x'.val : ℂ) * (θ : ℂ)) •
                  FormalRV.Framework.basis_vector (2^m) x'.val) x 0
        = ∑ x : Fin (2^m), IQFT_matrix m y x *
            (((1 : ℂ) / Real.sqrt (2^m : ℝ)) *
              Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ))) from by
    apply Finset.sum_congr rfl
    intro x _
    rw [fourier_weighted_state_apply m θ x]]
  unfold IQFT_matrix qpe_phase_state qpe_amp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [show ((1 : ℂ) / Real.sqrt (2^m : ℝ)) *
            Complex.exp (-(2 * Real.pi * Complex.I) * (x.val : ℂ) * (y.val : ℂ) / (2^m : ℂ)) *
            (((1 : ℂ) / Real.sqrt (2^m : ℝ)) *
              Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)))
        = (((1 : ℂ) / Real.sqrt (2^m : ℝ)) * ((1 : ℂ) / Real.sqrt (2^m : ℝ))) *
          (Complex.exp (-(2 * Real.pi * Complex.I) * (x.val : ℂ) * (y.val : ℂ) / (2^m : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ))) from by ring]
  rw [← Complex.exp_add]
  rw [inv_sqrt_two_pow_sq m]
  congr 1
  ring

/-! ## §2. Real inverse-QFT circuit (1-qubit base case)

The full recursive inverse-QFT requires controlled phase rotations
with decreasing angles, plus a bit-reversal step at the end. The
1-qubit case collapses to a single Hadamard, which is a clean base
case to certify against `IQFT_matrix`. -/

/-- **Real inverse-QFT circuit.** Base cases for `n ≤ 2`; the
recursive case for `n ≥ 3` is provided by `real_QFTinv_layer` below.
For `n = 2`, uses the verified `real_QFTinv2_candidate`. -/
noncomputable def real_QFTinv_on : (n : Nat) → BaseUCom n
  | 0 => SKIP
  | 1 => H 0
  | 2 => UCom.seq
           (UCom.seq
             (UCom.seq (SWAP 0 1) (H 1))
             (controlled_Rz 1 0 (-(Real.pi / 2))))
           (H 0)
  | _+3 => SKIP  -- General case: deferred to `real_QFTinv_layer` (see §4)

/-- The real 1-qubit inverse QFT is `H 0`. -/
theorem real_QFTinv_on_one : real_QFTinv_on 1 = (H 0 : BaseUCom 1) := rfl

/-- The real 0-qubit inverse QFT is `SKIP`. -/
theorem real_QFTinv_on_zero : real_QFTinv_on 0 = (SKIP : BaseUCom 0) := rfl

/-! ## §4. 2-qubit inverse-QFT circuit candidate + recursive layer

The 2-qubit inverse QFT is the smallest nontrivial case. With the
framework's MSB-first convention (`padEquiv` puts qubit `i` at weight
`2^(m-i-1)`, so qubit 0 is the most significant), the standard
forward-QFT decomposition is:

    H 0 ;  controlled_Rz 1 0 (π/2) ;  H 1 ;  SWAP 0 1

Its **inverse** (reverse order + adjoint angles) is:

    SWAP 0 1 ;  H 1 ;  controlled_Rz 1 0 (-π/2) ;  H 0

The latter is the `real_QFTinv2_candidate` defined below. Hand
verification (see the docstring): the matrix product
`H 0 · CR · H 1 · SWAP` evaluates entry-by-entry to
`(1/2) · [[1,1,1,1]; [1,-i,-1,i]; [1,-1,1,-1]; [1,i,-1,-i]]`,
which equals `IQFT_matrix 2`. The mechanized 16-entry matrix proof
requires per-gate basis-action infrastructure that does not yet
exist in the framework; the candidate is committed here as a
landing point and the matrix theorem is the next pass's target. -/

/-- **2-qubit inverse-QFT candidate.** Order: `SWAP 0 1 ; H 1 ;
controlled_Rz 1 0 (-π/2) ; H 0`. Hand-verified to equal
`IQFT_matrix 2` (mechanized proof deferred).

Action analysis (each basis vector `|x_0 x_1⟩`):
- `|00⟩ → (1/2)(|00⟩ + |01⟩ + |10⟩ + |11⟩)`
- `|01⟩ → (1/2)(|00⟩ - i|01⟩ - |10⟩ + i|11⟩)`
- `|10⟩ → (1/2)(|00⟩ - |01⟩ + |10⟩ - |11⟩)`
- `|11⟩ → (1/2)(|00⟩ + i|01⟩ - |10⟩ - i|11⟩)`
matching `IQFT_matrix 2`'s columns. -/
noncomputable def real_QFTinv2_candidate : BaseUCom 2 :=
  UCom.seq
    (UCom.seq
      (UCom.seq (SWAP 0 1) (H 1))
      (controlled_Rz 1 0 (-(Real.pi / 2))))
    (H 0)

/-- **Phase ladder for inverse QFT on the `target`-th qubit.**

SQIRPort-namespaced n-qubit version. Coexists with the
`{dim}`-polymorphic `Framework.BaseUCom.inverse_qft_phase_ladder`
(moved to the framework 2026-05-26 to support `QFTinv`'s replacement).
Equivalence between the two is established by
`SQIRPort_inverse_qft_phase_ladder_eq_Framework`. -/
noncomputable def inverse_qft_phase_ladder
    (n target : Nat) : FormalRV.Framework.BaseUCom n :=
  let rec loop (j : Nat) : FormalRV.Framework.BaseUCom n :=
    if j < n then
      UCom.seq (controlled_Rz j target (-(Real.pi / (2 ^ (j - target) : ℝ))))
               (loop (j + 1))
    else
      H target
  loop (target + 1)

/-- **Bit-reversal SWAP cascade for `n` qubits.** SQIRPort-namespaced
n-qubit version. See `inverse_qft_phase_ladder` for the framework
relationship note. -/
noncomputable def bit_reversal_swaps (n : Nat) : FormalRV.Framework.BaseUCom n :=
  let rec loop (i : Nat) : FormalRV.Framework.BaseUCom n :=
    if i + i + 1 < n then
      UCom.seq (SWAP i (n - 1 - i)) (loop (i + 1))
    else
      SKIP
  loop 0

/-- **Recursive layer of the real inverse-QFT for `n` qubits.**
SQIRPort-namespaced n-qubit version. See `inverse_qft_phase_ladder`
for the framework relationship note. -/
noncomputable def real_QFTinv_layer (n : Nat) : FormalRV.Framework.BaseUCom n :=
  let rec countdown (k : Nat) : FormalRV.Framework.BaseUCom n :=
    match k with
    | 0 => SKIP
    | k+1 => UCom.seq (inverse_qft_phase_ladder n k) (countdown k)
  UCom.seq (bit_reversal_swaps n) (countdown n)

/-- **At `n = 2`, the recursive layer matches the hand-written candidate.**

Both circuits evaluate to `H 0 · CR(-π/2) · H 1 · SWAP` as a 4×4 matrix.
The recursive layer has a trailing `SKIP`, which collapses via
`uc_eval_ID_eq_one`. -/
theorem real_QFTinv_layer_two_eq_candidate :
    FormalRV.Framework.uc_eval (real_QFTinv_layer 2)
      = FormalRV.Framework.uc_eval real_QFTinv2_candidate := by
  show FormalRV.Framework.uc_eval (UCom.seq (bit_reversal_swaps 2)
        (real_QFTinv_layer.countdown 2 2))
      = FormalRV.Framework.uc_eval real_QFTinv2_candidate
  unfold bit_reversal_swaps real_QFTinv2_candidate
  simp [real_QFTinv_layer.countdown, bit_reversal_swaps.loop,
        inverse_qft_phase_ladder, inverse_qft_phase_ladder.loop,
        show (SKIP : FormalRV.Framework.BaseUCom 2) = ID 0 from rfl,
        uc_eval_ID_eq_one (show (0 : Nat) < 2 from by omega)]
  rw [Matrix.mul_assoc, Matrix.mul_assoc]

/-! ## §3. 1-qubit circuit correctness

The 1-qubit inverse QFT collapses to a Hadamard. We prove
`uc_eval (real_QFTinv_on 1) = IQFT_matrix 1` directly by entry-wise
comparison. This is the base case for the eventual recursive
correctness theorem. -/

/-- Helper: `√2 / 2 = (√2)⁻¹` over ℂ. -/
private lemma sqrt_two_div_two_eq_inv :
    (Real.sqrt 2 : ℂ) / 2 = (Real.sqrt 2 : ℂ)⁻¹ := by
  have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast h_sqrt2_pos.ne'
  field_simp
  rw [show ((Real.sqrt 2 : ℂ))^2 = ((Real.sqrt 2)^2 : ℝ) from by push_cast; ring]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  push_cast; ring

/-- **m=1 circuit correctness.** The 1-qubit `real_QFTinv_on 1 = H 0`
has unitary evaluation matrix equal to `IQFT_matrix 1`. Proof: case
analysis on the 2×2 entries, with normalization `√2/2 = (√2)⁻¹` and
`exp(-π·I) = -1`. -/
theorem uc_eval_real_QFTinv_eq_IQFT_matrix_one :
    FormalRV.Framework.uc_eval (real_QFTinv_on 1 : BaseUCom 1)
      = IQFT_matrix 1 := by
  rw [real_QFTinv_on_one]
  rw [show FormalRV.Framework.uc_eval (H 0 : BaseUCom 1)
        = pad_u 1 0 hMatrix from by
    unfold H FormalRV.Framework.uc_eval ueval_r
    show pad_u 1 0 (rotation (Real.pi / 2) 0 Real.pi) = pad_u 1 0 hMatrix
    rw [rotation_H]]
  ext i j
  fin_cases i <;> fin_cases j <;>
  · unfold IQFT_matrix
    rw [pad_u_one_zero_eq hMatrix]
    simp [hMatrix]
    try exact sqrt_two_div_two_eq_inv
    try
      (rw [show -(2 * ↑Real.pi * Complex.I) / 2 = -((Real.pi : ℂ) * Complex.I) from by ring,
          Complex.exp_neg, Complex.exp_pi_mul_I]
       have h := sqrt_two_div_two_eq_inv
       linear_combination -h)

/-- **1-qubit semantic theorem.** The real 1-qubit inverse QFT applied
to the Fourier-weighted superposition `(1/√2) · ∑_x exp(2πi · x · θ) |x⟩`
yields `qpe_phase_state 1 θ`. Combines the circuit-correctness
theorem with the matrix-level `IQFT_matrix_on_fourier_weighted_state`. -/
theorem real_QFTinv_one_on_fourier_state (θ : ℝ) :
    FormalRV.Framework.uc_eval (real_QFTinv_on 1 : BaseUCom 1) *
      (((1 : ℂ) / Real.sqrt (2^1 : ℝ)) •
        ∑ x : Fin (2^1),
          Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
            FormalRV.Framework.basis_vector (2^1) x.val)
    = qpe_phase_state 1 θ := by
  rw [uc_eval_real_QFTinv_eq_IQFT_matrix_one]
  exact IQFT_matrix_on_fourier_weighted_state 1 θ

/-! ## §4. Building blocks for the 2-qubit matrix-equality theorem

The headline theorem `uc_eval real_QFTinv2_candidate = IQFT_matrix 2`
is established via `matrix_eq_of_basis_action` (Framework/PadAction):
suffices to show both matrices act identically on each of the four
basis vectors `basis_vector 4 k` for `k ∈ {0, 1, 2, 3}`.

This section lands:
- `H_one_eq_minus`: the `|1⟩` counterpart to `H_zero_eq_plus`.
- Two `uc_eval (H q : BaseUCom 2)` simplification lemmas (in terms of
  `pad_u 2 q hMatrix`).
- The four `IQFT_matrix_two_on_basis_*` lemmas giving the explicit
  exponential form of `IQFT_matrix 2 * basis_vector 4 k` for each k.

The remaining work for the next pass is: prove the analogous
explicit form of `uc_eval real_QFTinv2_candidate * basis_vector 4 k`
for each k by chaining SWAP → H 1 → controlled_Rz → H 0 actions, then
compose via `matrix_eq_of_basis_action`. -/

/-- **`H |1⟩ = (√2/2) · (|0⟩ − |1⟩)`** — the `|1⟩` counterpart to
`H_zero_eq_plus`. Direct 2×2 computation. -/
theorem H_one_eq_minus :
    FormalRV.Framework.uc_eval
        (FormalRV.Framework.BaseUCom.H 0 : FormalRV.Framework.BaseUCom 1) *
        FormalRV.Framework.basis_vector 2 1
      = ((Real.sqrt 2 / 2 : ℂ)) •
        (FormalRV.Framework.basis_vector 2 0 -
          FormalRV.Framework.basis_vector 2 1) := by
  show pad_u 1 0 (FormalRV.Framework.rotation (Real.pi / 2) 0 Real.pi) *
        FormalRV.Framework.basis_vector 2 1 = _
  rw [FormalRV.Framework.rotation_H]
  rw [pad_u_one_zero_eq]
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  fin_cases r
  · simp [Matrix.mul_apply, FormalRV.Framework.basis_vector, hMatrix,
          Matrix.sub_apply, smul_eq_mul, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, FormalRV.Framework.basis_vector, hMatrix,
          Matrix.sub_apply, smul_eq_mul, Fin.sum_univ_two]

/-- `uc_eval (H 0) = pad_u 2 0 hMatrix` at dim = 2. -/
theorem uc_eval_H_zero_two_eq_pad_u :
    FormalRV.Framework.uc_eval (BaseUCom.H 0 : FormalRV.Framework.BaseUCom 2)
      = pad_u 2 0 hMatrix := by
  unfold BaseUCom.H FormalRV.Framework.uc_eval ueval_r
  show pad_u 2 0 (rotation (Real.pi / 2) 0 Real.pi) = pad_u 2 0 hMatrix
  rw [rotation_H]

/-- `uc_eval (H 1) = pad_u 2 1 hMatrix` at dim = 2. -/
theorem uc_eval_H_one_two_eq_pad_u :
    FormalRV.Framework.uc_eval (BaseUCom.H 1 : FormalRV.Framework.BaseUCom 2)
      = pad_u 2 1 hMatrix := by
  unfold BaseUCom.H FormalRV.Framework.uc_eval ueval_r
  show pad_u 2 1 (rotation (Real.pi / 2) 0 Real.pi) = pad_u 2 1 hMatrix
  rw [rotation_H]

/-- **`IQFT_matrix 2` on `|0⟩`**: produces the uniform superposition
`(1/2) · (|0⟩ + |1⟩ + |2⟩ + |3⟩)`. All phases are 1 because
`exp(0) = 1`. -/
theorem IQFT_matrix_two_on_basis_zero :
    IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 0
      = ((1 : ℂ) / Real.sqrt (2^2 : ℝ)) •
        (FormalRV.Framework.basis_vector 4 0 +
         FormalRV.Framework.basis_vector 4 1 +
         FormalRV.Framework.basis_vector 4 2 +
         FormalRV.Framework.basis_vector 4 3) := by
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  fin_cases i <;>
    simp [Matrix.mul_apply, IQFT_matrix, FormalRV.Framework.basis_vector,
          Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- **`IQFT_matrix 2` on `|1⟩`**: `(1/2) · (|0⟩ + e^(-iπ/2)|1⟩ +
e^(-iπ)|2⟩ + e^(-i3π/2)|3⟩)`. -/
theorem IQFT_matrix_two_on_basis_one :
    IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 1
      = ((1 : ℂ) / Real.sqrt (2^2 : ℝ)) •
        (FormalRV.Framework.basis_vector 4 0
         + Complex.exp (-(Real.pi / 2) * Complex.I) • FormalRV.Framework.basis_vector 4 1
         + Complex.exp (-Real.pi * Complex.I) • FormalRV.Framework.basis_vector 4 2
         + Complex.exp (-(3 * Real.pi / 2) * Complex.I) • FormalRV.Framework.basis_vector 4 3) := by
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  fin_cases i <;>
    simp [Matrix.mul_apply, IQFT_matrix, FormalRV.Framework.basis_vector,
          Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  all_goals ring_nf

/-- **`IQFT_matrix 2` on `|2⟩`**: phases are `1, e^(-iπ), e^(-i2π),
e^(-i3π)` which collapse to `1, -1, 1, -1`. -/
theorem IQFT_matrix_two_on_basis_two :
    IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 2
      = ((1 : ℂ) / Real.sqrt (2^2 : ℝ)) •
        (FormalRV.Framework.basis_vector 4 0
         + Complex.exp (-Real.pi * Complex.I) • FormalRV.Framework.basis_vector 4 1
         + Complex.exp (-2 * Real.pi * Complex.I) • FormalRV.Framework.basis_vector 4 2
         + Complex.exp (-3 * Real.pi * Complex.I) • FormalRV.Framework.basis_vector 4 3) := by
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  fin_cases i <;>
    simp [Matrix.mul_apply, IQFT_matrix, FormalRV.Framework.basis_vector,
          Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  all_goals ring_nf

/-- **`IQFT_matrix 2` on `|3⟩`**: phases form the conjugate
`{1, -i, -1, i}` of the `|1⟩` column. -/
theorem IQFT_matrix_two_on_basis_three :
    IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 3
      = ((1 : ℂ) / Real.sqrt (2^2 : ℝ)) •
        (FormalRV.Framework.basis_vector 4 0
         + Complex.exp (-(3 * Real.pi / 2) * Complex.I) • FormalRV.Framework.basis_vector 4 1
         + Complex.exp (-3 * Real.pi * Complex.I) • FormalRV.Framework.basis_vector 4 2
         + Complex.exp (-(9 * Real.pi / 2) * Complex.I) • FormalRV.Framework.basis_vector 4 3) := by
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  fin_cases i <;>
    simp [Matrix.mul_apply, IQFT_matrix, FormalRV.Framework.basis_vector,
          Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  all_goals ring_nf

/-! ## §5. LHS circuit-action columns

For each k ∈ {0,1,2,3}, we prove
`uc_eval real_QFTinv2_candidate * basis_vector 4 k = IQFT_matrix 2 * basis_vector 4 k`
by chaining the gate-action lemmas (SWAP → H 1 → controlled_Rz → H 0)
and matching the resulting sum of basis vectors against the RHS
column lemmas from §4. -/

/-- `f_to_vec 2 f` in terms of `basis_vector 4` and the values of `f`
at bits 0 and 1. Recall that bit 0 is MSB (weight 2), bit 1 is LSB
(weight 1) in the framework's `funbool_to_nat` convention. -/
private lemma f_to_vec_two_eq (f : Nat → Bool) :
    f_to_vec 2 f = FormalRV.Framework.basis_vector 4
      ((if f 0 then 2 else 0) + (if f 1 then 1 else 0)) := by
  unfold f_to_vec
  congr 1
  by_cases h0 : f 0 = true <;> by_cases h1 : f 1 = true <;>
    simp [funbool_to_nat, h0, h1]

/-- `(√2/2)² = 1/2` over `ℂ`. -/
private lemma sqrt_two_half_sq :
    (Real.sqrt 2 / 2 : ℂ) * (Real.sqrt 2 / 2 : ℂ) = (1/2 : ℂ) := by
  rw [show (Real.sqrt 2 / 2 : ℂ) * (Real.sqrt 2 / 2 : ℂ) =
       ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) / 4 from by ring]
  rw [show (Real.sqrt 2 : ℂ) * Real.sqrt 2 =
       ((Real.sqrt 2 * Real.sqrt 2 : ℝ) : ℂ) from by push_cast; ring]
  rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  push_cast; norm_num

/-- `exp(-(π·I)) = -1`. -/
private lemma exp_neg_pi_I : Complex.exp (-((Real.pi : ℂ) * Complex.I)) = -1 := by
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- `exp(-(2π·I)) = 1`. -/
private lemma exp_neg_two_pi_I : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
  rw [show -(2 * (Real.pi : ℂ) * Complex.I)
        = -((Real.pi : ℂ) * Complex.I) + (-((Real.pi : ℂ) * Complex.I)) from by ring]
  rw [Complex.exp_add, exp_neg_pi_I]
  norm_num

/-- `exp(-(3π·I)) = -1`. -/
private lemma exp_neg_three_pi_I : Complex.exp (-(3 * (Real.pi : ℂ) * Complex.I)) = -1 := by
  rw [show -(3 * (Real.pi : ℂ) * Complex.I)
        = -((Real.pi : ℂ) * Complex.I) + (-(2 * (Real.pi : ℂ) * Complex.I)) from by ring]
  rw [Complex.exp_add, exp_neg_pi_I, exp_neg_two_pi_I]
  norm_num

/-- `exp(-(3π/2 · I)) = -exp(-(π/2 · I))`. -/
private lemma exp_neg_three_pi_half_I :
    Complex.exp (-(3 * (Real.pi : ℂ) / 2 * Complex.I))
      = -Complex.exp (-((Real.pi : ℂ) / 2 * Complex.I)) := by
  rw [show -(3 * (Real.pi : ℂ) / 2 * Complex.I)
        = -((Real.pi : ℂ) / 2 * Complex.I) + (-((Real.pi : ℂ) * Complex.I)) from by ring]
  rw [Complex.exp_add, exp_neg_pi_I]
  ring

/-- `exp(-(9π/2 · I)) = exp(-(π/2 · I))` — since `-9π/2 = -π/2 - 4π` and
`exp(-4π·I) = 1`. -/
private lemma exp_neg_nine_pi_half_I :
    Complex.exp (-(9 * (Real.pi : ℂ) / 2 * Complex.I))
      = Complex.exp (-((Real.pi : ℂ) / 2 * Complex.I)) := by
  rw [show -(9 * (Real.pi : ℂ) / 2 * Complex.I)
        = -((Real.pi : ℂ) / 2 * Complex.I) + (-(2 * (Real.pi : ℂ) * Complex.I))
          + (-(2 * (Real.pi : ℂ) * Complex.I))
       from by ring]
  rw [Complex.exp_add, Complex.exp_add, exp_neg_two_pi_I]
  ring

/-- `(√2 : ℂ)² = 2`. -/
private lemma sqrt_two_sq_complex : ((Real.sqrt 2 : ℂ))^2 = (2 : ℂ) := by
  rw [show ((Real.sqrt 2 : ℂ))^2 = ((Real.sqrt 2)^2 : ℝ) from by push_cast; ring]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  push_cast; ring

/-- Consolidate `(√2/2) * (e * (√2/2))` into `(1/2) * e`. -/
private lemma sqrt_two_half_smul_sandwich (e : ℂ) :
    (Real.sqrt 2 / 2 : ℂ) * (e * (Real.sqrt 2 / 2 : ℂ)) = (1/2 : ℂ) * e := by
  rw [show (Real.sqrt 2 / 2 : ℂ) * (e * (Real.sqrt 2 / 2 : ℂ))
        = ((Real.sqrt 2 / 2 : ℂ) * (Real.sqrt 2 / 2 : ℂ)) * e from by ring]
  rw [sqrt_two_half_sq]

/-- **Column 0: candidate on `|0⟩`.** Direct chain via `f_to_vec_SWAP`,
`f_to_vec_H_uc_eval`, `controlled_Rz_acts_on_basis_correct`. -/
theorem real_QFTinv2_candidate_on_basis_zero :
    FormalRV.Framework.uc_eval real_QFTinv2_candidate *
        FormalRV.Framework.basis_vector 4 0
      = IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 0 := by
  rw [IQFT_matrix_two_on_basis_zero]
  unfold real_QFTinv2_candidate
  rw [uc_eval_seq_mul, uc_eval_seq_mul, uc_eval_seq_mul]
  conv_lhs =>
    rw [show (FormalRV.Framework.basis_vector 4 0 : Matrix (Fin 4) (Fin 1) ℂ)
          = FormalRV.Framework.basis_vector (2^2) 0 from rfl]
    rw [basis_vector_eq_f_to_vec_nat 2 0 (by omega)]
  rw [show (BaseUCom.SWAP 0 1 : FormalRV.Framework.BaseUCom 2)
        = UCom.seq (BaseUCom.CNOT 0 1) (UCom.seq (BaseUCom.CNOT 1 0) (BaseUCom.CNOT 0 1))
        from rfl]
  rw [f_to_vec_SWAP 2 0 1 (by omega) (by omega) (by decide)]
  rw [f_to_vec_H_uc_eval 2 1 (by omega)]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [Matrix.mul_add]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq]
  simp only [update,
             show (nat_to_funbool 2 0 0) = false from by decide,
             show (nat_to_funbool 2 0 1) = false from by decide]
  simp
  rw [smul_smul, smul_smul, smul_smul, smul_smul, sqrt_two_half_sq]
  rw [show ((1 : ℂ) / 2) = 2⁻¹ from by ring]
  module

/-- **Column 1: candidate on `|1⟩`.** -/
theorem real_QFTinv2_candidate_on_basis_one :
    FormalRV.Framework.uc_eval real_QFTinv2_candidate *
        FormalRV.Framework.basis_vector 4 1
      = IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 1 := by
  rw [IQFT_matrix_two_on_basis_one]
  unfold real_QFTinv2_candidate
  rw [uc_eval_seq_mul, uc_eval_seq_mul, uc_eval_seq_mul]
  conv_lhs =>
    rw [show (FormalRV.Framework.basis_vector 4 1 : Matrix (Fin 4) (Fin 1) ℂ)
          = FormalRV.Framework.basis_vector (2^2) 1 from rfl]
    rw [basis_vector_eq_f_to_vec_nat 2 1 (by omega)]
  rw [show (BaseUCom.SWAP 0 1 : FormalRV.Framework.BaseUCom 2)
        = UCom.seq (BaseUCom.CNOT 0 1) (UCom.seq (BaseUCom.CNOT 1 0) (BaseUCom.CNOT 0 1))
        from rfl]
  rw [f_to_vec_SWAP 2 0 1 (by omega) (by omega) (by decide)]
  rw [f_to_vec_H_uc_eval 2 1 (by omega)]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [Matrix.mul_add]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq]
  simp only [update,
             show (nat_to_funbool 2 1 0) = false from by decide,
             show (nat_to_funbool 2 1 1) = true from by decide]
  simp
  rw [exp_neg_pi_I, exp_neg_three_pi_half_I]
  simp only [smul_smul, sqrt_two_half_sq, sqrt_two_half_smul_sandwich]
  rw [show ((1 : ℂ) / 2) = 2⁻¹ from by ring]
  module

/-- **Column 2: candidate on `|2⟩`.** -/
theorem real_QFTinv2_candidate_on_basis_two :
    FormalRV.Framework.uc_eval real_QFTinv2_candidate *
        FormalRV.Framework.basis_vector 4 2
      = IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 2 := by
  rw [IQFT_matrix_two_on_basis_two]
  unfold real_QFTinv2_candidate
  rw [uc_eval_seq_mul, uc_eval_seq_mul, uc_eval_seq_mul]
  conv_lhs =>
    rw [show (FormalRV.Framework.basis_vector 4 2 : Matrix (Fin 4) (Fin 1) ℂ)
          = FormalRV.Framework.basis_vector (2^2) 2 from rfl]
    rw [basis_vector_eq_f_to_vec_nat 2 2 (by omega)]
  rw [show (BaseUCom.SWAP 0 1 : FormalRV.Framework.BaseUCom 2)
        = UCom.seq (BaseUCom.CNOT 0 1) (UCom.seq (BaseUCom.CNOT 1 0) (BaseUCom.CNOT 0 1))
        from rfl]
  rw [f_to_vec_SWAP 2 0 1 (by omega) (by omega) (by decide)]
  rw [f_to_vec_H_uc_eval 2 1 (by omega)]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [Matrix.mul_add]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq]
  simp only [update,
             show (nat_to_funbool 2 2 0) = true from by decide,
             show (nat_to_funbool 2 2 1) = false from by decide]
  simp
  rw [exp_neg_pi_I, exp_neg_two_pi_I, exp_neg_three_pi_I]
  rw [smul_smul, smul_smul, smul_smul, smul_smul, sqrt_two_half_sq]
  rw [show ((1 : ℂ) / 2) = 2⁻¹ from by ring]
  module

/-- **Column 3: candidate on `|3⟩`.** -/
theorem real_QFTinv2_candidate_on_basis_three :
    FormalRV.Framework.uc_eval real_QFTinv2_candidate *
        FormalRV.Framework.basis_vector 4 3
      = IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 3 := by
  rw [IQFT_matrix_two_on_basis_three]
  unfold real_QFTinv2_candidate
  rw [uc_eval_seq_mul, uc_eval_seq_mul, uc_eval_seq_mul]
  conv_lhs =>
    rw [show (FormalRV.Framework.basis_vector 4 3 : Matrix (Fin 4) (Fin 1) ℂ)
          = FormalRV.Framework.basis_vector (2^2) 3 from rfl]
    rw [basis_vector_eq_f_to_vec_nat 2 3 (by omega)]
  rw [show (BaseUCom.SWAP 0 1 : FormalRV.Framework.BaseUCom 2)
        = UCom.seq (BaseUCom.CNOT 0 1) (UCom.seq (BaseUCom.CNOT 1 0) (BaseUCom.CNOT 0 1))
        from rfl]
  rw [f_to_vec_SWAP 2 0 1 (by omega) (by omega) (by decide)]
  rw [f_to_vec_H_uc_eval 2 1 (by omega)]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [Matrix.mul_add]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq]
  simp only [update,
             show (nat_to_funbool 2 3 0) = true from by decide,
             show (nat_to_funbool 2 3 1) = true from by decide]
  simp
  rw [exp_neg_three_pi_half_I, exp_neg_three_pi_I, exp_neg_nine_pi_half_I]
  simp only [smul_smul, sqrt_two_half_sq, sqrt_two_half_smul_sandwich]
  rw [show ((1 : ℂ) / 2) = 2⁻¹ from by ring]
  module

/-- **HEADLINE: 2-qubit IQFT matrix equality.** Lifts the four column
lemmas to matrix equality via `matrix_eq_of_basis_action`. -/
theorem uc_eval_real_QFTinv2_candidate_eq_IQFT_matrix :
    FormalRV.Framework.uc_eval real_QFTinv2_candidate = IQFT_matrix 2 := by
  apply matrix_eq_of_basis_action
  intro k
  fin_cases k
  · exact real_QFTinv2_candidate_on_basis_zero
  · exact real_QFTinv2_candidate_on_basis_one
  · exact real_QFTinv2_candidate_on_basis_two
  · exact real_QFTinv2_candidate_on_basis_three

/-- The `n = 2` case of `real_QFTinv_on` is syntactically equal to
`real_QFTinv2_candidate`. -/
theorem real_QFTinv_on_two : real_QFTinv_on 2 = real_QFTinv2_candidate := rfl

/-- **m=2 circuit correctness.** `uc_eval (real_QFTinv_on 2) = IQFT_matrix 2`,
the 2-qubit counterpart to `uc_eval_real_QFTinv_eq_IQFT_matrix_one`. -/
theorem uc_eval_real_QFTinv_eq_IQFT_matrix_two :
    FormalRV.Framework.uc_eval (real_QFTinv_on 2 : BaseUCom 2) = IQFT_matrix 2 := by
  rw [real_QFTinv_on_two]
  exact uc_eval_real_QFTinv2_candidate_eq_IQFT_matrix

/-- **2-qubit semantic theorem.** Mirrors `real_QFTinv_one_on_fourier_state`:
the real 2-qubit inverse QFT applied to the Fourier-weighted superposition
yields `qpe_phase_state 2 θ`. -/
theorem real_QFTinv_two_on_fourier_state (θ : ℝ) :
    FormalRV.Framework.uc_eval (real_QFTinv_on 2 : BaseUCom 2) *
      (((1 : ℂ) / Real.sqrt (2^2 : ℝ)) •
        ∑ x : Fin (2^2),
          Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
            FormalRV.Framework.basis_vector (2^2) x.val)
    = qpe_phase_state 2 θ := by
  rw [uc_eval_real_QFTinv_eq_IQFT_matrix_two]
  exact IQFT_matrix_on_fourier_weighted_state 2 θ

/-! ## §6. Real QPE pipeline assuming arbitrary-n IQFT correctness

This section closes the QPE pipeline at the level of `real_QFTinv_on`'s
matrix correctness. The final theorem `real_QPE_on_eigenstate_from_IQFT_correct`
shows that, once `uc_eval (real_QFTinv_on m) = IQFT_matrix m` is proved
for arbitrary `m`, the full QPE eigenstate semantic theorem follows.

This establishes a clean theorem boundary: the remaining work for
`QPE_MMI_correct` reduces to proving arbitrary-n IQFT matrix correctness
(the 2-qubit case is in §5; the recursive case is the next deliverable). -/

/-- **Real QPE circuit.** `npar_H` (prep) ; `controlled_powers` (oracle
ladder, lifted to the data register) ; `real_QFTinv_on m` (measurement
basis, lifted to the control register). -/
noncomputable def real_QPE (m anc : Nat) (f : Nat → BaseUCom anc) :
    BaseUCom (m + anc) :=
  UCom.seq (npar_H m)
    (UCom.seq
      (controlled_powers
        (fun i => (map_qubits (fun q => m + q) (f i) : BaseUCom (m + anc))) m)
      (map_qubits (fun q => q) (real_QFTinv_on m) : BaseUCom (m + anc)))

/-- **Lifted IQFT acts on the control factor.** Given `h_IQFT`, the
`real_QFTinv_on m` lifted to `m + anc` qubits acts on `kron_vec ψc ψd`
by applying `IQFT_matrix m` to the control factor `ψc`. -/
theorem real_QFTinv_lifted_on_kron
    {m anc : Nat}
    (ψc : Matrix (Fin (2^m)) (Fin 1) ℂ)
    (ψd : Matrix (Fin (2^anc)) (Fin 1) ℂ)
    (h_wt : UCom.WellTyped m (real_QFTinv_on m))
    (h_IQFT : FormalRV.Framework.uc_eval (real_QFTinv_on m : BaseUCom m)
                = IQFT_matrix m) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => q) (real_QFTinv_on m) : BaseUCom (m + anc))
      * kron_vec ψc ψd
    = kron_vec (IQFT_matrix m * ψc) ψd := by
  rw [uc_eval_control_register_circuit_kron_vec (real_QFTinv_on m) h_wt ψc ψd]
  rw [h_IQFT]

/-- **Distribute `kron_vec` into a Fourier-weighted sum.** Algebraic helper
exposing the `kron_vec ψc ψ` factorization of the Fourier-weighted
superposition. -/
theorem fourier_weighted_kron_sum_eq_kron_vec_fourier_state
    {m anc : Nat} (θ : ℝ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
      ∑ x : Fin (2^m),
        Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
    = kron_vec
        (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
          ∑ x : Fin (2^m),
            Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
              FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  rw [kron_vec_smul_left]
  congr 1
  rw [kron_vec_sum_left]
  apply Finset.sum_congr rfl
  intro x _
  rw [kron_vec_smul_left]

/-- **Post-QFT theorem from IQFT correctness.** Given `h_IQFT`, the
lifted `real_QFTinv_on m` applied to the Fourier-weighted kron
superposition yields `kron_vec (qpe_phase_state m θ) ψ`. -/
theorem real_QFTinv_on_fourier_weighted_kron_state_from_matrix_correct
    {m anc : Nat}
    (θ : ℝ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ)
    (h_wt : UCom.WellTyped m (real_QFTinv_on m))
    (h_IQFT : FormalRV.Framework.uc_eval (real_QFTinv_on m : BaseUCom m)
                = IQFT_matrix m) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => q) (real_QFTinv_on m) : BaseUCom (m + anc))
      *
    (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
      ∑ x : Fin (2^m),
        Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
    = kron_vec (qpe_phase_state m θ) ψ := by
  rw [fourier_weighted_kron_sum_eq_kron_vec_fourier_state]
  rw [real_QFTinv_lifted_on_kron _ ψ h_wt h_IQFT]
  rw [IQFT_matrix_on_fourier_weighted_state m θ]

/-! ### Recursive-layer-level building blocks for arbitrary-n IQFT correctness

These lemmas are the layer-level interface used by the arbitrary-n
correctness proof (deferred to a later pass). The matrix-level
decomposition `IQFT_matrix_succ_decomp` is the central recursion;
the circuit-level decomposition uses `real_QFTinv_layer` together
with the per-target `inverse_qft_phase_ladder` ladders. -/

/-- **Named entry formula for `IQFT_matrix`.** Definitional unfolding,
exposed as a reusable theorem for the recursive correctness proof. -/
theorem IQFT_matrix_apply (m : Nat) (y x : Fin (2^m)) :
    IQFT_matrix m y x
      = ((1 : ℂ) / Real.sqrt (2^m : ℝ)) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (x.val : ℂ) * (y.val : ℂ)
                     / (2^m : ℂ)) := rfl

/-- **At `n = 2`, the recursive `real_QFTinv_layer` produces `IQFT_matrix 2`.**
This is the first nontrivial inductive-base instance of the
arbitrary-n correctness `uc_eval_real_QFTinv_layer_eq_IQFT_matrix`,
proved by chaining `real_QFTinv_layer_two_eq_candidate` with
`uc_eval_real_QFTinv2_candidate_eq_IQFT_matrix`. -/
theorem uc_eval_real_QFTinv_layer_eq_IQFT_matrix_two :
    FormalRV.Framework.uc_eval (real_QFTinv_layer 2 : BaseUCom 2)
      = IQFT_matrix 2 := by
  rw [real_QFTinv_layer_two_eq_candidate]
  exact uc_eval_real_QFTinv2_candidate_eq_IQFT_matrix

/-- **Matrix-arithmetic index decomposition.** Pure scalar identity
underlying the recursive `IQFT_matrix` decomposition: when an index
splits into a high bit + low part (`z = 2^n · z_h + z_l`), the
product `xy / 2^(n+1)` decomposes into three additive terms:
- `2^(n-1) · x_h · y_h` — integer for `n ≥ 1`, contributes `exp(±2πi·N) = 1`.
- `(x_h · y_l + x_l · y_h) / 2` — half-integer offsets (the inter-bit phases).
- `x_l · y_l / 2^(n+1)` — the lower-block phase. Note the denominator
  is `2^(n+1)`, not `2^n`; the recursive lower block exponent is
  `exp(-π · I · x_l y_l / 2^n)`, which is half the `IQFT_matrix n`
  argument. This means the natural matrix-level recursion is not
  `IQFT_matrix (n+1) y x = ... · IQFT_matrix n y_l x_l` — the
  textbook QFT recursion uses a different decomposition involving
  controlled-phase corrections at every recursion level. -/
theorem IQFT_index_split (n : Nat) (_hn : 1 ≤ n) (xh yh xl yl : Nat) :
    ((2^n * xh + xl : ℂ) * (2^n * yh + yl) / 2^(n+1) : ℂ)
    = (2^(n-1) * xh * yh : ℂ)
      + ((xh * yl + xl * yh : ℂ)) / 2
      + ((xl * yl : ℂ) / 2^(n+1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  push_cast
  field_simp
  ring

/-- **High bit of a Fin (2^(n+1)) index.** MSB-first convention: the
high bit is `x.val / 2^n`. -/
noncomputable def iqftHighBit (n : Nat) (x : Fin (2^(n+1))) : Fin 2 :=
  ⟨x.val / 2^n, by
    have : x.val < 2^(n+1) := x.isLt
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)]
    omega⟩

/-- **Lower n bits of a Fin (2^(n+1)) index.** `x.val % 2^n`. -/
noncomputable def iqftLowBits (n : Nat) (x : Fin (2^(n+1))) : Fin (2^n) :=
  ⟨x.val % 2^n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-- **Index reconstruction from MSB + low.** `x.val = x_h · 2^n + x_l`. -/
theorem iqft_index_reconstruct (n : Nat) (x : Fin (2^(n+1))) :
    x.val = (iqftHighBit n x).val * 2^n + (iqftLowBits n x).val := by
  show x.val = x.val / 2^n * 2^n + x.val % 2^n
  rw [Nat.div_add_mod' x.val (2^n)]

/-- **`exp(-2πi · k) = 1` for natural `k`.** Consequence of
`Complex.exp_int_mul_two_pi_mul_I`. -/
theorem exp_neg_two_pi_I_mul_nat (k : Nat) :
    Complex.exp ((-2 * Real.pi * (k : ℝ) : ℂ) * Complex.I) = 1 := by
  have h := Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ))
  push_cast at h
  rw [show ((-2 * Real.pi * (k : ℝ) : ℂ) * Complex.I)
        = -(k : ℂ) * (2 * Real.pi * Complex.I) from by push_cast; ring]
  exact h

/-- **`exp(-π · I · k) = (-1)^k` for natural `k`.** Drives the
half-integer cross-term phase in the IQFT decomposition. -/
theorem exp_neg_pi_I_mul_nat (k : Nat) :
    Complex.exp (((-Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) = (-1 : ℂ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (((-Real.pi * ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)
          = (((-Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) + (-((Real.pi : ℂ) * Complex.I))
       from by push_cast; ring]
    rw [Complex.exp_add, ih]
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]
    rw [pow_succ]
    ring

/-- **Scalar normalization for the IQFT recursion.** Factors the
inverse square-root: `1/√(2^(n+1)) = (1/√2) · (1/√(2^n))`. -/
theorem inv_sqrt_pow_two_succ_factor (n : Nat) :
    (1 : ℂ) / Real.sqrt (2^(n+1) : ℝ)
      = ((1 : ℂ) / Real.sqrt 2) * ((1 : ℂ) / Real.sqrt (2^n : ℝ)) := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h_sqrt_mul : Real.sqrt (2^(n+1) : ℝ) = Real.sqrt 2 * Real.sqrt (2^n : ℝ) := by
    rw [show ((2 : ℝ)^(n+1)) = 2 * 2^n from by ring]
    rw [Real.sqrt_mul (le_of_lt h2_pos)]
  rw [h_sqrt_mul]
  push_cast
  field_simp

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

/-- **Ideal IQFT column**: the column vector `IQFT_matrix n · basis_vector (2^n) x.val`.
This is the target of the `real_QFTinv_layer n` action on basis vector `x`. -/
noncomputable def IQFT_column (n : Nat) (x : Fin (2^n)) :
    Matrix (Fin (2^n)) (Fin 1) ℂ :=
  IQFT_matrix n * FormalRV.Framework.basis_vector (2^n) x.val


/-! ### Bit-reversal SWAP cascade basis action

The `bit_reversal_swaps n` circuit applies SWAP gates `SWAP i (n-1-i)`
for `i = 0, 1, ..., ⌊n/2⌋-1`. On a basis state `f_to_vec n f`, the
result is `f_to_vec n` of the function with bits reversed across
positions `[0, n-1]`. -/

/-- **Bit-swap on Boolean functions.** Swaps the values at positions
`a` and `b`. -/
def swapBits (f : Nat → Bool) (a b : Nat) : Nat → Bool :=
  fun i => if i = a then f b else if i = b then f a else f i

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

/-- **Recursive cumulative bit-reversal function.** Result of applying
all SWAPs `(k, n-1-k), (k+1, n-2-k), ...` to `f`. Terminates when
`2k+1 ≥ n` (no more swap pairs). -/
def applySwapsFrom (n : Nat) : (k : Nat) → (Nat → Bool) → (Nat → Bool)
  | k, f =>
    if h : 2 * k + 1 < n then
      applySwapsFrom n (k+1) (swapBits f k (n-1-k))
    else
      f
  termination_by k _ => n - 2 * k

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

/-! ### Inverse-QFT phase ladder basis action

The `inverse_qft_phase_ladder n target` circuit consists of a sequence
of `controlled_Rz` gates targeting qubit `target` from controls
`target+1, target+2, ..., n-1`, followed by `H target`. Each `controlled_Rz`
contributes a phase factor `exp(-π · I / 2^(j-target))` when both
control bit `j` and target bit `target` are 1; otherwise contributes 1.

On a basis state `f_to_vec n f`, the action factors as
`(accumulated phase) • (H_target · f_to_vec n f)`. -/

/-- **Recursive ladder phase scalar.** Product of controlled-Rz phase
factors for controls `j ∈ [k, n)`. -/
noncomputable def inverse_qft_ladder_phase_from
    (n target : Nat) (f : Nat → Bool) (k : Nat) : ℂ :=
  ∏ j ∈ Finset.Ico k n,
    if f j ∧ f target then
      Complex.exp ((((-(Real.pi / 2 ^ (j - target))) : ℝ)) * Complex.I)
    else 1

/-- **Full ladder phase**: the accumulated phase scalar for the
inverse-QFT ladder targeting `target`. -/
noncomputable def inverse_qft_ladder_phase
    (n target : Nat) (f : Nat → Bool) : ℂ :=
  inverse_qft_ladder_phase_from n target f (target + 1)

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

/-- **Recursive countdown output.** The expected output of `countdown n k`
applied to `f_to_vec n f`. Mirrors `countdown_succ_acts`: at step k+1,
ladder k is applied first (producing a phase × two-branch sum), then
`countdown_output n k` recursively to each branch. -/
noncomputable def countdown_output
    (n : Nat) : Nat → (Nat → Bool) → Matrix (Fin (2^n)) (Fin 1) ℂ
  | 0, f => f_to_vec n f
  | k+1, f =>
      inverse_qft_ladder_phase n k f •
        (((Real.sqrt 2 / 2 : ℂ) • countdown_output n k (update f k false))
          + ((if f k then -(Real.sqrt 2 / 2 : ℂ) else (Real.sqrt 2 / 2 : ℂ))
              • countdown_output n k (update f k true)))

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

/-! ### Named helpers for the countdown column

The countdown column for a basis-vector input `x : Fin (2^n)` is the
result of applying `real_QFTinv_layer n` to `basis_vector (2^n) x.val`,
expressed via the recursive `countdown_output`. Naming these helpers
makes the arbitrary-n induction proof more readable. -/

/-- Boolean function encoding a `Fin (2^n)` index in MSB-first form. -/
noncomputable def basisFunOfIndex (n : Nat) (x : Fin (2^n)) : Nat → Bool :=
  nat_to_funbool n x.val

/-- Boolean function after applying the full bit-reversal of `basisFunOfIndex`. -/
noncomputable def bitReversedBasisFun (n : Nat) (x : Fin (2^n)) : Nat → Bool :=
  applySwapsFrom n 0 (basisFunOfIndex n x)

/-- The countdown column: the result of `real_QFTinv_layer n` applied to
`basis_vector (2^n) x.val`, as an explicit matrix column. -/
noncomputable def countdownColumn (n : Nat) (x : Fin (2^n)) :
    Matrix (Fin (2^n)) (Fin 1) ℂ :=
  countdown_output n n (bitReversedBasisFun n x)

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

/-! ### Countdown output dimension split

Bridges the (n+1)-qubit `countdown_output` to the n-qubit one with
an extra LSB qubit carried through. Each ladder for target `t < n`
in the (n+1)-qubit system contributes an extra phase from qubit n
acting as a control. The cumulative extra phase is tracked by
`cumulative_extra_phase`. -/

/-- **Embed an n-qubit state into an (n+1)-qubit state by appending
an extra LSB qubit.** Uses `kron_vec` with the n-qubit vector at the
high positions and the 1-qubit extra at the LSB. -/
noncomputable def embedWithExtraBit
    (n : Nat) (extra : Bool)
    (v : Matrix (Fin (2^n)) (Fin 1) ℂ) :
    Matrix (Fin (2^(n+1))) (Fin 1) ℂ :=
  kron_vec v (FormalRV.Framework.basis_vector 2 (if extra then 1 else 0))

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

/-- **Cumulative extra phase**: product over targets `t ∈ [0, k)` of the
phase factor contributed by qubit `n` controlling target `t`. -/
noncomputable def cumulative_extra_phase
    (n k : Nat) (f : Nat → Bool) : ℂ :=
  ∏ t ∈ Finset.range k,
    if f n ∧ f t then
      Complex.exp ((((-(Real.pi / 2 ^ (n - t))) : ℝ)) * Complex.I)
    else 1

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

/-! ### Index splits for the output column

The output index `y : Fin (2^(n+1))` of a column theorem needs to be
split into a high-n part and a low-1 (LSB) part, matching the
`embedWithExtraBit` structure (which uses `kron_vec` with n-qubit at
high positions and 1-qubit at LSB). -/

/-- **High n bits of an (n+1)-qubit index.** `y.val / 2`. -/
noncomputable def iqftHighBitsN (n : Nat) (y : Fin (2^(n+1))) : Fin (2^n) :=
  ⟨y.val / 2, by
    have : y.val < 2^(n+1) := y.isLt
    have h : 2^(n+1) = 2 * 2^n := by ring
    omega⟩

/-- **LSB of an (n+1)-qubit index.** `y.val % 2`. -/
noncomputable def iqftLowBitLSB (n : Nat) (y : Fin (2^(n+1))) : Fin 2 :=
  ⟨y.val % 2, by omega⟩

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
private theorem prod_exp_bits_eq_exp_sum_aux
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
private theorem inv_sqrt_two_eq_sqrt_two_div_two :
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

/-! ### Real, non-stub QPE circuit + unconditional single-eigenstate theorem

The companion to `real_QPE` that uses the arbitrary-n correct
`real_QFTinv_layer` instead of the stubbed `real_QFTinv_on`. The
single-eigenstate semantic theorem is now UNCONDITIONAL (no
`h_IQFT` hypothesis). -/

/-- **Real QPE circuit using `real_QFTinv_layer`.** The non-stub
counterpart to `real_QPE`. Structure:
  `npar_H m ; controlled_powers (lifted f) m ; lifted real_QFTinv_layer m`. -/
noncomputable def real_QPE_layer (m anc : Nat) (f : Nat → FormalRV.Framework.BaseUCom anc) :
    FormalRV.Framework.BaseUCom (m + anc) :=
  UCom.seq (npar_H m)
    (UCom.seq
      (controlled_powers
        (fun i => (map_qubits (fun q => m + q) (f i)
          : FormalRV.Framework.BaseUCom (m + anc))) m)
      (map_qubits (fun q => q) (real_QFTinv_layer m)
        : FormalRV.Framework.BaseUCom (m + anc)))

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

/-! ### Combined-register modmult eigenstate sum form

Lifts `modmult_eigenstate_as_sum` from the data register to the combined
data+ancilla register via `kron_vec_sum_left` + `kron_vec_smul_left` +
pointwise basis-vector match. Cannot live in `Eigenstate.lean` because
the `kron_vec_sum_left` helper lives in `PhaseKickback.lean` (which is
imported by `PostQFT` but not by `Eigenstate`). -/

/-- **Combined-register modmult eigenstate sum form**: the combined
eigenstate `kron_vec ψ_k |0⟩_anc` admits the basis-vector decomposition
`∑_j character_vector r k j • basis_vector (2^(n+anc)) (a^j%N · 2^anc)`,
matching the orbit basis vectors (data-register orbit index times
`2^anc` for the zero ancilla). Proven by combining
`modmult_eigenstate_as_sum` with `kron_vec_sum_left` /
`kron_vec_smul_left`, then a pointwise basis match using
`kron_vec_apply` + the `kron_vec_high`/`kron_vec_low` index decomposition. -/
theorem modmult_eigenstate_combined_as_sum (a r N n anc : Nat) (k : Fin r) :
    modmult_eigenstate_combined a r N n anc k
    = ∑ j : Fin r, character_vector r k j •
        FormalRV.Framework.basis_vector (2^(n+anc)) (a^j.val % N * 2^anc) := by
  unfold modmult_eigenstate_combined
  rw [modmult_eigenstate_as_sum, kron_vec_sum_left]
  apply Finset.sum_congr rfl
  intro j _
  rw [kron_vec_smul_left]
  congr 1
  ext i col
  rw [kron_vec_apply, basis_vector_apply, basis_vector_apply]
  unfold kron_zeros
  rw [basis_vector_apply]
  have h_decomp : i.val = (kron_vec_high i).val * 2^anc + (kron_vec_low i).val := by
    unfold kron_vec_high kron_vec_low
    show i.val = i.val / 2^anc * 2^anc + i.val % 2^anc
    rw [Nat.div_add_mod' i.val (2^anc)]
  by_cases hH : (kron_vec_high i).val = a^j.val % N
  · by_cases hL : (kron_vec_low i).val = 0
    · rw [if_pos hH, if_pos hL, mul_one]
      have h_i_eq : i.val = a^j.val % N * 2^anc := by
        rw [h_decomp, hH, hL, Nat.add_zero]
      rw [if_pos h_i_eq]
    · rw [if_neg hL, mul_zero]
      have h_i_ne : i.val ≠ a^j.val % N * 2^anc := by
        intro heq
        apply hL
        show i.val % 2^anc = 0
        rw [heq, Nat.mul_mod_left]
      rw [if_neg h_i_ne]
  · rw [if_neg hH, zero_mul]
    have h_i_ne : i.val ≠ a^j.val % N * 2^anc := by
      intro heq
      apply hH
      show i.val / 2^anc = a^j.val % N
      rw [heq, Nat.mul_div_cancel _ (Nat.two_pow_pos anc)]
    rw [if_neg h_i_ne]

/-- **Modmult action as orbit sum (intermediate step toward eigenvalue
theorem)**: applying `uc_eval (f i)` to `ψ_k^combined` and using the
`a^r % N = 1` periodicity gives a sum over `Fin r` where the basis
vector index is `a^((2^i + j.val) % r) % N · 2^anc` (the orbit position
reduced mod r). The next step (reindexing via `sum_fin_add_mod` + phase
extraction via `character_vector_shift_identity`) gives the eigenvalue
form `exp(2π·I · 2^i · k / r) • ψ_k^combined`. -/
theorem modmult_combined_action_as_orbit_sum
    (a r N n anc i : Nat) (k : Fin r)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_arN : a^r % N = 1)
    (h_N_pos : 0 < N) :
    FormalRV.Framework.uc_eval (f i)
      * modmult_eigenstate_combined a r N n anc k
    = ∑ j : Fin r, character_vector r k j •
        FormalRV.Framework.basis_vector (2^(n+anc))
          (a^((2^i + j.val) % r) % N * 2^anc) := by
  rw [modmult_eigenstate_combined_as_sum, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_smul]
  congr 1
  show FormalRV.SQIRPort.uc_eval (f i)
        (FormalRV.SQIRPort.basis_vector (2^(n+anc)) (a^j.val % N * 2^anc))
      = FormalRV.SQIRPort.basis_vector (2^(n+anc))
          (a^((2^i + j.val) % r) % N * 2^anc)
  rw [MultiplyCircuitProperty_acts_on_orbit_basis a N n anc i j.val f h_modmul h_N_pos]
  congr 2
  exact (a_pow_mod_periodic_in_n a N r (2^i + j.val) h_arN).symm

/-- **HEADLINE: Modmult eigenstate eigenvalue theorem (LSB form)**. The
combined-register modular-multiplier eigenstate `ψ_k^combined` is an
eigenstate of each `f i = U^{a^{2^i}}` (from `ModMulImpl`) with
eigenvalue `exp(2π·I · 2^i · k / r)` — the standard LSB-first
QPE-eigenvalue convention.

Proof: build on `modmult_combined_action_as_orbit_sum` (which reduces
`uc_eval (f i) * ψ_k_combined` to a sum over `Fin r` with basis-vector
index `a^((2^i + j.val) % r) % N · 2^anc`). Reindex via `sum_fin_add_mod`
with shift `s = r - 2^i % r` (the inverse shift). The basis vector index
simplifies to `a^j.val % N · 2^anc` via Nat arithmetic. The
`character_vector` picks up a phase factor `exp(-2π·I · s · k / r) =
exp(-2π·I · k) · exp(+2π·I · (2^i % r) · k / r) = 1 · exp(+2π·I · 2^i · k / r)`
(via `Complex.exp_int_mul_two_pi_mul_I` + `exp_mod_r_shift_pos`).
Finally `Finset.smul_sum` factors the phase out of the reassembled sum.

This is the LSB-form eigenvalue compatible with `QPE_var_lsb`. Use
together with `QPE_var_lsb_on_eigenstate_from_real_QFTinv` to obtain
the per-orbit QPE action on `modmult_eigenstate_combined`. -/
theorem modmult_eigenstate_combined_eigen_lsb
    (a r N n anc i : Nat) (k : Fin r)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_r_pos : 0 < r)
    (h_arN : a^r % N = 1)
    (h_N_pos : 0 < N) :
    FormalRV.Framework.uc_eval (f i)
      * modmult_eigenstate_combined a r N n anc k
    = Complex.exp
        (((2 * Real.pi * ((2^i : Nat) : ℝ) * (k.val : ℝ) / (r : ℝ) : ℝ) : ℂ) * Complex.I)
      • modmult_eigenstate_combined a r N n anc k := by
  rw [modmult_combined_action_as_orbit_sum a r N n anc i k f h_modmul h_arN h_N_pos]
  set s := r - 2^i % r with hs
  rw [sum_fin_add_mod r h_r_pos s
        (fun j => character_vector r k j •
          FormalRV.Framework.basis_vector (2^(n+anc))
            (a^((2^i + j.val) % r) % N * 2^anc))]
  rw [modmult_eigenstate_combined_as_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h_arith : (2^i + ((j.val + s) % r)) % r = j.val := by
    have h_2ir : 2^i % r < r := Nat.mod_lt _ h_r_pos
    have h_jr : j.val < r := j.isLt
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h_decomp : 2^i = 2^i % r + r * (2^i / r) := by
      have := Nat.div_add_mod (2^i) r; omega
    have h_eq : 2^i + (j.val + s) = j.val + r * (2^i / r + 1) := by
      have h_split : r * (2^i / r + 1) = r * (2^i / r) + r := by ring
      have h_2ir_le : 2^i % r ≤ r := le_of_lt h_2ir
      show 2^i + (j.val + (r - 2^i % r)) = j.val + r * (2^i / r + 1)
      omega
    rw [h_eq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt h_jr
  show character_vector r k ⟨(j.val + s) % r, Nat.mod_lt _ h_r_pos⟩ •
        FormalRV.Framework.basis_vector (2^(n+anc))
          (a^((2^i + (⟨(j.val + s) % r, Nat.mod_lt _ h_r_pos⟩ : Fin r).val) % r) % N * 2^anc)
      = Complex.exp _ • (character_vector r k j •
          FormalRV.Framework.basis_vector (2^(n+anc)) (a^j.val % N * 2^anc))
  rw [show ((⟨(j.val + s) % r, Nat.mod_lt _ h_r_pos⟩ : Fin r).val : Nat)
        = (j.val + s) % r from rfl]
  rw [h_arith]
  rw [character_vector_shift_identity r h_r_pos k j s]
  rw [smul_smul]
  congr 1
  rw [mul_comm]
  congr 1
  have h_r_ne : (r : ℂ) ≠ 0 := by exact_mod_cast h_r_pos.ne'
  have h_2i_mod_lt : 2^i % r ≤ r := le_of_lt (Nat.mod_lt _ h_r_pos)
  have h_s_cast : (s : ℂ) = (r : ℂ) - (2^i % r : Nat) := by
    show ((r - 2^i % r : Nat) : ℂ) = (r : ℂ) - (2^i % r : Nat)
    push_cast
    rw [Nat.cast_sub h_2i_mod_lt]
  rw [show -(2 * (Real.pi : ℂ) * Complex.I * (s * k.val : ℂ)) / (r : ℂ)
        = ((-(k.val : Nat) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
          + 2 * (Real.pi : ℂ) * Complex.I * ((2^i % r : Nat) * k.val : ℂ) / (r : ℂ) from by
      rw [h_s_cast]; push_cast; field_simp; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  rw [exp_mod_r_shift_pos r h_r_pos k (2^i)]
  push_cast
  ring_nf

/-- **HEADLINE: Per-orbit QPE action on the modmult eigenstate.**
Applying `QPE_var_lsb m (n+anc) f` to `|0⟩_m ⊗ ψ_k^combined` yields
`qpe_phase_state m (k.val / r) ⊗ ψ_k^combined`. Direct application of
`QPE_var_lsb_on_eigenstate_from_real_QFTinv` with the LSB eigenvalue
hypothesis discharged via `modmult_eigenstate_combined_eigen_lsb`. This
is the per-orbit step needed by the orbit-sum linearity that drives
the final Shor measurement-probability theorem. -/
theorem QPE_var_lsb_on_modmult_eigenstate
    {m n anc : Nat} (a r N : Nat) (k : Fin r)
    (hmanc : 0 < m + (n + anc)) (hm : 0 < m)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1) (h_N_pos : 0 < N)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped (n + anc) (f i)) :
    FormalRV.Framework.uc_eval (QPE_var_lsb m (n + anc) f)
      * kron_vec (FormalRV.Framework.kron_zeros m)
          (modmult_eigenstate_combined a r N n anc k)
    = kron_vec (qpe_phase_state m ((k.val : ℝ) / (r : ℝ)))
        (modmult_eigenstate_combined a r N n anc k) := by
  apply QPE_var_lsb_on_eigenstate_from_real_QFTinv hmanc hm f
        (modmult_eigenstate_combined a r N n anc k)
        ((k.val : ℝ) / (r : ℝ)) h_wt_all
  intro i _
  rw [modmult_eigenstate_combined_eigen_lsb a r N n anc i k f h_modmul
        h_r_pos h_arN h_N_pos]
  congr 1
  congr 1
  push_cast
  ring

/-! ### Toward `Shor_final_state_lsb_eq_shor_orbit_state`

The headline state-equality theorem connecting the LSB-compatible
Shor circuit output to the `shor_orbit_state` closed form. This
section sets up two pieces: a matrix-level orbit decomposition
(lifting the existing pointwise version), and the definition of
`Shor_final_state_lsb` itself. The full state equality is a
follow-up combining these with `QPE_var_lsb_on_modmult_eigenstate`
+ linearity over the orbit sum. -/

/-- **Matrix-level orbit decomposition.** Lifts the pointwise
`orbit_decomposition_combined_pointwise` to a Matrix equality:
`kron_vec |1⟩_n |0⟩_anc = (1/√r) • ∑_k modmult_eigenstate_combined ... k`.
Direct `Matrix.ext` + `Matrix.smul_apply` + `Matrix.sum_apply` chain. -/
theorem orbit_decomposition_combined_matrix
    (a r N n anc : Nat)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1)
    (h_min : ∀ s, 0 < s → s < r → a^s % N ≠ 1)
    (h_N : 1 < N) (h_N_lt : N ≤ 2^n) :
    kron_vec (FormalRV.Framework.basis_vector (2^n) 1)
             (FormalRV.Framework.kron_zeros anc)
    = (1 / (Real.sqrt r : ℂ)) •
        ∑ k : Fin r, modmult_eigenstate_combined a r N n anc k := by
  ext i col
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  exact orbit_decomposition_combined_pointwise a r N n anc h_r_pos h_arN h_min h_N h_N_lt i

/-- **LSB-compatible Shor final state** (parallel to `Shor_final_state`).
Uses `QPE_var_lsb` (the LSB-oracle-reversed wrapper) instead of `QPE_var`.
This is the state on which the LSB-chain semantic theorems apply
directly; bridging to the published `Shor_final_state` requires a
design decision per the autoresearch protocol. -/
noncomputable def Shor_final_state_lsb (m n anc : Nat)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc)) :
    QState (2^m * 2^n * 2^anc) :=
  QState.cast (by rw [pow_add, pow_add, mul_assoc])
    (uc_eval (QPE_var_lsb m (n + anc) f) (Shor_initial_state m n anc))

/-- **QPE_var_lsb action on the kron(|0⟩_m, (1/√r)·∑_k β_k) input.**
The linearity-and-eigenstate step: applying `uc_eval (QPE_var_lsb)` to
the kron of `|0⟩_m` with a `(1/√r)`-weighted sum of modmult eigenstates
yields the corresponding `(1/√r)`-weighted sum of
`qpe_phase_state m (k/r) ⊗ ψ_k`. Combines `kron_vec_smul_right` +
`kron_vec_sum_right` + `Matrix.mul_smul` + `Matrix.mul_sum` +
`QPE_var_lsb_on_modmult_eigenstate`. -/
theorem QPE_var_lsb_on_orbit_sum
    (a r N : Nat) {m n anc : Nat}
    (hmanc : 0 < m + (n + anc)) (hm : 0 < m)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1) (h_N_pos : 0 < N)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped (n + anc) (f i)) :
    FormalRV.Framework.uc_eval (QPE_var_lsb m (n + anc) f)
      * kron_vec (FormalRV.Framework.kron_zeros m)
          ((1 / (Real.sqrt r : ℂ)) •
            ∑ k : Fin r, modmult_eigenstate_combined a r N n anc k)
    = (1 / (Real.sqrt r : ℂ)) •
        ∑ k : Fin r,
          kron_vec (qpe_phase_state m ((k.val : ℝ) / (r : ℝ)))
                   (modmult_eigenstate_combined a r N n anc k) := by
  rw [kron_vec_smul_right, kron_vec_sum_right]
  rw [Matrix.mul_smul, Matrix.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact QPE_var_lsb_on_modmult_eigenstate a r N k hmanc hm h_r_pos h_arN h_N_pos
    f h_modmul h_wt_all

/-- **HEADLINE: pre-cast Shor state equality (LSB pipeline).** The
right-associated `kron_vec (kron_zeros m) (kron_vec |1⟩_n |0⟩_anc)`
input — which equals `Shor_initial_state` modulo the `Nat.add_assoc`
cast — produces `shor_orbit_state` after `uc_eval (QPE_var_lsb)`.

Proof chain (all kernel-clean atoms from prior ticks):
  `orbit_decomposition_combined_matrix` to express the data+ancilla
  part as the orbit sum →
  `QPE_var_lsb_on_orbit_sum` to apply QPE per orbit term →
  `shor_orbit_state` unfolding + pointwise match.

The follow-up theorem `Shor_final_state_lsb_eq_shor_orbit_state` adds
the `QState.cast` bookkeeping to connect with `Shor_final_state_lsb`'s
signature. -/
theorem QPE_var_lsb_on_Shor_initial_raw
    (a r N : Nat) {m n anc : Nat}
    (hmanc : 0 < m + (n + anc)) (hm : 0 < m)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1)
    (h_min : ∀ s, 0 < s → s < r → a^s % N ≠ 1)
    (h_N : 1 < N) (h_N_lt : N ≤ 2^n) (h_N_pos : 0 < N)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped (n + anc) (f i)) :
    FormalRV.Framework.uc_eval (QPE_var_lsb m (n + anc) f)
      * (kron_vec (FormalRV.Framework.kron_zeros m)
           (kron_vec (FormalRV.Framework.basis_vector (2^n) 1)
                     (FormalRV.Framework.kron_zeros anc))
          : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ)
    = shor_orbit_state a r N m n anc := by
  rw [orbit_decomposition_combined_matrix a r N n anc h_r_pos h_arN h_min h_N h_N_lt]
  rw [QPE_var_lsb_on_orbit_sum a r N hmanc hm h_r_pos h_arN h_N_pos f h_modmul h_wt_all]
  unfold shor_orbit_state
  ext i col
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]

/-- **`kron_vec` associativity** modulo the `Nat.add_assoc` cast.
`QState.cast (Nat.add_assoc) (kron(kron x y, z)) = kron x (kron y z)`
(at dim `2^(a+(b+c))`). Pointwise proof via division/mod arithmetic on
the index decomposition (`kron_vec_high` / `kron_vec_low` chains). -/
theorem kron_vec_assoc {a b c : Nat}
    (x : Matrix (Fin (2^a)) (Fin 1) ℂ)
    (y : Matrix (Fin (2^b)) (Fin 1) ℂ)
    (z : Matrix (Fin (2^c)) (Fin 1) ℂ) :
    QState.cast (by rw [Nat.add_assoc])
        (kron_vec (kron_vec x y) z : Matrix (Fin (2^((a+b)+c))) (Fin 1) ℂ)
    = (kron_vec x (kron_vec y z) : Matrix (Fin (2^(a+(b+c)))) (Fin 1) ℂ) := by
  funext i col
  show (kron_vec (kron_vec x y) z) (Fin.cast _ i) 0
      = kron_vec x (kron_vec y z) i col
  fin_cases col
  rw [kron_vec_apply, kron_vec_apply, kron_vec_apply, kron_vec_apply, mul_assoc]
  have h_cast : (Fin.cast (by rw [Nat.add_assoc] : 2^(a+(b+c)) = 2^((a+b)+c)) i).val
                  = i.val := rfl
  have h_pow_eq : (2^(b+c) : Nat) = 2^b * 2^c := by rw [pow_add]
  have h_x_idx : kron_vec_high (kron_vec_high (Fin.cast (by rw [Nat.add_assoc]
                  : 2^(a+(b+c)) = 2^((a+b)+c)) i)) = (kron_vec_high i : Fin (2^a)) := by
    apply Fin.ext
    show (Fin.cast _ i).val / 2^c / 2^b = i.val / 2^(b+c)
    rw [h_cast, Nat.div_div_eq_div_mul, mul_comm, ← pow_add]
  have h_y_idx : kron_vec_low (kron_vec_high (Fin.cast (by rw [Nat.add_assoc]
                  : 2^(a+(b+c)) = 2^((a+b)+c)) i))
                = (kron_vec_high (kron_vec_low i) : Fin (2^b)) := by
    apply Fin.ext
    show (Fin.cast _ i).val / 2^c % 2^b = i.val % 2^(b+c) / 2^c
    rw [h_cast, h_pow_eq, Nat.mod_mul_left_div_self]
  have h_z_idx : kron_vec_low (Fin.cast (by rw [Nat.add_assoc]
                  : 2^(a+(b+c)) = 2^((a+b)+c)) i)
                = (kron_vec_low (kron_vec_low i) : Fin (2^c)) := by
    apply Fin.ext
    show (Fin.cast _ i).val % 2^c = i.val % 2^(b+c) % 2^c
    rw [h_cast, h_pow_eq, Nat.mod_mul_left_mod]
  rw [h_x_idx, h_y_idx, h_z_idx]

/-- **HEADLINE: Fully-typed Shor LSB state equality.**
`Shor_final_state_lsb m n anc f = QState.cast _ (shor_orbit_state a r N m n anc)`.

Combines:
- Unfold `Shor_final_state_lsb` and `Shor_initial_state`.
- `kron_vec_assoc` to bridge the left-associated kron_vec inside
  `Shor_initial_state` with the right-associated form.
- `QPE_var_lsb_on_Shor_initial_raw` to apply QPE_var_lsb and produce
  `shor_orbit_state`.

This is the MATHEMATICAL CLOSURE of the LSB-pipeline state equality.
Bridging to the published `Shor_final_state` (using `QPE_var`, not
`QPE_var_lsb`) requires a separate DESIGN DECISION (per autoresearch
protocol stop conditions). -/
theorem Shor_final_state_lsb_eq_shor_orbit_state
    (a r N m n anc : Nat)
    (hmanc : 0 < m + (n + anc)) (hm : 0 < m)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1)
    (h_min : ∀ s, 0 < s → s < r → a^s % N ≠ 1)
    (h_N : 1 < N) (h_N_lt : N ≤ 2^n) (h_N_pos : 0 < N)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped (n + anc) (f i)) :
    Shor_final_state_lsb m n anc f
    = QState.cast (by rw [pow_add, pow_add, mul_assoc])
        (shor_orbit_state a r N m n anc) := by
  unfold Shor_final_state_lsb Shor_initial_state FormalRV.SQIRPort.uc_eval
  congr 1
  rw [kron_vec_assoc (FormalRV.Framework.kron_zeros m)
        (FormalRV.Framework.basis_vector (2^n) 1)
        (FormalRV.Framework.kron_zeros anc)]
  exact QPE_var_lsb_on_Shor_initial_raw a r N hmanc hm h_r_pos h_arN h_min h_N h_N_lt h_N_pos
    f h_modmul h_wt_all

/-! ### Final closure: replacing the `QPE_MMI_correct` axiom

The LSB-pipeline state equality `Shor_final_state_lsb_eq_shor_orbit_state`
combined with the design change to `Shor_final_state` (which now uses
`QPE_var_lsb` — see Shor.lean) unlocks the closure of `QPE_MMI_correct`.

The new theorem chain:
1. `qpe_semantics_measurement_eq_from_lsb`: discharges the
   `h_qpe_semantics` hypothesis of `QPE_MMI_correct_modulo_qpe_semantics`.
2. `theorem QPE_MMI_correct`: replaces the deleted axiom of the same name.
3. `theorem Shor_correct_var`: re-declares the (now axiom-free) Shor
   correctness theorem in this file (moved from Shor.lean since it
   depends on the new theorem).
4. `theorem Shor_correct`: re-declares the specialised version. -/

/-- **`h_qpe_semantics` discharge.** With `Shor_final_state` now defined
via `QPE_var_lsb`, the LSB-pipeline state equality
`Shor_final_state_lsb_eq_shor_orbit_state` reduces it to a `QState.cast`
of `shor_orbit_state`, and `prob_partial_meas_cast` strips the cast. -/
theorem qpe_semantics_measurement_eq_from_lsb
    (a r N m n anc k : Nat) (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_modmul : ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → uc_well_typed (f i)) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (Shor_final_state m n anc f)
    = prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (shor_orbit_state a r N m n anc) := by
  obtain ⟨⟨h_a_pos, h_a_lt⟩, h_ord, h_m_bounds, h_n_bounds⟩ := h_basic
  obtain ⟨h_r_pos, h_arN, h_min⟩ := h_ord
  have h_N_pos : 0 < N := by omega
  have h_N_gt_one : 1 < N := by omega
  have h_N_lt_pow : N ≤ 2^n := h_n_bounds.1.le
  have hm : 0 < m := by
    have h_2m_pos : 0 < 2^m := Nat.two_pow_pos m
    have h_Nsq_pos : 0 < N^2 := by positivity
    have h_Nsq_lt : N^2 < 2^m := h_m_bounds.1
    by_contra h
    push_neg at h
    interval_cases m
    simp at h_Nsq_lt
    omega
  have hmanc : 0 < m + (n + anc) := by omega
  -- Shor_final_state and Shor_final_state_lsb are rfl-equal after the design change.
  have h_state_eq : Shor_final_state m n anc f
      = QState.cast (by rw [pow_add, pow_add, mul_assoc])
          (shor_orbit_state a r N m n anc) := by
    show Shor_final_state_lsb m n anc f
        = QState.cast _ (shor_orbit_state a r N m n anc)
    exact Shor_final_state_lsb_eq_shor_orbit_state a r N m n anc hmanc hm
      h_r_pos h_arN h_min h_N_gt_one h_N_lt_pow h_N_pos f h_modmul
      (fun i hi => h_wt i hi)
  rw [h_state_eq, prob_partial_meas_cast]

/-- **HEADLINE: `QPE_MMI_correct` (theorem replacing the axiom).** Same
statement as the deleted axiom; proof chains through
`QPE_MMI_correct_modulo_qpe_semantics` (in Shor.lean) +
`qpe_semantics_measurement_eq_from_lsb` (above). -/
theorem QPE_MMI_correct
    (a r N m n anc k : Nat) (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_mmi : ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  apply QPE_MMI_correct_modulo_qpe_semantics a r N m n anc k f h_basic h_mmi h_wt h_k_lt
  exact qpe_semantics_measurement_eq_from_lsb a r N m n anc k f h_basic h_mmi h_wt

/-- **`Shor_correct_var`** (Coq: `Shor.v:1193`). Re-declared in PostQFT
since `Shor.lean`'s version was deleted along with the axiom. Now
uses the proved `QPE_MMI_correct` theorem instead of the axiom. -/
theorem Shor_correct_var
    (a r N m n anc : Nat) (u : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_modmul : ModMulImpl a N n anc u)
    (h_wt : ∀ i, i < m → uc_well_typed (u i)) :
    probability_of_success a r N m n anc u ≥ κ / (Nat.log2 N : ℝ)^4 :=
  Shor_correct_var_conditional a r N m n anc u h_basic h_modmul h_wt
    (fun a' r' N' m' n' anc' k' f' h_b h_m h_w h_k =>
      QPE_MMI_correct a' r' N' m' n' anc' k' f' h_b h_m h_w h_k)
    (fun r' N' h_pos h_le => phi_n_over_n_lowerbound r' N' h_pos h_le)

/-- **`Shor_correct`** (Coq: `Shor.v:1295`). The specialised version
at `f_modmult_circuit`. Re-declared in PostQFT since `Shor.lean`'s
version was deleted along with the axiom. Uses the proved
`Shor_correct_var`.

**DEPRECATED (2026-05-29, Tick 84):** This theorem depends on the
deprecated placeholder axioms `f_modmult_circuit`,
`f_modmult_circuit_MMI`, and `f_modmult_circuit_uc_well_typed`.
Cite `FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms`
instead — that is the verified, axiom-free Shor theorem using the
SQIR-faithful modular multiplier. -/
@[deprecated "Use FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms instead — that theorem does not depend on the placeholder f_modmult_circuit* axioms" (since := "2026-05-29")]
theorem Shor_correct
    (a N : Nat) (h_aN : 0 < a ∧ a < N) (h_coprime : Nat.gcd a N = 1) :
    let m := Nat.log2 (2 * N^2)
    let n := Nat.log2 (2 * N)
    probability_of_success a (ord a N) N m n (modmult_rev_anc n)
        (f_modmult_circuit a (modinv a N) N n)
      ≥ κ / (Nat.log2 N : ℝ)^4 := by
  obtain ⟨h_a_pos, h_a_lt⟩ := h_aN
  have h_N_gt_one : 1 < N := by omega
  have h_Nsq_ne : N^2 ≠ 0 := by positivity
  have h_2N_ne : (2 * N) ≠ 0 := by omega
  have h_2Nsq_ne : (2 * N^2) ≠ 0 := by
    have : 0 < 2 * N^2 := by positivity
    omega
  have h_N_ne : N ≠ 0 := by omega
  have h_ord : Order a (ord a N) N := ord_Order a N h_a_pos h_a_lt h_coprime
  have h_log2_m : Nat.log2 (2 * N^2) = Nat.log2 (N^2) + 1 :=
    Nat.log2_two_mul h_Nsq_ne
  have h_log2_n : Nat.log2 (2 * N) = Nat.log2 N + 1 :=
    Nat.log2_two_mul h_N_ne
  have h_m_lower : 2 ^ (Nat.log2 (2 * N^2)) ≤ 2 * N^2 :=
    Nat.log2_self_le h_2Nsq_ne
  have h_m_upper : N^2 < 2 ^ (Nat.log2 (2 * N^2)) := by
    rw [h_log2_m, pow_succ]
    have h1 : 2 ^ Nat.log2 (N^2) ≤ N^2 := Nat.log2_self_le h_Nsq_ne
    have h2 : N^2 < 2 ^ (Nat.log2 (N^2) + 1) := by
      rw [← Nat.log2_lt h_Nsq_ne]; omega
    rw [pow_succ] at h2
    omega
  have h_n_lower : 2 ^ (Nat.log2 (2 * N)) ≤ 2 * N :=
    Nat.log2_self_le h_2N_ne
  have h_n_upper : N < 2 ^ (Nat.log2 (2 * N)) := by
    rw [h_log2_n, pow_succ]
    have h1 : 2 ^ Nat.log2 N ≤ N := Nat.log2_self_le h_N_ne
    have h2 : N < 2 ^ (Nat.log2 N + 1) := by
      rw [← Nat.log2_lt h_N_ne]; omega
    rw [pow_succ] at h2
    omega
  have h_basic : BasicSetting a (ord a N) N
      (Nat.log2 (2 * N^2)) (Nat.log2 (2 * N)) :=
    ⟨⟨h_a_pos, h_a_lt⟩, h_ord, ⟨h_m_upper, h_m_lower⟩, ⟨h_n_upper, h_n_lower⟩⟩
  have h_minv_lt : modinv a N < N := modinv_upper_bound a N h_N_gt_one
  have h_minv_inv : a * modinv a N % N = 1 :=
    Order_modinv_correct a N (ord a N) h_ord h_a_lt
  exact Shor_correct_var a (ord a N) N
    (Nat.log2 (2 * N^2)) (Nat.log2 (2 * N))
    (modmult_rev_anc (Nat.log2 (2 * N)))
    (f_modmult_circuit a (modinv a N) N (Nat.log2 (2 * N)))
    h_basic
    (f_modmult_circuit_MMI a (modinv a N) N (Nat.log2 (2 * N))
      h_a_lt h_minv_lt h_minv_inv)
    (fun i _ => f_modmult_circuit_uc_well_typed a (modinv a N) N
      (Nat.log2 (2 * N)) h_N_gt_one h_a_lt h_minv_lt i)

end FormalRV.SQIRPort
