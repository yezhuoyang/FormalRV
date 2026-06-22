/-
  FormalRV.QFT.TwoRegisterQFT.CircuitMeasurement — the PROJECTION half of the measured two-register
  QFT run: it applies the verified QFT gate (`Circuit.lean`) to a post-oracle state and reads off the
  control-register Born probability as a `prob_partial_meas` statement of the shape the Shor
  measurement pipeline consumes.

  ## What this adds — and what it does NOT

  `Circuit.lean` gives the QFT gate + its unitary semantics.  This file models the measured run:

  1. `twoRegOracleState a b t c tgt` — the POST-ORACLE 3-register state
     `∑_{x<2^a} ∑_{y<2^b} c x y · |x⟩_A |y⟩_B |tgt x y⟩_T`.
     **Scope note (honest):** the oracle here is abstracted by its OUTPUT STATE — `twoRegOracleState`
     is posited directly, with arbitrary `c, tgt` and NO `BaseUCom`/`uc_eval`/unitarity hypothesis.
     This is *weaker* than the single-register pipeline's `MultiplyCircuitProperty`, which pins the
     full `uc_eval` action of an actual `BaseUCom` oracle (the post-oracle state is then *derived*).
     Realizing `twoRegOracleState` as `entangling-oracle-gate ∘ input-prep` is the remaining open seam;
     for the Ekerå–Håstad instantiation the chosen `(c, tgt)` IS the image of the standard reversible
     map `|x,y,0⟩ ↦ |x,y,(x−yd)⟩` on a normalized uniform input, but that is true by construction here,
     not discharged as a gate property.
  2. `twoRegQFTMeasState` — apply `twoRegQFT ⊗ I_target` (the verified QFT on the two control
     registers, identity on the target), via `uc_eval_control_register_circuit_kron_vec`.  This half
     IS gate-honest (genuine `uc_eval` of the verified `twoRegQFT`).
  3. `prob_partial_meas (basis_vector (2^(a+b)) ⟨control outcome⟩) twoRegQFTMeasState` — the genuine
     Born probability of measuring the two control registers at `(j,k)`, marginalising the target.

  ## Headline (`prob_partial_meas_twoRegQFTMeasState`)

      prob_partial_meas (basis_vector (2^(a+b)) (kron_vec_combine ⟨j⟩ ⟨k⟩).val) (twoRegQFTMeasState …)
        = ∑ i : Fin (2^t),
            ‖∑ x<2^a, ∑ y<2^b with tgt x y = i,  c x y · IQFT_matrix a j x · IQFT_matrix b k y‖²

  i.e. the genuine circuit Born probability is the fibre-sum over the target register — the
  inverse-kernel form of `Basic.qft2MeasProb`.  The Ekerå–Håstad instantiation (in the audit) reindexes
  the `Fin (2^t)` target sum to the value set `E` and uses the real-input conjugation symmetry to reach
  the forward-kernel `qft2MeasProb = ehProb`, after which `ehCircuit_per_run_ge_eighth` lands as a
  `prob_partial_meas ≥ 1/8` statement in pipeline form.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.

  Layering: depends on `Circuit.lean` (→ `PhaseKickback` → `Shor.MainAlgorithm`); kept OUT of the
  Shor-agnostic `FormalRV.QFT` umbrella, imported from the audit where it is used.
-/
import FormalRV.QFT.TwoRegisterQFT.Circuit
import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement.PartialMeasurementOrthogonalSum
import FormalRV.Core.PadAction.PadActionGateEntry
import FormalRV.Verifier.ProofGate

namespace FormalRV.QFT.TwoRegisterQFT

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.Framework

/-! ## §1. The post-oracle state and the measured QFT output state -/

/-- The control-register basis state `|x⟩_A |y⟩_B` on the two control registers (`2^a · 2^b` dims). -/
noncomputable def controlBasis (a b x y : ℕ) : Matrix (Fin (2 ^ (a + b))) (Fin 1) ℂ :=
  kron_vec (FormalRV.Framework.basis_vector (2 ^ a) x) (FormalRV.Framework.basis_vector (2 ^ b) y)

/-- **The post-oracle 3-register state** `∑_{x,y} c x y · |x⟩_A|y⟩_B|tgt x y⟩_T`.  The oracle is
abstracted by the value `tgt x y : ℕ` it writes into the target register. -/
noncomputable def twoRegOracleState (a b t : ℕ) (c : ℕ → ℕ → ℂ) (tgt : ℕ → ℕ → ℕ) :
    Matrix (Fin (2 ^ ((a + b) + t))) (Fin 1) ℂ :=
  ∑ x ∈ Finset.range (2 ^ a), ∑ y ∈ Finset.range (2 ^ b),
    c x y • kron_vec (controlBasis a b x y) (FormalRV.Framework.basis_vector (2 ^ t) (tgt x y))

/-- The two-register QFT lifted over the target register (`QFT ⊗ I_target`). -/
noncomputable def liftedTwoRegQFT (a b t : ℕ) : FormalRV.Framework.BaseUCom ((a + b) + t) :=
  map_qubits (fun q => q) (twoRegQFT a b)

/-- **The measured output state** `(twoRegQFT ⊗ I_target) · (post-oracle state)`. -/
noncomputable def twoRegQFTMeasState (a b t : ℕ) (c : ℕ → ℕ → ℂ) (tgt : ℕ → ℕ → ℕ) :
    Matrix (Fin (2 ^ ((a + b) + t))) (Fin 1) ℂ :=
  FormalRV.Framework.uc_eval (liftedTwoRegQFT a b t) * twoRegOracleState a b t c tgt

/-- The post-QFT control amplitude factor `(IQFT_a |x⟩) ⊗ (IQFT_b |y⟩)` on the two control
registers. -/
noncomputable def qftCtrlAmp (a b x y : ℕ) : Matrix (Fin (2 ^ (a + b))) (Fin 1) ℂ :=
  kron_vec (IQFT_matrix a * FormalRV.Framework.basis_vector (2 ^ a) x)
           (IQFT_matrix b * FormalRV.Framework.basis_vector (2 ^ b) y)

/-! ## §2. The QFT ⊗ I action on the post-oracle state -/

/-- **★ QFT ⊗ I_target action. ★**  The measured output state is the post-oracle state with each
control basis pair `|x⟩|y⟩` replaced by its two-register inverse-QFT image `(IQFT_a|x⟩)⊗(IQFT_b|y⟩)`,
the target factor untouched.  Reuses `uc_eval_control_register_circuit_kron_vec` (circuit on the
control block, identity on the target) and `uc_eval_twoRegQFT_kron` (the QFT tensor law). -/
theorem twoRegQFTMeasState_action (a b t : ℕ) (ha : 0 < a) (hb : 0 < b)
    (c : ℕ → ℕ → ℂ) (tgt : ℕ → ℕ → ℕ) :
    twoRegQFTMeasState a b t c tgt
      = ∑ x ∈ Finset.range (2 ^ a), ∑ y ∈ Finset.range (2 ^ b),
          c x y • kron_vec (qftCtrlAmp a b x y) (FormalRV.Framework.basis_vector (2 ^ t) (tgt x y)) := by
  unfold twoRegQFTMeasState twoRegOracleState liftedTwoRegQFT
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Matrix.mul_smul]
  congr 1
  rw [uc_eval_control_register_circuit_kron_vec (twoRegQFT a b) (twoRegQFT_wellTyped a b ha hb)
        (controlBasis a b x y) (FormalRV.Framework.basis_vector (2 ^ t) (tgt x y))]
  unfold controlBasis qftCtrlAmp
  rw [uc_eval_twoRegQFT_kron a b ha hb (FormalRV.Framework.basis_vector (2 ^ a) x)
        (FormalRV.Framework.basis_vector (2 ^ b) y)]

/-! ## §3. Regroup by target value, then measure -/

/-- The control-register amplitude on the target fibre `tgt x y = i`: the part of the post-QFT state
that lands on target basis state `|i⟩`. -/
noncomputable def fiberCtrl (a b t : ℕ) (c : ℕ → ℕ → ℂ) (tgt : ℕ → ℕ → ℕ) (i : Fin (2 ^ t)) :
    Matrix (Fin (2 ^ (a + b))) (Fin 1) ℂ :=
  ∑ x ∈ Finset.range (2 ^ a), ∑ y ∈ (Finset.range (2 ^ b)).filter (fun y => tgt x y = i.val),
    c x y • qftCtrlAmp a b x y

/-- **Regroup the measured output state by target value.**  The state is `∑_{i:Fin 2^t}` of the
fibre-`i` control amplitude tensored with the (distinct, hence orthonormal) target basis state `|i⟩`.
Proven by extensionality — the target basis collapse selects, per composite index, exactly the
matching fibre. -/
theorem twoRegQFTMeasState_regroup (a b t : ℕ) (ha : 0 < a) (hb : 0 < b)
    (c : ℕ → ℕ → ℂ) (tgt : ℕ → ℕ → ℕ) :
    twoRegQFTMeasState a b t c tgt
      = ∑ i : Fin (2 ^ t),
          kron_vec (fiberCtrl a b t c tgt i) (FormalRV.Framework.basis_vector (2 ^ t) i.val) := by
  rw [twoRegQFTMeasState_action a b t ha hb c tgt]
  ext I z
  have hz : z = (0 : Fin 1) := Subsingleton.elim _ _
  subst hz
  -- push the RHS target sum to the entry level, then collapse to i = kron_vec_low I
  conv_rhs => rw [Matrix.sum_apply]
  rw [Finset.sum_eq_single (FormalRV.Framework.kron_vec_low I)]
  · -- main term: i = kron_vec_low I
    rw [FormalRV.Framework.kron_vec_apply, FormalRV.Framework.basis_vector_apply, if_pos rfl, mul_one]
    unfold fiberCtrl
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, FormalRV.Framework.kron_vec_apply]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [FormalRV.Framework.basis_vector_apply]
    by_cases hh : (FormalRV.Framework.kron_vec_low I).val = tgt x y
    · rw [if_pos hh, if_pos hh.symm, mul_one]
    · rw [if_neg hh, if_neg (fun h => hh h.symm), mul_zero, mul_zero]
  · -- off term: i ≠ kron_vec_low I gives a zero target-basis factor
    intro i _ hne
    rw [FormalRV.Framework.kron_vec_apply, FormalRV.Framework.basis_vector_apply,
        if_neg (fun h => hne (Fin.ext h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Distinct target basis vectors are orthonormal — the hypothesis the orthogonal-sum measurement
lemma needs. -/
theorem target_basis_orthonormal (t : ℕ) :
    ∀ i i' : Fin (2 ^ t),
      (∑ y : Fin (2 ^ t),
        starRingEnd ℂ (FormalRV.Framework.basis_vector (2 ^ t) i'.val y 0)
          * FormalRV.Framework.basis_vector (2 ^ t) i.val y 0)
        = if i = i' then (1 : ℂ) else 0 := by
  intro i i'
  simp only [FormalRV.Framework.basis_vector_apply, apply_ite (starRingEnd ℂ), map_one, map_zero]
  by_cases h : i = i'
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single i]
    · rw [if_pos rfl, mul_one]
    · intro b _ hb
      rw [if_neg (fun hbi => hb (Fin.ext hbi)), mul_zero]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hyi : y.val = i.val
    · rw [if_pos hyi, if_neg (fun hyi' => h (Fin.ext (hyi.symm.trans hyi'))), zero_mul]
    · rw [if_neg hyi, mul_zero]

/-! ## §4. Headline: the circuit Born probability is the target-fibre sum -/

/-- **★ The genuine circuit Born probability of control outcome `(j,k)`. ★**  Measuring the two
control registers of `twoRegQFTMeasState` (the verified `twoRegQFT ⊗ I_target` applied to the
post-oracle state) at `(j,k)` gives the sum, over target values `i`, of the squared norm of the
fibre-`i` control amplitude — the gate-level realization of `Basic.qft2MeasProb` (inverse kernel). -/
theorem prob_partial_meas_twoRegQFTMeasState (a b t : ℕ) (ha : 0 < a) (hb : 0 < b)
    (c : ℕ → ℕ → ℂ) (tgt : ℕ → ℕ → ℕ) (j k : ℕ) (hj : j < 2 ^ a) (hk : k < 2 ^ b) :
    prob_partial_meas
        (FormalRV.SQIRPort.basis_vector (2 ^ (a + b))
          (FormalRV.Framework.kron_vec_combine (⟨j, hj⟩ : Fin (2 ^ a)) (⟨k, hk⟩ : Fin (2 ^ b))).val)
        (twoRegQFTMeasState a b t c tgt)
      = ∑ i : Fin (2 ^ t),
          Complex.normSq
            (fiberCtrl a b t c tgt i
              (FormalRV.Framework.kron_vec_combine (⟨j, hj⟩ : Fin (2 ^ a)) (⟨k, hk⟩ : Fin (2 ^ b))) 0) := by
  rw [twoRegQFTMeasState_regroup a b t ha hb c tgt]
  rw [prob_partial_meas_basis_sum_kron_orth
        (FormalRV.Framework.kron_vec_combine (⟨j, hj⟩ : Fin (2 ^ a)) (⟨k, hk⟩ : Fin (2 ^ b))).val
        (FormalRV.Framework.kron_vec_combine (⟨j, hj⟩ : Fin (2 ^ a)) (⟨k, hk⟩ : Fin (2 ^ b))).isLt
        (fiberCtrl a b t c tgt)
        (fun i => FormalRV.Framework.basis_vector (2 ^ t) i.val)
        (target_basis_orthonormal t)]

/-- **Explicit fibre control amplitude.**  The fibre-`i` control amplitude evaluated at control
outcome `(j,k)` is the inverse-QFT fibre sum `∑_{x} ∑_{y: tgt x y = i} c x y · IQFT_matrix a j x ·
IQFT_matrix b k y` — the inverse-kernel counterpart of `Basic.qft2FiberAmp`. -/
theorem fiberCtrl_apply_combine (a b t : ℕ) (c : ℕ → ℕ → ℂ) (tgt : ℕ → ℕ → ℕ)
    (i : Fin (2 ^ t)) (j k : ℕ) (hj : j < 2 ^ a) (hk : k < 2 ^ b) :
    fiberCtrl a b t c tgt i
        (FormalRV.Framework.kron_vec_combine (⟨j, hj⟩ : Fin (2 ^ a)) (⟨k, hk⟩ : Fin (2 ^ b))) 0
      = ∑ x ∈ Finset.range (2 ^ a),
          ∑ y ∈ (Finset.range (2 ^ b)).filter (fun y => tgt x y = i.val),
            c x y * (IQFT_matrix a * FormalRV.Framework.basis_vector (2 ^ a) x)
                      (⟨j, hj⟩ : Fin (2 ^ a)) 0
                  * (IQFT_matrix b * FormalRV.Framework.basis_vector (2 ^ b) y)
                      (⟨k, hk⟩ : Fin (2 ^ b)) 0 := by
  unfold fiberCtrl qftCtrlAmp
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Matrix.smul_apply, smul_eq_mul, FormalRV.Framework.kron_vec_apply_combine, mul_assoc]

end FormalRV.QFT.TwoRegisterQFT

/-! ## §5. Verifier gates -/
#verify_clean FormalRV.QFT.TwoRegisterQFT.twoRegQFTMeasState_action
#verify_clean FormalRV.QFT.TwoRegisterQFT.twoRegQFTMeasState_regroup
#verify_clean FormalRV.QFT.TwoRegisterQFT.target_basis_orthonormal
#verify_clean FormalRV.QFT.TwoRegisterQFT.prob_partial_meas_twoRegQFTMeasState
#verify_clean FormalRV.QFT.TwoRegisterQFT.fiberCtrl_apply_combine
