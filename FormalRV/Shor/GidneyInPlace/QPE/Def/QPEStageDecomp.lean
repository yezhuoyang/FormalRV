/-
  FormalRV.Shor.GidneyInPlace.QPEStageDecomp — QPE STAGE-DECOMPOSITION (oracle abstract).

  Convention #1 (the FIXED interface): numIter = m + 1.
    * the column of Hadamards `npar_H m` is folded into the INITIAL state
      (`qpeInit`);
    * stages `k = 0 .. m-1` are the controlled-oracle stages
      `control k (map_qubits (·+m) (f (revIndex m k)))`;
    * the LAST stage `k = m` is the inverse QFT `QFTinv m`.

  Purely syntactic stage folding: `f : Nat → BaseUCom (n+anc)` is ABSTRACT,
  no eigenstate / spectrum analysis, no concrete multiplier.
-/
import FormalRV.Shor.GidneyInPlace.Primitives.Def.OrbitState
import FormalRV.Shor.MainAlgorithm.QuantumAndContinuedFractions.ShorStatesAndHeadlineStatements
import FormalRV.Shor.MainAlgorithm.SuccessProbability.QPEEigenstateAndDimCast
import FormalRV.QPE.QPE

namespace FormalRV.Shor.GidneyInPlace.QPEStageDecomp

open FormalRV.SQIRPort
open FormalRV.Shor.GidneyInPlace.OrbitState (orbitState)

/-- The k-th controlled oracle `c k` of `QPE_var_lsb` (the lifted family). -/
noncomputable def qpeOracle (m n anc : Nat) (f : Nat → BaseUCom (n + anc)) (k : Nat) :
    BaseUCom (m + (n + anc)) :=
  FormalRV.SQIRPort.map_qubits (fun q => m + q) (f (revIndex m k))

/-- The k-th QPE stage circuit: oracle stages for `k < m`, the inverse QFT last. -/
noncomputable def qpeStageUCom (m n anc : Nat) (f : Nat → BaseUCom (n + anc)) (k : Nat) :
    BaseUCom (m + (n + anc)) :=
  if k < m then
    FormalRV.Framework.BaseUCom.control k (qpeOracle m n anc f k)
  else
    FormalRV.Framework.BaseUCom.QFTinv m

/-- The H-prepared, cast-d initial state. -/
noncomputable def qpeInit (m n anc : Nat) : QState (2^m * 2^n * 2^anc) :=
  QState.cast (dim_assoc_eq m n anc)
    (uc_eval (FormalRV.Framework.BaseUCom.npar_H m) (Shor_initial_state m n anc))

/-- The cast-CONJUGATED stage map. -/
noncomputable def qpeStageMap (m n anc : Nat) (f : Nat → BaseUCom (n + anc)) (k : Nat) :
    QState (2^m * 2^n * 2^anc) → QState (2^m * 2^n * 2^anc) :=
  fun psi =>
    QState.cast (dim_assoc_eq m n anc)
      (uc_eval (qpeStageUCom m n anc f k)
        (QState.cast (dim_assoc_eq m n anc).symm psi))

/-! ### Cast round-trip and the cast-conjugation helper. -/

/-- `QState.cast` round-trip: cast then cast-back is the identity. -/
theorem qstate_cast_cast {a b : Nat} (h : a = b) (s : QState a) :
    QState.cast h.symm (QState.cast h s) = s := by
  funext i col
  show s (Fin.cast h.symm (Fin.cast h.symm.symm i)) 0 = s i col
  have hi : (Fin.cast h.symm (Fin.cast h.symm.symm i)) = i := by
    apply Fin.ext; rfl
  rw [hi]
  congr 1
  exact Subsingleton.elim 0 col

/-- The KEY helper: the inner `cast.symm` cancels an outer `cast`, exposing the
    Framework matrix-vector product under a SINGLE outer cast. -/
theorem qpeStageMap_cast (m n anc : Nat) (f : Nat → BaseUCom (n + anc)) (k : Nat)
    (s : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ) :
    qpeStageMap m n anc f k (QState.cast (dim_assoc_eq m n anc) s)
      = QState.cast (dim_assoc_eq m n anc)
          (FormalRV.Framework.uc_eval (qpeStageUCom m n anc f k) * s) := by
  unfold qpeStageMap
  rw [qstate_cast_cast (dim_assoc_eq m n anc) s]
  rfl

/-! ### The telescoping stage-product matrix `stageProd`. -/

/-- Product of the first `j` Framework stage matrices (newest on the LEFT). -/
noncomputable def stageProd (m n anc : Nat) (f : Nat → BaseUCom (n + anc)) :
    Nat → FormalRV.Framework.Square (m + (n + anc))
  | 0 => 1
  | j + 1 =>
      FormalRV.Framework.uc_eval (qpeStageUCom m n anc f j) * stageProd m n anc f j

/-- `Shor_initial_state` re-typed as a bare column matrix (defeq), so matrix
    products against it resolve the `Matrix` HMul instance directly. -/
noncomputable def shorInitM (m n anc : Nat) :
    Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ :=
  Shor_initial_state m n anc

/-- `Q := uc_eval(npar_H m) * Shor_initial` — the H-prepared raw vector. -/
noncomputable def qpeRaw (m n anc : Nat) : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ :=
  FormalRV.Framework.uc_eval (FormalRV.Framework.BaseUCom.npar_H m) * shorInitM m n anc

theorem qpeInit_eq (m n anc : Nat) :
    qpeInit m n anc = QState.cast (dim_assoc_eq m n anc) (qpeRaw m n anc) := by
  rfl

/-- **TELESCOPING.** Folding `j` stages = a single outer cast of `stageProd j * qpeRaw`. -/
theorem orbitState_eq_stageProd (m n anc : Nat) (f : Nat → BaseUCom (n + anc)) :
    ∀ j, orbitState (qpeStageMap m n anc f) (qpeInit m n anc) j
        = QState.cast (dim_assoc_eq m n anc)
            ((stageProd m n anc f j * qpeRaw m n anc
              : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ)) := by
  intro j
  induction j with
  | zero =>
      show qpeInit m n anc = _
      rw [qpeInit_eq]
      congr 1
      show qpeRaw m n anc
          = ((1 : FormalRV.Framework.Square (m + (n + anc))) * qpeRaw m n anc
              : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ)
      rw [Matrix.one_mul]
  | succ j ih =>
      show qpeStageMap m n anc f j (orbitState (qpeStageMap m n anc f) (qpeInit m n anc) j) = _
      rw [ih, qpeStageMap_cast m n anc f j]
      congr 1
      show (FormalRV.Framework.uc_eval (qpeStageUCom m n anc f j)
            * (stageProd m n anc f j * qpeRaw m n anc)
              : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ)
          = ((FormalRV.Framework.uc_eval (qpeStageUCom m n anc f j) * stageProd m n anc f j)
              * qpeRaw m n anc
              : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ)
      rw [Matrix.mul_assoc]

/-! ### Matching the first `m` oracle stages to `controlled_powers`. -/

/-- For `j ≤ m`, all the first `j` stages are oracle stages, so `stageProd j`
    equals `uc_eval (controlled_powers (qpeOracle …) j)`. -/
theorem stageProd_eq_controlled_powers (m n anc : Nat) (f : Nat → BaseUCom (n + anc))
    (hdim_pos : 0 < m + (n + anc)) :
    ∀ j, j ≤ m →
      stageProd m n anc f j
        = FormalRV.Framework.uc_eval
            (FormalRV.Framework.BaseUCom.controlled_powers (qpeOracle m n anc f) j) := by
  intro j
  induction j with
  | zero =>
      intro _
      show (1 : FormalRV.Framework.Square (m + (n + anc))) = _
      rw [FormalRV.Framework.BaseUCom.uc_eval_controlled_powers_zero_eq_one
            (qpeOracle m n anc f) hdim_pos]
  | succ j ih =>
      intro hj
      have hjm : j < m := hj
      show FormalRV.Framework.uc_eval (qpeStageUCom m n anc f j) * stageProd m n anc f j = _
      rw [ih (Nat.le_of_lt hjm)]
      rw [FormalRV.Framework.BaseUCom.uc_eval_controlled_powers_succ]
      congr 1
      show FormalRV.Framework.uc_eval (qpeStageUCom m n anc f j)
          = FormalRV.Framework.uc_eval
              (FormalRV.Framework.BaseUCom.control j (qpeOracle m n anc f j))
      unfold qpeStageUCom
      rw [if_pos hjm]

/-! ### The headline stage-decomposition theorem. -/

/-- **`Shor_final_state` = the QPE orbit state after `m+1` stages.**
    Convention #1: H folded into `qpeInit`, `m` controlled-oracle stages,
    `QFTinv m` as the last stage. -/
theorem shor_final_eq_orbitState (m n anc : Nat) (f : Nat → BaseUCom (n + anc))
    (hdim_pos : 0 < m + (n + anc)) :
    Shor_final_state m n anc f
      = orbitState (qpeStageMap m n anc f) (qpeInit m n anc) (m + 1) := by
  rw [orbitState_eq_stageProd m n anc f (m + 1)]
  -- Unfold Shor_final_state and SQIRPort uc_eval to a single cast of a Framework product.
  unfold Shor_final_state FormalRV.SQIRPort.uc_eval
  -- the two cast proofs are the same Nat fact; reduce to the matrix equality.
  congr 1
  -- Peel the last (QFTinv) stage of `stageProd (m+1)` and match the first `m`.
  have hstage_last : qpeStageUCom m n anc f m = FormalRV.Framework.BaseUCom.QFTinv m := by
    unfold qpeStageUCom; rw [if_neg (Nat.lt_irrefl m)]
  have hstageProd : stageProd m n anc f (m + 1)
      = FormalRV.Framework.uc_eval (FormalRV.Framework.BaseUCom.QFTinv m)
          * FormalRV.Framework.uc_eval
              (FormalRV.Framework.BaseUCom.controlled_powers (qpeOracle m n anc f) m) := by
    show FormalRV.Framework.uc_eval (qpeStageUCom m n anc f m) * stageProd m n anc f m = _
    rw [hstage_last, stageProd_eq_controlled_powers m n anc f hdim_pos m (Nat.le_refl m)]
  -- The QPE 3-piece factorization of `QPE_var_lsb`.
  have hQPE : FormalRV.Framework.uc_eval (QPE_var_lsb m (n + anc) f)
      = FormalRV.Framework.uc_eval (FormalRV.Framework.BaseUCom.QFTinv m)
          * FormalRV.Framework.uc_eval
              (FormalRV.Framework.BaseUCom.controlled_powers (qpeOracle m n anc f) m)
          * FormalRV.Framework.uc_eval (FormalRV.Framework.BaseUCom.npar_H m) := by
    show FormalRV.Framework.uc_eval
          (FormalRV.Framework.BaseUCom.QPE m (n + anc) (qpeOracle m n anc f)) = _
    rw [FormalRV.Framework.BaseUCom.uc_eval_QPE]
  rw [hstageProd, hQPE]
  unfold qpeRaw shorInitM
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rfl

end FormalRV.Shor.GidneyInPlace.QPEStageDecomp
