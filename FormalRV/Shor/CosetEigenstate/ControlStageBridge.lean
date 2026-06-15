/-
  SCRATCH (attempt #3): the CONTROLLED SHIFTED-ORACLE jointIdx LAYOUT BRIDGE.
  Keep g/f abstract.  Translate uc_eval(control k (map_qubits(.+m) g)) into the
  jointIdx (phase x work) factorization the EmbedAgreeOff engine uses.
-/
import FormalRV.Shor.CosetEigenstate.QPEStageDecomp
import FormalRV.QPE.ControlledGates
import FormalRV.QPE.PhaseKickback
import FormalRV.Shor.CosetMarginalShorBound
import FormalRV.Shor.ApproxTransfer

namespace FormalRV.Shor.CosetEigenstate.ControlStageBridge

open FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom
open FormalRV.SQIRPort.ApproxTransfer (jointIdx jointIdx_eq_finProdFinEquiv)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.CosetEigenstate.QPEStageDecomp

/-! ## §0. The control matrix on a basis-control kron — the data-factor action.
(Re-proven from `uc_eval_control_eq_proj_decomp` + the shifted-lift locality
lemma + the control-side `pad_u`/`kron` factorization; this is the prior
attempt-#2 result, inlined here so the file is self-contained.) -/

theorem control_shift_on_kron_basis {m anc k : Nat} (hk : k < m)
    (g : FormalRV.Framework.BaseUCom anc) (h_wt : UCom.WellTyped anc g)
    (x : Fin (2 ^ m)) (ψ : Matrix (Fin (2 ^ anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (control k (map_qubits (fun q => m + q) g) : FormalRV.Framework.BaseUCom (m + anc))
      * kron_vec (FormalRV.Framework.basis_vector (2 ^ m) x.val) ψ
      = kron_vec (FormalRV.Framework.basis_vector (2 ^ m) x.val)
          (if controlBit m k hk x then FormalRV.Framework.uc_eval g * ψ else ψ) := by
  have hdim : k < m + anc := by omega
  have hfresh : is_fresh k
      (map_qubits (fun q => m + q) g : FormalRV.Framework.BaseUCom (m + anc)) :=
    is_fresh_map_qubits_shift g hk
  have hwt_shift : UCom.WellTyped (m + anc)
      (map_qubits (fun q => m + q) g : FormalRV.Framework.BaseUCom (m + anc)) :=
    wellTyped_map_qubits_shift g h_wt
  rw [uc_eval_control_eq_proj_decomp k
        (map_qubits (fun q => m + q) g : FormalRV.Framework.BaseUCom (m + anc))
        hdim hfresh hwt_shift]
  rw [Matrix.add_mul]
  rw [pad_u_control_kron_vec_factors hk proj0
        (FormalRV.Framework.basis_vector (2 ^ m) x.val) ψ]
  rw [Matrix.mul_assoc]
  rw [uc_eval_map_qubits_shift_kron_basis_control_vec g h_wt x ψ]
  rw [pad_u_control_kron_vec_factors hk proj1
        (FormalRV.Framework.basis_vector (2 ^ m) x.val)
        (FormalRV.Framework.uc_eval g * ψ)]
  obtain ⟨⟨⟨xH, xM⟩, xL⟩, hx⟩ : ∃ p, padEquiv m k hk p = x :=
    ⟨(padEquiv m k hk).symm x, (padEquiv m k hk).apply_symm_apply x⟩
  subst hx
  rcases Fin.exists_fin_two.mp ⟨xM, rfl⟩ with rfl | rfl
  · rw [pad_u_proj0_on_basis_vector_zero hk xH xL]
    rw [pad_u_proj1_on_basis_vector_zero hk xH xL]
    have h_ctrl : controlBit m k hk (padEquiv m k hk ((xH, 0), xL)) = false := by
      unfold controlBit; rw [Equiv.symm_apply_apply]; simp
    rw [h_ctrl]
    rw [show kron_vec (0 : Matrix (Fin (2 ^ m)) (Fin 1) ℂ)
          (FormalRV.Framework.uc_eval g * ψ) = 0 from kron_vec_zero_left _]
    rw [add_zero]
    simp
  · rw [pad_u_proj0_on_basis_vector_one hk xH xL]
    rw [pad_u_proj1_on_basis_vector_one hk xH xL]
    have h_ctrl : controlBit m k hk (padEquiv m k hk ((xH, 1), xL)) = true := by
      unfold controlBit; rw [Equiv.symm_apply_apply]; simp
    rw [h_ctrl]
    rw [show kron_vec (0 : Matrix (Fin (2 ^ m)) (Fin 1) ℂ) ψ = 0 from kron_vec_zero_left _]
    rw [zero_add]
    simp

/-! ## §1. Dimension bookkeeping for the work (data) factor.

The "data factor" dimension that `jointIdx` ranges its second index over is
`(2^m*2^n*2^anc)/2^m`, which equals `2^n*2^anc = 2^(n+anc)` — the work register
that `Framework.uc_eval g` (`g : BaseUCom (n+anc)`) acts on. -/

/-- The work-register dim equality:  `(2^m*2^n*2^anc)/2^m = 2^(n+anc)`. -/
theorem workDim_eq (m n anc : Nat) :
    (2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m = 2 ^ (n + anc) := by
  rw [mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos m), pow_add]

/-! ## §2. Phase-register decomposition of an arbitrary native vector.

Any `s : Fin (2^(m+d))` column equals the sum, over phase values `xp`, of the
basis-control kron of `|xp⟩` with the "work block" `workBlock s xp` = the slice
`yi ↦ s (xp · 2^d + yi)`.  This is the linearity hook that lets the per-block
`control_shift_on_kron_basis` lemma act on an arbitrary cast-in vector. -/

/-- The work-register slice of `s` at a fixed phase value `xp`. -/
noncomputable def workBlock {m d : Nat}
    (s : Matrix (Fin (2 ^ (m + d))) (Fin 1) ℂ) (xp : Fin (2 ^ m)) :
    Matrix (Fin (2 ^ d)) (Fin 1) ℂ :=
  fun yi _ => s (kron_vec_combine xp yi) 0

/-- Phase-register decomposition: `s = ∑_{xp} |xp⟩ ⊗ workBlock s xp`. -/
theorem vec_eq_sum_phase_kron {m d : Nat}
    (s : Matrix (Fin (2 ^ (m + d))) (Fin 1) ℂ) :
    s = ∑ xp : Fin (2 ^ m),
          kron_vec (FormalRV.Framework.basis_vector (2 ^ m) xp.val) (workBlock s xp) := by
  ext i col
  have hcol : col = (0 : Fin 1) := Subsingleton.elim _ _
  subst hcol
  rw [Matrix.sum_apply]
  rw [Finset.sum_eq_single (kron_vec_high i)]
  · rw [kron_vec_apply]
    rw [FormalRV.Framework.basis_vector_apply_eq _ _ _ _ rfl]
    rw [one_mul]
    show s i 0 = workBlock s (kron_vec_high i) (kron_vec_low i) 0
    unfold workBlock
    rw [kron_vec_combine_high_low]
  · intro xp _ hxp
    rw [kron_vec_apply]
    rw [FormalRV.Framework.basis_vector_apply_ne _ _ _ _ (by
      intro h; exact hxp (Fin.ext h.symm))]
    rw [zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h


/-! ## §3. The jointIdx ↔ kron_vec_combine index bridge.

`jointIdx (shorDvd m n anc) x y` (an index of `Fin (2^m*2^n*2^anc)`) is, after the
`dim_assoc_eq`-cast back to the native `Fin (2^(m+(n+anc)))`, exactly the composite
`kron_vec_combine x (Fin.cast workDim_eq y)`.  Both have val `x·2^(n+anc) + y`. -/
theorem cast_jointIdx_eq_combine (m n anc : Nat)
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)) :
    (Fin.cast (dim_assoc_eq m n anc).symm (jointIdx (shorDvd m n anc) x y)
      : Fin (2 ^ (m + (n + anc))))
      = kron_vec_combine x (Fin.cast (workDim_eq m n anc) y) := by
  apply Fin.ext
  show (jointIdx (shorDvd m n anc) x y).val
      = x.val * 2 ^ (n + anc) + (Fin.cast (workDim_eq m n anc) y).val
  show x.val * ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) + y.val
      = x.val * 2 ^ (n + anc) + y.val
  rw [show x.val * ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)
        = x.val * 2 ^ (n + anc) from by rw [workDim_eq]]

/-! ## §4. The headline jointIdx oracle-stage bridge. -/

theorem qpeStage_oracle_jointIdx (m n anc k : Nat) (hk : k < m)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (hwt : ∀ j, UCom.WellTyped (n + anc) (f j))
    (phi : QState (2 ^ m * 2 ^ n * 2 ^ anc))
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)) :
    qpeStageMap m n anc f k phi (jointIdx (shorDvd m n anc) x y) 0
      = if controlBit m k hk x then
          (∑ yp : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m),
             FormalRV.Framework.uc_eval (f (revIndex m k))
               (Fin.cast (workDim_eq m n anc) y) (Fin.cast (workDim_eq m n anc) yp)
               * phi (jointIdx (shorDvd m n anc) x yp) 0)
        else phi (jointIdx (shorDvd m n anc) x y) 0 := by
  -- Expose the native Framework product under a single outer cast.
  set s : Matrix (Fin (2 ^ (m + (n + anc)))) (Fin 1) ℂ :=
    QState.cast (dim_assoc_eq m n anc).symm phi with hs
  have hphi : phi = QState.cast (dim_assoc_eq m n anc) s := by
    rw [hs]; exact (qstate_cast_cast (dim_assoc_eq m n anc).symm phi).symm
  rw [hphi]
  rw [qpeStageMap_cast m n anc f k s]
  -- The oracle stage circuit (k < m).
  have hstage : qpeStageUCom m n anc f k
      = control k (qpeOracle m n anc f k) := by
    unfold qpeStageUCom; rw [if_pos hk]
  rw [hstage]
  unfold qpeOracle
  -- Abbreviate the abstract work oracle and the matrix product.
  set g : FormalRV.Framework.BaseUCom (n + anc) := f (revIndex m k) with hg
  have hwtg : UCom.WellTyped (n + anc) g := hwt (revIndex m k)
  -- Read the outer cast at jointIdx as a native read at kron_vec_combine.
  have hread : ∀ (v : Matrix (Fin (2 ^ (m + (n + anc)))) (Fin 1) ℂ)
      (z : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)),
      (QState.cast (dim_assoc_eq m n anc) v) (jointIdx (shorDvd m n anc) x z) 0
        = v (kron_vec_combine x (Fin.cast (workDim_eq m n anc) z)) 0 := by
    intro v z
    show v (Fin.cast (dim_assoc_eq m n anc).symm (jointIdx (shorDvd m n anc) x z)) 0
        = v (kron_vec_combine x (Fin.cast (workDim_eq m n anc) z)) 0
    rw [cast_jointIdx_eq_combine]
  simp only [hread]
  -- Decompose s over the phase register inside the LHS product only.
  -- Each block factorizes through control_shift_on_kron_basis.
  have hblock : ∀ xp : Fin (2 ^ m),
      (FormalRV.Framework.uc_eval (control k (map_qubits (fun q => m + q) g))
          * kron_vec (FormalRV.Framework.basis_vector (2 ^ m) xp.val) (workBlock s xp))
        = kron_vec (FormalRV.Framework.basis_vector (2 ^ m) xp.val)
            (if controlBit m k hk xp then FormalRV.Framework.uc_eval g * workBlock s xp
             else workBlock s xp) := by
    intro xp
    exact control_shift_on_kron_basis hk g hwtg xp (workBlock s xp)
  -- Matrix-level identity for the whole product.
  have hM : FormalRV.Framework.uc_eval (control k (map_qubits (fun q => m + q) g)) * s
      = ∑ xp : Fin (2 ^ m),
          kron_vec (FormalRV.Framework.basis_vector (2 ^ m) xp.val)
            (if controlBit m k hk xp then FormalRV.Framework.uc_eval g * workBlock s xp
             else workBlock s xp) := by
    conv_lhs => rw [vec_eq_sum_phase_kron s]
    refine Eq.trans (Matrix.mul_sum _ _ _) ?_
    exact Finset.sum_congr rfl (fun xp _ => hblock xp)
  refine Eq.trans
    (congrFun (congrFun hM (kron_vec_combine x (Fin.cast (workDim_eq m n anc) y))) 0) ?_
  rw [Matrix.sum_apply]
  -- Only the c = x phase block survives (the basis_vector factor).
  rw [Finset.sum_eq_single x]
  · -- the surviving block, read at the combined index
    rw [kron_vec_apply, kron_vec_high_combine, kron_vec_low_combine]
    rw [FormalRV.Framework.basis_vector_apply_eq _ _ _ _ rfl, one_mul]
    -- Split on the control bit; both sides share the same condition.
    by_cases hcb : controlBit m k hk x
    · rw [if_pos hcb, if_pos hcb]
      -- bit = 1 : the data-factor action is the matrix-entry sum
      rw [Matrix.mul_apply]
      -- reindex Fin (2^(n+anc)) ← Fin (full/2^m)
      rw [← Fintype.sum_equiv (finCongr (workDim_eq m n anc))
            (fun yp : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) =>
              FormalRV.Framework.uc_eval g (Fin.cast (workDim_eq m n anc) y)
                (Fin.cast (workDim_eq m n anc) yp)
                * s (kron_vec_combine x (Fin.cast (workDim_eq m n anc) yp)) 0)
            (fun j : Fin (2 ^ (n + anc)) =>
              FormalRV.Framework.uc_eval g (Fin.cast (workDim_eq m n anc) y) j
                * workBlock s x j 0)]
      intro yp
      show FormalRV.Framework.uc_eval g (Fin.cast (workDim_eq m n anc) y)
              (Fin.cast (workDim_eq m n anc) yp)
            * s (kron_vec_combine x (Fin.cast (workDim_eq m n anc) yp)) 0
          = FormalRV.Framework.uc_eval g (Fin.cast (workDim_eq m n anc) y)
              (finCongr (workDim_eq m n anc) yp)
            * workBlock s x (finCongr (workDim_eq m n anc) yp) 0
      rfl
    · rw [if_neg hcb, if_neg hcb]
      -- bit = 0 : identity branch
      show workBlock s x (Fin.cast (workDim_eq m n anc) y) 0
          = s (kron_vec_combine x (Fin.cast (workDim_eq m n anc) y)) 0
      rfl
  · intro c _ hcx
    rw [kron_vec_apply, kron_vec_high_combine]
    rw [FormalRV.Framework.basis_vector_apply_ne _ _ _ _ (by
      intro h; exact hcx (Fin.ext h.symm))]
    rw [zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h


end FormalRV.Shor.CosetEigenstate.ControlStageBridge