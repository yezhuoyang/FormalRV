/-
  FormalRV.Shor.CosetEigenstate.UCEvalBridge — the abstract basis permutation
  `gateToPerm g` IS the literal SQIR semantics `uc_eval (toUCom g)`.
  ════════════════════════════════════════════════════════════════════════════

  `GatePerm.gateToPerm g` is a permutation of `Fin (2^dim)` built (in the funbool
  coordinatization) from `applyNat g`.  This file proves it agrees EXTENSIONALLY
  with the genuine SQIR unitary `uc_eval (Gate.toUCom dim g)`:

    * `uc_eval_basis_agree` — on basis states: `uc_eval (toUCom g) |i⟩ = |gateToPerm g i⟩`
      (i.e. `uc_eval · basis_vector i = basis_vector (gateToPerm g i)`), straight from
      `uc_eval_toUCom_acts_on_basis` + the funbool encoding.
    * `uc_eval_eq_permState` — lifted to ALL states by linearity (matrix–vector):
      `uc_eval (toUCom g) · s = permState (gateToPerm g).symm s`.  (The `.symm` is the
      pull-back convention of `permState s i = s (σ i)`: `|i⟩ ↦ |σ i⟩` on basis states
      means `(U s)_i = s_{σ⁻¹ i}`.)
    * `gate_uc_eval_normSqDist_perm` — hence the LITERAL gate action is a `normSqDist`
      isometry, discharging the `U_rev`/swap hypotheses for the SQIR semantics.

  ENDIAN / ENCODING AUDIT.  Every basis index here is the Nat VALUE: `basis_vector n k`
  is `1` at index `i.val = k`; `f_to_vec dim f = basis_vector (2^dim) (funbool_to_nat
  dim f)`; `cosetState` support is `i.val = k + j·N` — all Nat values.  `funbool_to_nat`
  is big-endian (index 0 = MSB), but that convention is INTERNAL to the bijection; the
  value-based indexing it produces is shared by `applyNat`/`toUCom`/`uc_eval` (matrix
  forms live in `FormalRV.Framework`) and by the `cosetState` indices, so they are
  mutually consistent.

  SCOPE: classical reversible fragment only (`I/X/CX/CCX/seq`) — see `GatePerm`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.GatePerm
import FormalRV.Arithmetic.Correctness

namespace FormalRV.Shor.CosetEigenstate.UCEvalBridge

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.CosetEigenstate.ApproxOp (permState normSqDist_perm_invariant)
open FormalRV.Shor.CosetEigenstate.GatePerm

/-- `funbool_to_nat dim` depends only on the values on `[0,dim)`. -/
theorem funbool_to_nat_congr : ∀ (dim : Nat) (f g : Nat → Bool),
    (∀ k, k < dim → f k = g k) → funbool_to_nat dim f = funbool_to_nat dim g := by
  intro dim
  induction dim with
  | zero => intro f g _; rfl
  | succ n ih =>
      intro f g h
      rw [funbool_to_nat_succ, funbool_to_nat_succ,
          ih f g (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]

/-- **BASIS-STATE AGREEMENT.**  `uc_eval (toUCom g) |i⟩ = |gateToPerm g i⟩`. -/
theorem uc_eval_basis_agree (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (i : Fin (2 ^ dim)) :
    Framework.uc_eval (Gate.toUCom dim g) * Framework.basis_vector (2 ^ dim) i.val
      = Framework.basis_vector (2 ^ dim) (gateToPerm g dim hwt i).val := by
  set φ := (funboolEquiv dim).symm i with hφ
  have hival : i.val = funbool_to_nat dim (extendBool dim φ) := by
    conv_lhs => rw [← Equiv.apply_symm_apply (funboolEquiv dim) i]
    rw [← hφ, funboolEquiv_val]
  rw [show Framework.basis_vector (2 ^ dim) i.val = f_to_vec dim (extendBool dim φ) by
        rw [f_to_vec, hival]]
  rw [uc_eval_toUCom_acts_on_basis dim g hwt (extendBool dim φ), f_to_vec]
  congr 1
  have hgp : (gateToPerm g dim hwt i).val
      = funbool_to_nat dim (extendBool dim (applyFin g dim φ)) := by
    rw [gateToPerm, Equiv.permCongr_apply, ← hφ, gateClassicalPerm_apply, funboolEquiv_val]
  rw [hgp]
  exact funbool_to_nat_congr dim _ _ (fun k hk => by
    simp only [extendBool, applyFin, dif_pos hk])

/-- **Matrix entry of the SQIR unitary**: `1` at `(i, k)` iff `i = gateToPerm g k`. -/
theorem uc_eval_entry (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (i k : Fin (2 ^ dim)) :
    Framework.uc_eval (Gate.toUCom dim g) i k = if i = gateToPerm g dim hwt k then 1 else 0 := by
  have hC := congrFun (congrFun (uc_eval_basis_agree g dim hwt k) i) 0
  rw [Matrix.mul_apply,
      Finset.sum_eq_single k
        (fun l _ hl => by
          rw [Framework.basis_vector_apply, if_neg (fun hc => hl (Fin.val_injective hc)), mul_zero])
        (fun h => absurd (Finset.mem_univ k) h),
      Framework.basis_vector_apply, if_pos rfl, mul_one] at hC
  rw [hC, Framework.basis_vector_apply]
  simp only [Fin.ext_iff]

/-- **THE LINEARITY LIFT.**  `uc_eval (toUCom g) · s = permState (gateToPerm g).symm s`
    for EVERY state `s` — the abstract permutation is the literal SQIR semantics. -/
theorem uc_eval_eq_permState (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (s : Matrix (Fin (2 ^ dim)) (Fin 1) ℂ) :
    Framework.uc_eval (Gate.toUCom dim g) * s = permState (gateToPerm g dim hwt).symm s := by
  funext i z
  have hz : z = 0 := Subsingleton.elim z 0
  subst hz
  rw [Matrix.mul_apply]
  have hstep : ∀ k, Framework.uc_eval (Gate.toUCom dim g) i k * s k 0
      = (if k = (gateToPerm g dim hwt).symm i then s k 0 else 0) := by
    intro k
    rw [uc_eval_entry g dim hwt i k]
    by_cases hik : k = (gateToPerm g dim hwt).symm i
    · rw [if_pos (by rw [hik]; exact (Equiv.apply_symm_apply (gateToPerm g dim hwt) i).symm),
          if_pos hik, one_mul]
    · rw [if_neg (fun h => hik (by rw [h]; exact (Equiv.symm_apply_apply _ _).symm)),
          if_neg hik, zero_mul]
  rw [Finset.sum_congr rfl (fun k _ => hstep k),
      Finset.sum_ite_eq' Finset.univ ((gateToPerm g dim hwt).symm i) (fun k => s k 0),
      if_pos (Finset.mem_univ _)]
  rfl

/-- **THE LITERAL SQIR GATE ACTION IS A `normSqDist` ISOMETRY (classical fragment).**
    Discharges the `U_rev` / swap permutation hypotheses for the genuine SQIR
    semantics `uc_eval (toUCom g)`, not just an abstract permutation. -/
theorem gate_uc_eval_normSqDist_perm (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (s₁ s₂ : Matrix (Fin (2 ^ dim)) (Fin 1) ℂ) :
    normSqDist (Framework.uc_eval (Gate.toUCom dim g) * s₁)
        (Framework.uc_eval (Gate.toUCom dim g) * s₂)
      = normSqDist s₁ s₂ := by
  rw [uc_eval_eq_permState g dim hwt s₁, uc_eval_eq_permState g dim hwt s₂]
  exact normSqDist_perm_invariant (gateToPerm g dim hwt).symm s₁ s₂

end FormalRV.Shor.CosetEigenstate.UCEvalBridge
