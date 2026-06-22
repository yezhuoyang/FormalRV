/-
  FormalRV.Shor.GidneyInPlace.InPlaceNormBound
  ───────────────────────────────────────────────
  The TRIANGLE + UNITARY-INVARIANCE backbone of the two-register in-place coset
  multiplier norm bound (Architecture B).  The whole-gate `normSqDist` deviation is
  reduced to TWO FORWARD windowed-multiply deviations — no coupled bad set, no inverse
  direction — via:

    normSqDist (U_gate · in) tgt
      ≤ normSqDist (U_gate · in) (U_rev2 · M1)   +   normSqDist (U_rev2 · M1) tgt   [triangle]
      = normSqDist (U_p1 · in) M1                +   normSqDist M1 (U_p2 · tgt)      [U_rev2 unitary]

  where  in = cosetInputTwoReg x 0,  M1 = cosetInputTwoReg x ((k·x)%N)  (ideal post-pass-1
  intermediate),  tgt = cosetInputTwoReg 0 ((k·x)%N),  U_gate = uc_eval(pass1 ; reverse pass2).

  The two equalities are EXACT:
   • `normSqDist_triangle` (ApproxOp) — the L1 triangle inequality.
   • `gate_uc_eval_normSqDist_perm` (UCEvalBridge) — `uc_eval` of any well-typed gate is a
     `normSqDist` isometry (permutation reindex), peeling `U_rev2` off BOTH terms.
   • `uc_eval_reverse_cancel` (NEW, below) — `U_rev2 · (U_p2 · tgt) = tgt` (reverse undoes
     forward), letting the second term be peeled too.

  Result (`gidneyTwoRegInPlace_coset_norm_bound_of_legs`): given the two FORWARD leg
  deviations each `≤ L`, the whole gate deviates `≤ 2·L`.  Plugging the forward windowed
  multiply bound `L = numWin·(2/2^cm)` (next sub-bricks, via `cosetOutOfPlace_hfwd_E`)
  gives the honest `4·numWin/2^cm`.  This file proves NO per-leg bound — only the
  reduction.  branch_action / agree_off are NOT used (Architecture B is leg-decomposed,
  not whole-gate per-branch).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Input.InPlaceCosetInputTwoReg
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceReverseLeg
import FormalRV.Shor.GidneyInPlace.Gate.Spec.UCEvalBridge

namespace FormalRV.Shor.GidneyInPlace.InPlaceNormBound

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.GidneyInPlace.ApproxOp (permState normSqDist_triangle)
open FormalRV.Shor.GidneyInPlace.GatePerm (gateToPerm reverse_wellTyped)
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_eq_permState gate_uc_eval_normSqDist_perm)
open FormalRV.Shor.GidneyInPlace.InPlaceReverseLeg (gateToPerm_reverse_cancel)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg (cosetInputTwoReg)
open FormalRV.Shor.GidneyInPlace.GidneyTwoRegInPlace
  (pass1 pass2 gidneyTwoRegInPlaceCosetMul gidneyTwoRegInPlaceCosetMul_unfold)
open FormalRV.Shor.GidneyInPlace.ProductAddWrapper
  (gidneyProductAdd_pass1_wellTyped gidneyProductAdd_pass2_wellTyped)

/-- The two-register coset input as an explicit state VECTOR (`Matrix … (Fin 1)`), so
    that `uc_eval(…) * cosetInputVec …` type-checks — avoids the `Square * QState` HMul
    instance gap.  Defeq to `cosetInputTwoReg`. -/
noncomputable def cosetInputVec (w bits N cm xa xb : Nat) :
    Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ :=
  cosetInputTwoReg w bits N cm xa xb

/-! ## §1. Reverse undoes forward at the `uc_eval` level. -/

/-- **`uc_eval(reverse g)` cancels `uc_eval(g)` on every state.**  For any well-typed
    `g`, `uc_eval(reverse g) · (uc_eval(g) · s) = s`.  Proven via the permutation bridge
    `uc_eval_eq_permState` + `gateToPerm_reverse_cancel` (the abstract reverse-cancel),
    NOT by asserting matrix inverses. -/
theorem uc_eval_reverse_cancel (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (s : Matrix (Fin (2 ^ dim)) (Fin 1) ℂ) :
    Framework.uc_eval (Gate.toUCom dim (GateReversible.Gate.reverse g))
        * (Framework.uc_eval (Gate.toUCom dim g) * s) = s := by
  rw [uc_eval_eq_permState g dim hwt s,
      uc_eval_eq_permState (GateReversible.Gate.reverse g) dim (reverse_wellTyped g dim hwt)
        (permState (gateToPerm g dim hwt).symm s)]
  funext i z
  show s ((gateToPerm g dim hwt).symm
      ((gateToPerm (GateReversible.Gate.reverse g) dim (reverse_wellTyped g dim hwt)).symm i)) z
    = s i z
  congr 1
  set σ := gateToPerm g dim hwt with hσ
  set τ := gateToPerm (GateReversible.Gate.reverse g) dim (reverse_wellTyped g dim hwt) with hτ
  have hpt : ∀ j, τ j = σ.symm j := by
    intro j
    have h := gateToPerm_reverse_cancel g dim hwt (σ.symm j)
    rw [hσ, hτ] at *
    rw [Equiv.apply_symm_apply] at h
    exact h
  have hkey : τ (τ.symm i) = σ.symm (τ.symm i) := hpt (τ.symm i)
  rw [Equiv.apply_symm_apply] at hkey
  exact hkey.symm

/-! ## §2. The architecture reduction: whole-gate bound from the two forward legs. -/

/-- **Whole-gate bound from the two FORWARD legs (Architecture B).**  Given:
     • `hleg1 : normSqDist (uc_eval(pass1) · cosetInputTwoReg x 0)
                            (cosetInputTwoReg x ((k·x)%N)) ≤ L`   (pass-1 forward leg), and
     • `hleg2 : normSqDist (cosetInputTwoReg x ((k·x)%N))
                            (uc_eval(pass2) · cosetInputTwoReg 0 ((k·x)%N)) ≤ L`  (pass-2 leg),
    the whole in-place gate `pass1 ; reverse pass2` deviates from the target
    `cosetInputTwoReg 0 ((k·x)%N)` by `≤ 2·L`.  Pure backbone — triangle + unitary
    invariance + reverse-cancel; NO per-leg coset arithmetic, NO bad set. -/
theorem gidneyTwoRegInPlace_coset_norm_bound_of_legs
    (w bits numWin N cm k x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (L : ℝ)
    (hleg1 : normSqDist
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits) (pass1 w bits TfamK numWin))
          * cosetInputVec w bits N cm x 0)
        (cosetInputVec w bits N cm x ((k * x) % N)) ≤ L)
    (hleg2 : normSqDist
        (cosetInputVec w bits N cm x ((k * x) % N))
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits) (pass2 w bits TfamKinv numWin))
          * cosetInputVec w bits N cm 0 ((k * x) % N)) ≤ L) :
    normSqDist
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin))
          * cosetInputVec w bits N cm x 0)
        (cosetInputVec w bits N cm 0 ((k * x) % N)) ≤ 2 * L := by
  have hp2wt : Gate.WellTyped (cosetDim w bits) (pass2 w bits TfamKinv numWin) :=
    gidneyProductAdd_pass2_wellTyped w bits TfamKinv numWin hw hbits
  have hrevwt : Gate.WellTyped (cosetDim w bits)
      (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)) := reverse_wellTyped _ _ hp2wt
  -- decompose uc_eval(gate)·input = U_rev2 · (U_p1 · input)
  have hdecomp : Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin))
      * cosetInputVec w bits N cm x 0
      = Framework.uc_eval (Gate.toUCom (cosetDim w bits)
          (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)))
        * (Framework.uc_eval (Gate.toUCom (cosetDim w bits) (pass1 w bits TfamK numWin))
          * cosetInputVec w bits N cm x 0) := by
    rw [gidneyTwoRegInPlaceCosetMul_unfold, Gate.toUCom_seq, uc_eval_seq_mul]
  rw [hdecomp]
  -- triangle with the midpoint  U_rev2 · M1
  refine le_trans (normSqDist_triangle _
    (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)))
      * cosetInputVec w bits N cm x ((k * x) % N)) _) ?_
  -- Term 1: peel U_rev2 (isometry) ⇒ pass-1 forward leg
  have hterm1 : normSqDist
      (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
          (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)))
        * (Framework.uc_eval (Gate.toUCom (cosetDim w bits) (pass1 w bits TfamK numWin))
          * cosetInputVec w bits N cm x 0))
      (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
          (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)))
        * cosetInputVec w bits N cm x ((k * x) % N)) ≤ L := by
    rw [gate_uc_eval_normSqDist_perm _ (cosetDim w bits) hrevwt]
    exact hleg1
  -- Term 2: target = U_rev2 · (U_p2 · target); peel U_rev2 ⇒ pass-2 forward leg
  have hterm2 : normSqDist
      (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
          (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)))
        * cosetInputVec w bits N cm x ((k * x) % N))
      (cosetInputVec w bits N cm 0 ((k * x) % N)) ≤ L := by
    have hcancel : cosetInputVec w bits N cm 0 ((k * x) % N)
        = Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)))
          * (Framework.uc_eval (Gate.toUCom (cosetDim w bits) (pass2 w bits TfamKinv numWin))
            * cosetInputVec w bits N cm 0 ((k * x) % N)) :=
      (uc_eval_reverse_cancel (pass2 w bits TfamKinv numWin) (cosetDim w bits) hp2wt
        (cosetInputVec w bits N cm 0 ((k * x) % N))).symm
    rw [hcancel, gate_uc_eval_normSqDist_perm _ (cosetDim w bits) hrevwt]
    exact hleg2
  linarith [hterm1, hterm2]

end FormalRV.Shor.GidneyInPlace.InPlaceNormBound
