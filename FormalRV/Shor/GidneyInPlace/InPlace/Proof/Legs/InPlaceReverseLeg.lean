/-
  FormalRV.Shor.GidneyInPlace.InPlaceReverseLeg
  ─────────────────────────────────────────────────
  BRICK 7 of the two-register in-place coset-multiplier DYNAMICS transport: the
  REVERSE LEG.  The in-place gate is `pass1 ; Gate.reverse pass2`; this brick makes
  `Gate.reverse pass2` formally compatible with the eGid/permutation framework, WITHOUT
  ever using the words "subtract" or "inverse" as proof steps — only genuine
  reversibility (`applyNat_reverse_cancel` / `gidneyTwoReg_reverse_leg_cancel`).

  Given a FORWARD `pass2` theorem `pass2 final0 = mid`, the reverse leg recovers
  `reverse pass2 mid = final0`, at three layers:
   • `forward_to_reverse_applyNat` — boolean/basis-state level, via
     `applyNat_reverse_cancel` (generic).  `pass2_forward_to_reverse_applyNat` — the
     `pass2` instance via `gidneyTwoReg_reverse_leg_cancel`.
   • `forward_to_reverse_gateToPerm` — the basis-PERMUTATION level, via the new
     `gateToPerm_reverse_cancel` (the gateToPerm analog of `applyNat_reverse_cancel`,
     built through `extendBool`/`applyFin` + `gateToPerm_funboolNat`).
   • `forward_to_reverse_basis` — the `uc_eval` basis-vector level, via
     `uc_eval_basis_agree` (the basis-vector form of `UCEvalBridge.uc_eval_eq_permState`).
   • `pass2_reverse_through_eGid` — the pass-2 INSTANTIATED corollary: combining the
     Brick-5 forward `gidneyProductAddTOf_pass2_perm_through_eGid` with the reverse
     transport, `reverse pass2` sends `eGid (xCtrlGid, ⟨(z + ∑ kInv-table) % 2^bits⟩)`
     back to `eGid (xCtrlGid, ⟨z⟩)`.  (The residue centering — input `(k·x)%N`, output
     `x` — comes from Brick 6's `pass2_endpoint_embed_off`; the cosetState SUM is NOT
     done here.)

  Strictly LOCAL (per directive): NO "subtract"/"inverse" proof steps; NO cosetState
  sum; NO norm bound.  The reverse leg is pinned ONLY by genuine reversibility.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceFoldAction
import FormalRV.Shor.GidneyInPlace.InPlace.Def.GidneyTwoRegInPlace
import FormalRV.Shor.GidneyInPlace.Gate.Spec.UCEvalBridge

namespace FormalRV.Shor.GidneyInPlace.InPlaceReverseLeg

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedArith (window)
open FormalRV.Shor.GidneyInPlace.GatePerm
open FormalRV.Shor.GidneyInPlace.CuccaroGatePerm (gateToPerm_funboolNat)
open FormalRV.Shor.GidneyInPlace.GateReversible (applyNat_reverse_cancel)
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_basis_agree)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate
open FormalRV.Shor.GidneyInPlace.GidneyTwoRegInPlace (pass2 gidneyTwoReg_reverse_leg_cancel)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput (xCtrlGid)
open FormalRV.Shor.GidneyInPlace.InPlaceFoldAction (gidneyProductAddTOf_pass2_perm_through_eGid)

/-! ## §1. The `extendBool`/`applyFin` bridge (reverse-cancel at the basis-permutation
       level). -/

/-- Extending the restricted `applyFin g φ` is the same as `applyNat g` of the extended
    `φ` — because `g` (well-typed) only touches `[0, dim)`, so both are `false` above
    `dim` and agree below.  The bridge that lets the boolean `applyNat_reverse_cancel`
    lift to `applyFin`/`gateToPerm`. -/
theorem extendBool_applyFin (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (φ : Fin dim → Bool) :
    extendBool dim (applyFin g dim φ) = Gate.applyNat g (extendBool dim φ) := by
  funext k
  by_cases hk : k < dim
  · have h1 : extendBool dim (applyFin g dim φ) k = applyFin g dim φ ⟨k, hk⟩ := by
      unfold extendBool; exact dif_pos hk
    rw [h1]; rfl
  · have h1 : extendBool dim (applyFin g dim φ) k = false := by unfold extendBool; exact dif_neg hk
    have h2 : extendBool dim φ k = false := by unfold extendBool; exact dif_neg hk
    rw [h1, applyNat_frame g dim hwt (extendBool dim φ) k (by omega), h2]

/-- **`applyFin` reverse-cancel.**  `applyFin (reverse g) (applyFin g φ) = φ` — the
    `applyFin` analog of `applyNat_reverse_cancel`, via `extendBool_applyFin`. -/
theorem applyFin_reverse_cancel (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (φ : Fin dim → Bool) :
    applyFin (GateReversible.Gate.reverse g) dim (applyFin g dim φ) = φ := by
  funext i
  show Gate.applyNat (GateReversible.Gate.reverse g)
      (extendBool dim (applyFin g dim φ)) i.val = φ i
  rw [extendBool_applyFin g dim hwt φ, applyNat_reverse_cancel g dim hwt (extendBool dim φ)]
  show extendBool dim φ i.val = φ i
  unfold extendBool
  rw [dif_pos i.isLt]

/-- **`gateToPerm` reverse-cancel (the basis-PERMUTATION reverse-cancel).**  The reverse
    gate's basis permutation undoes the forward gate's — `gateToPerm (reverse g)
    (gateToPerm g idx) = idx`.  Built from `applyFin_reverse_cancel` through
    `gateToPerm_funboolNat`.  NO "inverse" as a proof step — pure reversibility. -/
theorem gateToPerm_reverse_cancel (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (idx : Fin (2 ^ dim)) :
    gateToPerm (GateReversible.Gate.reverse g) dim (reverse_wellTyped g dim hwt)
        (gateToPerm g dim hwt idx) = idx := by
  set φ := (funboolEquiv dim).symm idx with hφ
  have heq : funboolNat dim φ = (funboolEquiv dim) φ := by
    apply Fin.ext
    show funbool_to_nat dim (extendBool dim φ) = ((funboolEquiv dim) φ).val
    rw [funboolEquiv_val]
  have hidx : idx = funboolNat dim φ := by
    rw [heq, hφ, Equiv.apply_symm_apply]
  rw [hidx, gateToPerm_funboolNat g dim hwt φ,
      gateToPerm_funboolNat (GateReversible.Gate.reverse g) dim (reverse_wellTyped g dim hwt)
        (applyFin g dim φ),
      applyFin_reverse_cancel g dim hwt φ]

/-! ## §2. The reverse-leg transports (forward theorem → reverse theorem). -/

/-- **Reverse transport (boolean/basis-state level).**  Given the forward action
    `applyNat g final0 = mid`, the reverse leg recovers `applyNat (reverse g) mid =
    final0` — purely by `applyNat_reverse_cancel`. -/
theorem forward_to_reverse_applyNat (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (final0 mid : Nat → Bool) (h : Gate.applyNat g final0 = mid) :
    Gate.applyNat (GateReversible.Gate.reverse g) mid = final0 := by
  rw [← h]; exact applyNat_reverse_cancel g dim hwt final0

/-- **Reverse transport (basis-permutation level).**  Given `gateToPerm g idxA = idxB`,
    the reverse leg recovers `gateToPerm (reverse g) idxB = idxA` — via
    `gateToPerm_reverse_cancel`. -/
theorem forward_to_reverse_gateToPerm (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (idxA idxB : Fin (2 ^ dim)) (h : gateToPerm g dim hwt idxA = idxB) :
    gateToPerm (GateReversible.Gate.reverse g) dim (reverse_wellTyped g dim hwt) idxB = idxA := by
  rw [← h]; exact gateToPerm_reverse_cancel g dim hwt idxA

/-- **Reverse transport (`uc_eval` basis-vector level).**  Given `gateToPerm g idxA =
    idxB`, the reverse leg's literal SQIR unitary sends the basis vector of `idxB` back
    to that of `idxA` — via `uc_eval_basis_agree` (the basis-vector form of
    `UCEvalBridge.uc_eval_eq_permState`). -/
theorem forward_to_reverse_basis (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (idxA idxB : Fin (2 ^ dim)) (h : gateToPerm g dim hwt idxA = idxB) :
    Framework.uc_eval (Gate.toUCom dim (GateReversible.Gate.reverse g))
        * Framework.basis_vector (2 ^ dim) idxB.val
      = Framework.basis_vector (2 ^ dim) idxA.val := by
  rw [uc_eval_basis_agree (GateReversible.Gate.reverse g) dim (reverse_wellTyped g dim hwt) idxB,
      forward_to_reverse_gateToPerm g dim hwt idxA idxB h]

/-! ## §3. The pass-2 reverse-leg, instantiated against the Brick-5 forward. -/

/-- **`pass2` reverse-cancel (boolean level), via `gidneyTwoReg_reverse_leg_cancel`.**
    Given the FORWARD `applyNat pass2 final0 = mid`, the in-place gate's uncompute leg
    `reverse pass2` recovers `final0`.  Pinned by genuine reversibility — NOT "subtract". -/
theorem pass2_forward_to_reverse_applyNat (w bits : Nat) (TfamKinv : Nat → Nat → Nat)
    (numWin : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (final0 mid : Nat → Bool)
    (h : Gate.applyNat (pass2 w bits TfamKinv numWin) final0 = mid) :
    Gate.applyNat (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)) mid = final0 := by
  rw [← h]; exact gidneyTwoReg_reverse_leg_cancel w bits TfamKinv numWin hw hbits final0

/-- **THE pass-2 reverse leg through `eGid`.**  Combining the Brick-5 forward
    `gidneyProductAddTOf_pass2_perm_through_eGid` (which sends `eGid (xCtrlGid, ⟨z⟩)` to
    `eGid (xCtrlGid, ⟨(z + ∑ kInv-table) % 2^bits⟩)`) with the reverse transport, the
    uncompute leg `reverse pass2` sends `eGid (xCtrlGid, ⟨(z + ∑) % 2^bits⟩)` BACK to
    `eGid (xCtrlGid, ⟨z⟩)` — same work/control branch.  (Residue centering: by Brick 6
    the input `b = (k·x)%N` makes `∑` land on `x`'s coset; the cosetState SUM is NOT
    done here.) -/
theorem pass2_reverse_through_eGid (w bits numWin : Nat) (TfamKinv : Nat → Nat → Nat)
    (y z : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (hz : z < 2 ^ bits)
    (hz2 : (z + ∑ k ∈ Finset.range numWin, TfamKinv k (window w y k)) % 2 ^ bits < 2 ^ bits)
    (hwt : Gate.WellTyped (cosetDim w bits) (pass2 w bits TfamKinv numWin)) :
    gateToPerm (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)) (cosetDim w bits)
        (reverse_wellTyped (pass2 w bits TfamKinv numWin) (cosetDim w bits) hwt)
        (eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) y,
            ⟨(z + ∑ k ∈ Finset.range numWin, TfamKinv k (window w y k)) % 2 ^ bits, hz2⟩))
      = eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) y, ⟨z, hz⟩) :=
  forward_to_reverse_gateToPerm (pass2 w bits TfamKinv numWin) (cosetDim w bits) hwt _ _
    (gidneyProductAddTOf_pass2_perm_through_eGid w bits numWin TfamKinv y z hw hbits hz hz2 hwt)

end FormalRV.Shor.GidneyInPlace.InPlaceReverseLeg
