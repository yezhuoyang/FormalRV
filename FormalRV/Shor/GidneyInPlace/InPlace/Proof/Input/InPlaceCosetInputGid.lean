/-
  FormalRV.Shor.GidneyInPlace.InPlaceCosetInputGid
  ────────────────────────────────────────────────────
  BRICK 3 of the two-register in-place coset-multiplier DYNAMICS transport:
  REPRESENTATIONAL packaging only — the equiv `eGid` (Brick 1) applied to the clean
  control value `xCtrlGid` (Brick 2), and the whole-register coset input `cosetInputGid`
  it factors.  NO product-add dynamics, NO bad-set, NO norm bound.

  The relocated-layout analog of `ReducedLookupEgate.e_gate_apply` / `cosetInput` /
  `branchOfE_cosetInput_active`/`_zero`:
   • `eGid_apply` — the FORWARD map (the direction `branchOfE` consumes):
       `eGid (xCtrlGid, z) = funboolNat (inplaceAccInput z)`.
     (Composes `Equiv.ofBijective_apply` with the Brick-2 pointwise
     `assembleEGid_xCtrlGid`.)
   • `cosetInputGid` — the whole-register state: `cosetState (2^bits) N cm k` placed in
     the `xCtrlGid` control branch (the accumulator-block data factor), zero elsewhere,
     laid out through `eGid`.
   • `branchOfE_cosetInputGid_active`/`_zero` — the `branchOfE` projection facts: in the
     `xCtrlGid` branch the data substate IS `cosetState (2^bits) N cm k`; off it, zero.
   • `cosetInputGid_at_accInput` — the explicit "each branch is `inplaceAccInput z`":
     the basis amplitude of `cosetInputGid` at the basis state `funboolNat
     (inplaceAccInput z)` is exactly `cosetState (2^bits) N cm k z`.

  AUDIT (per directive).  The branch variable `z` is a RAW accumulator-register branch
  index `Fin (2^bits)` (a `Nat` register value), NEVER a decoded logical residue mod N.
  `cosetState (2^bits) N cm k` assigns the amplitude as a function of that raw index
  (whether `z ∈ cosetWindow`); no step here moves to residues mod N.  PARAMETRIC in
  `accBase`/`yBase` (serves both passes) via the Brick-2 `xCtrlGid`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Def.InPlaceEgateInput

namespace FormalRV.Shor.GidneyInPlace.InPlaceCosetInputGid

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate
open FormalRV.Shor.GidneyInPlace.GatePerm (funboolNat)
open FormalRV.Shor.GidneyInPlace.ApproxOp (cosetState)
open FormalRV.Shor.GidneyInPlace.BranchFactor (branchOfE)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput

/-! ## §1. The forward map `eGid_apply`. -/

/-- **The forward defining property (the direction `branchOfE` consumes).**  `eGid`
    sends the clean control value `xCtrlGid` paired with accumulator branch value `z`
    to the funbool index of `inplaceAccInput z` — the basis state with the work/control
    branch fixed and the accumulator block holding `z`.  Composes
    `Equiv.ofBijective_apply` with the Brick-2 pointwise `assembleEGid_xCtrlGid`. -/
theorem eGid_apply (w bits numWin accBase yBase y z : Nat) (hz : z < 2 ^ bits)
    (haccfit : accBase + bits ≤ cosetDim w bits) :
    eGid w bits accBase haccfit (xCtrlGid w bits numWin accBase yBase y, ⟨z, hz⟩)
      = funboolNat (cosetDim w bits)
          (fun p => inplaceAccInput w bits numWin accBase yBase z y p.val) := by
  unfold eGid
  rw [Equiv.ofBijective_apply]
  unfold eFunGid
  congr 1
  funext p
  exact assembleEGid_xCtrlGid w bits numWin accBase yBase y z p.val haccfit p.isLt

/-! ## §2. The whole-register coset input `cosetInputGid`. -/

/-- The whole-register coset input: the coset state `cosetState (2^bits) N cm k` placed
    in the control branch `xCtrlGid` (the accumulator-block data factor), zero in every
    other control branch, laid out through `eGid`.  `k` is the coset residue label, `z`
    (below) the RAW accumulator branch index. -/
noncomputable def cosetInputGid (w bits numWin N cm accBase yBase k y : Nat)
    (haccfit : accBase + bits ≤ cosetDim w bits) : QState (2 ^ cosetDim w bits) :=
  fun idx _ =>
    if ((eGid w bits accBase haccfit).symm idx).1 = xCtrlGid w bits numWin accBase yBase y
    then cosetState (2 ^ bits) N cm k ((eGid w bits accBase haccfit).symm idx).2 0
    else 0

/-! ## §3. The `branchOfE` projection facts. -/

/-- **Active branch.**  In the `xCtrlGid` control branch, the `branchOfE` data substate
    of `cosetInputGid` is exactly the coset state `cosetState (2^bits) N cm k`. -/
theorem branchOfE_cosetInputGid_active (w bits numWin N cm accBase yBase k y : Nat)
    (haccfit : accBase + bits ≤ cosetDim w bits) :
    branchOfE (eGid w bits accBase haccfit)
        (cosetInputGid w bits numWin N cm accBase yBase k y haccfit)
        (xCtrlGid w bits numWin accBase yBase y)
      = cosetState (2 ^ bits) N cm k := by
  funext z hz
  have h0 : hz = 0 := Subsingleton.elim hz 0
  subst h0
  show cosetInputGid w bits numWin N cm accBase yBase k y haccfit
      (eGid w bits accBase haccfit (xCtrlGid w bits numWin accBase yBase y, z)) 0
    = cosetState (2 ^ bits) N cm k z 0
  unfold cosetInputGid
  rw [Equiv.symm_apply_apply, if_pos rfl]

/-- **Inactive branch.**  Off the `xCtrlGid` control branch, the `branchOfE` data
    substate of `cosetInputGid` is identically zero. -/
theorem branchOfE_cosetInputGid_zero (w bits numWin N cm accBase yBase k y : Nat)
    (haccfit : accBase + bits ≤ cosetDim w bits)
    (x : Fin (2 ^ (cosetDim w bits - bits))) (hx : x ≠ xCtrlGid w bits numWin accBase yBase y) :
    branchOfE (eGid w bits accBase haccfit)
        (cosetInputGid w bits numWin N cm accBase yBase k y haccfit) x
      = fun _ _ => 0 := by
  funext z hz
  show cosetInputGid w bits numWin N cm accBase yBase k y haccfit
      (eGid w bits accBase haccfit (x, z)) 0 = 0
  unfold cosetInputGid
  rw [Equiv.symm_apply_apply, if_neg hx]

/-! ## §4. Each branch of `cosetInputGid` is `inplaceAccInput z`. -/

/-- **The explicit branch identity.**  The basis amplitude of `cosetInputGid` at the
    basis state `funboolNat (inplaceAccInput z)` (the work branch fixed at `xCtrlGid`,
    accumulator block holding the RAW value `z`) is exactly the coset amplitude
    `cosetState (2^bits) N cm k z`.  This is "each branch of `cosetInputGid` is
    `inplaceAccInput z`", with `z` a raw `Fin (2^bits)` branch index — NOT a residue. -/
theorem cosetInputGid_at_accInput (w bits numWin N cm accBase yBase k y z : Nat)
    (hz : z < 2 ^ bits) (haccfit : accBase + bits ≤ cosetDim w bits) :
    cosetInputGid w bits numWin N cm accBase yBase k y haccfit
        (funboolNat (cosetDim w bits)
          (fun p => inplaceAccInput w bits numWin accBase yBase z y p.val)) 0
      = cosetState (2 ^ bits) N cm k ⟨z, hz⟩ 0 := by
  rw [← eGid_apply w bits numWin accBase yBase y z hz haccfit]
  unfold cosetInputGid
  rw [Equiv.symm_apply_apply, if_pos rfl]

end FormalRV.Shor.GidneyInPlace.InPlaceCosetInputGid
