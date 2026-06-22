/-
  FormalRV.Shor.GidneyInPlace.IdealPermLift — P1.1b of the hybrid route:
  lift the a-VALUE residue-shift permutation `resShiftPerm` to a FULL-INDEX
  permutation `idealPerm` on `Fin (2 ^ cosetDim w bits)`, and prove the SUPPORT
  TRANSPORT of `cosetInputVec`.
  ════════════════════════════════════════════════════════════════════════════

  P1.1a (`RunwayShiftPerm`) built the clean ideal residue-shift `resShiftPerm` on the
  a-block VALUE register `Fin (2^bits)`.  P1.0 (`CosetInputSupport`) characterized the
  raw-index support of `cosetInputVec z 0`.  This file BRIDGES them: it lifts
  `resShiftPerm` through the `eGid` (control × a-data) factorization to a permutation
  `idealPerm` of the full register, and proves that `idealPerm` carries the support of
  `cosetInputVec z 0` onto the support of `cosetInputVec ((mult·z)%N) 0` — the a-window
  base `z` shifts to `(mult·z)%N`, the b-window (base `0`) and the scratch are invariant.

  STRATEGY.  `idealPerm = eGid.permCongr (refl × resShiftPerm)` permutes the full index by:
  conjugating through `eGid`, it acts as `resShiftPerm` on the a-data factor and the
  identity on the control factor.  Concretely, writing `(ctrl, aval) := eGid.symm idx`,
  `idealPerm idx = eGid (ctrl, resShiftPerm aval)`.  Then:
    • the a-decode of `idealPerm idx` = `guardedShift mult` of the a-decode of `idx`
      (the a-data factor is shifted; `eGid_aDecode` reads the data block as the factor);
    • the b-decode and the scratch are UNCHANGED (the b-block and scratch lie OFF the
      a-data block, and `eGid` keeps the control factor — and hence those positions — fixed).
  The a-window leg then reduces, on the SUPPORT (under the FULL-BLOCKS budget
  `2^cm·N ≤ 2^bits`), to `guarded_on_support`: `z + j·N ↦ (mult·z)%N + j·N`, which is
  exactly the `j`-th rep of the target window.

  ⚠ The FULL-BLOCKS budget `2^cm·N ≤ 2^bits` and the coprimality data
  (`(mult·kInv)%N = (kInv·mult)%N = 1`) are REQUIRED and EXPLICIT in every signature, and
  `z < N` is threaded (a verified counterexample exists under the weaker runway-fit).

  Stops at the SUPPORT transport — NO amplitude/vector equality, NO physical gate, NO bad
  sets, NO QPE induction.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Ideal.Proof.CosetInputSupport
import FormalRV.Shor.GidneyInPlace.Ideal.Def.RunwayShiftPerm

namespace FormalRV.Shor.GidneyInPlace.IdealPermLift

open FormalRV.Framework (nat_to_funbool)
open FormalRV.BQAlgo (decodeReg decodeReg_ext)
open FormalRV.Shor.WindowedCircuit (decodeReg_lt_two_pow decodeReg_eq_mod_of_testBit)
open FormalRV.Shor.GidneyInPlace.GatePerm (funboolNat)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg
  (aBase bBase scratchClean scratchClean_congr_offBlocks nat_to_funbool_funboolNat_agree
   assembleEGid_off_block_zindep)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate
open FormalRV.Shor.GidneyInPlace.RunwayShiftPerm
  (guardedShift resShiftPerm guarded_leftinv guarded_on_support)
open FormalRV.Shor.GidneyInPlace.CosetInputSupport (inSupport cosetInputVec_amp)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.ApproxOp (permState)
open scoped Classical

/-! ## §0. The lifted ideal permutation. -/

set_option linter.unusedVariables false in
/-- **The full-index ideal permutation.**  Conjugating through the `eGid` (control × a-data)
    factorization, act as `resShiftPerm` (= `guardedShift mult`) on the a-data factor and as
    the identity on the control factor.  `cm` is threaded for a uniform parameter list with the
    transport lemmas (it is not used in the def). -/
noncomputable def idealPerm (w bits N cm mult kInv : Nat)
    (hN : 1 < N) (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1) :
    Equiv.Perm (Fin (2 ^ cosetDim w bits)) :=
  (eGid w bits (aBase w) (pass2_accfit w bits)).permCongr
    (Equiv.prodCongr
      (Equiv.refl (Fin (2 ^ (cosetDim w bits - bits))))
      (resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd))

/-! ## §1. Reading the data block of an `eGid` image. -/

/-- The bit-function recovered from the `eGid` image agrees with the assembled bit-function
    on `[0, cosetDim)` — the funbool round-trip applied to `eFunGid`'s assembled value. -/
theorem nat_to_funbool_eGid (w bits accBase : Nat)
    (haccfit : accBase + bits ≤ cosetDim w bits)
    (ctrl : Fin (2 ^ (cosetDim w bits - bits))) (z : Fin (2 ^ bits))
    (p : Nat) (hp : p < cosetDim w bits) :
    nat_to_funbool (cosetDim w bits) (eGid w bits accBase haccfit (ctrl, z)).val p
      = assembleEGid w bits accBase ctrl.val z.val p := by
  have hImg : eGid w bits accBase haccfit (ctrl, z)
      = funboolNat (cosetDim w bits)
          (fun i => assembleEGid w bits accBase ctrl.val z.val i.val) := rfl
  rw [hImg, nat_to_funbool_funboolNat_agree (cosetDim w bits) _ p hp]
  simp only [GatePerm.extendBool, dif_pos hp]

/-- **D1 — the data block of an `eGid` image decodes to the data factor value.**  For the
    contiguous accumulator block `[accBase, accBase+bits)`, the `eGid`-assembled index for
    `(ctrl, z)` decodes (via `nat_to_funbool`) to the raw value `z.val`. -/
theorem eGid_aDecode (w bits accBase : Nat)
    (haccfit : accBase + bits ≤ cosetDim w bits)
    (ctrl : Fin (2 ^ (cosetDim w bits - bits))) (z : Fin (2 ^ bits)) :
    decodeReg (fun i => accBase + i) bits
        (nat_to_funbool (cosetDim w bits) (eGid w bits accBase haccfit (ctrl, z)).val)
      = z.val := by
  rw [decodeReg_eq_mod_of_testBit (fun i => accBase + i) bits z.val _
        (fun i hi => by
          rw [nat_to_funbool_eGid w bits accBase haccfit ctrl z (accBase + i)
                (by omega)]
          exact assembleEGid_data w bits accBase ctrl.val z.val i hi)]
  exact Nat.mod_eq_of_lt z.isLt

/-! ## §2. The action of `idealPerm` as `eGid` of the shifted data factor. -/

/-- **`idealPerm` acts as `eGid` of the shifted data factor.**  Writing
    `(ctrl, aval) := eGid.symm idx`, `idealPerm idx = eGid (ctrl, resShiftPerm aval)` — the
    control factor is untouched, the a-data factor is `resShiftPerm`-shifted.  Direct from
    `permCongr_apply` + `prodCongr_apply` + `Equiv.refl_apply`. -/
theorem idealPerm_apply (w bits N cm mult kInv : Nat)
    (hN : 1 < N) (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (idx : Fin (2 ^ cosetDim w bits)) :
    idealPerm w bits N cm mult kInv hN hfwd hbwd idx
      = eGid w bits (aBase w) (pass2_accfit w bits)
          (((eGid w bits (aBase w) (pass2_accfit w bits)).symm idx).1,
           resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd
             (((eGid w bits (aBase w) (pass2_accfit w bits)).symm idx).2)) := by
  unfold idealPerm
  rw [Equiv.permCongr_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]

/-! ## §3. The three decode-transport lemmas. -/

/-- The a-data factor value of `resShiftPerm aval` is `guardedShift mult aval` (definitional). -/
theorem resShiftPerm_val (N mult kInv : Nat)
    (hN : 1 < N) (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (aval : Fin (2 ^ bits)) :
    (resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd aval).val
      = guardedShift (2 ^ bits) N mult aval.val := rfl

/-- **(1a) a-decode transport.**  The a-block decode of `idealPerm idx` is the
    `guardedShift mult` of the a-block decode of `idx` — the a-data factor is shifted by
    `resShiftPerm = guardedShift mult`, read off via `eGid_aDecode` on both sides. -/
theorem aDecode_idealPerm (w bits N cm mult kInv : Nat)
    (hN : 1 < N) (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (idx : Fin (2 ^ cosetDim w bits)) :
    decodeReg (fun i => aBase w + i) bits
        (nat_to_funbool (cosetDim w bits)
          (idealPerm w bits N cm mult kInv hN hfwd hbwd idx).val)
      = guardedShift (2 ^ bits) N mult
          (decodeReg (fun i => aBase w + i) bits
            (nat_to_funbool (cosetDim w bits) idx.val)) := by
  set e := eGid w bits (aBase w) (pass2_accfit w bits) with he
  set ctrl := (e.symm idx).1 with hctrl
  set aval := (e.symm idx).2 with haval
  -- LHS: rewrite idealPerm via idealPerm_apply and read off via eGid_aDecode.
  rw [idealPerm_apply w bits N cm mult kInv hN hfwd hbwd idx]
  rw [eGid_aDecode w bits (aBase w) (pass2_accfit w bits) ctrl
        (resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd aval)]
  rw [resShiftPerm_val (bits := bits) N mult kInv hN hfwd hbwd aval]
  -- RHS inner: idx = e (ctrl, aval), then eGid_aDecode.
  congr 1
  have hidx : idx = e (ctrl, aval) := by
    rw [hctrl, haval]; exact (e.apply_symm_apply idx).symm
  rw [hidx, eGid_aDecode w bits (aBase w) (pass2_accfit w bits) ctrl aval]

/-- **Off-the-a-block agreement of the two `eGid` images.**  At a position `p < cosetDim`
    OUTSIDE the a-data block `[aBase, aBase+bits)`, the bit-function of `idealPerm idx`
    agrees with that of `idx`: both equal `assembleEGid` of the (common) control factor with
    `z` irrelevant.  This is the engine for the b-decode and scratch invariance. -/
theorem nat_to_funbool_idealPerm_off_aBlock (w bits N cm mult kInv : Nat)
    (hN : 1 < N) (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (idx : Fin (2 ^ cosetDim w bits)) (p : Nat) (hp : p < cosetDim w bits)
    (hoff : ¬ (aBase w ≤ p ∧ p < aBase w + bits)) :
    nat_to_funbool (cosetDim w bits)
        (idealPerm w bits N cm mult kInv hN hfwd hbwd idx).val p
      = nat_to_funbool (cosetDim w bits) idx.val p := by
  set e := eGid w bits (aBase w) (pass2_accfit w bits) with he
  set ctrl := (e.symm idx).1 with hctrl
  set aval := (e.symm idx).2 with haval
  have hidx : idx = e (ctrl, aval) := by
    rw [hctrl, haval]; exact (e.apply_symm_apply idx).symm
  rw [idealPerm_apply w bits N cm mult kInv hN hfwd hbwd idx]
  rw [nat_to_funbool_eGid w bits (aBase w) (pass2_accfit w bits) ctrl _ p hp]
  conv_rhs => rw [hidx, nat_to_funbool_eGid w bits (aBase w) (pass2_accfit w bits) ctrl aval p hp]
  rw [assembleEGid_off_block_zindep w bits (aBase w) ctrl.val _ p
        (pass2_accfit w bits) hp hoff]
  exact (assembleEGid_off_block_zindep w bits (aBase w) ctrl.val aval.val p
    (pass2_accfit w bits) hp hoff).symm

/-- **(1b) b-decode invariant.**  The b-block decode is unchanged by `idealPerm` (the b-block
    lies off the a-data block; `eGid` keeps the control factor — hence those positions — fixed). -/
theorem bDecode_idealPerm (w bits N cm mult kInv : Nat)
    (hN : 1 < N) (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (idx : Fin (2 ^ cosetDim w bits)) :
    decodeReg (fun i => bBase w bits + i) bits
        (nat_to_funbool (cosetDim w bits)
          (idealPerm w bits N cm mult kInv hN hfwd hbwd idx).val)
      = decodeReg (fun i => bBase w bits + i) bits
          (nat_to_funbool (cosetDim w bits) idx.val) := by
  refine decodeReg_ext _ _ _ _ (fun i hi => ?_)
  exact nat_to_funbool_idealPerm_off_aBlock w bits N cm mult kInv hN hfwd hbwd idx
    (bBase w bits + i) (by unfold bBase cosetDim; omega) (by unfold aBase bBase; omega)

/-- **(1c) scratch-clean invariant.**  Scratch-cleanliness is preserved by `idealPerm`: it
    reads only positions off BOTH data blocks (in particular off the a-data block), where
    `idealPerm` agrees with the identity. -/
theorem scratchClean_idealPerm (w bits N cm mult kInv : Nat)
    (hN : 1 < N) (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (idx : Fin (2 ^ cosetDim w bits)) :
    scratchClean w bits
        (nat_to_funbool (cosetDim w bits)
          (idealPerm w bits N cm mult kInv hN hfwd hbwd idx).val)
      ↔ scratchClean w bits (nat_to_funbool (cosetDim w bits) idx.val) := by
  refine scratchClean_congr_offBlocks w bits _ _ (fun p hp hna _ => ?_)
  exact nat_to_funbool_idealPerm_off_aBlock w bits N cm mult kInv hN hfwd hbwd idx p hp hna

/-! ## §4. The a-window transport (the load-bearing leg). -/

/-- The modular round-trip `(kInv·((mult·z)%N))%N = z` under `(kInv·mult)%N = 1` and `z < N`. -/
theorem kInv_mult_mod (N mult kInv z : Nat) (hN : 1 < N)
    (hbwd : (kInv * mult) % N = 1) (hz : z < N) :
    (kInv * ((mult * z) % N)) % N = z := by
  have hN0 : 0 < N := by omega
  -- kInv·((mult·z)%N) ≡ kInv·(mult·z) ≡ (kInv·mult)·z ≡ 1·z = z  [MOD N]
  have hkm : kInv * mult ≡ 1 [MOD N] := by
    show (kInv * mult) % N = 1 % N
    rw [hbwd, Nat.mod_eq_of_lt hN]
  have h1 : kInv * ((mult * z) % N) ≡ kInv * (mult * z) [MOD N] :=
    (Nat.ModEq.refl kInv).mul (Nat.mod_modEq _ _)
  have h2 : kInv * (mult * z) ≡ z [MOD N] := by
    have heq : kInv * (mult * z) = (kInv * mult) * z := (mul_assoc kInv mult z).symm
    rw [heq]
    have hmr : (kInv * mult) * z ≡ 1 * z [MOD N] := Nat.ModEq.mul_right z hkm
    rwa [Nat.one_mul] at hmr
  have h3 := (h1.trans h2)
  unfold Nat.ModEq at h3
  rw [Nat.mod_eq_of_lt hz] at h3
  exact h3

/-- **The a-window transport.**  Under the FULL-BLOCKS budget `2^cm·N ≤ 2^bits`, the
    coprimality data, and `z < N`, a raw value `va` lies in the source window `cosetWindow z`
    iff its `guardedShift mult` lies in the target window `cosetWindow ((mult·z)%N)`.  Forward
    via `guarded_on_support` (the `j`-th source rep maps to the `j`-th target rep); reverse via
    `guarded_leftinv` + the modular round-trip. -/
theorem aWindow_guardedShift (bits N cm mult kInv z va : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (hbudget : 2 ^ cm * N ≤ 2 ^ bits) (hz : z < N) (hva : va < 2 ^ bits) :
    (⟨va, hva⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm z
      ↔ (⟨guardedShift (2 ^ bits) N mult va,
            RunwayShiftPerm.guarded_lt (2 ^ bits) N mult va (by omega) hva⟩ : Fin (2 ^ bits))
          ∈ cosetWindow (2 ^ bits) N cm ((mult * z) % N) := by
  have hN0 : 0 < N := by omega
  have hres : (mult * z) % N < N := Nat.mod_lt _ hN0
  rw [mem_cosetWindow (2 ^ bits) N cm z hN0, mem_cosetWindow (2 ^ bits) N cm ((mult * z) % N) hN0]
  constructor
  · rintro ⟨j, hj, hvj⟩
    have hvaj : va = z + j * N := hvj
    refine ⟨j, hj, ?_⟩
    -- guardedShift mult (z + j·N) = (mult·z)%N + j·N
    show guardedShift (2 ^ bits) N mult va = (mult * z) % N + j * N
    rw [hvaj]
    exact guarded_on_support (2 ^ bits) N cm mult z j hN0 hz hj hbudget
  · rintro ⟨j, hj, hvj⟩
    have hgm : guardedShift (2 ^ bits) N mult va = (mult * z) % N + j * N := hvj
    refine ⟨j, hj, ?_⟩
    show va = z + j * N
    -- apply guardedShift kInv to both sides; LHS ↦ va, RHS ↦ z + j·N
    have hback : guardedShift (2 ^ bits) N kInv (guardedShift (2 ^ bits) N mult va) = va :=
      guarded_leftinv (2 ^ bits) N mult kInv va hN hfwd
    have hrhs : guardedShift (2 ^ bits) N kInv ((mult * z) % N + j * N)
        = (kInv * ((mult * z) % N)) % N + j * N :=
      guarded_on_support (2 ^ bits) N cm kInv ((mult * z) % N) j hN0 hres hj hbudget
    have hval : va = (kInv * ((mult * z) % N)) % N + j * N := by
      rw [← hback, hgm, hrhs]
    rw [hval, kInv_mult_mod N mult kInv z hN hbwd hz]

/-! ## §5. The support transport. -/

/-- **D3-fwd — forward support transport.**  Under the FULL-BLOCKS budget `2^cm·N ≤ 2^bits`,
    the coprimality data, and `z < N`, `idealPerm` carries the support of `cosetInputVec z 0`
    onto the support of `cosetInputVec ((mult·z)%N) 0`: the a-window base shifts `z ↦ (mult·z)%N`,
    while the b-window (base `0`) and the scratch are invariant.  Scratch leg via (1c), b-window
    leg via (1b) (`xb = 0` both sides), a-window leg via (1a) + `aWindow_guardedShift`. -/
theorem inSupport_idealPerm_fwd (w bits N cm mult kInv z : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (hfull : 2 ^ cm * N ≤ 2 ^ bits) (hz : z < N)
    (idx : Fin (2 ^ cosetDim w bits)) :
    inSupport w bits N cm z 0 idx
      ↔ inSupport w bits N cm ((mult * z) % N) 0
          (idealPerm w bits N cm mult kInv hN hfwd hbwd idx) := by
  unfold inSupport
  -- scratch leg
  rw [scratchClean_idealPerm w bits N cm mult kInv hN hfwd hbwd idx]
  -- b-window leg: the b-decode is invariant (xb = 0 on both sides)
  have hb : (⟨decodeReg (fun i => bBase w bits + i) bits
              (nat_to_funbool (cosetDim w bits)
                (idealPerm w bits N cm mult kInv hN hfwd hbwd idx).val),
            decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
        ∈ cosetWindow (2 ^ bits) N cm 0
      ↔ (⟨decodeReg (fun i => bBase w bits + i) bits
              (nat_to_funbool (cosetDim w bits) idx.val),
            decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
        ∈ cosetWindow (2 ^ bits) N cm 0 := by
    rw [show (⟨decodeReg (fun i => bBase w bits + i) bits
              (nat_to_funbool (cosetDim w bits)
                (idealPerm w bits N cm mult kInv hN hfwd hbwd idx).val),
            decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
        = ⟨decodeReg (fun i => bBase w bits + i) bits
              (nat_to_funbool (cosetDim w bits) idx.val),
            decodeReg_lt_two_pow _ _ _⟩ from
      Fin.ext (bDecode_idealPerm w bits N cm mult kInv hN hfwd hbwd idx)]
  rw [hb]
  -- a-window leg
  have hava : decodeReg (fun i => aBase w + i) bits
        (nat_to_funbool (cosetDim w bits) idx.val) < 2 ^ bits := decodeReg_lt_two_pow _ _ _
  have ha : (⟨decodeReg (fun i => aBase w + i) bits
              (nat_to_funbool (cosetDim w bits)
                (idealPerm w bits N cm mult kInv hN hfwd hbwd idx).val),
            decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
        ∈ cosetWindow (2 ^ bits) N cm ((mult * z) % N)
      ↔ (⟨decodeReg (fun i => aBase w + i) bits
              (nat_to_funbool (cosetDim w bits) idx.val),
            hava⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm z := by
    -- rewrite the a-decode of idealPerm idx to guardedShift mult of the a-decode of idx
    rw [show (⟨decodeReg (fun i => aBase w + i) bits
              (nat_to_funbool (cosetDim w bits)
                (idealPerm w bits N cm mult kInv hN hfwd hbwd idx).val),
            decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
        = ⟨guardedShift (2 ^ bits) N mult
              (decodeReg (fun i => aBase w + i) bits
                (nat_to_funbool (cosetDim w bits) idx.val)),
            RunwayShiftPerm.guarded_lt (2 ^ bits) N mult _ (by omega) hava⟩ from
      Fin.ext (aDecode_idealPerm w bits N cm mult kInv hN hfwd hbwd idx)]
    exact (aWindow_guardedShift bits N cm mult kInv z _ hN hfwd hbwd hfull hz hava).symm
  rw [ha]

/-- **D3-symm — the symm support transport (the form P1.1d consumes).**  With
    `idealFi := permState idealPerm.symm`, so `(idealFi · v) idx = v (idealPerm.symm idx)`, the
    support test reads through `idealPerm.symm`.  Derived from `inSupport_idealPerm_fwd` at
    `idx' := idealPerm.symm idx` via `Equiv.apply_symm_apply`. -/
theorem inSupport_idealPerm_symm (w bits N cm mult kInv z : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (hfull : 2 ^ cm * N ≤ 2 ^ bits) (hz : z < N)
    (idx : Fin (2 ^ cosetDim w bits)) :
    inSupport w bits N cm z 0
        ((idealPerm w bits N cm mult kInv hN hfwd hbwd).symm idx)
      ↔ inSupport w bits N cm ((mult * z) % N) 0 idx := by
  have h := inSupport_idealPerm_fwd w bits N cm mult kInv z hN hfwd hbwd hfull hz
    ((idealPerm w bits N cm mult kInv hN hfwd hbwd).symm idx)
  rwa [Equiv.apply_symm_apply] at h

/-! ## §6. P1.1c/d — the clean ideal column identity. -/

/-- **P1.1c/d — the clean ideal coset-shift column identity.**  Under the FULL-BLOCKS budget
    `2^cm·N ≤ 2^bits`, the coprimality data, and `z < N`, the ideal permutation (in the pinned
    orientation `permState idealPerm.symm`) sends the two-register coset input `cosetInputVec z 0`
    to the shifted input `cosetInputVec ((mult·z)%N) 0`.  Pure support/amplitude bookkeeping: at
    every column `idx`, both sides are `(1/√2^cm)²` on support and `0` off, and
    `inSupport_idealPerm_symm` matches the two support memberships.  No physical gate, no bad set,
    no QPE induction — this is the clean ideal step P1.2 / H3.2 consume. -/
theorem idealShift_cosetInputVec (w bits N cm mult kInv z : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (hfull : 2 ^ cm * N ≤ 2 ^ bits) (hz : z < N) :
    permState (idealPerm w bits N cm mult kInv hN hfwd hbwd).symm
        (cosetInputVec w bits N cm z 0)
      = cosetInputVec w bits N cm ((mult * z) % N) 0 := by
  funext idx col
  have hcol : col = 0 := Subsingleton.elim _ _
  subst hcol
  show cosetInputVec w bits N cm z 0
        ((idealPerm w bits N cm mult kInv hN hfwd hbwd).symm idx) 0
      = cosetInputVec w bits N cm ((mult * z) % N) 0 idx 0
  rw [cosetInputVec_amp w bits N cm z 0 _,
      cosetInputVec_amp w bits N cm ((mult * z) % N) 0 idx]
  exact if_congr
    (inSupport_idealPerm_symm w bits N cm mult kInv z hN hfwd hbwd hfull hz idx) rfl rfl

end FormalRV.Shor.GidneyInPlace.IdealPermLift
