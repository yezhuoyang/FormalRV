/-
  FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthRunwayGate —
  SYNTH-4 (attempt A): realize the IDEAL RUNWAY SHIFT on the a-block, and prove
  the route-S COLUMN IDENTITY.
  ════════════════════════════════════════════════════════════════════════════
-/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthPerm
import FormalRV.Shor.GidneyInPlace.Ideal.Def.IdealPermLift
import FormalRV.Shor.GidneyInPlace.InPlace.Def.InPlaceSwapBlocks
import FormalRV.Shor.GidneyInPlace.Gate.Def.GateReversible

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthRunwayGate

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthPerm
open FormalRV.SQIRPort
open FormalRV.Framework (nat_to_funbool)
open FormalRV.Shor.WindowedCircuit (decodeReg_lt_two_pow)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg
  (aBase bBase scratchClean cosetInputTwoReg cosetInputTwoReg_funboolNat
   scratchClean_congr_offBlocks nat_to_funbool_funboolNat_agree)
open FormalRV.Shor.GidneyInPlace.RunwayShiftPerm (guardedShift resShiftPerm guarded_lt)
open FormalRV.Shor.GidneyInPlace.GatePerm
  (gateToPerm funboolNat funboolEquiv extendBool applyFin)
open FormalRV.Shor.GidneyInPlace.CuccaroGatePerm (gateToPerm_funboolNat)
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_eq_permState)
open FormalRV.Shor.GidneyInPlace.ApproxOp (permState)
open FormalRV.Shor.GidneyInPlace.InPlaceReverseLeg (extendBool_applyFin)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow)
open FormalRV.Shor.GidneyInPlace.CosetInputSupport (inSupport cosetInputVec_amp)
open FormalRV.Shor.GidneyInPlace.IdealPermLift (aWindow_guardedShift)
open FormalRV.Shor.GidneyInPlace.GateReversible (applyNat_reverse_cancel)
open scoped Classical

/-! ## §0. The a-block register and the runway ancilla. -/

/-- The a-block register: the `bits` wires `[aBase, aBase+bits)`. -/
def aReg (w bits : Nat) : List Nat := (List.range bits).map (fun i => aBase w + i)

/-- The runway ancilla: the `bits` CLEAN temp wires `[1+2w+2·bits, 1+2w+3·bits)`. -/
def runAnc (w bits : Nat) : List Nat := (List.range bits).map (fun i => 1 + 2 * w + 2 * bits + i)

theorem aReg_length (w bits : Nat) : (aReg w bits).length = bits := by
  unfold aReg; rw [List.length_map, List.length_range]

theorem runAnc_length (w bits : Nat) : (runAnc w bits).length = bits := by
  unfold runAnc; rw [List.length_map, List.length_range]

theorem aReg_getElem (w bits : Nat) (i : Nat) (hi : i < (aReg w bits).length) :
    (aReg w bits)[i] = aBase w + i := by
  unfold aReg
  rw [List.getElem_map, List.getElem_range]

/-- `regIdx (aReg w bits) i = aBase w + i` for `i < bits`. -/
theorem regIdx_aReg (w bits : Nat) (i : Nat) (hi : i < bits) :
    regIdx (aReg w bits) i = aBase w + i := by
  unfold regIdx
  have hi' : i < (aReg w bits).length := by rw [aReg_length]; exact hi
  rw [List.getD_eq_getElem (aReg w bits) 0 hi', aReg_getElem w bits i hi']

theorem aReg_nodup (w bits : Nat) : (aReg w bits).Nodup := by
  unfold aReg
  apply List.Nodup.map (fun a b h => by omega) List.nodup_range

theorem runAnc_nodup (w bits : Nat) : (runAnc w bits).Nodup := by
  unfold runAnc
  apply List.Nodup.map (fun a b h => by omega) List.nodup_range

theorem mem_aReg (w bits p : Nat) : p ∈ aReg w bits ↔ ∃ i, i < bits ∧ aBase w + i = p := by
  unfold aReg
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, List.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, List.mem_range.mpr hi, rfl⟩

theorem mem_runAnc (w bits p : Nat) :
    p ∈ runAnc w bits ↔ ∃ i, i < bits ∧ 1 + 2 * w + 2 * bits + i = p := by
  unfold runAnc
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, List.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, List.mem_range.mpr hi, rfl⟩

/-- The runway ancilla is disjoint from the a-block (temp wires are above the b-block). -/
theorem runAnc_disj_aReg (w bits : Nat) : ∀ a ∈ runAnc w bits, a ∉ aReg w bits := by
  intro a ha hra
  obtain ⟨i, hi, rfl⟩ := (mem_runAnc w bits a).mp ha
  obtain ⟨j, hj, hj2⟩ := (mem_aReg w bits _).mp hra
  unfold aBase at hj2; omega

/-! ## §1. The runway gate. -/

/-- **The runway gate.**  `permGate` the a-block register with the guarded residue-shift
    permutation `resShiftPerm` (its `.val` action is `guardedShift mult`), using the clean
    temp wires as ancilla.  The `aReg_length` rewrite transports the perm of `Fin (2^bits)`
    to a perm of `Fin (2^(aReg w bits).length)`. -/
noncomputable def runwayGate (w bits N cm mult kInv : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1) : Gate :=
  permGate (aReg w bits)
    ((aReg_length w bits).symm ▸ resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd)
    (runAnc w bits)

/-- Applying a length-transported perm reads off the same value as the untransported one. -/
theorem perm_cast_apply {a b : Nat} (h : a = b) (τ : Equiv.Perm (Fin (2 ^ a)))
    (v : Nat) (hb : v < 2 ^ b) (ha : v < 2 ^ a) :
    ((h ▸ τ) ⟨v, hb⟩ : Fin (2 ^ b)).val = (τ ⟨v, ha⟩).val := by
  subst h; rfl

/-- The runway gate's value permutation is `guardedShift mult` on in-range values. -/
theorem runway_permOnVal (w bits N cm mult kInv : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (v : Nat) (hv : v < 2 ^ bits) :
    permOnVal (aReg w bits)
        ((aReg_length w bits).symm ▸ resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd) v
      = guardedShift (2 ^ bits) N mult v := by
  have hlen := aReg_length w bits
  have hvL : v < 2 ^ (aReg w bits).length := by rw [hlen]; exact hv
  unfold permOnVal
  rw [dif_pos hvL]
  rw [perm_cast_apply (aReg_length w bits).symm
        (resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd) v hvL hv]
  rfl

/-- **`runwayGate_RegAct`.**  On the a-block register with the clean temp-wire ancilla,
    `runwayGate` applies the guarded residue shift `guardedShift mult` to the a-block VALUE,
    framing everything else and restoring the ancilla. -/
theorem runwayGate_RegAct (w bits N cm mult kInv : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1) :
    RegAct (runwayGate w bits N cm mult kInv hN hfwd hbwd) (aReg w bits) (runAnc w bits)
      (permOnVal (aReg w bits)
        ((aReg_length w bits).symm ▸ resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd)) := by
  unfold runwayGate
  exact permGate_RegAct (aReg w bits)
    ((aReg_length w bits).symm ▸ resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd)
    (runAnc w bits) (aReg_nodup w bits) (runAnc_nodup w bits) (runAnc_disj_aReg w bits)
    (by rw [aReg_length, runAnc_length]; omega)

theorem aReg_lt_cosetDim (w bits : Nat) : ∀ a ∈ aReg w bits, a < cosetDim w bits := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := (mem_aReg w bits a).mp ha
  unfold aBase cosetDim; omega

theorem runAnc_lt_cosetDim (w bits : Nat) : ∀ a ∈ runAnc w bits, a < cosetDim w bits := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := (mem_runAnc w bits a).mp ha
  unfold cosetDim; omega

/-- **`runwayGate_wellTyped`.** -/
theorem runwayGate_wellTyped (w bits N cm mult kInv : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1) :
    Gate.WellTyped (cosetDim w bits) (runwayGate w bits N cm mult kInv hN hfwd hbwd) := by
  unfold runwayGate
  exact permGate_wellTyped (aReg w bits)
    ((aReg_length w bits).symm ▸ resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd)
    (runAnc w bits) (cosetDim w bits) (aReg_nodup w bits) (runAnc_nodup w bits)
    (runAnc_disj_aReg w bits) (by unfold cosetDim; omega)
    (aReg_lt_cosetDim w bits) (runAnc_lt_cosetDim w bits)
    (by rw [aReg_length, runAnc_length]; omega)

/-! ## §1b. Generic reverse-RegAct (for the scratch-clean reverse direction). -/

/-- A scratch-clean state forces the runway-ancilla (temp) wires to `false`. -/
theorem runAnc_clean_of_scratchClean (w bits : Nat) (g : Nat → Bool)
    (hcl : scratchClean w bits g) : ∀ a ∈ runAnc w bits, g a = false := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := (mem_runAnc w bits a).mp ha
  obtain ⟨_, h2⟩ := hcl
  refine h2 (1 + 2 * w + 2 * bits + i) (by unfold cosetDim; omega) ?_ ?_ ?_
  · unfold aBase; omega
  · unfold bBase; omega
  · unfold ulookup_ctrl_idx; omega

/-- Writing a register's CURRENT value is the identity. -/
theorem setReg_self (reg : List Nat) (f : Nat → Bool) (hnd : reg.Nodup) :
    setReg reg (regVal reg f) f = f := by
  funext p
  by_cases hp : p ∈ reg
  · obtain ⟨i, hi, rfl⟩ := (mem_reg_iff_regIdx reg p).mp hp
    rw [setReg_at reg _ f hnd i hi, regVal_testBit reg f i hi]
  · rw [setReg_frame reg _ f p hp]

/-- **Generic reverse-RegAct.**  If `g` acts as the range-preserving value map `σ` on
    `reg` (clean ancilla `anc`), and `τ` is a range-preserving right inverse of `σ` on
    `[0, 2^k)`, then `reverse g` acts as `τ`.  (Used only via its frame consequence: the
    reverse gate also leaves every off-register wire fixed on clean states.) -/
theorem RegAct_reverse (g : Gate) (reg anc : List Nat) (dim : Nat)
    (σ τ : Nat → Nat) (hnd : reg.Nodup) (hdisj : ∀ a ∈ anc, a ∉ reg)
    (hwt : Gate.WellTyped dim g) (hga : RegAct g reg anc σ)
    (hτrange : ∀ v, v < 2 ^ reg.length → τ v < 2 ^ reg.length)
    (hστ : ∀ v, v < 2 ^ reg.length → σ (τ v) = v) :
    RegAct (GateReversible.Gate.reverse g) reg anc τ := by
  obtain ⟨_, hact⟩ := hga
  refine ⟨hτrange, ?_⟩
  intro h hclean
  set v := regVal reg h with hv
  have hvlt : v < 2 ^ reg.length := hv ▸ regVal_lt reg h
  set f := setReg reg (τ v) h with hf
  have hfclean : ∀ a ∈ anc, f a = false := setReg_clean reg anc (τ v) h hdisj hclean
  have hfval : regVal reg f = τ v := regVal_setReg reg (τ v) h hnd (hτrange v hvlt)
  have hgf : Gate.applyNat g f = setReg reg (σ (τ v)) f := by rw [hact f hfclean, hfval]
  rw [hστ v hvlt] at hgf
  have hsv : setReg reg v f = h := by
    rw [hf, setReg_setReg reg (τ v) v h hnd, hv, setReg_self reg h hnd]
  rw [hsv] at hgf
  have hcancel := applyNat_reverse_cancel g dim hwt f
  rw [hgf] at hcancel
  rw [hcancel, hf]

/-- The runway gate's permutation, with the INVERSE multiplier `kInv` (a right inverse
    of `permOnVal … resShiftPerm`). -/
theorem runway_permOnVal_inv (w bits N cm mult kInv : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (v : Nat) (hv : v < 2 ^ bits) :
    permOnVal (aReg w bits)
        ((aReg_length w bits).symm ▸ resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd)
        (guardedShift (2 ^ bits) N kInv v)
      = v := by
  rw [runway_permOnVal w bits N cm mult kInv hN hfwd hbwd _
        (guarded_lt (2 ^ bits) N kInv v (by omega) hv)]
  -- guardedShift mult (guardedShift kInv v) = v   (inverse law with kInv·mult ≡ 1)
  exact FormalRV.Shor.GidneyInPlace.RunwayShiftPerm.guarded_leftinv (2 ^ bits) N kInv mult v hN hbwd

/-- **`reverse runwayGate` frames every wire off the a-block** (on scratch-clean states). -/
theorem reverse_runwayGate_frame_off_aReg (w bits N cm mult kInv : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (g : Nat → Bool) (hcl : scratchClean w bits g) (p : Nat) (hp : p ∉ aReg w bits) :
    Gate.applyNat (GateReversible.Gate.reverse (runwayGate w bits N cm mult kInv hN hfwd hbwd)) g p
      = g p := by
  have hrev : RegAct (GateReversible.Gate.reverse (runwayGate w bits N cm mult kInv hN hfwd hbwd))
      (aReg w bits) (runAnc w bits)
      (fun v => guardedShift (2 ^ bits) N kInv v) := by
    refine RegAct_reverse (runwayGate w bits N cm mult kInv hN hfwd hbwd) (aReg w bits)
      (runAnc w bits) (cosetDim w bits)
      (permOnVal (aReg w bits)
        ((aReg_length w bits).symm ▸ resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd))
      (fun v => guardedShift (2 ^ bits) N kInv v)
      (aReg_nodup w bits) (runAnc_disj_aReg w bits)
      (runwayGate_wellTyped w bits N cm mult kInv hN hfwd hbwd)
      (runwayGate_RegAct w bits N cm mult kInv hN hfwd hbwd) ?_ ?_
    · intro v hv
      rw [aReg_length] at hv ⊢
      exact guarded_lt (2 ^ bits) N kInv v (by omega) hv
    · intro v hv
      rw [aReg_length] at hv
      exact runway_permOnVal_inv w bits N cm mult kInv hN hfwd hbwd v hv
  obtain ⟨_, hact⟩ := hrev
  rw [hact g (runAnc_clean_of_scratchClean w bits g hcl)]
  exact setReg_frame (aReg w bits) _ g p hp

/-! ## §2. Per-support-index action.

The runway ancilla is forced clean on scratch-clean states, so `permGate_RegAct` applies
on the whole `cosetInputVec` support; the a-block value is shifted by `guardedShift mult`,
the b-block and scratch are framed. -/

/-- `decodeReg` depends only on the index family on `[0,n)`. -/
theorem decodeReg_idx_congr (idx idx' : Nat → Nat) (n : Nat) (f : Nat → Bool)
    (h : ∀ i, i < n → idx i = idx' i) :
    decodeReg idx n f = decodeReg idx' n f := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · rw [FormalRV.Shor.WindowedCircuit.decodeReg_testBit idx n f j hj,
        FormalRV.Shor.WindowedCircuit.decodeReg_testBit idx' n f j hj, h j hj]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (decodeReg_lt_two_pow _ _ _)
          (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (decodeReg_lt_two_pow _ _ _)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- `regVal (aReg w bits)` reads the a-block as the coset layout's a-decode. -/
theorem regVal_aReg_eq (w bits : Nat) (g : Nat → Bool) :
    regVal (aReg w bits) g = decodeReg (fun i => aBase w + i) bits g := by
  unfold regVal
  rw [show (aReg w bits).length = bits from aReg_length w bits]
  exact decodeReg_idx_congr (regIdx (aReg w bits)) (fun i => aBase w + i) bits g
    (fun i hi => regIdx_aReg w bits i hi)

/-- **The a-decode of `applyNat runwayGate g` is `guardedShift mult` of the a-decode of `g`.**
    On a scratch-clean `g` (so the temp ancilla is clean), `runwayGate` writes the a-block to
    the shifted value. -/
theorem aDecode_runwayGate (w bits N cm mult kInv : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (g : Nat → Bool) (hcl : scratchClean w bits g) :
    decodeReg (fun i => aBase w + i) bits
        (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g)
      = guardedShift (2 ^ bits) N mult
          (decodeReg (fun i => aBase w + i) bits g) := by
  -- the a-value of g
  set va := decodeReg (fun i => aBase w + i) bits g with hvadef
  have hva : va < 2 ^ bits := hvadef ▸ decodeReg_lt_two_pow _ _ _
  have hrv : regVal (aReg w bits) g = va := by rw [regVal_aReg_eq]
  -- permOnVal evaluated at va is guardedShift mult va
  have hperm : permOnVal (aReg w bits)
      ((aReg_length w bits).symm ▸ resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd)
      (regVal (aReg w bits) g) = guardedShift (2 ^ bits) N mult va := by
    rw [hrv]; exact runway_permOnVal w bits N cm mult kInv hN hfwd hbwd va hva
  -- the written value is in range
  have hwlt : permOnVal (aReg w bits)
      ((aReg_length w bits).symm ▸ resShiftPerm (2 ^ bits) N mult kInv hN hfwd hbwd)
      (regVal (aReg w bits) g) < 2 ^ (aReg w bits).length := by
    rw [hperm, aReg_length]
    exact guarded_lt (2 ^ bits) N mult va (by omega) hva
  obtain ⟨_, hact⟩ := runwayGate_RegAct w bits N cm mult kInv hN hfwd hbwd
  rw [hact g (runAnc_clean_of_scratchClean w bits g hcl)]
  -- a-decode of the written register: regVal of setReg = written value
  rw [← regVal_aReg_eq w bits, regVal_setReg (aReg w bits) _ g (aReg_nodup w bits) hwlt, hperm]

/-- **`runwayGate` frames every wire off the a-block** (on scratch-clean states). -/
theorem runwayGate_frame_off_aReg (w bits N cm mult kInv : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (g : Nat → Bool) (hcl : scratchClean w bits g) (p : Nat) (hp : p ∉ aReg w bits) :
    Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g p = g p := by
  obtain ⟨_, hact⟩ := runwayGate_RegAct w bits N cm mult kInv hN hfwd hbwd
  rw [hact g (runAnc_clean_of_scratchClean w bits g hcl)]
  exact setReg_frame (aReg w bits) _ g p hp

/-- A position `p` off the a-block `[aBase, aBase+bits)` (with `p < cosetDim`) is not in `aReg`. -/
theorem not_mem_aReg_of_off (w bits p : Nat) (hoff : ¬ (aBase w ≤ p ∧ p < aBase w + bits)) :
    p ∉ aReg w bits := by
  intro hp
  obtain ⟨i, hi, rfl⟩ := (mem_aReg w bits p).mp hp
  exact hoff ⟨Nat.le_add_right _ _, by omega⟩

/-- **The b-decode is invariant under `runwayGate`** (on scratch-clean states; b-block off a-block). -/
theorem bDecode_runwayGate (w bits N cm mult kInv : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (g : Nat → Bool) (hcl : scratchClean w bits g) :
    decodeReg (fun i => bBase w bits + i) bits
        (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g)
      = decodeReg (fun i => bBase w bits + i) bits g := by
  refine decodeReg_ext _ _ _ _ (fun i hi => ?_)
  exact runwayGate_frame_off_aReg w bits N cm mult kInv hN hfwd hbwd g hcl
    (bBase w bits + i) (not_mem_aReg_of_off w bits _ (by unfold aBase bBase; omega))

/-- **Scratch-cleanliness is invariant under `runwayGate`** (scratch off a-block). -/
theorem scratchClean_runwayGate (w bits N cm mult kInv : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (g : Nat → Bool) (hcl : scratchClean w bits g) :
    scratchClean w bits (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g) := by
  refine (scratchClean_congr_offBlocks w bits _ g (fun p _ hna _ => ?_)).mpr hcl
  exact runwayGate_frame_off_aReg w bits N cm mult kInv hN hfwd hbwd g hcl p
    (not_mem_aReg_of_off w bits p hna)

/-- **Reverse scratch-clean direction.**  If `applyNat runwayGate g` is scratch-clean, so is
    `g`.  (The reverse gate, run on the clean image, frames every off-a-block wire back, and
    `scratchClean` reads only off-a-block wires.) -/
theorem scratchClean_of_runwayGate (w bits N cm mult kInv : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (g : Nat → Bool)
    (hcl' : scratchClean w bits (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g)) :
    scratchClean w bits g := by
  set g' := Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g with hg'
  have hgrec : Gate.applyNat (GateReversible.Gate.reverse
      (runwayGate w bits N cm mult kInv hN hfwd hbwd)) g' = g := by
    rw [hg']
    exact applyNat_reverse_cancel (runwayGate w bits N cm mult kInv hN hfwd hbwd)
      (cosetDim w bits) (runwayGate_wellTyped w bits N cm mult kInv hN hfwd hbwd) g
  -- scratchClean reads only off-a-block wires, where reverse frames g' back to g.
  refine (scratchClean_congr_offBlocks w bits g' g (fun p _ hna _ => ?_)).mp hcl'
  rw [← hgrec]
  exact (reverse_runwayGate_frame_off_aReg w bits N cm mult kInv hN hfwd hbwd g' hcl' p
    (not_mem_aReg_of_off w bits p hna)).symm

/-- **The scratch-clean iff under `runwayGate`.** -/
theorem scratchClean_runwayGate_iff (w bits N cm mult kInv : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1) (g : Nat → Bool) :
    scratchClean w bits (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g)
      ↔ scratchClean w bits g :=
  ⟨scratchClean_of_runwayGate w bits N cm mult kInv hN hfwd hbwd g,
   scratchClean_runwayGate w bits N cm mult kInv hN hfwd hbwd g⟩

/-! ## §3. The support transport and the column identity. -/

/-- **Per-basis-state support transport.**  For any bit-function `g`, `applyNat runwayGate g`
    lies in the support of `cosetInputVec ((mult·z)%N) 0` iff `g` lies in the support of
    `cosetInputVec z 0`.  (Forward via the clean-state transports + `aWindow_guardedShift`;
    the scratch leg is the iff `scratchClean_runwayGate_iff`, so the dirty case matches too.) -/
theorem support_transport_applyNat (w bits N cm mult kInv z : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (hfull : 2 ^ cm * N ≤ 2 ^ bits) (hz : z < N) (g : Nat → Bool) :
    (scratchClean w bits (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g)
      ∧ (⟨decodeReg (fun i => aBase w + i) bits
            (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
            ∈ cosetWindow (2 ^ bits) N cm ((mult * z) % N)
      ∧ (⟨decodeReg (fun i => bBase w bits + i) bits
            (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
            ∈ cosetWindow (2 ^ bits) N cm 0)
    ↔ (scratchClean w bits g
      ∧ (⟨decodeReg (fun i => aBase w + i) bits g, decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
            ∈ cosetWindow (2 ^ bits) N cm z
      ∧ (⟨decodeReg (fun i => bBase w bits + i) bits g, decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
            ∈ cosetWindow (2 ^ bits) N cm 0) := by
  constructor
  · rintro ⟨hsc', ha', hb'⟩
    have hsc : scratchClean w bits g :=
      (scratchClean_runwayGate_iff w bits N cm mult kInv hN hfwd hbwd g).mp hsc'
    refine ⟨hsc, ?_, ?_⟩
    · -- a-window: rewrite the shifted a-decode and apply aWindow_guardedShift
      have hava : decodeReg (fun i => aBase w + i) bits g < 2 ^ bits := decodeReg_lt_two_pow _ _ _
      rw [show (⟨decodeReg (fun i => aBase w + i) bits
              (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g),
            decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
          = ⟨guardedShift (2 ^ bits) N mult (decodeReg (fun i => aBase w + i) bits g),
              guarded_lt (2 ^ bits) N mult _ (by omega) hava⟩ from
        Fin.ext (aDecode_runwayGate w bits N cm mult kInv hN hfwd hbwd g hsc)] at ha'
      exact (aWindow_guardedShift bits N cm mult kInv z _ hN hfwd hbwd hfull hz hava).mpr ha'
    · -- b-window: the b-decode is invariant
      rwa [show (⟨decodeReg (fun i => bBase w bits + i) bits
              (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g),
            decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
          = ⟨decodeReg (fun i => bBase w bits + i) bits g, decodeReg_lt_two_pow _ _ _⟩ from
        Fin.ext (bDecode_runwayGate w bits N cm mult kInv hN hfwd hbwd g hsc)] at hb'
  · rintro ⟨hsc, ha, hb⟩
    refine ⟨scratchClean_runwayGate w bits N cm mult kInv hN hfwd hbwd g hsc, ?_, ?_⟩
    · have hava : decodeReg (fun i => aBase w + i) bits g < 2 ^ bits := decodeReg_lt_two_pow _ _ _
      rw [show (⟨decodeReg (fun i => aBase w + i) bits
              (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g),
            decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
          = ⟨guardedShift (2 ^ bits) N mult (decodeReg (fun i => aBase w + i) bits g),
              guarded_lt (2 ^ bits) N mult _ (by omega) hava⟩ from
        Fin.ext (aDecode_runwayGate w bits N cm mult kInv hN hfwd hbwd g hsc)]
      exact (aWindow_guardedShift bits N cm mult kInv z _ hN hfwd hbwd hfull hz hava).mp ha
    · rw [show (⟨decodeReg (fun i => bBase w bits + i) bits
              (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g),
            decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
          = ⟨decodeReg (fun i => bBase w bits + i) bits g, decodeReg_lt_two_pow _ _ _⟩ from
        Fin.ext (bDecode_runwayGate w bits N cm mult kInv hN hfwd hbwd g hsc)]
      exact hb

/-- The forward `permState` action of the runway gate's permutation sends the SHIFTED coset
    input to the unshifted one (the orientation `swapAB_cosetInputTwoReg` uses). -/
theorem runway_permState_key (w bits N cm mult kInv z : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (hfull : 2 ^ cm * N ≤ 2 ^ bits) (hz : z < N) :
    permState (gateToPerm (runwayGate w bits N cm mult kInv hN hfwd hbwd) (cosetDim w bits)
        (runwayGate_wellTyped w bits N cm mult kInv hN hfwd hbwd))
        (cosetInputVec w bits N cm ((mult * z) % N) 0)
      = cosetInputVec w bits N cm z 0 := by
  set hwt := runwayGate_wellTyped w bits N cm mult kInv hN hfwd hbwd with hhwt
  set σ := gateToPerm (runwayGate w bits N cm mult kInv hN hfwd hbwd) (cosetDim w bits) hwt with hσ
  funext idx col
  obtain rfl : col = 0 := Subsingleton.elim col 0
  obtain ⟨φ, hidx⟩ : ∃ φ, funboolNat (cosetDim w bits) φ = idx :=
    ⟨(funboolEquiv (cosetDim w bits)).symm idx, by
      exact Equiv.apply_symm_apply (funboolEquiv (cosetDim w bits)) idx⟩
  show cosetInputTwoReg w bits N cm ((mult * z) % N) 0 (σ idx) 0
    = cosetInputTwoReg w bits N cm z 0 idx 0
  rw [← hidx, hσ, gateToPerm_funboolNat (runwayGate w bits N cm mult kInv hN hfwd hbwd)
        (cosetDim w bits) hwt φ,
      cosetInputTwoReg_funboolNat w bits N cm ((mult * z) % N) 0
        (applyFin (runwayGate w bits N cm mult kInv hN hfwd hbwd) (cosetDim w bits) φ),
      cosetInputTwoReg_funboolNat w bits N cm z 0 φ,
      extendBool_applyFin (runwayGate w bits N cm mult kInv hN hfwd hbwd) (cosetDim w bits) hwt φ]
  set g := extendBool (cosetDim w bits) φ with hg
  by_cases hsc : scratchClean w bits g
  · rw [if_pos (scratchClean_runwayGate w bits N cm mult kInv hN hfwd hbwd g hsc), if_pos hsc]
    -- a-decode of g' = guardedShift mult (a-decode g); b-decode invariant
    have hava : decodeReg (fun i => aBase w + i) bits g < 2 ^ bits := decodeReg_lt_two_pow _ _ _
    rw [show (⟨decodeReg (fun i => aBase w + i) bits
            (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
        = ⟨guardedShift (2 ^ bits) N mult (decodeReg (fun i => aBase w + i) bits g),
            guarded_lt (2 ^ bits) N mult _ (by omega) hava⟩ from
      Fin.ext (aDecode_runwayGate w bits N cm mult kInv hN hfwd hbwd g hsc)]
    rw [show (⟨decodeReg (fun i => bBase w bits + i) bits
            (Gate.applyNat (runwayGate w bits N cm mult kInv hN hfwd hbwd) g),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
        = ⟨decodeReg (fun i => bBase w bits + i) bits g, decodeReg_lt_two_pow _ _ _⟩ from
      Fin.ext (bDecode_runwayGate w bits N cm mult kInv hN hfwd hbwd g hsc)]
    congr 1
    exact if_congr
      (aWindow_guardedShift bits N cm mult kInv z _ hN hfwd hbwd hfull hz hava).symm rfl rfl
  · rw [if_neg hsc,
        if_neg (fun hc => hsc ((scratchClean_runwayGate_iff w bits N cm mult kInv hN hfwd hbwd g).mp hc))]

/-- **THE ROUTE-S COLUMN IDENTITY.**  Under the FULL-BLOCKS budget `2^cm·N ≤ 2^bits`, the
    coprimality data, and `z < N`, the runway gate realizes the ideal coset shift on the
    two-register coset input: it sends `cosetInputVec z 0` to `cosetInputVec ((mult·z)%N) 0`.
    This is exactly the shape M4's `hf_runway_of_column_identity` consumes. -/
theorem runwayGate_column_identity (w bits N cm mult kInv z : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (hfull : 2 ^ cm * N ≤ 2 ^ bits) (hz : z < N) :
    Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (runwayGate w bits N cm mult kInv hN hfwd hbwd))
        * cosetInputVec w bits N cm z 0
      = cosetInputVec w bits N cm ((mult * z) % N) 0 := by
  have key := runway_permState_key w bits N cm mult kInv z hN hfwd hbwd hfull hz
  rw [uc_eval_eq_permState (runwayGate w bits N cm mult kInv hN hfwd hbwd) (cosetDim w bits)
        (runwayGate_wellTyped w bits N cm mult kInv hN hfwd hbwd), ← key]
  funext idx col
  simp only [permState, Equiv.apply_symm_apply]

end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthRunwayGate
