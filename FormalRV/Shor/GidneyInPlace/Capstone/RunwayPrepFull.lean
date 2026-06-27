/-
  FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepFull — assembling the FULL
  `E2runwayInitPrep` prep circuit for the `E2runwayInit` runway state (gap-3).
  ════════════════════════════════════════════════════════════════════════════

  GOAL (the headline).
      uc_eval (E2runwayInitPrep …) * basis0 (m + cosetDim w bits)
          = E2runwayInit m w bits N cm     (modulo the dimension cast).

  This module BUILDS ON the rock-solid kernel-clean sub-block coset prep
  `RunwayPrepSubBlock.cosetPrepSubGate_column_identity` (the a-block permGate that
  consumes an H-window genTwoReg and outputs the coset-window genTwoReg, framing
  b/ctrl/scratch) and `RunwayPrepCore` (the npar_H closed forms).

  DELIVERED HERE.
   (2a)  The B-BLOCK MIRROR.  `bReg`/(reused `runAnc` as) the b-block ancilla, the
         b-decode lemmas, and `cosetPrepSubGateB_column_identity` — the exact mirror
         of `cosetPrepSubGate_column_identity` for the b-block (framing the a-block).
         A near-verbatim port from `RunwayPrepSubBlock` with `aReg → bReg`,
         `aBase → bBase`.  ROCK-SOLID, kernel-clean.

   (2b)  INTERIOR-BLOCK npar_H.  See §B.  Status / precise blocker documented there.

   (2c)  ASSEMBLE.  See §C.  Status / precise remaining goal documented there.

  Kernel-clean: axioms ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`,
  no `native_decide`.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepSubBlock
import FormalRV.QFT.TwoRegisterQFT.Circuit
import FormalRV.Arithmetic.MCPBridge

namespace FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepFull

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap
  (regVal setReg RegAct regVal_lt setReg_clean regVal_setReg setReg_frame)
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthPerm
  (permGate permGate_RegAct permGate_wellTyped permOnVal)
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthRunwayGate
  (runAnc runAnc_length runAnc_nodup perm_cast_apply RegAct_reverse
   runAnc_clean_of_scratchClean)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg
  (aBase bBase scratchClean cosetInputTwoReg cosetInputTwoReg_funboolNat
   scratchClean_congr_offBlocks)
open FormalRV.Shor.GidneyInPlace.GatePerm
  (gateToPerm funboolNat funboolEquiv extendBool applyFin)
open FormalRV.Shor.GidneyInPlace.CuccaroGatePerm (gateToPerm_funboolNat)
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_eq_permState)
open FormalRV.Shor.GidneyInPlace.ApproxOp (permState cosetState)
open FormalRV.Shor.GidneyInPlace.InPlaceReverseLeg (extendBool_applyFin)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow)
open FormalRV.Shor.WindowedCircuit (decodeReg_lt_two_pow)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepCore
  (σ_k σ_k_window σ_k_not_window σ_k_bijOn hWindow cWindow)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepSubBlock
  (genTwoReg genTwoReg_funboolNat genTwoReg_eq_cosetInputTwoReg genTwoReg_eq_cosetInputVec
   σ_k_window_iff winA)
open FormalRV.Shor.GidneyInPlace.GateReversible (applyNat_reverse_cancel)
open scoped Classical

/-! ## §A. (2a) THE B-BLOCK MIRROR.

The b-block register `bReg w bits` is the `bits` wires `[bBase, bBase+bits)`.  Its
clean ancilla is the SAME runway temp block `runAnc w bits` at `[1+2w+2·bits,
1+2w+3·bits)` — disjoint from BOTH the a-block and the b-block — so we reuse it.

Everything below is a verbatim port of the `RunwayPrepSubBlock` a-block development
with `aReg → bReg`, `aBase → bBase`, framing the a-block in place of the b-block. -/

/-- The b-block register: the `bits` wires `[bBase, bBase+bits)`. -/
def bReg (w bits : Nat) : List Nat := (List.range bits).map (fun i => bBase w bits + i)

theorem bReg_length (w bits : Nat) : (bReg w bits).length = bits := by
  unfold bReg; rw [List.length_map, List.length_range]

theorem bReg_getElem (w bits : Nat) (i : Nat) (hi : i < (bReg w bits).length) :
    (bReg w bits)[i] = bBase w bits + i := by
  unfold bReg
  rw [List.getElem_map, List.getElem_range]

/-- `regIdx (bReg w bits) i = bBase w bits + i` for `i < bits`. -/
theorem regIdx_bReg (w bits : Nat) (i : Nat) (hi : i < bits) :
    FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.regIdx (bReg w bits) i
      = bBase w bits + i := by
  unfold FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.regIdx
  have hi' : i < (bReg w bits).length := by rw [bReg_length]; exact hi
  rw [List.getD_eq_getElem (bReg w bits) 0 hi', bReg_getElem w bits i hi']

theorem bReg_nodup (w bits : Nat) : (bReg w bits).Nodup := by
  unfold bReg
  apply List.Nodup.map (fun a b h => by omega) List.nodup_range

theorem mem_bReg (w bits p : Nat) : p ∈ bReg w bits ↔ ∃ i, i < bits ∧ bBase w bits + i = p := by
  unfold bReg
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, List.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, List.mem_range.mpr hi, rfl⟩

/-- The runway ancilla is disjoint from the b-block (temp wires are above the b-block). -/
theorem runAnc_disj_bReg (w bits : Nat) : ∀ a ∈ runAnc w bits, a ∉ bReg w bits := by
  intro a ha hrb
  obtain ⟨i, hi, rfl⟩ :=
    (FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthRunwayGate.mem_runAnc w bits a).mp ha
  obtain ⟨j, hj, hj2⟩ := (mem_bReg w bits _).mp hrb
  unfold bBase at hj2; omega

theorem bReg_lt_cosetDim (w bits : Nat) : ∀ a ∈ bReg w bits, a < cosetDim w bits := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := (mem_bReg w bits a).mp ha
  unfold bBase cosetDim; omega

/-- A position `p` off the b-block `[bBase, bBase+bits)` (with `p < cosetDim`) is not in `bReg`. -/
theorem not_mem_bReg_of_off (w bits p : Nat)
    (hoff : ¬ (bBase w bits ≤ p ∧ p < bBase w bits + bits)) : p ∉ bReg w bits := by
  intro hp
  obtain ⟨i, hi, rfl⟩ := (mem_bReg w bits p).mp hp
  exact hoff ⟨Nat.le_add_right _ _, by omega⟩

/-- `regVal (bReg w bits)` reads the b-block as the coset layout's b-decode. -/
theorem regVal_bReg_eq (w bits : Nat) (g : Nat → Bool) :
    regVal (bReg w bits) g = decodeReg (fun i => bBase w bits + i) bits g := by
  unfold FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.regVal
  rw [show (bReg w bits).length = bits from bReg_length w bits]
  exact FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthRunwayGate.decodeReg_idx_congr
    (FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.regIdx (bReg w bits))
    (fun i => bBase w bits + i) bits g (fun i hi => regIdx_bReg w bits i hi)

/-! ### §A.1. The b-block coset-prep gate. -/

/-- **The b-block sub-block coset-prep permutation gate.** `permGate` the b-block register
    `bReg w (cm+rest)` with the window permutation `σ_k rest cm N k`, using the runway
    ancilla `runAnc`. -/
noncomputable def cosetPrepSubGateB (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) : Gate :=
  permGate (bReg w (cm + rest))
    ((bReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)
    (runAnc w (cm + rest))

/-- The b-prep gate's value permutation is `(σ_k ⟨vb⟩).val` on in-range values. -/
theorem cosetPrepSubB_permOnVal (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (vb : Nat) (hvb : vb < 2 ^ (cm + rest)) :
    permOnVal (bReg w (cm + rest))
        ((bReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget) vb
      = (σ_k rest cm N k hN hk hbudget ⟨vb, hvb⟩).val := by
  have hvbL : vb < 2 ^ (bReg w (cm + rest)).length := by rw [bReg_length]; exact hvb
  unfold permOnVal
  rw [dif_pos hvbL]
  rw [perm_cast_apply (bReg_length w (cm + rest)).symm
        (σ_k rest cm N k hN hk hbudget) vb hvbL hvb]

/-- **`cosetPrepSubGateB_RegAct`.** -/
theorem cosetPrepSubGateB_RegAct (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    RegAct (cosetPrepSubGateB w rest cm N k hN hk hbudget) (bReg w (cm + rest)) (runAnc w (cm + rest))
      (permOnVal (bReg w (cm + rest))
        ((bReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)) := by
  unfold cosetPrepSubGateB
  exact permGate_RegAct (bReg w (cm + rest))
    ((bReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)
    (runAnc w (cm + rest)) (bReg_nodup w (cm + rest)) (runAnc_nodup w (cm + rest))
    (runAnc_disj_bReg w (cm + rest))
    (by rw [bReg_length, runAnc_length]; omega)

/-- **`cosetPrepSubGateB_wellTyped`.** -/
theorem cosetPrepSubGateB_wellTyped (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    Gate.WellTyped (cosetDim w (cm + rest)) (cosetPrepSubGateB w rest cm N k hN hk hbudget) := by
  unfold cosetPrepSubGateB
  exact permGate_wellTyped (bReg w (cm + rest))
    ((bReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)
    (runAnc w (cm + rest)) (cosetDim w (cm + rest)) (bReg_nodup w (cm + rest))
    (runAnc_nodup w (cm + rest)) (runAnc_disj_bReg w (cm + rest)) (by unfold cosetDim; omega)
    (bReg_lt_cosetDim w (cm + rest))
    (FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthRunwayGate.runAnc_lt_cosetDim w (cm + rest))
    (by rw [bReg_length, runAnc_length]; omega)

/-! ### §A.2. Per-decode action of the b-prep gate. -/

/-- A scratch-clean state forces the runway-ancilla wires to `false`. -/
theorem runAnc_clean_of_scratchClean' (w rest cm : Nat) (g : Nat → Bool)
    (hcl : scratchClean w (cm + rest) g) : ∀ a ∈ runAnc w (cm + rest), g a = false :=
  runAnc_clean_of_scratchClean w (cm + rest) g hcl

/-- **The b-decode of `applyNat (cosetPrepSubGateB) g`.** -/
theorem bDecode_cosetPrepSubB (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool)
    (hcl : scratchClean w (cm + rest) g) :
    decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest)
        (Gate.applyNat (cosetPrepSubGateB w rest cm N k hN hk hbudget) g)
      = (σ_k rest cm N k hN hk hbudget
          ⟨decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest) g,
            decodeReg_lt_two_pow _ _ _⟩).val := by
  set vb := decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest) g with hvbdef
  have hvb : vb < 2 ^ (cm + rest) := hvbdef ▸ decodeReg_lt_two_pow _ _ _
  have hrv : regVal (bReg w (cm + rest)) g = vb := by rw [regVal_bReg_eq]
  have hperm : permOnVal (bReg w (cm + rest))
      ((bReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)
      (regVal (bReg w (cm + rest)) g)
        = (σ_k rest cm N k hN hk hbudget ⟨vb, hvb⟩).val := by
    rw [hrv]; exact cosetPrepSubB_permOnVal w rest cm N k hN hk hbudget vb hvb
  have hwlt : permOnVal (bReg w (cm + rest))
      ((bReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)
      (regVal (bReg w (cm + rest)) g) < 2 ^ (bReg w (cm + rest)).length := by
    rw [hperm, bReg_length]; exact (σ_k rest cm N k hN hk hbudget ⟨vb, hvb⟩).isLt
  obtain ⟨_, hact⟩ := cosetPrepSubGateB_RegAct w rest cm N k hN hk hbudget
  rw [hact g (runAnc_clean_of_scratchClean' w rest cm g hcl)]
  rw [← regVal_bReg_eq w (cm + rest), regVal_setReg (bReg w (cm + rest)) _ g
        (bReg_nodup w (cm + rest)) hwlt, hperm]

/-- **The b-prep gate frames every wire off the b-block** (on scratch-clean states). -/
theorem cosetPrepSubB_frame_off_bReg (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool)
    (hcl : scratchClean w (cm + rest) g) (p : Nat) (hp : p ∉ bReg w (cm + rest)) :
    Gate.applyNat (cosetPrepSubGateB w rest cm N k hN hk hbudget) g p = g p := by
  obtain ⟨_, hact⟩ := cosetPrepSubGateB_RegAct w rest cm N k hN hk hbudget
  rw [hact g (runAnc_clean_of_scratchClean' w rest cm g hcl)]
  exact setReg_frame (bReg w (cm + rest)) _ g p hp

/-- **The a-decode is invariant under the b-prep gate** (a-block off the b-block). -/
theorem aDecode_cosetPrepSubB (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool)
    (hcl : scratchClean w (cm + rest) g) :
    decodeReg (fun i => aBase w + i) (cm + rest)
        (Gate.applyNat (cosetPrepSubGateB w rest cm N k hN hk hbudget) g)
      = decodeReg (fun i => aBase w + i) (cm + rest) g := by
  refine FormalRV.BQAlgo.decodeReg_ext _ _ _ _ (fun i hi => ?_)
  exact cosetPrepSubB_frame_off_bReg w rest cm N k hN hk hbudget g hcl
    (aBase w + i) (not_mem_bReg_of_off w (cm + rest) _ (by unfold aBase bBase; omega))

/-- **Scratch-cleanliness is invariant under the b-prep gate.** -/
theorem scratchClean_cosetPrepSubB (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool)
    (hcl : scratchClean w (cm + rest) g) :
    scratchClean w (cm + rest)
      (Gate.applyNat (cosetPrepSubGateB w rest cm N k hN hk hbudget) g) := by
  refine (scratchClean_congr_offBlocks w (cm + rest) _ g (fun p _ _ hnb => ?_)).mpr hcl
  exact cosetPrepSubB_frame_off_bReg w rest cm N k hN hk hbudget g hcl p
    (not_mem_bReg_of_off w (cm + rest) p hnb)

/-! ### §A.3. Reverse scratch-clean direction for the b-prep gate. -/

/-- The cast inverse permutation, with its `permOnVal` a right inverse of `permOnVal σ_k`. -/
theorem cosetPrepSubB_permOnVal_inv (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (v : Nat) (hv : v < 2 ^ (cm + rest)) :
    permOnVal (bReg w (cm + rest))
        ((bReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)
        (permOnVal (bReg w (cm + rest))
          ((bReg_length w (cm + rest)).symm ▸ (σ_k rest cm N k hN hk hbudget).symm) v)
      = v := by
  have hvL : v < 2 ^ (bReg w (cm + rest)).length := by rw [bReg_length]; exact hv
  have hinner : permOnVal (bReg w (cm + rest))
      ((bReg_length w (cm + rest)).symm ▸ (σ_k rest cm N k hN hk hbudget).symm) v
        = ((σ_k rest cm N k hN hk hbudget).symm ⟨v, hv⟩).val := by
    unfold permOnVal
    rw [dif_pos hvL,
        perm_cast_apply (bReg_length w (cm + rest)).symm
          (σ_k rest cm N k hN hk hbudget).symm v hvL hv]
  rw [hinner]
  have hinnerlt : ((σ_k rest cm N k hN hk hbudget).symm ⟨v, hv⟩).val < 2 ^ (cm + rest) :=
    ((σ_k rest cm N k hN hk hbudget).symm ⟨v, hv⟩).isLt
  rw [cosetPrepSubB_permOnVal w rest cm N k hN hk hbudget _ hinnerlt]
  rw [show (⟨((σ_k rest cm N k hN hk hbudget).symm ⟨v, hv⟩).val, hinnerlt⟩ : Fin (2 ^ (cm + rest)))
        = (σ_k rest cm N k hN hk hbudget).symm ⟨v, hv⟩ from Fin.ext rfl]
  rw [Equiv.apply_symm_apply]

/-- **`reverse (cosetPrepSubGateB)` frames every wire off the b-block** (on clean states). -/
theorem reverse_cosetPrepSubB_frame_off_bReg (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool)
    (hcl : scratchClean w (cm + rest) g) (p : Nat) (hp : p ∉ bReg w (cm + rest)) :
    Gate.applyNat (GateReversible.Gate.reverse (cosetPrepSubGateB w rest cm N k hN hk hbudget)) g p
      = g p := by
  have hrev : RegAct (GateReversible.Gate.reverse (cosetPrepSubGateB w rest cm N k hN hk hbudget))
      (bReg w (cm + rest)) (runAnc w (cm + rest))
      (permOnVal (bReg w (cm + rest))
        ((bReg_length w (cm + rest)).symm ▸ (σ_k rest cm N k hN hk hbudget).symm)) := by
    refine RegAct_reverse (cosetPrepSubGateB w rest cm N k hN hk hbudget) (bReg w (cm + rest))
      (runAnc w (cm + rest)) (cosetDim w (cm + rest))
      (permOnVal (bReg w (cm + rest))
        ((bReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget))
      (permOnVal (bReg w (cm + rest))
        ((bReg_length w (cm + rest)).symm ▸ (σ_k rest cm N k hN hk hbudget).symm))
      (bReg_nodup w (cm + rest)) (runAnc_disj_bReg w (cm + rest))
      (cosetPrepSubGateB_wellTyped w rest cm N k hN hk hbudget)
      (cosetPrepSubGateB_RegAct w rest cm N k hN hk hbudget) ?_ ?_
    · intro v hv
      unfold permOnVal
      rw [dif_pos hv]
      exact (((bReg_length w (cm + rest)).symm ▸ (σ_k rest cm N k hN hk hbudget).symm) _).isLt
    · intro v hv
      rw [bReg_length] at hv
      exact cosetPrepSubB_permOnVal_inv w rest cm N k hN hk hbudget v hv
  obtain ⟨_, hact⟩ := hrev
  rw [hact g (runAnc_clean_of_scratchClean' w rest cm g hcl)]
  exact setReg_frame (bReg w (cm + rest)) _ g p hp

/-- **Reverse scratch-clean direction (b-block).** -/
theorem scratchClean_of_cosetPrepSubB (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool)
    (hcl' : scratchClean w (cm + rest)
      (Gate.applyNat (cosetPrepSubGateB w rest cm N k hN hk hbudget) g)) :
    scratchClean w (cm + rest) g := by
  set g' := Gate.applyNat (cosetPrepSubGateB w rest cm N k hN hk hbudget) g with hg'
  have hgrec : Gate.applyNat (GateReversible.Gate.reverse
      (cosetPrepSubGateB w rest cm N k hN hk hbudget)) g' = g := by
    rw [hg']
    exact applyNat_reverse_cancel (cosetPrepSubGateB w rest cm N k hN hk hbudget)
      (cosetDim w (cm + rest)) (cosetPrepSubGateB_wellTyped w rest cm N k hN hk hbudget) g
  refine (scratchClean_congr_offBlocks w (cm + rest) g' g (fun p _ _ hnb => ?_)).mp hcl'
  rw [← hgrec]
  exact (reverse_cosetPrepSubB_frame_off_bReg w rest cm N k hN hk hbudget g' hcl' p
    (not_mem_bReg_of_off w (cm + rest) p hnb)).symm

/-- **The scratch-clean iff under the b-prep gate.** -/
theorem scratchClean_cosetPrepSubB_iff (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool) :
    scratchClean w (cm + rest) (Gate.applyNat (cosetPrepSubGateB w rest cm N k hN hk hbudget) g)
      ↔ scratchClean w (cm + rest) g :=
  ⟨scratchClean_of_cosetPrepSubB w rest cm N k hN hk hbudget g,
   scratchClean_cosetPrepSubB w rest cm N k hN hk hbudget g⟩

/-! ### §A.4. The b-block column identity (deliverable 2a headline). -/

/-- **The b-prep-gate permState key.** `permState (gateToPerm cosetPrepSubGateB)` maps the
    TARGET coset-window b-block state to the SOURCE H-window b-block state (a-block `Wa`
    arbitrary, framed). -/
theorem cosetPrepSubB_permState_key (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (Wa : Finset (Fin (2 ^ (cm + rest)))) :
    permState (gateToPerm (cosetPrepSubGateB w rest cm N k hN hk hbudget) (cosetDim w (cm + rest))
        (cosetPrepSubGateB_wellTyped w rest cm N k hN hk hbudget))
        (genTwoReg w (cm + rest) cm Wa (winA rest cm N k))
      = genTwoReg w (cm + rest) cm Wa (winA rest cm (2 ^ rest) 0) := by
  set hwt := cosetPrepSubGateB_wellTyped w rest cm N k hN hk hbudget with hhwt
  set σ := gateToPerm (cosetPrepSubGateB w rest cm N k hN hk hbudget) (cosetDim w (cm + rest)) hwt
    with hσ
  funext idx col
  obtain rfl : col = 0 := Subsingleton.elim col 0
  obtain ⟨φ, hidx⟩ : ∃ φ, funboolNat (cosetDim w (cm + rest)) φ = idx :=
    ⟨(funboolEquiv (cosetDim w (cm + rest))).symm idx, by
      exact Equiv.apply_symm_apply (funboolEquiv (cosetDim w (cm + rest))) idx⟩
  show genTwoReg w (cm + rest) cm Wa (winA rest cm N k) (σ idx) 0
    = genTwoReg w (cm + rest) cm Wa (winA rest cm (2 ^ rest) 0) idx 0
  rw [← hidx, hσ, gateToPerm_funboolNat (cosetPrepSubGateB w rest cm N k hN hk hbudget)
        (cosetDim w (cm + rest)) hwt φ,
      genTwoReg_funboolNat w (cm + rest) cm Wa (winA rest cm N k)
        (applyFin (cosetPrepSubGateB w rest cm N k hN hk hbudget) (cosetDim w (cm + rest)) φ),
      genTwoReg_funboolNat w (cm + rest) cm Wa (winA rest cm (2 ^ rest) 0) φ,
      extendBool_applyFin (cosetPrepSubGateB w rest cm N k hN hk hbudget)
        (cosetDim w (cm + rest)) hwt φ]
  set g := extendBool (cosetDim w (cm + rest)) φ with hg
  by_cases hsc : scratchClean w (cm + rest) g
  · rw [if_pos (scratchClean_cosetPrepSubB w rest cm N k hN hk hbudget g hsc), if_pos hsc]
    have hbvb : decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest) g < 2 ^ (cm + rest) :=
      decodeReg_lt_two_pow _ _ _
    -- b-decode of g' = (σ_k ⟨b-decode g⟩).val ; a-decode invariant
    rw [show (⟨decodeReg (fun i => aBase w + i) (cm + rest)
            (Gate.applyNat (cosetPrepSubGateB w rest cm N k hN hk hbudget) g),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ (cm + rest)))
        = (⟨decodeReg (fun i => aBase w + i) (cm + rest) g,
            decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ (cm + rest))) from
      Fin.ext (aDecode_cosetPrepSubB w rest cm N k hN hk hbudget g hsc)]
    rw [show (⟨decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest)
            (Gate.applyNat (cosetPrepSubGateB w rest cm N k hN hk hbudget) g),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ (cm + rest)))
        = σ_k rest cm N k hN hk hbudget
            ⟨decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest) g, hbvb⟩ from
      Fin.ext (bDecode_cosetPrepSubB w rest cm N k hN hk hbudget g hsc)]
    congr 1
    exact if_congr
      (σ_k_window_iff rest cm N k _ hN hk hbudget hbvb).symm rfl rfl
  · rw [if_neg hsc,
        if_neg (fun hc => hsc
          ((scratchClean_cosetPrepSubB_iff w rest cm N k hN hk hbudget g).mp hc))]

/-- **THE B-BLOCK COLUMN IDENTITY (deliverable 2a).**  Applying `cosetPrepSubGateB` to the
    SOURCE two-register state (b-block at the H-window `winA (2^rest) 0`, a-block `Wa`) yields
    the TARGET (b-block at the coset window `winA N k`).  The a-block window `Wa`, the ctrl,
    and the scratch are framed. -/
theorem cosetPrepSubGateB_column_identity (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (Wa : Finset (Fin (2 ^ (cm + rest)))) :
    Framework.uc_eval (Gate.toUCom (cosetDim w (cm + rest))
        (cosetPrepSubGateB w rest cm N k hN hk hbudget))
        * genTwoReg w (cm + rest) cm Wa (winA rest cm (2 ^ rest) 0)
      = genTwoReg w (cm + rest) cm Wa (winA rest cm N k) := by
  have key := cosetPrepSubB_permState_key w rest cm N k hN hk hbudget Wa
  rw [uc_eval_eq_permState (cosetPrepSubGateB w rest cm N k hN hk hbudget) (cosetDim w (cm + rest))
        (cosetPrepSubGateB_wellTyped w rest cm N k hN hk hbudget), ← key]
  funext idx col
  simp only [permState, Equiv.apply_symm_apply]

-- Kernel-cleanliness check for the (2a) headline.
#print axioms cosetPrepSubGateB_column_identity
#print axioms cosetPrepSubB_permState_key
#print axioms scratchClean_cosetPrepSubB_iff

/-! ## §A.5. The COMPOSED data-prep gate (a-prep ; b-prep) and its column identity.

Sequencing the a-block prep at `k = 1` (residue-1 a-window) THEN the b-block prep at
`k = 0` (residue-0 b-window) carries the DOUBLY-H-window `genTwoReg` (both blocks at the
H-window) into the actual runway data factor `cosetInputVec w (cm+rest) N cm 1 0`
(a-block at coset window `N 1`, b-block at coset window `N 0`).

  * a-prep ( `cosetPrepSubGate … 1` ) consumes a-block H-window, frames b-block `Wb`;
  * b-prep ( `cosetPrepSubGateB … 0` ) consumes b-block H-window, frames a-block `Wa`.

The composite gate runs a-prep FIRST (so `uc_eval (seq) * s = uc_eval(b-prep) *
(uc_eval(a-prep) * s)`), matching the data half of `E2runwayInitPrep`. -/

/-- **The data-prep composite gate.**  `Gate.seq (a-prep @ k=1) (b-prep @ k=0)` — a-prep
    first, b-prep second.  Acts on the `cosetDim w (cm+rest)`-wire register. -/
noncomputable def cosetDataPrepGate (w rest cm N : Nat) (hN : 0 < N) (h1N : 1 < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) : Gate :=
  Gate.seq
    (RunwayPrepSubBlock.cosetPrepSubGate w rest cm N 1 hN h1N hbudget)
    (cosetPrepSubGateB w rest cm N 0 hN hN hbudget)

/-- **THE COMPOSED DATA COLUMN IDENTITY (deliverable bridge for 2c).**  Applying the
    composite data-prep gate to the doubly-H-window `genTwoReg` (both blocks at the
    H-window `winA (2^rest) 0`) yields the actual runway data factor
    `cosetInputVec w (cm+rest) N cm 1 0`. -/
theorem cosetDataPrepGate_to_cosetInputVec (w rest cm N : Nat) (hN : 0 < N) (h1N : 1 < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    Framework.uc_eval (Gate.toUCom (cosetDim w (cm + rest))
        (cosetDataPrepGate w rest cm N hN h1N hbudget))
        * genTwoReg w (cm + rest) cm (winA rest cm (2 ^ rest) 0) (winA rest cm (2 ^ rest) 0)
      = FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w (cm + rest) N cm 1 0 := by
  -- Unfold the composite: a-prep first, b-prep second.
  rw [cosetDataPrepGate, Gate.toUCom_seq, FormalRV.Framework.uc_eval_seq_mul]
  -- a-prep on (a = H-window, b = H-window) -> (a = coset N 1, b = H-window):
  rw [RunwayPrepSubBlock.cosetPrepSubGate_column_identity w rest cm N 1 hN h1N hbudget
        (winA rest cm (2 ^ rest) 0)]
  -- b-prep on (a = coset N 1, b = H-window) -> (a = coset N 1, b = coset N 0):
  rw [cosetPrepSubGateB_column_identity w rest cm N 0 hN hN hbudget (winA rest cm N 1)]
  -- both blocks now at their coset windows = cosetInputVec 1 0.
  rw [show winA rest cm N 1 = cosetWindow (2 ^ (cm + rest)) N cm 1 from rfl,
      show winA rest cm N 0 = cosetWindow (2 ^ (cm + rest)) N cm 0 from rfl]
  exact genTwoReg_eq_cosetInputVec w (cm + rest) N cm 1 0

-- Kernel-cleanliness check for the composed data column identity.
#print axioms cosetDataPrepGate_to_cosetInputVec

/-! ## §B. (2b) INTERIOR-BLOCK npar_H — the source `genTwoReg`.

The composed data column identity §A.5 consumes the DOUBLY-H-window `genTwoReg`
(both blocks at the H-window indicator).  Producing THAT from `basis0` is the new
interior-block npar_H step.

WHY THIS IS A SEPARATE, HARDER STEP (vs. the §A permGate column identities).
The §A development is entirely about BASIS PERMUTATIONS: every gate there is a
`permGate`, whose action is a `gateToPerm`, so the column identity reduces to the
funboolNat/permState lift (no superposition is created).  The H column, by
contrast, CREATES superposition — it is NOT a permutation — so `gateToPerm` does
not apply and a genuinely different argument is required.

The framework's closed form `npar_H_kron_zeros_eq_uniform_sum`
(QPE/PhaseKickback.lean:1199) places H on the LEADING `cm` wires `[0, cm)` of an
`(cm + anc)`-qubit register, giving `(1/√2^cm) ∑_{x<2^cm} |x⟩ ⊗ ψ`.  In the
`cosetDim w bits` layout, however, the a-block sits at the INTERIOR wires
`[aBase, aBase+cm)` (`aBase = 1+2w`) and the b-block at `[bBase, bBase+cm)`
(`bBase = 1+2w+bits`), with the ctrl wire 0 and the lookup zone `[1, 1+2w]`
BELOW them and the rest ABOVE — so the leading-qubit form does not apply directly.

THE REQUIRED LEMMA (the interior-block npar_H), stated precisely below as the
hypothesis `hInteriorH` of the conditional headline `uc_eval_E2runwayInitPrep_of_*`:

    uc_eval (dataHPrep w cm rest)  *  basis0 (cosetDim w (cm+rest))
        =  genTwoReg w (cm+rest) cm (winA rest cm (2^rest) 0) (winA rest cm (2^rest) 0)

where `dataHPrep` is the circuit  `X ulookup_ctrl_idx ;  npar_H on [aBase, aBase+cm) ;
npar_H on [bBase, bBase+cm)`  (the ctrl-set plus the two interior H windows).

PROOF STRATEGY (the documented next step; NOT carried out here, to keep the module
`sorry`-free / kernel-clean).  Three-way kron split of the `cosetDim`-register, in
two stages, one per block:

  1.  Split the register as  (low wires `[0, aBase)`) ⊗ (a-block H-window `[aBase,
      aBase+cm)`) ⊗ (high wires `[aBase+cm, cosetDim)`)  via `pad_u`/`kron_vec_assoc`
      (Core/UnitaryOps + QPEEigenstateAndDimCast kron-split tooling), reducing the
      a-block H column to the LEADING form `npar_H_kron_zeros_eq_uniform_sum` on the
      middle factor; this yields the uniform `(1/√2^cm) ∑_{xa} |xa·2^rest⟩` on the
      a-block wires, i.e. the a-block H-window indicator `winA (2^rest) 0` (matching
      `RunwayPrepCore.uniform_window_sum_eq_cosetState`), while the ctrl bit (set by
      the `X`) and the rest stay `0`.
  2.  Symmetrically for the b-block, on the high factor, giving the b-block H-window.
  3.  Re-tensor and rewrite the resulting uniform double-sum-of-basis-vectors into the
      `genTwoReg` indicator form via the `decodeReg`/`scratchClean` bridge (the
      interleaved-layout analogue of `RunwayPrepCore.uniform_window_sum_eq_cosetState`,
      `npar_H_sum_over_hWindow`), reading off each block's window membership and the
      clean ctrl/scratch.

PRECISE BLOCKER.  The framework's kron-split lemmas (`npar_H_kron_zeros_eq_uniform_sum`,
`uc_eval_map_qubits_shift_kron_vec`) are stated for a LEADING block of a TWO-way
(low ⊗ high) split; the `cosetDim` layout needs a genuine THREE-way (low ⊗ block ⊗
high) split with the H block in the MIDDLE, and there is currently no middle-block
kron-split lemma in the library — it must be built (associativity of `kron_vec`
composed with `map_qubits (·+aBase)` and `npar_H_kron_zeros_eq_uniform_sum` on the
shifted sub-register).  This is the single substantial piece left for (2b); the
assembly that CONSUMES its output (§A.5 → §C) is fully discharged and kernel-clean
below. -/

/-- The interior-block source state the §A.5 composite consumes: the DOUBLY-H-window
    `genTwoReg` (both blocks at the H-window indicator `winA (2^rest) 0`).  This is the
    OUTPUT spec of the interior-block npar_H step (2b) — see §B for the precise
    statement, strategy, and blocker. -/
noncomputable def doublyHWindowSource (w rest cm : Nat) :
    Matrix (Fin (2 ^ cosetDim w (cm + rest))) (Fin 1) ℂ :=
  genTwoReg w (cm + rest) cm (winA rest cm (2 ^ rest) 0) (winA rest cm (2 ^ rest) 0)

/-! ## §C. (2c) ASSEMBLE — `E2runwayInitPrep` and the headline.

We assemble the full prep circuit and prove the headline GIVEN the two not-yet-closed
pieces, each supplied as an explicit hypothesis (the `uc_eval_cosetStatePrep_of_bridge`
pattern of `RunwayPrepCore`).  The assembly LOGIC below — the leading-m / interior-data
kron split, and the funnel of §A.5 — is fully verified and kernel-clean.

`E2runwayInitPrep` on `m + cosetDim w bits` qubits is
    `npar_H m`  (leading phase register, the `1/√2^m ∑_x |x⟩` uniform)
  ; `map_qubits (·+m) (dataHPrep)`         (interior H windows + ctrl set ⇒ §B source)
  ; `map_qubits (·+m) (toUCom (cosetDataPrepGate))`   (§A.5 ⇒ data factor `cosetInputVec 1 0`).

The two leading-m/data factorizations both go through `uc_eval_map_qubits_shift_kron_vec`. -/

open FormalRV.SQIRPort (npar_H_kron_zeros_eq_uniform_sum kron_vec_basis_eq_basis_combine)
open FormalRV.Framework (kron_vec kron_zeros)
open FormalRV.QFT.TwoRegisterQFT (uc_eval_map_qubits_shift_kron_vec)
open FormalRV.BQAlgo (uc_well_typed_toUCom_of_Gate_WellTyped)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepCore (basis0)

/-- **The data-prep leg** as a circuit on the `cosetDim`-block, parametrized by the (2b)
    interior-H circuit `dataH`.  Runs the interior-H prep FIRST (basis0 → §B source),
    then the §A.5 composite data-prep (§B source → `cosetInputVec 1 0`). -/
noncomputable def dataPrepLeg (w rest cm N : Nat) (hN : 0 < N) (h1N : 1 < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest))
    (dataH : Framework.BaseUCom (cosetDim w (cm + rest))) :
    Framework.BaseUCom (cosetDim w (cm + rest)) :=
  UCom.seq dataH (Gate.toUCom (cosetDim w (cm + rest)) (cosetDataPrepGate w rest cm N hN h1N hbudget))

/-- **The data-prep leg produces `cosetInputVec 1 0`** from `basis0`, GIVEN the interior-H
    step `hInteriorH` (the (2b) output spec).  Pure composition of §B-output and §A.5. -/
theorem dataPrepLeg_to_cosetInputVec (w rest cm N : Nat) (hN : 0 < N) (h1N : 1 < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest))
    (dataH : Framework.BaseUCom (cosetDim w (cm + rest)))
    (hInteriorH : Framework.uc_eval dataH * basis0 (cosetDim w (cm + rest))
      = doublyHWindowSource w rest cm) :
    Framework.uc_eval (dataPrepLeg w rest cm N hN h1N hbudget dataH)
        * basis0 (cosetDim w (cm + rest))
      = FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w (cm + rest) N cm 1 0 := by
  rw [dataPrepLeg, FormalRV.Framework.uc_eval_seq_mul, hInteriorH, doublyHWindowSource,
      cosetDataPrepGate_to_cosetInputVec w rest cm N hN h1N hbudget]

/-- **THE FULL PREP CIRCUIT** `E2runwayInitPrep` on `m + cosetDim w bits` qubits:
    `npar_H m` (phase register) then the data-prep leg shifted onto `[m, m+cosetDim)`.
    Parametrized by the (2b) interior-H circuit `dataH`. -/
noncomputable def E2runwayInitPrep (m w rest cm N : Nat) (hN : 0 < N) (h1N : 1 < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest))
    (dataH : Framework.BaseUCom (cosetDim w (cm + rest))) :
    Framework.BaseUCom (m + cosetDim w (cm + rest)) :=
  UCom.seq (FormalRV.Framework.BaseUCom.npar_H m)
    (map_qubits (fun q => m + q)
      (dataPrepLeg w rest cm N hN h1N hbudget dataH))

/-- `basis0 (m + D) = kron_vec (kron_zeros m) (basis0 D)` — the leading-m/data split of
    the all-zeros input.  (`basis0 D` and `kron_zeros D` are both `basis_vector (2^D) 0`.) -/
theorem basis0_split_m (m D : Nat) :
    basis0 (m + D) = kron_vec (FormalRV.Framework.kron_zeros m) (basis0 D) := by
  rw [basis0,
      show (FormalRV.Framework.kron_zeros m : Matrix (Fin (2 ^ m)) (Fin 1) ℂ)
        = FormalRV.Framework.basis_vector (2 ^ m) 0 from rfl,
      show (basis0 D : Matrix (Fin (2 ^ D)) (Fin 1) ℂ)
        = FormalRV.Framework.basis_vector (2 ^ D) 0 from rfl,
      show (0 : Nat) = ((⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m)) : Nat) from rfl,
      FormalRV.SQIRPort.kron_vec_basis_eq_basis_combine m D ⟨0, Nat.two_pow_pos m⟩
        ⟨0, Nat.two_pow_pos D⟩]
  congr 1
  show (0 : Nat) = (FormalRV.Framework.kron_vec_combine
      (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m)) (⟨0, Nat.two_pow_pos D⟩ : Fin (2 ^ D))).val
  show (0 : Nat) = 0 * 2 ^ D + 0
  omega

/-- **THE HEADLINE, modulo the (2b) interior-H bridge.**  GIVEN the interior-H step
    `hInteriorH` (the (2b) output spec, `basis0 → doublyHWindowSource`), the full prep
    circuit carries `|0…0⟩` on `m + cosetDim` qubits to the PHASE-UNIFORM ⊗ DATA tensor
    `(1/√2^m ∑_x |x⟩) ⊗ cosetInputVec 1 0` — the kron form of `E2runwayInit` (§C remaining
    step: rewrite this kron form into `E2runwayInit`'s `jointEquiv`/`E2shor_dim_eq`
    factorization, see the report).

    The leading-m / data split is `uc_eval_map_qubits_shift_kron_vec`; the data factor is
    `dataPrepLeg_to_cosetInputVec`; the phase factor is `npar_H_kron_zeros_eq_uniform_sum`.
    Requires `0 < m`. -/
theorem uc_eval_E2runwayInitPrep_of_interiorH (m w rest cm N : Nat) (hm : 0 < m)
    (hN : 0 < N) (h1N : 1 < N) (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest))
    (dataH : Framework.BaseUCom (cosetDim w (cm + rest)))
    (hdataH_wt : UCom.WellTyped (cosetDim w (cm + rest)) dataH)
    (hInteriorH : Framework.uc_eval dataH * basis0 (cosetDim w (cm + rest))
      = doublyHWindowSource w rest cm) :
    Framework.uc_eval (E2runwayInitPrep m w rest cm N hN h1N hbudget dataH)
        * basis0 (m + cosetDim w (cm + rest))
      = kron_vec
          (((1 : ℂ) / Real.sqrt (2 ^ m : ℝ)) •
            ∑ x : Fin (2 ^ m), FormalRV.Framework.basis_vector (2 ^ m) x.val)
          (FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w (cm + rest) N cm 1 0) := by
  -- well-typedness of the data-prep leg (needed by the shift-kron lemma)
  have hleg_wt : UCom.WellTyped (cosetDim w (cm + rest))
      (dataPrepLeg w rest cm N hN h1N hbudget dataH) :=
    UCom.WellTyped.seq hdataH_wt
      (uc_well_typed_toUCom_of_Gate_WellTyped (cosetDim w (cm + rest))
        (cosetDataPrepGate w rest cm N hN h1N hbudget)
        ⟨RunwayPrepSubBlock.cosetPrepSubGate_wellTyped w rest cm N 1 hN h1N hbudget,
         cosetPrepSubGateB_wellTyped w rest cm N 0 hN hN hbudget⟩)
  set χ : Matrix (Fin (2 ^ m)) (Fin 1) ℂ :=
    ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ)) •
      ∑ x : Fin (2 ^ m), FormalRV.Framework.basis_vector (2 ^ m) x.val with hχ
  -- RHS: rewrite cosetInputVec back to the data circuit on basis0, then factor the kron.
  rw [← dataPrepLeg_to_cosetInputVec w rest cm N hN h1N hbudget dataH hInteriorH,
      ← uc_eval_map_qubits_shift_kron_vec (dataPrepLeg w rest cm N hN h1N hbudget dataH)
        hleg_wt χ (basis0 (cosetDim w (cm + rest)))]
  -- LHS: unfold the prep circuit and split off the leading-m H column.
  rw [E2runwayInitPrep, FormalRV.Framework.uc_eval_seq_mul,
      basis0_split_m m (cosetDim w (cm + rest))]
  -- reduces to: uc_eval(npar_H m) * (kron_zeros m ⊗ basis0 D) = χ ⊗ basis0 D
  congr 1
  rw [npar_H_kron_zeros_eq_uniform_sum hm (basis0 (cosetDim w (cm + rest))), hχ,
      kron_vec_smul_left, FormalRV.SQIRPort.kron_vec_sum_left]

-- Kernel-cleanliness checks for the (2c) assembly.
#print axioms dataPrepLeg_to_cosetInputVec
#print axioms uc_eval_E2runwayInitPrep_of_interiorH

end FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepFull
