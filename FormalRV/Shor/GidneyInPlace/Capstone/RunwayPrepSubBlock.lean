/-
  FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepSubBlock — SUB-BLOCK coset
  state-prep for the `E2runwayInit` runway state (gap-3).
  ════════════════════════════════════════════════════════════════════════════

  GOAL.  Prepare each coset block of the two-register runway input ON ITS OWN
  SUB-REGISTER (a-block / b-block) inside `cosetDim`, using a clean ancilla drawn
  from the OTHER wires — never the full register (a full-register `permGate` is
  structurally blocked: `mcxClean` needs ≥ reg.length−1 clean ancilla DISJOINT
  from the value register).

  STRUCTURE (ported from `E2RunwaySynthRunwayGate.runwayGate_column_identity` and
  `RunwayPrepCore`):

  * The SUB-BLOCK prep gate `cosetPrepSubGate` is a `permGate` on a block register
    `reg` (here the a-block `aReg w bits`) with a clean ancilla block (`runAnc`),
    carrying the abstract window permutation `σ_k` of `RunwayPrepCore` (which sends
    the H-window `{x·2^rest}` bijectively onto the coset window `{k+j·N}`).

  * Its COLUMN IDENTITY (`cosetPrepSubGate_column_identity`) transforms a
    two-register state whose a-block holds the SOURCE window (the H-window, step
    `2^rest`, base `0`) into the same state with the a-block at the TARGET window
    (the coset window, step `N`, base `k`), framing the b-block, the ctrl, and the
    scratch.  This is exactly the runway template, generalized from "shift base"
    (`guardedShift`) to "arbitrary window → window" (`σ_k`).

  We work with the GENERALIZED two-register state `genTwoReg`, which decouples the
  a-block window `(Na, ca, ka)` from the b-block window `(Nb, cb, kb)` so the H-window
  source (`Na = 2^rest, ca = cm, ka = 0`) and the coset target (`Na = N, ca = cm,
  ka = k`) are both expressible.  `genTwoReg` is defeq-shaped after `cosetInputTwoReg`
  and reduces to it when both blocks share `(N, cm)`.

  Kernel-clean: axioms ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`,
  no `native_decide`.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepCore
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthRunwayGate

namespace FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepSubBlock

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap
  (regVal setReg RegAct regVal_lt setReg_clean regVal_setReg)
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthPerm
  (permGate permGate_RegAct permGate_wellTyped permOnVal)
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthRunwayGate
  (aReg runAnc aReg_length runAnc_length aReg_nodup runAnc_nodup runAnc_disj_aReg
   aReg_lt_cosetDim runAnc_lt_cosetDim regIdx_aReg aReg_getElem mem_aReg mem_runAnc
   regVal_aReg_eq not_mem_aReg_of_off perm_cast_apply RegAct_reverse
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
open FormalRV.Shor.GidneyInPlace.GateReversible (applyNat_reverse_cancel)
open scoped Classical

/-! ## §0. The GENERALIZED two-register block state `genTwoReg`.

`cosetInputTwoReg w bits N cm xa xb` is the scratch-clean-gated PRODUCT of the two
block coset-window indicators, both with the SAME `(N, cm)` step/window-count.  To
prepare the a-block from the H-window we need to decouple the a-window from the
b-window (the H-window has step `2^rest`, not `N`), so we generalize to ARBITRARY
window Finsets `Wa Wb : Finset (Fin (2^bits))`, gating the per-block amplitude `1/√2^cm`
by membership.  When `Wa = cosetWindow (2^bits) N cm xa` and `Wb = cosetWindow … xb`,
`genTwoReg` reduces DEFINITIONALLY to `cosetInputTwoReg` (`genTwoReg_eq_cosetInputTwoReg`).
-/

open Classical in
/-- The generalized two-register block state.  Block-neutral on the index's
    bit-function `nat_to_funbool (cosetDim) idx.val`, exactly like `cosetInputTwoReg`,
    but with per-block window predicates `Wa`/`Wb` instead of coset windows. -/
noncomputable def genTwoReg (w bits cm : Nat) (Wa Wb : Finset (Fin (2 ^ bits))) :
    Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ :=
  fun idx _ =>
    let g := nat_to_funbool (cosetDim w bits) idx.val
    let va := decodeReg (fun i => aBase w + i) bits g
    let vb := decodeReg (fun i => bBase w bits + i) bits g
    if scratchClean w bits g then
      (if (⟨va, decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ Wa
        then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
      * (if (⟨vb, decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ Wb
        then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
    else 0

/-- `genTwoReg` with COSET windows IS `cosetInputTwoReg`. -/
theorem genTwoReg_eq_cosetInputTwoReg (w bits N cm xa xb : Nat) :
    genTwoReg w bits cm (cosetWindow (2 ^ bits) N cm xa) (cosetWindow (2 ^ bits) N cm xb)
      = cosetInputTwoReg w bits N cm xa xb := rfl

/-- **The funboolNat value lemma for `genTwoReg`.**  Mirrors `cosetInputTwoReg_funboolNat`:
    the amplitude at `funboolNat (cosetDim) f` reads the bits of `extendBool … f`. -/
theorem genTwoReg_funboolNat (w bits cm : Nat) (Wa Wb : Finset (Fin (2 ^ bits)))
    (f : Fin (cosetDim w bits) → Bool) :
    genTwoReg w bits cm Wa Wb (funboolNat (cosetDim w bits) f) 0
      = if scratchClean w bits (extendBool (cosetDim w bits) f) then
          (if (⟨decodeReg (fun i => aBase w + i) bits (extendBool (cosetDim w bits) f),
                decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ Wa
            then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
          * (if (⟨decodeReg (fun i => bBase w bits + i) bits (extendBool (cosetDim w bits) f),
                  decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ Wb
              then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
        else 0 := by
  have hagree : ∀ p, p < cosetDim w bits →
      nat_to_funbool (cosetDim w bits) (funboolNat (cosetDim w bits) f).val p
        = extendBool (cosetDim w bits) f p :=
    fun p hp =>
      FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg.nat_to_funbool_funboolNat_agree
        (cosetDim w bits) f p hp
  have hda : decodeReg (fun i => aBase w + i) bits
        (nat_to_funbool (cosetDim w bits) (funboolNat (cosetDim w bits) f).val)
      = decodeReg (fun i => aBase w + i) bits (extendBool (cosetDim w bits) f) :=
    FormalRV.BQAlgo.decodeReg_ext _ _ _ _
      (fun i hi => hagree (aBase w + i) (by unfold aBase cosetDim; omega))
  have hdb : decodeReg (fun i => bBase w bits + i) bits
        (nat_to_funbool (cosetDim w bits) (funboolNat (cosetDim w bits) f).val)
      = decodeReg (fun i => bBase w bits + i) bits (extendBool (cosetDim w bits) f) :=
    FormalRV.BQAlgo.decodeReg_ext _ _ _ _
      (fun i hi => hagree (bBase w bits + i) (by unfold bBase cosetDim; omega))
  have hsc : scratchClean w bits
        (nat_to_funbool (cosetDim w bits) (funboolNat (cosetDim w bits) f).val)
      ↔ scratchClean w bits (extendBool (cosetDim w bits) f) :=
    scratchClean_congr_offBlocks w bits _ _ (fun p hp _ _ => hagree p hp)
  unfold genTwoReg
  simp only []
  by_cases hcl : scratchClean w bits (extendBool (cosetDim w bits) f)
  · rw [if_pos (hsc.mpr hcl), if_pos hcl]
    congr 1
    · congr 2; exact Fin.ext hda
    · congr 2; exact Fin.ext hdb
  · rw [if_neg (fun hc => hcl (hsc.mp hc)), if_neg hcl]

/-! ## §1. The sub-block coset-prep gate.

We work with the a-block width `bits = cm + rest`, so the abstract window
permutation `σ_k rest cm N k : Equiv.Perm (Fin (2^(cm+rest)))` plugs directly into
`permGate (aReg w (cm+rest))` after the `aReg_length` transport.  This is the
runway gate with the abstract window perm `σ_k` (which routes the H-window onto
the coset window) instead of `resShiftPerm`. -/

/-- **The sub-block coset-prep permutation gate.**  `permGate` the a-block register
    `aReg w (cm+rest)` with the window permutation `σ_k rest cm N k`, using the clean
    runway ancilla `runAnc`.  `σ_k` sends the H-window `{x·2^rest}` bijectively onto
    the coset window `{k+j·N}`, so this gate prepares the coset block from the
    H-window block. -/
noncomputable def cosetPrepSubGate (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) : Gate :=
  permGate (aReg w (cm + rest))
    ((aReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)
    (runAnc w (cm + rest))

/-- The prep gate's value permutation is `(σ_k ⟨va⟩).val` on in-range values. -/
theorem cosetPrepSub_permOnVal (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (va : Nat) (hva : va < 2 ^ (cm + rest)) :
    permOnVal (aReg w (cm + rest))
        ((aReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget) va
      = (σ_k rest cm N k hN hk hbudget ⟨va, hva⟩).val := by
  have hvaL : va < 2 ^ (aReg w (cm + rest)).length := by rw [aReg_length]; exact hva
  unfold permOnVal
  rw [dif_pos hvaL]
  rw [perm_cast_apply (aReg_length w (cm + rest)).symm
        (σ_k rest cm N k hN hk hbudget) va hvaL hva]

/-- **`cosetPrepSubGate_RegAct`.**  On the a-block register with the clean runway
    ancilla, the gate applies the window value-permutation `permOnVal … σ_k`. -/
theorem cosetPrepSubGate_RegAct (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    RegAct (cosetPrepSubGate w rest cm N k hN hk hbudget) (aReg w (cm + rest)) (runAnc w (cm + rest))
      (permOnVal (aReg w (cm + rest))
        ((aReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)) := by
  unfold cosetPrepSubGate
  exact permGate_RegAct (aReg w (cm + rest))
    ((aReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)
    (runAnc w (cm + rest)) (aReg_nodup w (cm + rest)) (runAnc_nodup w (cm + rest))
    (runAnc_disj_aReg w (cm + rest))
    (by rw [aReg_length, runAnc_length]; omega)

/-- **`cosetPrepSubGate_wellTyped`.** -/
theorem cosetPrepSubGate_wellTyped (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    Gate.WellTyped (cosetDim w (cm + rest)) (cosetPrepSubGate w rest cm N k hN hk hbudget) := by
  unfold cosetPrepSubGate
  exact permGate_wellTyped (aReg w (cm + rest))
    ((aReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)
    (runAnc w (cm + rest)) (cosetDim w (cm + rest)) (aReg_nodup w (cm + rest))
    (runAnc_nodup w (cm + rest)) (runAnc_disj_aReg w (cm + rest)) (by unfold cosetDim; omega)
    (aReg_lt_cosetDim w (cm + rest)) (runAnc_lt_cosetDim w (cm + rest))
    (by rw [aReg_length, runAnc_length]; omega)

/-! ## §1b. The value-level window bijection (the analogue of `aWindow_guardedShift`).

`σ_k` sends the H-window onto the coset window; on individual in-range values this is the
iff `va ∈ hWindow ↔ σ_k va ∈ cWindow`.  The H-window is `cosetWindow (2^(cm+rest))
(2^rest) cm 0`; the coset window is `cosetWindow (2^(cm+rest)) N cm k`. -/

/-- **The value-window iff.**  For `va < 2^(cm+rest)`: the source value lies in the
    H-window iff its `σ_k`-image lies in the coset window.  Forward = `σ_k_window`,
    backward = contrapositive of `σ_k_not_window`. -/
theorem σ_k_window_iff (rest cm N k va : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (hva : va < 2 ^ (cm + rest)) :
    (⟨va, hva⟩ : Fin (2 ^ (cm + rest))) ∈ cosetWindow (2 ^ (cm + rest)) (2 ^ rest) cm 0
      ↔ (σ_k rest cm N k hN hk hbudget ⟨va, hva⟩)
          ∈ cosetWindow (2 ^ (cm + rest)) N cm k := by
  constructor
  · intro hmem
    exact σ_k_window rest cm N k hN hk hbudget ⟨va, hva⟩ hmem
  · intro hmem
    by_contra hnot
    exact σ_k_not_window rest cm N k hN hk hbudget ⟨va, hva⟩ hnot hmem

/-- The a-block window value (`cosetState`'s window) at residue `r`, step `M`: the
    Finset `cosetWindow (2^(cm+rest)) M cm r`.  Abbreviation for readability. -/
abbrev winA (rest cm M r : Nat) : Finset (Fin (2 ^ (cm + rest))) :=
  cosetWindow (2 ^ (cm + rest)) M cm r

/-! ## §2. Per-decode action of the prep gate (ported from `aDecode_runwayGate`). -/

/-- A scratch-clean state forces the runway-ancilla wires to `false` (same as the
    runway gate; reproduced here for the `cm+rest` instance). -/
theorem runAnc_clean_of_scratchClean' (w rest cm : Nat) (g : Nat → Bool)
    (hcl : scratchClean w (cm + rest) g) : ∀ a ∈ runAnc w (cm + rest), g a = false :=
  runAnc_clean_of_scratchClean w (cm + rest) g hcl

/-- **The a-decode of `applyNat (cosetPrepSubGate) g`.**  On a scratch-clean `g`, the prep
    gate writes the a-block to `(σ_k ⟨a-decode g⟩).val`. -/
theorem aDecode_cosetPrepSub (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool)
    (hcl : scratchClean w (cm + rest) g) :
    decodeReg (fun i => aBase w + i) (cm + rest)
        (Gate.applyNat (cosetPrepSubGate w rest cm N k hN hk hbudget) g)
      = (σ_k rest cm N k hN hk hbudget
          ⟨decodeReg (fun i => aBase w + i) (cm + rest) g, decodeReg_lt_two_pow _ _ _⟩).val := by
  set va := decodeReg (fun i => aBase w + i) (cm + rest) g with hvadef
  have hva : va < 2 ^ (cm + rest) := hvadef ▸ decodeReg_lt_two_pow _ _ _
  have hrv : regVal (aReg w (cm + rest)) g = va := by rw [regVal_aReg_eq]
  -- permOnVal at va = (σ_k ⟨va⟩).val
  have hperm : permOnVal (aReg w (cm + rest))
      ((aReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)
      (regVal (aReg w (cm + rest)) g)
        = (σ_k rest cm N k hN hk hbudget ⟨va, hva⟩).val := by
    rw [hrv]; exact cosetPrepSub_permOnVal w rest cm N k hN hk hbudget va hva
  have hwlt : permOnVal (aReg w (cm + rest))
      ((aReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)
      (regVal (aReg w (cm + rest)) g) < 2 ^ (aReg w (cm + rest)).length := by
    rw [hperm, aReg_length]; exact (σ_k rest cm N k hN hk hbudget ⟨va, hva⟩).isLt
  obtain ⟨_, hact⟩ := cosetPrepSubGate_RegAct w rest cm N k hN hk hbudget
  rw [hact g (runAnc_clean_of_scratchClean' w rest cm g hcl)]
  rw [← regVal_aReg_eq w (cm + rest), regVal_setReg (aReg w (cm + rest)) _ g
        (aReg_nodup w (cm + rest)) hwlt, hperm]

/-- **The prep gate frames every wire off the a-block** (on scratch-clean states). -/
theorem cosetPrepSub_frame_off_aReg (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool)
    (hcl : scratchClean w (cm + rest) g) (p : Nat) (hp : p ∉ aReg w (cm + rest)) :
    Gate.applyNat (cosetPrepSubGate w rest cm N k hN hk hbudget) g p = g p := by
  obtain ⟨_, hact⟩ := cosetPrepSubGate_RegAct w rest cm N k hN hk hbudget
  rw [hact g (runAnc_clean_of_scratchClean' w rest cm g hcl)]
  exact FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.setReg_frame
    (aReg w (cm + rest)) _ g p hp

/-- **The b-decode is invariant under the prep gate** (b-block off the a-block). -/
theorem bDecode_cosetPrepSub (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool)
    (hcl : scratchClean w (cm + rest) g) :
    decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest)
        (Gate.applyNat (cosetPrepSubGate w rest cm N k hN hk hbudget) g)
      = decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest) g := by
  refine FormalRV.BQAlgo.decodeReg_ext _ _ _ _ (fun i hi => ?_)
  exact cosetPrepSub_frame_off_aReg w rest cm N k hN hk hbudget g hcl
    (bBase w (cm + rest) + i) (not_mem_aReg_of_off w (cm + rest) _ (by unfold aBase bBase; omega))

/-- **Scratch-cleanliness is invariant under the prep gate** (scratch off the a-block). -/
theorem scratchClean_cosetPrepSub (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool)
    (hcl : scratchClean w (cm + rest) g) :
    scratchClean w (cm + rest) (Gate.applyNat (cosetPrepSubGate w rest cm N k hN hk hbudget) g) := by
  refine (scratchClean_congr_offBlocks w (cm + rest) _ g (fun p _ hna _ => ?_)).mpr hcl
  exact cosetPrepSub_frame_off_aReg w rest cm N k hN hk hbudget g hcl p
    (not_mem_aReg_of_off w (cm + rest) p hna)

/-! ## §2b. Reverse scratch-clean direction (for the dirty branch of the column identity).

`σ_k` is an `Equiv.Perm`, so its value action `permOnVal … σ_k` has a value right inverse
`permOnVal … σ_k⁻¹`.  Feeding that to the generic `RegAct_reverse` shows `reverse
(cosetPrepSubGate)` frames every off-a-block wire on clean states, hence `scratchClean`
transfers backward. -/

/-- The cast inverse permutation, with its `permOnVal` a right inverse of `permOnVal σ_k`. -/
theorem cosetPrepSub_permOnVal_inv (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (v : Nat) (hv : v < 2 ^ (cm + rest)) :
    permOnVal (aReg w (cm + rest))
        ((aReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget)
        (permOnVal (aReg w (cm + rest))
          ((aReg_length w (cm + rest)).symm ▸ (σ_k rest cm N k hN hk hbudget).symm) v)
      = v := by
  -- inner: permOnVal (cast σ_k⁻¹) v = (σ_k⁻¹ ⟨v⟩).val
  have hvL : v < 2 ^ (aReg w (cm + rest)).length := by rw [aReg_length]; exact hv
  have hinner : permOnVal (aReg w (cm + rest))
      ((aReg_length w (cm + rest)).symm ▸ (σ_k rest cm N k hN hk hbudget).symm) v
        = ((σ_k rest cm N k hN hk hbudget).symm ⟨v, hv⟩).val := by
    unfold permOnVal
    rw [dif_pos hvL,
        perm_cast_apply (aReg_length w (cm + rest)).symm
          (σ_k rest cm N k hN hk hbudget).symm v hvL hv]
  rw [hinner]
  have hinnerlt : ((σ_k rest cm N k hN hk hbudget).symm ⟨v, hv⟩).val < 2 ^ (cm + rest) :=
    ((σ_k rest cm N k hN hk hbudget).symm ⟨v, hv⟩).isLt
  rw [cosetPrepSub_permOnVal w rest cm N k hN hk hbudget _ hinnerlt]
  rw [show (⟨((σ_k rest cm N k hN hk hbudget).symm ⟨v, hv⟩).val, hinnerlt⟩ : Fin (2 ^ (cm + rest)))
        = (σ_k rest cm N k hN hk hbudget).symm ⟨v, hv⟩ from Fin.ext rfl]
  rw [Equiv.apply_symm_apply]

/-- **`reverse (cosetPrepSubGate)` frames every wire off the a-block** (on clean states). -/
theorem reverse_cosetPrepSub_frame_off_aReg (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool)
    (hcl : scratchClean w (cm + rest) g) (p : Nat) (hp : p ∉ aReg w (cm + rest)) :
    Gate.applyNat (GateReversible.Gate.reverse (cosetPrepSubGate w rest cm N k hN hk hbudget)) g p
      = g p := by
  have hrev : RegAct (GateReversible.Gate.reverse (cosetPrepSubGate w rest cm N k hN hk hbudget))
      (aReg w (cm + rest)) (runAnc w (cm + rest))
      (permOnVal (aReg w (cm + rest))
        ((aReg_length w (cm + rest)).symm ▸ (σ_k rest cm N k hN hk hbudget).symm)) := by
    refine RegAct_reverse (cosetPrepSubGate w rest cm N k hN hk hbudget) (aReg w (cm + rest))
      (runAnc w (cm + rest)) (cosetDim w (cm + rest))
      (permOnVal (aReg w (cm + rest))
        ((aReg_length w (cm + rest)).symm ▸ σ_k rest cm N k hN hk hbudget))
      (permOnVal (aReg w (cm + rest))
        ((aReg_length w (cm + rest)).symm ▸ (σ_k rest cm N k hN hk hbudget).symm))
      (aReg_nodup w (cm + rest)) (runAnc_disj_aReg w (cm + rest))
      (cosetPrepSubGate_wellTyped w rest cm N k hN hk hbudget)
      (cosetPrepSubGate_RegAct w rest cm N k hN hk hbudget) ?_ ?_
    · intro v hv
      unfold permOnVal
      rw [dif_pos hv]
      exact (((aReg_length w (cm + rest)).symm ▸ (σ_k rest cm N k hN hk hbudget).symm) _).isLt
    · intro v hv
      rw [aReg_length] at hv
      exact cosetPrepSub_permOnVal_inv w rest cm N k hN hk hbudget v hv
  obtain ⟨_, hact⟩ := hrev
  rw [hact g (runAnc_clean_of_scratchClean' w rest cm g hcl)]
  exact FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.setReg_frame
    (aReg w (cm + rest)) _ g p hp

/-- **Reverse scratch-clean direction.**  If `applyNat (cosetPrepSubGate) g` is scratch-clean,
    so is `g`. -/
theorem scratchClean_of_cosetPrepSub (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool)
    (hcl' : scratchClean w (cm + rest)
      (Gate.applyNat (cosetPrepSubGate w rest cm N k hN hk hbudget) g)) :
    scratchClean w (cm + rest) g := by
  set g' := Gate.applyNat (cosetPrepSubGate w rest cm N k hN hk hbudget) g with hg'
  have hgrec : Gate.applyNat (GateReversible.Gate.reverse
      (cosetPrepSubGate w rest cm N k hN hk hbudget)) g' = g := by
    rw [hg']
    exact applyNat_reverse_cancel (cosetPrepSubGate w rest cm N k hN hk hbudget)
      (cosetDim w (cm + rest)) (cosetPrepSubGate_wellTyped w rest cm N k hN hk hbudget) g
  refine (scratchClean_congr_offBlocks w (cm + rest) g' g (fun p _ hna _ => ?_)).mp hcl'
  rw [← hgrec]
  exact (reverse_cosetPrepSub_frame_off_aReg w rest cm N k hN hk hbudget g' hcl' p
    (not_mem_aReg_of_off w (cm + rest) p hna)).symm

/-- **The scratch-clean iff under the prep gate.** -/
theorem scratchClean_cosetPrepSub_iff (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (g : Nat → Bool) :
    scratchClean w (cm + rest) (Gate.applyNat (cosetPrepSubGate w rest cm N k hN hk hbudget) g)
      ↔ scratchClean w (cm + rest) g :=
  ⟨scratchClean_of_cosetPrepSub w rest cm N k hN hk hbudget g,
   scratchClean_cosetPrepSub w rest cm N k hN hk hbudget g⟩

/-! ## §3. The SUB-BLOCK column identity (the deliverable-(1) headline).

The prep gate's `permState` sends the TARGET `genTwoReg` (a-block at the coset window
`winA N k`) BACK to the SOURCE `genTwoReg` (a-block at the H-window `winA (2^rest) 0`),
framing the b-block `Wb`, the ctrl, and the scratch.  This is the runway template
(`runway_permState_key`) with the abstract window perm `σ_k`. -/

/-- **The prep-gate permState key.**  `permState (gateToPerm cosetPrepSubGate)` maps the
    TARGET coset-window a-block state to the SOURCE H-window a-block state (b-block `Wb`
    arbitrary, framed). -/
theorem cosetPrepSub_permState_key (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (Wb : Finset (Fin (2 ^ (cm + rest)))) :
    permState (gateToPerm (cosetPrepSubGate w rest cm N k hN hk hbudget) (cosetDim w (cm + rest))
        (cosetPrepSubGate_wellTyped w rest cm N k hN hk hbudget))
        (genTwoReg w (cm + rest) cm (winA rest cm N k) Wb)
      = genTwoReg w (cm + rest) cm (winA rest cm (2 ^ rest) 0) Wb := by
  set hwt := cosetPrepSubGate_wellTyped w rest cm N k hN hk hbudget with hhwt
  set σ := gateToPerm (cosetPrepSubGate w rest cm N k hN hk hbudget) (cosetDim w (cm + rest)) hwt
    with hσ
  funext idx col
  obtain rfl : col = 0 := Subsingleton.elim col 0
  obtain ⟨φ, hidx⟩ : ∃ φ, funboolNat (cosetDim w (cm + rest)) φ = idx :=
    ⟨(funboolEquiv (cosetDim w (cm + rest))).symm idx, by
      exact Equiv.apply_symm_apply (funboolEquiv (cosetDim w (cm + rest))) idx⟩
  show genTwoReg w (cm + rest) cm (winA rest cm N k) Wb (σ idx) 0
    = genTwoReg w (cm + rest) cm (winA rest cm (2 ^ rest) 0) Wb idx 0
  rw [← hidx, hσ, gateToPerm_funboolNat (cosetPrepSubGate w rest cm N k hN hk hbudget)
        (cosetDim w (cm + rest)) hwt φ,
      genTwoReg_funboolNat w (cm + rest) cm (winA rest cm N k) Wb
        (applyFin (cosetPrepSubGate w rest cm N k hN hk hbudget) (cosetDim w (cm + rest)) φ),
      genTwoReg_funboolNat w (cm + rest) cm (winA rest cm (2 ^ rest) 0) Wb φ,
      extendBool_applyFin (cosetPrepSubGate w rest cm N k hN hk hbudget)
        (cosetDim w (cm + rest)) hwt φ]
  set g := extendBool (cosetDim w (cm + rest)) φ with hg
  by_cases hsc : scratchClean w (cm + rest) g
  · rw [if_pos (scratchClean_cosetPrepSub w rest cm N k hN hk hbudget g hsc), if_pos hsc]
    -- a-decode of g' = (σ_k ⟨a-decode g⟩).val ; b-decode invariant
    have hava : decodeReg (fun i => aBase w + i) (cm + rest) g < 2 ^ (cm + rest) :=
      decodeReg_lt_two_pow _ _ _
    rw [show (⟨decodeReg (fun i => aBase w + i) (cm + rest)
            (Gate.applyNat (cosetPrepSubGate w rest cm N k hN hk hbudget) g),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ (cm + rest)))
        = σ_k rest cm N k hN hk hbudget
            ⟨decodeReg (fun i => aBase w + i) (cm + rest) g, hava⟩ from
      Fin.ext (aDecode_cosetPrepSub w rest cm N k hN hk hbudget g hsc)]
    rw [show (⟨decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest)
            (Gate.applyNat (cosetPrepSubGate w rest cm N k hN hk hbudget) g),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ (cm + rest)))
        = (⟨decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest) g,
            decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ (cm + rest))) from
      Fin.ext (bDecode_cosetPrepSub w rest cm N k hN hk hbudget g hsc)]
    congr 1
    exact if_congr
      (σ_k_window_iff rest cm N k _ hN hk hbudget hava).symm rfl rfl
  · rw [if_neg hsc,
        if_neg (fun hc => hsc
          ((scratchClean_cosetPrepSub_iff w rest cm N k hN hk hbudget g).mp hc))]

/-- **THE SUB-BLOCK COLUMN IDENTITY (deliverable 1).**  Applying `cosetPrepSubGate` to the
    SOURCE two-register state (a-block at the H-window `winA (2^rest) 0`, b-block `Wb`) yields
    the TARGET (a-block at the coset window `winA N k`).  The b-block window `Wb`, the ctrl,
    and the scratch are framed.  Hypotheses: `0 < N`, `k < N`, the FULL-BLOCKS budget
    `2^cm·N ≤ 2^(cm+rest)` (so the coset window fits). -/
theorem cosetPrepSubGate_column_identity (w rest cm N k : Nat) (hN : 0 < N) (hk : k < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) (Wb : Finset (Fin (2 ^ (cm + rest)))) :
    Framework.uc_eval (Gate.toUCom (cosetDim w (cm + rest))
        (cosetPrepSubGate w rest cm N k hN hk hbudget))
        * genTwoReg w (cm + rest) cm (winA rest cm (2 ^ rest) 0) Wb
      = genTwoReg w (cm + rest) cm (winA rest cm N k) Wb := by
  have key := cosetPrepSub_permState_key w rest cm N k hN hk hbudget Wb
  rw [uc_eval_eq_permState (cosetPrepSubGate w rest cm N k hN hk hbudget) (cosetDim w (cm + rest))
        (cosetPrepSubGate_wellTyped w rest cm N k hN hk hbudget), ← key]
  funext idx col
  simp only [permState, Equiv.apply_symm_apply]

/-! ## §4. Bridge to the named runway target `cosetInputVec`.

When the b-block window is the coset window `cosetWindow N cm 0`, the a-block prep at
`k = 1` transforms the genTwoReg with a-block H-window into EXACTLY
`cosetInputVec w (cm+rest) N cm 1 0` (the a-factor of the runway state).  This is the
concrete consumer of `cosetPrepSubGate_column_identity` for the a-block of `E2runwayInit`. -/

/-- `genTwoReg` with coset windows for both blocks IS `cosetInputVec`. -/
theorem genTwoReg_eq_cosetInputVec (w bits N cm xa xb : Nat) :
    genTwoReg w bits cm (cosetWindow (2 ^ bits) N cm xa) (cosetWindow (2 ^ bits) N cm xb)
      = FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w bits N cm xa xb :=
  rfl

/-- **A-block runway prep (concrete).**  With the b-block already at the coset window
    `cosetWindow N cm 0`, `cosetPrepSubGate … 1` carries the genTwoReg with a-block at the
    H-window into the actual runway a-factor `cosetInputVec w (cm+rest) N cm 1 0`. -/
theorem cosetPrepSubGate_to_cosetInputVec (w rest cm N : Nat) (hN : 0 < N) (h1N : 1 < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    Framework.uc_eval (Gate.toUCom (cosetDim w (cm + rest))
        (cosetPrepSubGate w rest cm N 1 hN h1N hbudget))
        * genTwoReg w (cm + rest) cm (winA rest cm (2 ^ rest) 0)
            (cosetWindow (2 ^ (cm + rest)) N cm 0)
      = FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w (cm + rest) N cm 1 0 := by
  rw [cosetPrepSubGate_column_identity w rest cm N 1 hN h1N hbudget
        (cosetWindow (2 ^ (cm + rest)) N cm 0)]
  rw [show winA rest cm N 1 = cosetWindow (2 ^ (cm + rest)) N cm 1 from rfl]
  exact genTwoReg_eq_cosetInputVec w (cm + rest) N cm 1 0

-- Kernel-cleanliness check (axioms ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms cosetPrepSubGate_column_identity
#print axioms cosetPrepSub_permState_key
#print axioms cosetPrepSubGate_to_cosetInputVec
#print axioms genTwoReg_funboolNat
#print axioms σ_k_window_iff
#print axioms cosetPrepSubGate_wellTyped
#print axioms scratchClean_cosetPrepSub_iff

/-! ## §5. The REMAINING obligation for deliverable (2) (the full `E2runwayInitPrep`).

Deliverable (1) above — `cosetPrepSubGate_column_identity` / `cosetPrepSubGate_to_cosetInputVec` —
is the rock-solid kernel-clean SUB-BLOCK coset prep: it places the coset state on the a-block
(a genuine sub-register, clean ancilla `runAnc` drawn from the other wires) while FRAMING the
b-block, the ctrl, and the scratch, phrased as the funboolNat/permState lift exactly as the
existing `runwayGate_column_identity`.

To assemble the FULL `E2runwayInitPrep` (deliverable 2), three further pieces are needed,
each a substantial sub-project (none of which is started here, to keep this file
`sorry`-free / kernel-clean):

  (2a) **The b-block analogue.**  A `bReg`/`bRunAnc` mirror of `aReg`/`runAnc` (the b-block
       `[bBase, bBase+bits)` with a disjoint clean ancilla), and the b-block versions of
       `aDecode_cosetPrepSub` / `bDecode_cosetPrepSub` / `scratchClean_cosetPrepSub` etc., giving
       `cosetPrepSubGateB_column_identity`: it sends the genTwoReg with b-block at the H-window
       to the b-block at `cosetWindow N cm 0`, framing the a-block.  Composing (a-prep ; b-prep)
       on the doubly-H-window genTwoReg then yields `cosetInputVec w (cm+rest) N cm 1 0` (both
       blocks at their coset windows).

  (2b) **basis0 → doubly-H-window genTwoReg.**  An `X` on the ctrl wire (wire 0,
       `ulookup_ctrl_idx`) to set ctrl = true, plus `npar_H cm` on EACH block's low `cm`
       wires at the INTERIOR positions `[aBase, aBase+cm)` and `[bBase, bBase+cm)`.  This is
       the flagged NEW interior-block npar_H lemma: the existing `npar_H_kron_zeros_eq_uniform_sum`
       puts H on the LEADING qubits, so a 3-way (or 5-way) kron split (low, a-block, mid,
       b-block, high) through `pad_u` is required to land H on the interior block wires, producing the
       `cosetState (2^(cm+rest)) (2^rest) cm 0 = winA (2^rest) 0` H-window indicator on each block
       while keeping ctrl = 1 and the rest = 0.  This is the genTwoReg source of (1)/(2a).

  (2c) **kron split to `E2runwayInit`.**  The phase factor (npar_H on the m-qubit phase register,
       directly from `RunwayPrepCore.uc_eval_npar_H_basis0`) ⊗ the data factor (2a∘2b output =
       `cosetInputVec … 1 0`), reconciled with `E2runwayInit`'s `jointEquiv`/`shorDvd`
       factorization (`InPlaceE2IdealTrajectory.shorInitM_eq`) and the `E2shor_dim_eq` cast
       between `2^m·2^bits·2^(cosetAnc w bits)` and `2^(m + cosetDim w bits)` (note
       `bits + cosetAnc w bits = cosetDim w bits`).  The final headline:
       `uc_eval (E2runwayInitPrep m w bits N cm) * basis0 (m + cosetDim w bits)
          = E2runwayInit m w bits N cm`
       (modulo the dimension cast), with `E2runwayInitPrep` =
       `npar_H(phase m) ; X(ctrl) ; H-on-a-block-low-cm ; cosetPrepSubGate(a,1) ;
        H-on-b-block-low-cm ; cosetPrepSubGateB(b,0)`. -/

end FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepSubBlock
