/-
  FormalRV.Shor.GidneyInPlace.InPlaceSwapBlocks
  ───────────────────────────────────────────────
  PACKAGING checkpoint 1 (toward the single-register contract): the a↔b block SWAP
  acting on the two-register coset input.  After the frozen two-register multiplier
  `gidneyTwoRegInPlaceCosetMul` leaves the product in the b-block (a-block cleared),
  this SWAP moves the result back onto the a-block — so the contract can read input
  AND output from the SAME physical block (`a`), with `b` documented as the temporary
  product block before the swap.

      swapAB = swapReg (aBase+·) (bBase+·) bits   (the qubit-by-qubit a↔b block swap)

  THE THEOREM (exact, no approximation — a pure register relabel):

      uc_eval (toUCom (cosetDim) swapAB) · cosetInputTwoReg xa xb  =  cosetInputTwoReg xb xa

  i.e. swapping the two physical blocks swaps the two coset LABELS (`xa ↔ xb`), leaving
  the scratch/lookup/temp/carry clean (the swap fixes every non-block position).  The
  constant is untouched: `uc_eval` of a register permutation is a `normSqDist`-isometry,
  so this lemma will peel off the frozen bound without changing `4·numWin/2^cm`.

  NO contract packaging here — only the SWAP action on the input state.

  Method: `uc_eval(swapAB)·s = permState σ.symm s` (`uc_eval_eq_permState`); apply the
  forward `permState σ` (no involution needed) and cancel `permState σ.symm ∘ permState σ`.
  The block-swap reads the a-block from the old b-block and vice versa (`swapReg_idxA/idxB`,
  bounded-disjointness variants), preserves scratch (`swapReg_frame`), and the two coset
  factors of `cosetInputTwoReg` commute (`mul_comm`).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Def.InPlace
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Input.InPlaceCosetInputTwoReg
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceReverseLeg
import FormalRV.Shor.GidneyInPlace.Gate.Proof.CuccaroGatePerm
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Mass.InPlaceNormBound

namespace FormalRV.Shor.GidneyInPlace.InPlaceSwapBlocks

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedCircuit (decodeReg_testBit decodeReg_lt_two_pow)
open FormalRV.Shor.GidneyInPlace.InPlace (swapReg swapPair applyNat_swapPair)
open FormalRV.Shor.GidneyInPlace.GatePerm
  (gateToPerm funboolNat funboolEquiv extendBool applyFin)
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_eq_permState)
open FormalRV.Shor.GidneyInPlace.ApproxOp (permState)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg
  (aBase bBase scratchClean cosetInputTwoReg cosetInputTwoReg_funboolNat
   scratchClean_congr_offBlocks)
open FormalRV.Shor.GidneyInPlace.CuccaroGatePerm (gateToPerm_funboolNat)
open FormalRV.Shor.GidneyInPlace.InPlaceReverseLeg (extendBool_applyFin)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)

/-! ## §1. Bounded-disjointness variants of the `swapReg` action lemmas.

  The block index families `aBase+·` and `bBase+·` collide GLOBALLY (at `i = bits`,
  `aBase+bits = bBase`), so `InPlace.swapReg_{frame,idxA,idxB}`'s `∀ i i'` global
  disjointness is unsatisfiable for them — though those proofs only ever use it at
  indices `< n`.  We reprove the three with disjointness BOUNDED to `i, i' < n`
  (which the blocks DO satisfy: `aBase+i < bBase ≤ bBase+i'` for `i, i' < bits`).
  Injectivity stays global (the affine families are globally injective). -/

theorem swapReg_frameB (idxA idxB : Nat → Nat) :
    ∀ (n : Nat) (f : Nat → Bool) (p : Nat),
      (∀ i i', i < n → i' < n → idxA i ≠ idxB i') →
      (∀ i, i < n → p ≠ idxA i ∧ p ≠ idxB i) →
      Gate.applyNat (swapReg idxA idxB n) f p = f p := by
  intro n
  induction n with
  | zero => intro f p _ _; rfl
  | succ m ih =>
      intro f p hAB hp
      show Gate.applyNat (swapPair (idxA m) (idxB m))
        (Gate.applyNat (swapReg idxA idxB m) f) p = f p
      rw [applyNat_swapPair (idxA m) (idxB m)
        (hAB m m (Nat.lt_succ_self m) (Nat.lt_succ_self m)) _ p]
      obtain ⟨hpa, hpb⟩ := hp m (Nat.lt_succ_self m)
      rw [if_neg hpa, if_neg hpb]
      exact ih f p (fun i i' hi hi' => hAB i i' (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hi'))
            (fun i hi => hp i (Nat.lt_succ_of_lt hi))

theorem swapReg_idxAB (idxA idxB : Nat → Nat)
    (hAinj : ∀ i i', idxA i = idxA i' → i = i') (hBinj : ∀ i i', idxB i = idxB i' → i = i') :
    ∀ (n : Nat) (f : Nat → Bool) (j : Nat), j < n →
      (∀ i i', i < n → i' < n → idxA i ≠ idxB i') →
      Gate.applyNat (swapReg idxA idxB n) f (idxA j) = f (idxB j) := by
  intro n
  induction n with
  | zero => intro f j hj _; omega
  | succ m ih =>
      intro f j hj hAB
      show Gate.applyNat (swapPair (idxA m) (idxB m))
        (Gate.applyNat (swapReg idxA idxB m) f) (idxA j) = f (idxB j)
      rw [applyNat_swapPair (idxA m) (idxB m)
        (hAB m m (Nat.lt_succ_self m) (Nat.lt_succ_self m)) _ (idxA j)]
      by_cases hjm : j = m
      · rw [hjm, if_pos rfl]
        exact swapReg_frameB idxA idxB m f (idxB m)
          (fun i i' hi hi' => hAB i i' (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hi'))
          (fun i hi => ⟨(hAB i m (Nat.lt_succ_of_lt hi) (Nat.lt_succ_self m)).symm,
            fun he => absurd (hBinj i m he.symm) (by omega)⟩)
      · rw [if_neg (fun he => hjm (hAinj j m he)), if_neg (hAB j m hj (Nat.lt_succ_self m))]
        exact ih f j (by omega)
          (fun i i' hi hi' => hAB i i' (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hi'))

theorem swapReg_idxBB (idxA idxB : Nat → Nat)
    (hAinj : ∀ i i', idxA i = idxA i' → i = i') (hBinj : ∀ i i', idxB i = idxB i' → i = i') :
    ∀ (n : Nat) (f : Nat → Bool) (j : Nat), j < n →
      (∀ i i', i < n → i' < n → idxA i ≠ idxB i') →
      Gate.applyNat (swapReg idxA idxB n) f (idxB j) = f (idxA j) := by
  intro n
  induction n with
  | zero => intro f j hj _; omega
  | succ m ih =>
      intro f j hj hAB
      show Gate.applyNat (swapPair (idxA m) (idxB m))
        (Gate.applyNat (swapReg idxA idxB m) f) (idxB j) = f (idxA j)
      rw [applyNat_swapPair (idxA m) (idxB m)
        (hAB m m (Nat.lt_succ_self m) (Nat.lt_succ_self m)) _ (idxB j)]
      by_cases hjm : j = m
      · rw [hjm, if_neg (fun he => (hAB m m (Nat.lt_succ_self m) (Nat.lt_succ_self m)) he.symm),
            if_pos rfl]
        exact swapReg_frameB idxA idxB m f (idxA m)
          (fun i i' hi hi' => hAB i i' (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hi'))
          (fun i hi => ⟨fun he => absurd (hAinj i m he.symm) (by omega),
            hAB m i (Nat.lt_succ_self m) (Nat.lt_succ_of_lt hi)⟩)
      · rw [if_neg (fun he => (hAB m j (Nat.lt_succ_self m) hj) he.symm),
            if_neg (fun he => hjm (hBinj j m he))]
        exact ih f j (by omega)
          (fun i i' hi hi' => hAB i i' (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hi'))

/-! ## §2. The concrete a↔b block swap and its per-position / well-typed facts. -/

/-- The a↔b block swap on the two-register coset layout: swaps qubit `aBase+i` with
    `bBase+i` for each `i < bits`. -/
def swapAB (w bits : Nat) : Gate :=
  swapReg (fun i => aBase w + i) (fun i => bBase w bits + i) bits

/-- Bounded disjointness of the two block families (holds: `aBase+i < bBase ≤ bBase+i'`
    for `i, i' < bits`). -/
theorem swapAB_disj (w bits : Nat) :
    ∀ i i', i < bits → i' < bits → (fun i => aBase w + i) i ≠ (fun i => bBase w bits + i) i' := by
  intro i i' hi hi'; simp only []; unfold aBase bBase; omega

theorem swapAB_injA (w : Nat) : ∀ i i', (fun i => aBase w + i) i = (fun i => aBase w + i) i' → i = i' :=
  fun _ _ h => Nat.add_left_cancel h

theorem swapAB_injB (w bits : Nat) :
    ∀ i i', (fun i => bBase w bits + i) i = (fun i => bBase w bits + i) i' → i = i' :=
  fun _ _ h => Nat.add_left_cancel h

/-- The swap reads the a-block position from the old b-block value. -/
theorem swapAB_posA (w bits : Nat) (g : Nat → Bool) (j : Nat) (hj : j < bits) :
    Gate.applyNat (swapAB w bits) g (aBase w + j) = g (bBase w bits + j) :=
  swapReg_idxAB (fun i => aBase w + i) (fun i => bBase w bits + i)
    (swapAB_injA w) (swapAB_injB w bits) bits g j hj (swapAB_disj w bits)

/-- The swap reads the b-block position from the old a-block value. -/
theorem swapAB_posB (w bits : Nat) (g : Nat → Bool) (j : Nat) (hj : j < bits) :
    Gate.applyNat (swapAB w bits) g (bBase w bits + j) = g (aBase w + j) :=
  swapReg_idxBB (fun i => aBase w + i) (fun i => bBase w bits + i)
    (swapAB_injA w) (swapAB_injB w bits) bits g j hj (swapAB_disj w bits)

/-- The swap fixes every position off both data blocks (in particular all scratch). -/
theorem swapAB_frameOff (w bits : Nat) (g : Nat → Bool) (p : Nat)
    (hpa : ¬ (aBase w ≤ p ∧ p < aBase w + bits))
    (hpb : ¬ (bBase w bits ≤ p ∧ p < bBase w bits + bits)) :
    Gate.applyNat (swapAB w bits) g p = g p :=
  swapReg_frameB (fun i => aBase w + i) (fun i => bBase w bits + i) bits g p
    (swapAB_disj w bits)
    (fun i hi => ⟨fun he => hpa ⟨by simp only [] at he; omega, by simp only [] at he; omega⟩,
                  fun he => hpb ⟨by simp only [] at he; omega, by simp only [] at he; omega⟩⟩)

theorem swapAB_wellTyped (w bits : Nat) :
    Gate.WellTyped (cosetDim w bits) (swapAB w bits) := by
  have hgen : ∀ (idxA idxB : Nat → Nat) (dim : Nat), 0 < dim →
      ∀ (n : Nat), (∀ i, i < n → idxA i < dim ∧ idxB i < dim ∧ idxA i ≠ idxB i) →
        Gate.WellTyped dim (swapReg idxA idxB n) := by
    intro idxA idxB dim hdim n
    induction n with
    | zero => intro _; exact hdim
    | succ m ih =>
        intro hb
        refine ⟨ih (fun i hi => hb i (Nat.lt_succ_of_lt hi)), ?_⟩
        obtain ⟨hA, hB, hAB⟩ := hb m (Nat.lt_succ_self m)
        exact ⟨⟨hA, hB, hAB⟩, ⟨hB, hA, Ne.symm hAB⟩, hA, hB, hAB⟩
  exact hgen _ _ (cosetDim w bits) (by unfold cosetDim; omega) bits
    (fun i hi => ⟨by unfold aBase cosetDim; omega, by unfold bBase cosetDim; omega,
                  by unfold aBase bBase; omega⟩)

/-! ## §3. The block-decode / scratch transport under the swap. -/

/-- The a-block decode of the swapped function equals the b-block decode of the original. -/
theorem swapAB_decodeA (w bits : Nat) (g : Nat → Bool) :
    decodeReg (fun i => aBase w + i) bits (Gate.applyNat (swapAB w bits) g)
      = decodeReg (fun i => bBase w bits + i) bits g := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < bits
  · rw [decodeReg_testBit _ _ _ j hj, decodeReg_testBit _ _ _ j hj]
    exact swapAB_posA w bits g j hj
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (decodeReg_lt_two_pow _ _ _)
          (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (decodeReg_lt_two_pow _ _ _)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- The b-block decode of the swapped function equals the a-block decode of the original. -/
theorem swapAB_decodeB (w bits : Nat) (g : Nat → Bool) :
    decodeReg (fun i => bBase w bits + i) bits (Gate.applyNat (swapAB w bits) g)
      = decodeReg (fun i => aBase w + i) bits g := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < bits
  · rw [decodeReg_testBit _ _ _ j hj, decodeReg_testBit _ _ _ j hj]
    exact swapAB_posB w bits g j hj
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (decodeReg_lt_two_pow _ _ _)
          (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (decodeReg_lt_two_pow _ _ _)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- The swap preserves the clean-scratch predicate (it fixes every non-block position). -/
theorem swapAB_scratchClean (w bits : Nat) (g : Nat → Bool) :
    scratchClean w bits (Gate.applyNat (swapAB w bits) g) ↔ scratchClean w bits g :=
  scratchClean_congr_offBlocks w bits _ _ (fun p _ hna hnb => swapAB_frameOff w bits g p hna hnb)

/-! ## §4. THE CHECKPOINT: the swap action on the two-register coset input. -/

/-- **Block swap on the coset input.**  Applying the a↔b block swap to the two-register
    coset input `cosetInputTwoReg xa xb` swaps the two coset LABELS, giving
    `cosetInputTwoReg xb xa` — EXACTLY (a pure register relabel, no approximation).
    The scratch/lookup/temp/carry are preserved (the swap fixes every non-block position),
    and the two coset block factors commute. -/
theorem swapAB_cosetInputTwoReg (w bits N cm xa xb : Nat) :
    Framework.uc_eval (Gate.toUCom (cosetDim w bits) (swapAB w bits))
        * cosetInputVec w bits N cm xa xb
      = cosetInputVec w bits N cm xb xa := by
  have hwt := swapAB_wellTyped w bits
  set σ := gateToPerm (swapAB w bits) (cosetDim w bits) hwt with hσ
  -- Forward direction (no involution): `permState σ` sends `xb xa` to `xa xb`.
  have key : permState σ (cosetInputVec w bits N cm xb xa)
      = cosetInputVec w bits N cm xa xb := by
    funext idx z
    obtain rfl : z = 0 := Subsingleton.elim z 0
    obtain ⟨φ, hidx⟩ : ∃ φ, funboolNat (cosetDim w bits) φ = idx :=
      ⟨(funboolEquiv (cosetDim w bits)).symm idx, by
        exact Equiv.apply_symm_apply (funboolEquiv (cosetDim w bits)) idx⟩
    show cosetInputTwoReg w bits N cm xb xa (σ idx) 0
      = cosetInputTwoReg w bits N cm xa xb idx 0
    rw [← hidx, hσ, gateToPerm_funboolNat (swapAB w bits) (cosetDim w bits) hwt φ,
        cosetInputTwoReg_funboolNat w bits N cm xb xa (applyFin (swapAB w bits) (cosetDim w bits) φ),
        cosetInputTwoReg_funboolNat w bits N cm xa xb φ,
        extendBool_applyFin (swapAB w bits) (cosetDim w bits) hwt φ]
    by_cases hcl : scratchClean w bits (extendBool (cosetDim w bits) φ)
    · rw [if_pos hcl, if_pos ((swapAB_scratchClean w bits _).mpr hcl)]
      simp only [swapAB_decodeA w bits (extendBool (cosetDim w bits) φ),
                 swapAB_decodeB w bits (extendBool (cosetDim w bits) φ)]
      ring
    · rw [if_neg hcl, if_neg (fun h => hcl ((swapAB_scratchClean w bits _).mp h))]
  rw [uc_eval_eq_permState (swapAB w bits) (cosetDim w bits) hwt, ← hσ, ← key]
  funext idx z
  simp only [permState, Equiv.apply_symm_apply]

/-- **Symmetric form** (criterion 4): the same lemma with the labels swapped — the swap
    is its own inverse on the coset input. -/
theorem swapAB_cosetInputTwoReg_symm (w bits N cm xa xb : Nat) :
    Framework.uc_eval (Gate.toUCom (cosetDim w bits) (swapAB w bits))
        * cosetInputVec w bits N cm xb xa
      = cosetInputVec w bits N cm xa xb :=
  swapAB_cosetInputTwoReg w bits N cm xb xa

end FormalRV.Shor.GidneyInPlace.InPlaceSwapBlocks
