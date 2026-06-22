/-
  FormalRV.Shor.MeasuredCoherentUncompute — GAP ① brick 1: the PHYSICAL measurement-uncompute
  channel = the reversible re-read, AS QUANTUM CHANNELS on loaded SUPERPOSITIONS.
  ════════════════════════════════════════════════════════════════════════════════════════════

  THE COHERENCE KEYSTONE.  `MeasuredWindowedModN.mzClear_eq_lookupRead_on_loaded` proves the
  measurement-clear equals the reversible re-read at the VALUE (single-basis-state) level.  But the
  Shor success bound needs the AMPLITUDE/SUPERPOSITION level: the success probability lives in the
  QPE control-register marginal, which is destroyed if the uncompute decoheres the data.  The naive
  Z-basis measure-and-reset (`EGateToUnitaryBridge.measReset`) DOES decohere (it reveals which-path
  info about a data-dependent ancilla).  The PHYSICAL Gidney uncompute does not — it measures in the
  X basis with a CZ-based phase fixup, whose superposition-level perfection is
  `PhaseLookupFixup.measWordUncompute_phaseLookup` (axiom-clean).

  This file welds those two: on a SUPERPOSITION `∑ᵢ αᵢ|gᵢ⟩` of loaded states (lookup ctrl set,
  AND-ladder clean, address holding `addr i`, word holding `T[addr i]`), the physical
  measurement-uncompute CHANNEL equals the re-read UNITARY's conjugation —

      `c_eval (measWordUncompute … phaseLookup … W) (ψψ†) = U (ψψ†) U†`,   U := lookupReadAt,

  with ALL coherences `|gᵢ⟩⟨gⱼ|` (i ≠ j) preserved.  This is the atom that makes "the measured
  circuit IS the unitary on the encoded subspace" go through at the amplitude level — exactly the
  off-diagonal frontier `EGateToUnitaryBridge` flagged, now closed for the lookup-uncompute gadget
  on the real phase-lookup circuit.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.PhaseLookupFixup
import FormalRV.Shor.WindowedModNShor
import FormalRV.Arithmetic.Correctness

namespace FormalRV.Shor.MeasuredCoherentUncompute

open FormalRV.Framework
open FormalRV.Framework.BaseCom
open FormalRV.BQAlgo
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.MeasuredLookupUncompute
open FormalRV.Shor.MeasuredANDUncompute (conj_outer_product)
open FormalRV.Shor.PhaseLookupFixup
open Matrix

noncomputable section

/-- Word positions are cleared to `false` by `clearWord` (the positive companion of
    `clearWord_apply_ne`), provided `pos` is injective on `[0, W)`. -/
private theorem clearWord_word_false (pos : Nat → Nat) (W : Nat)
    (hpinj : ∀ j k, j < W → k < W → pos j = pos k → j = k)
    (f : Nat → Bool) (j : Nat) (hj : j < W) :
    clearWord pos W f (pos j) = false := by
  induction W with
  | zero => omega
  | succ W ih =>
      simp only [clearWord]
      rcases Nat.lt_or_ge j W with hjW | hjW
      · have hne : pos j ≠ pos W := fun h => by
          have := hpinj j W (by omega) (Nat.lt_succ_self W) h; omega
        rw [update_neq _ _ _ _ hne]
        exact ih (fun a b ha hb hab => hpinj a b (by omega) (by omega) hab) hjW
      · have hjeq : j = W := by omega
        subst hjeq
        simp

/-- **★ COHERENCE KEYSTONE — physical measurement-uncompute = reversible re-read, as channels. ★**
    On a superposition `∑ᵢ αᵢ|gᵢ⟩` of loaded lookup states (ctrl set, ladder clean, address `addr i`,
    word `pos 0 … pos (W-1)` holding `T[addr i]`), Gidney's measurement-based lookup-uncompute with
    the CONCRETE phase-lookup fixups acts EXACTLY as the reversible re-read `lookupReadAt`'s unitary
    conjugation — coefficients and all coherences intact.  The off-diagonal (amplitude) lift of
    `MeasuredWindowedModN.mzClear_eq_lookupRead_on_loaded`. -/
theorem measUncompute_eq_reread_on_loaded
    {dim : Nat} {ι : Type*} (w W : Nat) (pos : Nat → Nat) (T : Nat → Nat)
    (hw : 0 < w) (hdim : 2 * w + 1 ≤ dim)
    (hpos : ∀ j, j < W → pos j < dim)
    (hpos_high : ∀ j, j < W → 2 * w < pos j)
    (hinj : ∀ j, j < W → ∀ k, k < W → j ≠ k → pos j ≠ pos k)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool) (addr : ι → Nat)
    (hav : ∀ i ∈ s, addr i < 2 ^ w)
    (hgood : ∀ i ∈ s, GoodState w (g i))
    (haddr : ∀ i ∈ s, ∀ k, k < w → g i (ulookup_address_idx k) = (addr i).testBit k)
    (hword : ∀ i ∈ s, ∀ j, j < W → g i (pos j) = (T (addr i)).testBit j) :
    c_eval (measWordUncompute dim pos
        (fun j => phaseLookup dim w (fun v => (T v).testBit j)) W)
        ((∑ i ∈ s, α i • f_to_vec dim (g i)) * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
      = uc_eval (Gate.toUCom dim (lookupReadAt w pos W T))
          * ((∑ i ∈ s, α i • f_to_vec dim (g i)) * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
          * (uc_eval (Gate.toUCom dim (lookupReadAt w pos W T)))ᴴ := by
  -- pos injectivity, functional form
  have hpinj : ∀ j k, j < W → k < W → pos j = pos k → j = k := by
    intro j k hj hk hjk; by_contra hne; exact hinj j hj k hk hne hjk
  -- (1) VALUE FACT — on each loaded state, re-read = clearWord
  have hread : ∀ i ∈ s, Gate.applyNat (lookupReadAt w pos W T) (g i) = clearWord pos W (g i) := by
    intro i hi
    obtain ⟨hsel_w, hsel_f⟩ := lookupReadAt_selects w W T pos (g i) (addr i) hw (hav i hi)
      (hgood i hi).1 (haddr i hi) (hgood i hi).2 hpos_high hpinj
    funext p
    by_cases hp : ∃ j, j < W ∧ p = pos j
    · obtain ⟨j, hj, rfl⟩ := hp
      rw [hsel_w j hj, hword i hi j hj, Bool.xor_self, clearWord_word_false pos W hpinj (g i) j hj]
    · have hpne : ∀ j, j < W → p ≠ pos j := fun j hj hpe => hp ⟨j, hj, hpe⟩
      rw [hsel_f p hpne, clearWord_apply_ne pos W (g i) p hpne]
  -- (2) the re-read is well-typed
  have hwt : Gate.WellTyped dim (lookupReadAt w pos W T) :=
    lookupReadAt_wellTyped w W pos T dim hw hdim
      (fun j hj => ⟨hpos j hj, by have := hpos_high j hj; simp only [ulookup_and_idx]; omega⟩)
  -- (3) the unitary sends the encoded superposition to the cleared one
  set U := Gate.toUCom dim (lookupReadAt w pos W T) with hU
  have hUbasis : ∀ i ∈ s, uc_eval U * f_to_vec dim (g i) = f_to_vec dim (clearWord pos W (g i)) := by
    intro i hi
    rw [hU, uc_eval_toUCom_acts_on_basis dim _ hwt (g i), hread i hi]
  have hUpsi : uc_eval U * (∑ i ∈ s, α i • f_to_vec dim (g i))
      = ∑ i ∈ s, α i • f_to_vec dim (clearWord pos W (g i)) := by
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Matrix.mul_smul, hUbasis i hi]
  -- (4) hword in the decoder form `measWordUncompute_phaseLookup` consumes
  have hword' : ∀ i ∈ s, ∀ j, j < W → g i (pos j) = (T (decAddr w (g i))).testBit j := by
    intro i hi j hj
    rw [decAddr_eq w (g i) (addr i) (hav i hi) (haddr i hi)]
    exact hword i hi j hj
  -- LHS: the physical channel clears the word (coherences intact)
  rw [measWordUncompute_phaseLookup w W pos T (by omega) hpos hpos_high hinj s α g hgood hword']
  -- RHS: conjugation by U of the encoded density, then U·ψ = cleared superposition
  rw [conj_outer_product (uc_eval U) (∑ i ∈ s, α i • f_to_vec dim (g i)), hUpsi]

/-- **★ BRICK 2 — compute-then-uncompute = a single net unitary conjugation. ★**  A unitary
    compute prefix `Pre` (which maps each encoded input `e i` to a loaded state `g i`) followed by
    the physical measurement-uncompute is, on the encoded superposition `∑ᵢ αᵢ|eᵢ⟩`, EXACTLY the
    conjugation by the single unitary `lookupReadAt · Pre` — coherences intact.  This is the
    reusable composition atom: it turns one (unitary ; measured-uncompute) block into a unitary,
    so the whole measured multiplier collapses to its reversible counterpart `V` block by block. -/
theorem physUncompute_after_prefix
    {dim : Nat} {ι : Type*} (w W : Nat) (pos : Nat → Nat) (T : Nat → Nat) (Pre : BaseUCom dim)
    (hw : 0 < w) (hdim : 2 * w + 1 ≤ dim)
    (hpos : ∀ j, j < W → pos j < dim)
    (hpos_high : ∀ j, j < W → 2 * w < pos j)
    (hinj : ∀ j, j < W → ∀ k, k < W → j ≠ k → pos j ≠ pos k)
    (s : Finset ι) (α : ι → ℂ) (e : ι → Nat → Bool) (g : ι → Nat → Bool) (addr : ι → Nat)
    (hload : ∀ i ∈ s, uc_eval Pre * f_to_vec dim (e i) = f_to_vec dim (g i))
    (hav : ∀ i ∈ s, addr i < 2 ^ w)
    (hgood : ∀ i ∈ s, GoodState w (g i))
    (haddr : ∀ i ∈ s, ∀ k, k < w → g i (ulookup_address_idx k) = (addr i).testBit k)
    (hword : ∀ i ∈ s, ∀ j, j < W → g i (pos j) = (T (addr i)).testBit j) :
    c_eval (Com.useq (Com.embedU Pre)
        (measWordUncompute dim pos (fun j => phaseLookup dim w (fun v => (T v).testBit j)) W))
        ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
      = (uc_eval (Gate.toUCom dim (lookupReadAt w pos W T)) * uc_eval Pre)
          * ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
          * (uc_eval (Gate.toUCom dim (lookupReadAt w pos W T)) * uc_eval Pre)ᴴ := by
  set Ur := uc_eval (Gate.toUCom dim (lookupReadAt w pos W T)) with hUr
  -- the prefix sends the encoded superposition to the loaded superposition
  have hPre : uc_eval Pre * (∑ i ∈ s, α i • f_to_vec dim (e i))
      = ∑ i ∈ s, α i • f_to_vec dim (g i) := by
    rw [Matrix.mul_sum]; refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Matrix.mul_smul, hload i hi]
  -- RHS = Ur · ((∑g)(∑g)†) · Ur†
  have hRHS : (Ur * uc_eval Pre)
        * ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
        * (Ur * uc_eval Pre)ᴴ
      = Ur * ((∑ i ∈ s, α i • f_to_vec dim (g i)) * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ) * Urᴴ := by
    rw [conj_outer_product (Ur * uc_eval Pre) (∑ i ∈ s, α i • f_to_vec dim (e i)),
        Matrix.mul_assoc Ur (uc_eval Pre) (∑ i ∈ s, α i • f_to_vec dim (e i)), hPre,
        ← conj_outer_product Ur (∑ i ∈ s, α i • f_to_vec dim (g i))]
  -- LHS: unfold the seq, conjugate by Pre, then apply brick 1
  rw [c_eval_useq, c_eval_embedU,
      conj_outer_product (uc_eval Pre) (∑ i ∈ s, α i • f_to_vec dim (e i)), hPre,
      measUncompute_eq_reread_on_loaded w W pos T hw hdim hpos hpos_high hinj s α g addr
        hav hgood haddr hword, hRHS]

/-- **★ BRICK 3a — the chaining ENGINE. ★**  Prepending a unitary prefix `Pre` (which loads the
    encoded inputs `e i` into the states `g i`) to ANY density program `C` that already acts as a
    `V`-conjugation on the loaded superposition, yields a `(V · Pre)`-conjugation on the encoded
    superposition.  This generalises `physUncompute_after_prefix` (there `C` is the uncompute and
    `V = lookupReadAt`): `C` may now be a whole already-collapsed block.  Folding this from the
    right turns the entire measured step `read·add·[mz]·reduce·read·regCompare·[mz]` into the single
    reversible-unitary conjugation, one block at a time. -/
theorem conj_after_prefix
    {dim : Nat} {ι : Type*} (C : BaseCom dim) (Pre V : BaseUCom dim)
    (s : Finset ι) (α : ι → ℂ) (e : ι → Nat → Bool) (g : ι → Nat → Bool)
    (hload : ∀ i ∈ s, uc_eval Pre * f_to_vec dim (e i) = f_to_vec dim (g i))
    (hC : c_eval C ((∑ i ∈ s, α i • f_to_vec dim (g i)) * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
        = uc_eval V * ((∑ i ∈ s, α i • f_to_vec dim (g i)) * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
            * (uc_eval V)ᴴ) :
    c_eval (Com.useq (Com.embedU Pre) C)
        ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
      = (uc_eval V * uc_eval Pre)
          * ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
          * (uc_eval V * uc_eval Pre)ᴴ := by
  have hPre : uc_eval Pre * (∑ i ∈ s, α i • f_to_vec dim (e i))
      = ∑ i ∈ s, α i • f_to_vec dim (g i) := by
    rw [Matrix.mul_sum]; refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Matrix.mul_smul, hload i hi]
  have hRHS : (uc_eval V * uc_eval Pre)
        * ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
        * (uc_eval V * uc_eval Pre)ᴴ
      = uc_eval V
          * ((∑ i ∈ s, α i • f_to_vec dim (g i)) * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
          * (uc_eval V)ᴴ := by
    rw [conj_outer_product (uc_eval V * uc_eval Pre) (∑ i ∈ s, α i • f_to_vec dim (e i)),
        Matrix.mul_assoc (uc_eval V) (uc_eval Pre) (∑ i ∈ s, α i • f_to_vec dim (e i)), hPre,
        ← conj_outer_product (uc_eval V) (∑ i ∈ s, α i • f_to_vec dim (g i))]
  rw [c_eval_useq, c_eval_embedU,
      conj_outer_product (uc_eval Pre) (∑ i ∈ s, α i • f_to_vec dim (e i)), hPre, hC, hRHS]

/-- **Density push-through for a unitary gate.**  Embedding a well-typed reversible gate `G` as a
    density program acts on an encoded superposition exactly by `Gate.applyNat G` on each branch,
    coefficients and coherences intact.  The unitary (non-measured) blocks of the measured step
    propagate through the fold by this lemma. -/
theorem embedU_gate_on_superposition
    {dim : Nat} {ι : Type*} (G : Gate) (hwt : Gate.WellTyped dim G)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool) :
    c_eval (Com.embedU (Gate.toUCom dim G))
        ((∑ i ∈ s, α i • f_to_vec dim (g i)) * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
      = (∑ i ∈ s, α i • f_to_vec dim (Gate.applyNat G (g i)))
          * (∑ i ∈ s, α i • f_to_vec dim (Gate.applyNat G (g i)))ᴴ := by
  have hpush : uc_eval (Gate.toUCom dim G) * (∑ i ∈ s, α i • f_to_vec dim (g i))
      = ∑ i ∈ s, α i • f_to_vec dim (Gate.applyNat G (g i)) := by
    rw [Matrix.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_smul, uc_eval_toUCom_acts_on_basis dim G hwt (g i)]
  rw [c_eval_embedU, conj_outer_product (uc_eval (Gate.toUCom dim G))
        (∑ i ∈ s, α i • f_to_vec dim (g i)), hpush]

end

end FormalRV.Shor.MeasuredCoherentUncompute
