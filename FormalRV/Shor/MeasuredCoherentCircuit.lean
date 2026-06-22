/-
  FormalRV.Shor.MeasuredCoherentCircuit — GAP ① brick 3: lift the PHYSICAL measured-STEP
  density-channel equality up to the WHOLE physical measured modular multiplier.
  ════════════════════════════════════════════════════════════════════════════════════════════

  `MeasuredCoherentStep.physMeasStep_channel` proves the PHYSICAL measured mod-N lookup-add STEP,
  as a density channel on an encoded superposition of clean inputs, equals the reversible
  `modNLookupAddStep`'s unitary conjugation — coefficients and ALL coherences intact.  This file
  mirrors the VALUE-level fold/transport of `MeasuredWindowedModN` at the density (superposition)
  level:

    • `physMeasWindowedModNStep`  — `copyWindow ; physMeasModNLookupAddStep ; copyWindow`, the
      density analog of `measWindowedModNStep`;
    • `physMeasWindowedModNMul`   — the left-fold of window steps, the density analog of
      `measWindowedModNMul`;
    • `physMeasWindowedModNMulInPlace` — two passes around `accYSwap`, the density analog of
      `measWindowedModNMulInPlace`.

  The headline `physMeasWindowedModNMulInPlace_channel` is the amplitude-level lift of
  `MeasuredWindowedModN.measWindowedModNMulInPlace_eq`: on an encoded superposition of per-component
  `ModNMulReady` inputs (each with its own multiplicand `y i < N`), the whole physical measured
  multiplier's channel equals `uc_eval(toUCom (windowedModNMulInPlace …))` conjugation, ALL
  coherences intact.

  The proof reuses the EXACT register/frame bookkeeping of the value template, applied per
  component (∀ i ∈ s), and pushes the unitary `copyWindow` wrappers through the density layer with
  `embedU_gate_on_superposition`, the measured step through with `physMeasStep_channel`.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.MeasuredCoherentStep

namespace FormalRV.Shor.MeasuredCoherentCircuit

open FormalRV.Framework
open FormalRV.Framework.BaseCom
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.MeasuredLookupUncompute
open FormalRV.Shor.MeasuredANDUncompute (conj_outer_product)
open FormalRV.Shor.PhaseLookupFixup
open FormalRV.Shor.MeasuredCoherentUncompute
open FormalRV.Shor.MeasuredWindowedModN
open FormalRV.Shor.MeasuredCoherentStep
open Matrix

noncomputable section

/-! ## §0. A reusable repackaging lemma.

The density transports keep flipping between two shapes of a pure ensemble: the *outer-product*
shape `(∑ᵢ αᵢ|gᵢ⟩)(∑ᵢ αᵢ|gᵢ⟩)ᴴ` and that same shape after a well-typed gate `G`,
`(∑ᵢ αᵢ|applyNat G gᵢ⟩)(…)ᴴ`.  The conjugation `U ρ Uᴴ` (with `U = uc_eval (toUCom G)`) carries
the first to the second.  This is the per-component push reused at every block. -/

/-- **Conjugation by a well-typed gate's unitary = the pushed superposition's outer product.** -/
theorem conj_eq_pushed_superposition
    {dim : Nat} {ι : Type*} (G : Gate) (hwt : Gate.WellTyped dim G)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool) :
    uc_eval (Gate.toUCom dim G)
        * ((∑ i ∈ s, α i • f_to_vec dim (g i)) * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
        * (uc_eval (Gate.toUCom dim G))ᴴ
      = (∑ i ∈ s, α i • f_to_vec dim (Gate.applyNat G (g i)))
          * (∑ i ∈ s, α i • f_to_vec dim (Gate.applyNat G (g i)))ᴴ := by
  have hpush : uc_eval (Gate.toUCom dim G) * (∑ i ∈ s, α i • f_to_vec dim (g i))
      = ∑ i ∈ s, α i • f_to_vec dim (Gate.applyNat G (g i)) := by
    rw [Matrix.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_smul, uc_eval_toUCom_acts_on_basis dim G hwt (g i)]
  rw [conj_outer_product (uc_eval (Gate.toUCom dim G)) (∑ i ∈ s, α i • f_to_vec dim (g i)), hpush]

/-! ## §1. The density measured window step + its channel transport. -/

/-- **The PHYSICAL measured mod-N window step as a density program.**  `copyWindow` (T-free,
    embedded as a unitary), then the PHYSICAL measured mod-N lookup-add step
    (`physMeasModNLookupAddStep`), then `copyWindow` again — the density analog of the `EGate`
    `MeasuredWindowedModN.measWindowedModNStep`. -/
def physMeasWindowedModNStep (w bits a N q_start yBase flagPos dim j : Nat) : BaseCom dim :=
  Com.useq (Com.embedU (Gate.toUCom dim (copyWindow w yBase j)))
    (Com.useq (physMeasModNLookupAddStep w bits N (WindowedArith.tableValue a N w j)
        q_start flagPos dim)
      (Com.embedU (Gate.toUCom dim (copyWindow w yBase j))))

/-- **★ COHERENCE-LEVEL WINDOW-STEP TRANSPORT ★** — the physical measured mod-N window step, as a
    density channel on an encoded superposition `∑ᵢ αᵢ|eᵢ⟩` whose every component `eᵢ` is a
    `ModNStepInv`-state (with its own multiplicand `Y i` and accumulator value `S i < N`), equals
    the reversible `windowedModNStep`'s unitary conjugation, coefficients and ALL coherences
    intact.  The amplitude-level lift of `MeasuredWindowedModN.measWindowedModNStep_eq`. -/
theorem physMeasWindowedModNStep_channel
    {dim : Nat} {ι : Type*} (w bits a N numWin j : Nat)
    (Y : ι → Nat) (S : ι → Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hj : j < numWin)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim)
    (s : Finset ι) (α : ι → ℂ) (e : ι → Nat → Bool)
    (hS : ∀ i ∈ s, S i < N)
    (hg : ∀ i ∈ s, ModNStepInv w bits numWin (Y i) (S i) (e i)) :
    c_eval (physMeasWindowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
        (1 + 2 * w + (2 * bits + 1) + numWin * w) dim j)
        ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
      = uc_eval (Gate.toUCom dim (windowedModNStep w bits a N (1 + 2 * w)
            (1 + 2 * w + (2 * bits + 1)) (1 + 2 * w + (2 * bits + 1) + numWin * w) j))
          * ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
          * (uc_eval (Gate.toUCom dim (windowedModNStep w bits a N (1 + 2 * w)
            (1 + 2 * w + (2 * bits + 1)) (1 + 2 * w + (2 * bits + 1) + numWin * w) j)))ᴴ := by
  -- layout abbreviations (inlined exactly as the value template; literal so `omega` sees them)
  -- yBase   = 1 + 2 * w + (2 * bits + 1)
  -- q_start = 1 + 2 * w
  -- flagPos = 1 + 2 * w + (2 * bits + 1) + numWin * w
  -- standing position fact (window block fits)
  have hjw_le : j * w + w ≤ numWin * w := by
    have h1 : (j + 1) * w ≤ numWin * w := Nat.mul_le_mul_right w (by omega)
    have h2 : (j + 1) * w = j * w + w := by ring
    omega
  have hctrl_addr : ∀ i k, i < w → k < w →
      (1 + 2 * w + (2 * bits + 1)) + j * w + i ≠ ulookup_address_idx k :=
    ctrl_ne_addr_of_le_yBase w (1 + 2 * w + (2 * bits + 1)) j (by omega)
  -- the value `v i` loaded for component `i`, and the constant table for this window
  set T : Nat → Nat := WindowedArith.tableValue a N w j with hT
  set v : ι → Nat := fun i => WindowedArith.window w (Y i) j with hv
  -- well-typedness of the two copyWindow wrappers
  have hcw_wt : Gate.WellTyped dim (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) := by
    apply copyWindow_wellTyped w (1 + 2 * w + (2 * bits + 1)) j dim (by omega)
    · intro i hi; omega
    · intro i hi; omega
  -- the inner step is `physMeasStep_channel` with these parameters
  -- per-component cw-facts (mirror `measWindowedModNStep_eq` exactly, per i)
  set cw : ι → Nat → Bool :=
    fun i => Gate.applyNat (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) (e i) with hcw
  -- derive the pre-copyWindow facts + the post-copyWindow facts per component
  have hcw_ctrl : ∀ i ∈ s, cw i ulookup_ctrl_idx = true := fun i hi => by
    obtain ⟨hF, hD, hC, hG, hV⟩ := hg i hi
    have hg_ctrl : e i ulookup_ctrl_idx = true := by
      rw [hF ulookup_ctrl_idx (by unfold inBlock ulookup_ctrl_idx; omega)
            (by unfold ulookup_ctrl_idx; omega)]
      exact mulInputOf_ctrl cuccaroAdder w bits numWin (Y i)
    simp only [hcw]
    rw [copyWindow_frame w (1 + 2 * w + (2 * bits + 1)) j (e i) _
      (fun k hk => by unfold ulookup_ctrl_idx ulookup_address_idx; omega)]
    exact hg_ctrl
  have hcw_addr : ∀ i ∈ s, ∀ k, k < w → cw i (ulookup_address_idx k) = (v i).testBit k :=
    fun i hi k hk => by
      obtain ⟨hF, hD, hC, hG, hV⟩ := hg i hi
      have hg_addr : ∀ m, m < w → e i (ulookup_address_idx m) = false := fun m hm => by
        rw [hF _ (by unfold inBlock ulookup_address_idx; omega)
              (by unfold ulookup_address_idx; omega)]
        exact mulInputOf_low cuccaroAdder w bits numWin (Y i) _
          (by unfold ulookup_ctrl_idx ulookup_address_idx; omega)
          (by unfold ulookup_address_idx; omega)
      have hg_y : ∀ m, m < w →
          e i ((1 + 2 * w + (2 * bits + 1)) + j * w + m)
            = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) (Y i)
                ((1 + 2 * w + (2 * bits + 1)) + j * w + m) := fun m hm => by
        rw [hF _ (by unfold inBlock; omega) (by omega)]
        exact mulInputOf_eq_encodeReg cuccaroAdder w bits numWin (Y i) _
          (by unfold ulookup_ctrl_idx; omega)
      simp only [hcw, hv]
      exact copyWindow_loads_window w (1 + 2 * w + (2 * bits + 1)) numWin (Y i) j (e i)
        hctrl_addr hg_addr hg_y hj k hk
  have hcw_and : ∀ i ∈ s, ∀ k, k < w → cw i (ulookup_and_idx k) = false := fun i hi k hk => by
    obtain ⟨hF, hD, hC, hG, hV⟩ := hg i hi
    have hg_and : e i (ulookup_and_idx k) = false := by
      rw [hF _ (by unfold inBlock ulookup_and_idx; omega) (by unfold ulookup_and_idx; omega)]
      exact mulInputOf_low cuccaroAdder w bits numWin (Y i) _
        (by unfold ulookup_ctrl_idx ulookup_and_idx; omega) (by unfold ulookup_and_idx; omega)
    simp only [hcw]
    rw [copyWindow_frame w (1 + 2 * w + (2 * bits + 1)) j (e i) _
      (fun m hm => by unfold ulookup_and_idx ulookup_address_idx; omega)]
    exact hg_and
  have hcw_addend : ∀ i ∈ s, ∀ k, k < bits → cw i (addendIdx (1 + 2 * w) k) = false :=
    fun i hi k hk => by
      obtain ⟨hF, hD, hC, hG, hV⟩ := hg i hi
      simp only [hcw]
      rw [copyWindow_frame w (1 + 2 * w + (2 * bits + 1)) j (e i) _
        (fun m hm => by unfold addendIdx ulookup_address_idx; omega)]
      exact hD k hk
  have hcw_acc : ∀ i ∈ s, ∀ k, k < bits → cw i ((1 + 2 * w) + 2 * k + 1) = (S i).testBit k :=
    fun i hi k hk => by
      obtain ⟨hF, hD, hC, hG, hV⟩ := hg i hi
      simp only [hcw]
      rw [copyWindow_frame w (1 + 2 * w + (2 * bits + 1)) j (e i) _
        (fun m hm => by unfold ulookup_address_idx; omega)]
      exact hV k hk
  have hcw_cin : ∀ i ∈ s, cw i (1 + 2 * w) = false := fun i hi => by
    obtain ⟨hF, hD, hC, hG, hV⟩ := hg i hi
    simp only [hcw]
    rw [copyWindow_frame w (1 + 2 * w + (2 * bits + 1)) j (e i) _
      (fun m hm => by unfold ulookup_address_idx; omega)]
    exact hC
  have hcw_flag : ∀ i ∈ s, cw i (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := fun i hi => by
    obtain ⟨hF, hD, hC, hG, hV⟩ := hg i hi
    simp only [hcw]
    rw [copyWindow_frame w (1 + 2 * w + (2 * bits + 1)) j (e i) _
      (fun m hm => by unfold ulookup_address_idx; omega)]
    exact hG
  -- value bounds for `physMeasStep_channel`
  have hv_lt : ∀ i ∈ s, v i < 2 ^ w := fun i _ => WindowedArith.window_lt w (Y i) j
  have hTv_lt : ∀ i ∈ s, T (v i) < N := fun i _ => by
    simp only [hT]; unfold WindowedArith.tableValue; exact Nat.mod_lt _ hN_pos
  -- ════ push the superposition through the density program ════
  unfold physMeasWindowedModNStep
  -- copyWindow #1
  rw [c_eval_useq, embedU_gate_on_superposition (copyWindow w (1 + 2 * w + (2 * bits + 1)) j)
        hcw_wt s α e]
  -- (`set cw` already folds `applyNat (copyWindow ...) (e i)` to `cw i` in the goal)
  -- the measured step (= the reversible step's conjugation, on the loaded superposition)
  rw [c_eval_useq,
      physMeasStep_channel w bits N T (1 + 2 * w) (1 + 2 * w + (2 * bits + 1) + numWin * w)
        s α cw v S
        hw hN_pos hN2 (by omega) (by omega) (by omega) (by omega)
        hv_lt hS hTv_lt hcw_ctrl hcw_addr hcw_and hcw_addend hcw_acc hcw_cin hcw_flag]
  -- well-typedness of the inner reversible step (for repackaging) and the outer step
  have hwt_step : Gate.WellTyped dim
      (modNLookupAddStep w bits N T (1 + 2 * w) (1 + 2 * w + (2 * bits + 1) + numWin * w)) := by
    have h_look : Gate.WellTyped dim (lookupReadAt w (addendIdx (1 + 2 * w)) bits T) := by
      apply lookupReadAt_wellTyped w bits (addendIdx (1 + 2 * w)) T dim hw (by omega)
      intro jj hjj; unfold addendIdx ulookup_and_idx; constructor <;> omega
    exact ⟨h_look, cuccaro_n_bit_adder_full_wellTyped bits (1 + 2 * w) dim (by omega),
      h_look,
      modNReduceFlag_wellTyped bits (1 + 2 * w) N (1 + 2 * w + (2 * bits + 1) + numWin * w) dim
        (by omega) (by omega) (by omega) (by intro i hi; omega),
      h_look, regCompareXor_wellTyped bits (1 + 2 * w) (1 + 2 * w + (2 * bits + 1) + numWin * w) dim
        (by omega) (by omega) (by omega),
      h_look⟩
  -- repackage the inner conjugation as the pushed superposition `∑ α • |applyNat step (cw i)⟩`
  rw [conj_eq_pushed_superposition (modNLookupAddStep w bits N T (1 + 2 * w)
        (1 + 2 * w + (2 * bits + 1) + numWin * w)) hwt_step s α cw]
  -- copyWindow #2
  rw [c_eval_embedU,
      conj_eq_pushed_superposition (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) hcw_wt s α
        (fun i => Gate.applyNat (modNLookupAddStep w bits N T (1 + 2 * w)
          (1 + 2 * w + (2 * bits + 1) + numWin * w)) (cw i))]
  -- the whole window step sends each `e i` to its image; repackage the RHS conjugation
  have hwt_win : Gate.WellTyped dim
      (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
        (1 + 2 * w + (2 * bits + 1) + numWin * w) j) := by
    refine ⟨hcw_wt, ?_, hcw_wt⟩
    -- the table inside windowedModNStep is `tableValue a N w j = T`
    show Gate.WellTyped dim (modNLookupAddStep w bits N (WindowedArith.tableValue a N w j)
      (1 + 2 * w) (1 + 2 * w + (2 * bits + 1) + numWin * w))
    rw [← hT]; exact hwt_step
  rw [conj_eq_pushed_superposition (windowedModNStep w bits a N (1 + 2 * w)
        (1 + 2 * w + (2 * bits + 1)) (1 + 2 * w + (2 * bits + 1) + numWin * w) j) hwt_win s α e]
  -- both sides are now `(∑ α • |g i⟩)(…)ᴴ`; match the per-component images
  have himg : ∀ i,
      Gate.applyNat (copyWindow w (1 + 2 * w + (2 * bits + 1)) j)
          (Gate.applyNat (modNLookupAddStep w bits N T (1 + 2 * w)
            (1 + 2 * w + (2 * bits + 1) + numWin * w)) (cw i))
        = Gate.applyNat (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) j) (e i) := fun i => by
    simp only [windowedModNStep, Gate.applyNat_seq, hcw, hT]
  have hsum : (∑ i ∈ s, α i • f_to_vec dim
        (Gate.applyNat (copyWindow w (1 + 2 * w + (2 * bits + 1)) j)
          (Gate.applyNat (modNLookupAddStep w bits N T (1 + 2 * w)
            (1 + 2 * w + (2 * bits + 1) + numWin * w)) (cw i))))
      = ∑ i ∈ s, α i • f_to_vec dim
          (Gate.applyNat (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) j) (e i)) :=
    Finset.sum_congr rfl (fun i _ => by rw [himg i])
  rw [hsum]

/-! ## §2. The density measured per-window multiplier (fold) + its channel transport. -/

/-- Window-step well-typedness (public; the value version in `WindowedModNShor` is `private`). -/
theorem windowedModNStep_wellTyped' (w bits a N numWin j dim : Nat)
    (hw : 0 < w) (hj : j < numWin)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) :
    Gate.WellTyped dim
      (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
        (1 + 2 * w + (2 * bits + 1) + numWin * w) j) := by
  have hjw' : j * w + w ≤ numWin * w := by
    have h1 : (j + 1) * w ≤ numWin * w := Nat.mul_le_mul_right w (by omega)
    have h2 : (j + 1) * w = j * w + w := by ring
    omega
  have hcw : Gate.WellTyped dim (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) := by
    apply copyWindow_wellTyped w (1 + 2 * w + (2 * bits + 1)) j dim (by omega)
    · intro i hi; omega
    · intro i hi; omega
  refine ⟨hcw, ?_, hcw⟩
  have h_look : Gate.WellTyped dim
      (lookupReadAt w (addendIdx (1 + 2 * w)) bits (WindowedArith.tableValue a N w j)) := by
    apply lookupReadAt_wellTyped w bits (addendIdx (1 + 2 * w)) _ dim hw (by omega)
    intro jj hjj; unfold addendIdx ulookup_and_idx; constructor <;> omega
  exact ⟨h_look, cuccaro_n_bit_adder_full_wellTyped bits (1 + 2 * w) dim (by omega),
    h_look,
    modNReduceFlag_wellTyped bits (1 + 2 * w) N (1 + 2 * w + (2 * bits + 1) + numWin * w) dim
      (by omega) (by omega) (by omega) (by intro i hi; omega),
    h_look, regCompareXor_wellTyped bits (1 + 2 * w) (1 + 2 * w + (2 * bits + 1) + numWin * w) dim
      (by omega) (by omega) (by omega),
    h_look⟩

/-- Well-typedness of the unitary per-window multiplier fold for any prefix `n ≤ numWin`. -/
theorem windowedModNMul_wellTyped' (w bits a N numWin dim : Nat)
    (hw : 0 < w) (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) :
    ∀ n, n ≤ numWin →
      Gate.WellTyped dim
        (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) n) := by
  intro n hn
  unfold windowedModNMul
  apply wellTyped_foldl_seq_range _ n dim (by omega)
  intro j hj
  exact windowedModNStep_wellTyped' w bits a N numWin j dim hw (by omega) hdim

/-- **The PHYSICAL measured per-window mod-N multiplier as a density program**: a left fold of
    `physMeasWindowedModNStep` over `List.range numWin`, starting from the embedded identity.  The
    density analog of `MeasuredWindowedModN.measWindowedModNMul`; splits under `c_eval_useq` the
    same way the value fold splits under `EGate.applyNat`. -/
def physMeasWindowedModNMul (w bits a N q_start yBase flagPos dim numWin : Nat) : BaseCom dim :=
  (List.range numWin).foldl
    (fun g j => Com.useq g (physMeasWindowedModNStep w bits a N q_start yBase flagPos dim j))
    (Com.embedU (Gate.toUCom dim Gate.I))

/-- **★ COHERENCE-LEVEL FOLD TRANSPORT (generalized) ★** — on an encoded superposition whose every
    component is a `ModNStepInv`-state (with its own multiplicand `Y i` and accumulator `S i < N`),
    the density measured per-window multiplier's channel equals the reversible
    `windowedModNMul`'s unitary conjugation, for every prefix `n ≤ numWin`.  Density analog of
    `MeasuredWindowedModN.measWindowedModNMul_eq_gen`, the per-component invariant maintained by
    `unitFold_inv_gen`. -/
theorem physMeasWindowedModNMul_channel_gen
    {dim : Nat} {ι : Type*} (w bits a N numWin : Nat)
    (Y : ι → Nat) (S : ι → Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim)
    (s : Finset ι) (α : ι → ℂ) (e : ι → Nat → Bool)
    (hS : ∀ i ∈ s, S i < N)
    (hg : ∀ i ∈ s, ModNStepInv w bits numWin (Y i) (S i) (e i)) :
    ∀ n, n ≤ numWin →
      c_eval (physMeasWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) dim n)
          ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
        = uc_eval (Gate.toUCom dim (windowedModNMul w bits a N (1 + 2 * w)
              (1 + 2 * w + (2 * bits + 1)) (1 + 2 * w + (2 * bits + 1) + numWin * w) n))
            * ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
            * (uc_eval (Gate.toUCom dim (windowedModNMul w bits a N (1 + 2 * w)
              (1 + 2 * w + (2 * bits + 1)) (1 + 2 * w + (2 * bits + 1) + numWin * w) n)))ᴴ := by
  intro n
  induction n with
  | zero =>
    intro _
    -- both folds are the embedded identity; the channel is the identity conjugation
    simp only [physMeasWindowedModNMul, List.range_zero, List.foldl_nil, windowedModNMul,
      c_eval_embedU]
  | succ n ih =>
    intro hn
    have hn' : n ≤ numWin := by omega
    -- split both folds at the last window (same shape as the value template)
    have hsplit_m : physMeasWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) dim (n + 1)
        = Com.useq (physMeasWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) dim n)
            (physMeasWindowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) dim n) := by
      unfold physMeasWindowedModNMul
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hsplit_u : windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) (n + 1)
        = Gate.seq (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
            (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n) := by
      unfold windowedModNMul
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit_m, c_eval_useq, ih hn']
    -- well-typedness of the n-window prefix fold
    have hwt_fold : Gate.WellTyped dim
        (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) n) :=
      windowedModNMul_wellTyped' w bits a N numWin dim hw hdim n hn'
    -- the IH's conjugation = the pushed superposition over the evolved per-component states
    set gn : ι → Nat → Bool :=
      fun i => Gate.applyNat (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
        (1 + 2 * w + (2 * bits + 1) + numWin * w) n) (e i) with hgn
    rw [conj_eq_pushed_superposition (windowedModNMul w bits a N (1 + 2 * w)
          (1 + 2 * w + (2 * bits + 1)) (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
          hwt_fold s α e]
    -- the evolved states are still `ModNStepInv` with some per-component accumulator < N
    have hinv : ∀ i ∈ s, ∃ sn, sn < N ∧ ModNStepInv w bits numWin (Y i) sn (gn i) := fun i hi =>
      unitFold_inv_gen w bits a N numWin (Y i) hw hN_pos hN2 (S i) (e i) (hS i hi) (hg i hi) n hn'
    -- choose the per-component evolved accumulator
    classical
    set Sn : ι → Nat := fun i => if h : i ∈ s then (hinv i h).choose else 0 with hSn
    have hSn_lt : ∀ i ∈ s, Sn i < N := fun i hi => by
      simp only [hSn, dif_pos hi]; exact (hinv i hi).choose_spec.1
    have hgn_inv : ∀ i ∈ s, ModNStepInv w bits numWin (Y i) (Sn i) (gn i) := fun i hi => by
      simp only [hSn, dif_pos hi]; exact (hinv i hi).choose_spec.2
    -- the new step's channel, on the evolved superposition
    rw [physMeasWindowedModNStep_channel w bits a N numWin n Y Sn hw hN_pos hN2
          (show n < numWin by omega) hdim s α gn hSn_lt hgn_inv]
    -- repackage: fold the unitary step back into the (n+1)-window unitary
    rw [hsplit_u]
    -- both sides are conjugation of ρ₀ by the composed unitary; chain the two conjugations
    have hwt_step : Gate.WellTyped dim
        (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) n) :=
      windowedModNStep_wellTyped' w bits a N numWin n dim hw (by omega) hdim
    -- conjugation by the step, of the conjugation by the prefix = conjugation by the composition
    rw [conj_eq_pushed_superposition (windowedModNStep w bits a N (1 + 2 * w)
          (1 + 2 * w + (2 * bits + 1)) (1 + 2 * w + (2 * bits + 1) + numWin * w) n) hwt_step s α gn,
        conj_eq_pushed_superposition (Gate.seq (windowedModNMul w bits a N (1 + 2 * w)
          (1 + 2 * w + (2 * bits + 1)) (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
          (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n)) ⟨hwt_fold, hwt_step⟩ s α e]
    -- the per-component images match: step ∘ prefix = composed gate, on each `e i`
    have himg : ∀ i,
        Gate.applyNat (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n) (gn i)
          = Gate.applyNat (Gate.seq (windowedModNMul w bits a N (1 + 2 * w)
              (1 + 2 * w + (2 * bits + 1)) (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
              (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
                (1 + 2 * w + (2 * bits + 1) + numWin * w) n)) (e i) := fun i => by
      simp only [Gate.applyNat_seq, hgn]
    have hsum : (∑ i ∈ s, α i • f_to_vec dim
          (Gate.applyNat (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n) (gn i)))
        = ∑ i ∈ s, α i • f_to_vec dim
            (Gate.applyNat (Gate.seq (windowedModNMul w bits a N (1 + 2 * w)
              (1 + 2 * w + (2 * bits + 1)) (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
              (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
                (1 + 2 * w + (2 * bits + 1) + numWin * w) n)) (e i)) :=
      Finset.sum_congr rfl (fun i _ => by rw [himg i])
    rw [hsum]

/-- **The full density measured per-window mod-N multiplier circuit** at the standard layout
    (the density analog of `MeasuredWindowedModN.measWindowedModNMulCircuit`). -/
def physMeasWindowedModNMulCircuit (w bits a N dim numWin : Nat) : BaseCom dim :=
  physMeasWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
    (1 + 2 * w + (2 * bits + 1) + numWin * w) dim numWin

/-- **★ COHERENCE-LEVEL CIRCUIT TRANSPORT (generalized) ★** — the density measured per-window
    multiplier CIRCUIT's channel = `windowedModNMulCircuit`'s conjugation, on any per-component
    `ModNStepInv` superposition.  Density analog of `measWindowedModNMulCircuit_eq_gen`. -/
theorem physMeasWindowedModNMulCircuit_channel_gen
    {dim : Nat} {ι : Type*} (w bits a N numWin : Nat)
    (Y : ι → Nat) (S : ι → Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim)
    (s : Finset ι) (α : ι → ℂ) (e : ι → Nat → Bool)
    (hS : ∀ i ∈ s, S i < N)
    (hg : ∀ i ∈ s, ModNStepInv w bits numWin (Y i) (S i) (e i)) :
    c_eval (physMeasWindowedModNMulCircuit w bits a N dim numWin)
        ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
      = uc_eval (Gate.toUCom dim (windowedModNMulCircuit w bits a N numWin))
          * ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
          * (uc_eval (Gate.toUCom dim (windowedModNMulCircuit w bits a N numWin)))ᴴ := by
  unfold physMeasWindowedModNMulCircuit windowedModNMulCircuit
  exact physMeasWindowedModNMul_channel_gen w bits a N numWin Y S hw hN_pos hN2 hdim s α e hS hg
    numWin (le_refl numWin)

/-! ## §3. The density measured IN-PLACE multiplier + the headline channel transport. -/

/-- **The post-pass-1 + swap state is a `ModNStepInv` for pass 2.**  Mirrors the value bookkeeping
    inside `MeasuredWindowedModN.measWindowedModNMulInPlace_eq` (using only public lemmas): on a
    `ModNMulReady` input `f` with y-value `y < N`, the unitary `windowedModNMulCircuit a` followed
    by `accYSwap` leaves a `ModNStepInv` state with multiplicand `(a·y) mod N` and accumulator
    value `y`.  This is the input characterization the second pass consumes. -/
theorem postSwap_ModNStepInv (w bits a N numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < N) (f : Nat → Bool) (hf : ModNMulReady w bits numWin y f) :
    ModNStepInv w bits numWin (a * y % N) y
      (Gate.applyNat (accYSwap cuccaroAdder w bits)
        (Gate.applyNat (windowedModNMulCircuit w bits a N numWin) f)) := by
  have hN_le : N ≤ 2 ^ bits := by omega
  have hpow : (2 : Nat) ^ (w * numWin) = 2 ^ bits := by rw [Nat.mul_comm w numWin, hbits]
  have hy1 : y < 2 ^ (w * numWin) := by rw [hpow]; exact Nat.lt_of_lt_of_le hy hN_le
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  -- public replacement for the private `mulInputOf_cuccaro_y_bit`
  have hy_bit : ∀ (v i : Nat), i < numWin * w →
      mulInputOf cuccaroAdder w bits numWin v (1 + 2 * w + (2 * bits + 1) + i) = v.testBit i := by
    intro v i hi
    rw [mulInputOf_eq_encodeReg cuccaroAdder w bits numWin v _ (by unfold ulookup_ctrl_idx; omega)]
    exact encodeReg_at _ _ _ i hi
  set s1 : Nat → Bool := Gate.applyNat (windowedModNMulCircuit w bits a N numWin) f with hs1def
  set s2 : Nat → Bool := Gate.applyNat (accYSwap cuccaroAdder w bits) s1 with hs2def
  have h1 := modNStepInv_full_pass w bits a N numWin y 0 hw hN_pos hN2 hN_pos hy1 f hf.toStepInv
  rw [Nat.zero_add] at h1
  obtain ⟨h1F, h1D, h1C, h1G, h1V⟩ := h1
  rw [← hs1def] at h1F h1D h1C h1G h1V
  have h1y : ∀ i, i < bits → s1 (1 + 2 * w + (2 * bits + 1) + i) = y.testBit i := by
    intro i hi
    rw [h1F _ (by unfold inBlock; omega) (by omega)]
    exact hy_bit y i (by omega)
  obtain ⟨hsw_acc, hsw_y, hsw_fr⟩ := accYSwap_apply cuccaroAdder w bits s1
    (fun i j _ _ h => cuccaroAdder_augendIdx_inj (1 + 2 * w) i j h)
  rw [← hs2def] at hsw_acc hsw_y hsw_fr
  have hsw_acc' : ∀ i, i < bits →
      s2 (1 + 2 * w + 2 * i + 1) = s1 (1 + 2 * w + (2 * bits + 1) + i) := fun i hi => hsw_acc i hi
  have hsw_y' : ∀ i, i < bits →
      s2 (1 + 2 * w + (2 * bits + 1) + i) = s1 (1 + 2 * w + 2 * i + 1) := fun i hi => hsw_y i hi
  have hsw_fr' : ∀ p, (∀ i, i < bits →
      p ≠ 1 + 2 * w + 2 * i + 1 ∧ p ≠ 1 + 2 * w + (2 * bits + 1) + i) → s2 p = s1 p :=
    fun p hp => hsw_fr p (fun i hi => hp i hi)
  have h2F : ∀ p, ¬ inBlock (1 + 2 * w) (2 * bits + 1) p →
      p ≠ 1 + 2 * w + (2 * bits + 1) + numWin * w →
      s2 p = mulInputOf cuccaroAdder w bits numWin (a * y % N) p := by
    intro p hpb hpf
    by_cases hpy : ∃ i, i < bits ∧ p = 1 + 2 * w + (2 * bits + 1) + i
    · obtain ⟨i, hi, rfl⟩ := hpy
      rw [hsw_y' i hi, h1V i hi, hy_bit (a * y % N) i (by omega)]
    · push Not at hpy
      have hp_out : p < 1 + 2 * w ∨ 1 + 2 * w + 2 * bits + 1 ≤ p := by unfold inBlock at hpb; omega
      rw [hsw_fr' p (fun i hi => ⟨by omega, hpy i hi⟩), h1F p hpb hpf]
      by_cases hpc : p = ulookup_ctrl_idx
      · rw [hpc, mulInputOf_ctrl, mulInputOf_ctrl]
      · rcases hp_out with hlow | hhigh
        · rw [mulInputOf_low cuccaroAdder w bits numWin y p hpc (by omega),
              mulInputOf_low cuccaroAdder w bits numWin _ p hpc (by omega)]
        · have hphigh : 1 + 2 * w + (2 * bits + 1) + bits ≤ p := by
            by_contra hcon
            exact hpy (p - (1 + 2 * w + (2 * bits + 1))) (by omega) (by omega)
          rw [mulInputOf_eq_encodeReg cuccaroAdder w bits numWin y p hpc,
              mulInputOf_eq_encodeReg cuccaroAdder w bits numWin (a * y % N) p hpc,
              encodeReg_high (1 + 2 * w + cuccaroAdder.span bits) (numWin * w) y p
                (by rw [hspan]; omega),
              encodeReg_high (1 + 2 * w + cuccaroAdder.span bits) (numWin * w) (a * y % N) p
                (by rw [hspan]; omega)]
  have h2D : ∀ i, i < bits → s2 (1 + 2 * w + 2 * i + 2) = false := by
    intro i hi; rw [hsw_fr' _ (fun k hk => ⟨by omega, by omega⟩)]; exact h1D i hi
  have h2C : s2 (1 + 2 * w) = false := by
    rw [hsw_fr' _ (fun k hk => ⟨by omega, by omega⟩)]; exact h1C
  have h2G : s2 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hsw_fr' _ (fun k hk => ⟨by omega, by omega⟩)]; exact h1G
  have h2V : ∀ i, i < bits → s2 (1 + 2 * w + 2 * i + 1) = y.testBit i := by
    intro i hi; rw [hsw_acc' i hi]; exact h1y i hi
  exact ⟨h2F, h2D, h2C, h2G, h2V⟩

/-- **The PHYSICAL measured IN-PLACE windowed mod-N multiplier as a density program** — two
    `physMeasWindowedModNMulCircuit` passes around the T-free `accYSwap` (embedded as a unitary).
    The density analog of `MeasuredWindowedModN.measWindowedModNMulInPlace`. -/
def physMeasWindowedModNMulInPlace (w bits a ainv N dim numWin : Nat) : BaseCom dim :=
  Com.useq (Com.useq (physMeasWindowedModNMulCircuit w bits a N dim numWin)
      (Com.embedU (Gate.toUCom dim (accYSwap cuccaroAdder w bits))))
    (physMeasWindowedModNMulCircuit w bits (N - ainv) N dim numWin)

/-- **★★ THE MEASURED-COHERENT IN-PLACE MULTIPLIER CHANNEL — HEADLINE ★★** — on an encoded
    superposition `∑ᵢ αᵢ|eᵢ⟩` of per-component `ModNMulReady` inputs (each with its own
    multiplicand `Y i < N`), the WHOLE physical measured modular multiplier's density channel
    equals `uc_eval(toUCom (windowedModNMulInPlace …))` conjugation — coefficients and ALL
    coherences `|eᵢ⟩⟨eⱼ|` intact.  The amplitude-level lift of
    `MeasuredWindowedModN.measWindowedModNMulInPlace_eq`.

    Pass 1 transports the clean `ModNStepInv` (partial sum 0) superposition; `accYSwap` is pushed
    through as a unitary; the post-swap state of each component is the `ModNStepInv` state
    (multiplicand `(a·Y i) mod N`, accumulator value `Y i`) characterized by `postSwap_ModNStepInv`,
    so the generalized fold transport applies to pass 2 too.

    The mod-N inverse hypotheses (`ainv < N`, `a·ainv ≡ 1`) are carried to mirror
    `measWindowedModNMulInPlace_eq`'s signature, but the channel EQUALITY itself does not depend on
    them (the measured-vs-reversible transport holds for any `a, ainv`); they are only needed
    downstream for the value-clearing of the accumulator.  Hence they are intentionally unused. -/
theorem physMeasWindowedModNMulInPlace_channel
    {dim : Nat} {ι : Type*} (w bits a ainv N numWin : Nat)
    (Y : ι → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (_hainv : ainv < N) (_hinv : a * ainv % N = 1)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim)
    (s : Finset ι) (α : ι → ℂ) (e : ι → Nat → Bool)
    (hY : ∀ i ∈ s, Y i < N)
    (hf : ∀ i ∈ s, ModNMulReady w bits numWin (Y i) (e i)) :
    c_eval (physMeasWindowedModNMulInPlace w bits a ainv N dim numWin)
        ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
      = uc_eval (Gate.toUCom dim (windowedModNMulInPlace w bits a ainv N numWin))
          * ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
          * (uc_eval (Gate.toUCom dim (windowedModNMulInPlace w bits a ainv N numWin)))ᴴ := by
  -- well-typedness facts
  have hwt_circ1 : Gate.WellTyped dim (windowedModNMulCircuit w bits a N numWin) := by
    unfold windowedModNMulCircuit
    exact windowedModNMul_wellTyped' w bits a N numWin dim hw hdim numWin (le_refl numWin)
  have hwt_swap : Gate.WellTyped dim (accYSwap cuccaroAdder w bits) :=
    accYSwap_cuccaro_wellTyped w bits dim (by omega)
  have hwt_circ2 : Gate.WellTyped dim (windowedModNMulCircuit w bits (N - ainv) N numWin) := by
    unfold windowedModNMulCircuit
    exact windowedModNMul_wellTyped' w bits (N - ainv) N numWin dim hw hdim numWin (le_refl numWin)
  -- ════ PASS 1: clean ModNStepInv superposition (accumulator value 0) ════
  unfold physMeasWindowedModNMulInPlace
  rw [c_eval_useq, c_eval_useq,
      physMeasWindowedModNMulCircuit_channel_gen w bits a N numWin Y (fun _ => 0)
        hw hN_pos hN2 hdim s α e (fun i _ => hN_pos) (fun i hi => (hf i hi).toStepInv)]
  -- repackage pass-1 conjugation as the pushed superposition over `s1 i`
  set s1 : ι → Nat → Bool :=
    fun i => Gate.applyNat (windowedModNMulCircuit w bits a N numWin) (e i) with hs1
  rw [conj_eq_pushed_superposition (windowedModNMulCircuit w bits a N numWin) hwt_circ1 s α e]
  -- ════ THE SWAP: push the embedded `accYSwap` through ════
  rw [c_eval_embedU,
      conj_eq_pushed_superposition (accYSwap cuccaroAdder w bits) hwt_swap s α s1]
  -- the post-swap per-component state `s2 i`, and its `ModNStepInv` characterization
  set s2 : ι → Nat → Bool :=
    fun i => Gate.applyNat (accYSwap cuccaroAdder w bits) (s1 i) with hs2
  have hs2_inv : ∀ i ∈ s, ModNStepInv w bits numWin (a * Y i % N) (Y i) (s2 i) := fun i hi => by
    simp only [hs2, hs1]
    exact postSwap_ModNStepInv w bits a N numWin (Y i) hw hbits hN_pos hN2 (hY i hi) (e i) (hf i hi)
  -- ════ PASS 2: the generalized fold transport on the post-swap superposition ════
  rw [physMeasWindowedModNMulCircuit_channel_gen w bits (N - ainv) N numWin
        (fun i => a * Y i % N) Y hw hN_pos hN2 hdim s α s2 hY hs2_inv]
  -- ════ REPACKAGE: chain the three unitary conjugations into the in-place gate's ════
  rw [conj_eq_pushed_superposition (windowedModNMulCircuit w bits (N - ainv) N numWin) hwt_circ2
        s α s2]
  -- the in-place gate well-typedness, and the RHS conjugation in pushed form
  have hwt_inplace : Gate.WellTyped dim (windowedModNMulInPlace w bits a ainv N numWin) :=
    ⟨⟨hwt_circ1, hwt_swap⟩, hwt_circ2⟩
  rw [conj_eq_pushed_superposition (windowedModNMulInPlace w bits a ainv N numWin) hwt_inplace s α e]
  -- per-component images match: pass2 ∘ swap ∘ pass1 (e i) = windowedModNMulInPlace (e i)
  have himg : ∀ i,
      Gate.applyNat (windowedModNMulCircuit w bits (N - ainv) N numWin) (s2 i)
        = Gate.applyNat (windowedModNMulInPlace w bits a ainv N numWin) (e i) := fun i => by
    simp only [windowedModNMulInPlace, Gate.applyNat_seq, hs2, hs1]
  have hsum : (∑ i ∈ s, α i • f_to_vec dim
        (Gate.applyNat (windowedModNMulCircuit w bits (N - ainv) N numWin) (s2 i)))
      = ∑ i ∈ s, α i • f_to_vec dim
          (Gate.applyNat (windowedModNMulInPlace w bits a ainv N numWin) (e i)) :=
    Finset.sum_congr rfl (fun i _ => by rw [himg i])
  rw [hsum]

end

end FormalRV.Shor.MeasuredCoherentCircuit
