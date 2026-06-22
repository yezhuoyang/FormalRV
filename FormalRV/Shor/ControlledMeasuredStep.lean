/-
  FormalRV.Shor.ControlledMeasuredStep — GAP ① controlled brick 1: the CONTROLLED PHYSICAL
  measured mod-N lookup-add STEP, as a density channel, equals its CONTROLLED reversible unitary
  counterpart's conjugation on encoded superpositions.
  ════════════════════════════════════════════════════════════════════════════════════════════

  This is the controlled analog of `MeasuredCoherentStep.physMeasStep_channel`.  Gidney's
  controlled modular multiplier controls ONLY the value-moving gate (the Cuccaro adder into the
  accumulator) and keeps the table loads / uncomputes UNCONTROLLED.  Consequence: at every
  uncompute measurement the addend word holds `T[v]` REGARDLESS of the control bit (the load is
  uncontrolled), so the measurement-uncompute coherence (brick 1) applies UNIFORMLY across both
  control branches — no decoherence.

  So the controlled step is the EXACT same 7-block fold as the uncontrolled one, with the Cuccaro
  adder block replaced by its controlled version `control cq (toUCom cuccaro)`.  The brick-1
  hypotheses (addend loaded = `T v`, lookup registers clean, address = `v`) hold on BOTH control
  branches because they are control-INDEPENDENT (set by the uncontrolled load), which is exactly
  why the measured uncompute = re-read bridge fires on both branches.

  CONTROL-QUBIT PLACEMENT.  The bridge `embedU_control_gate_on_superposition` needs the SYNTACTIC
  freshness `is_fresh cq (toUCom dim cuccaro)`.  Because the Cuccaro adder's `n=0` base case is
  `Gate.I = ID 0` (which touches qubit `0`), `is_fresh cq cuccaro` requires `cq ≠ 0`; the honest
  always-true placement is `cq` ABOVE the arithmetic register, `q_start + 2*bits + 1 ≤ cq`
  (a fresh precision/control qubit sitting above the multiplier, like the flag).  This is the
  hypothesis we take; it discharges both `is_fresh` (via `maxIdx_cuccaro_full`) and the
  preservation `hpres` (via `cuccaro_n_bit_adder_full_frame_above`).

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.MeasuredCoherentStep
import FormalRV.Shor.ControlledMeasuredOracle
import FormalRV.Arithmetic.Windowed.WindowedWidth

namespace FormalRV.Shor.ControlledMeasuredStep

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
open FormalRV.Shor.ControlledMeasuredOracle
open FormalRV.Framework.BaseUCom
open Matrix

noncomputable section

/-! ## §1. A reusable freshness helper: `cq` above the highest qubit ⇒ fresh in the gate. -/

/-- **`is_fresh` from a `maxIdx` upper bound.**  If the control qubit `cq` lies strictly above
    the highest qubit index touched by the `Gate` `G`, then `cq` is syntactically fresh in
    `toUCom dim G`.  Proven by induction on the `Gate` IR; the `CCX` case uses SQIR's `fresh_CCX_mp`
    on the 15-gate decomposition, the `I` case is the identity at qubit `0 < cq`. -/
theorem is_fresh_toUCom_of_maxIdx_lt {dim : Nat} (cq : Nat) :
    ∀ (G : Gate), maxIdx G < cq → is_fresh cq (Gate.toUCom dim G) := by
  intro G
  induction G with
  | I =>
      intro h
      -- toUCom dim I = ID 0 = app1 U_I 0 ; is_fresh cq (app1 _ 0) = (cq ≠ 0)
      show cq ≠ 0
      have : maxIdx Gate.I = 0 := rfl
      omega
  | X q =>
      intro h
      -- toUCom dim (X q) = X q = app1 U_X q ; is_fresh = (cq ≠ q)
      show cq ≠ q
      have : maxIdx (Gate.X q) = q := rfl
      omega
  | CX c t =>
      intro h
      -- toUCom dim (CX c t) = CNOT c t ; is_fresh = (cq ≠ c ∧ cq ≠ t)
      have hm : maxIdx (Gate.CX c t) = max c t := rfl
      exact ⟨by omega, by omega⟩
  | CCX a b c =>
      intro h
      have hm : maxIdx (Gate.CCX a b c) = max a (max b c) := rfl
      exact FormalRV.Framework.BaseUCom.fresh_CCX_mp cq a b c (by omega) (by omega) (by omega)
  | seq g₁ g₂ ih₁ ih₂ =>
      intro h
      have hm : maxIdx (Gate.seq g₁ g₂) = max (maxIdx g₁) (maxIdx g₂) := rfl
      exact ⟨ih₁ (by omega), ih₂ (by omega)⟩

/-- **`is_fresh cq cuccaro` for a control qubit above the adder register.**  Specialization of
    `is_fresh_toUCom_of_maxIdx_lt` to the Cuccaro adder via `maxIdx_cuccaro_full`. -/
theorem is_fresh_cuccaro_of_above {dim : Nat} (cq bits q_start : Nat)
    (h : q_start + 2 * bits + 1 ≤ cq) :
    is_fresh cq (Gate.toUCom dim (cuccaro_n_bit_adder_full bits q_start)) :=
  is_fresh_toUCom_of_maxIdx_lt cq (cuccaro_n_bit_adder_full bits q_start)
    (lt_of_le_of_lt (FormalRV.Shor.WindowedWidth.maxIdx_cuccaro_full bits q_start) (by omega))

/-- **The measurement-uncompute IS the re-read embedding, on a loaded superposition.**  Local copy
    of `MeasuredCoherentStep.measWord_eq_embedRead_on_loaded` (which is `private` there): on a
    superposition of loaded states, Gidney's measurement-uncompute channel and the embedded
    reversible re-read have the SAME density action. -/
private theorem measWord_eq_embedRead_on_loaded
    {dim : Nat} {ι : Type*} (w bits : Nat) (pos : Nat → Nat) (T : Nat → Nat)
    (hw : 0 < w) (hdim : 2 * w + 1 ≤ dim)
    (hpos : ∀ j, j < bits → pos j < dim)
    (hpos_high : ∀ j, j < bits → 2 * w < pos j)
    (hinj : ∀ j, j < bits → ∀ k, k < bits → j ≠ k → pos j ≠ pos k)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool) (addr : ι → Nat)
    (hav : ∀ i ∈ s, addr i < 2 ^ w)
    (hgood : ∀ i ∈ s, GoodState w (g i))
    (haddr : ∀ i ∈ s, ∀ k, k < w → g i (ulookup_address_idx k) = (addr i).testBit k)
    (hword : ∀ i ∈ s, ∀ j, j < bits → g i (pos j) = (T (addr i)).testBit j) :
    c_eval (measWordUncompute dim pos (fun j => phaseLookup dim w (fun v => (T v).testBit j)) bits)
        ((∑ i ∈ s, α i • f_to_vec dim (g i)) * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
      = c_eval (Com.embedU (Gate.toUCom dim (lookupReadAt w pos bits T)))
        ((∑ i ∈ s, α i • f_to_vec dim (g i)) * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ) := by
  rw [measUncompute_eq_reread_on_loaded w bits pos T hw hdim hpos hpos_high hinj s α g addr
        hav hgood haddr hword, c_eval_embedU]

/-! ## §2. The controlled physical measured mod-N lookup-add step and its channel transport. -/

/-- **The CONTROLLED physical measured mod-N lookup-add step as a density program.**  Identical to
    `MeasuredCoherentStep.physMeasModNLookupAddStep` EXCEPT the Cuccaro adder block is controlled by
    the fresh qubit `cq`: `Com.embedU (toUCom cuccaro)` becomes
    `Com.embedU (control cq (toUCom cuccaro))`.  The table loads and the two measurement uncomputes
    stay UNCONTROLLED — exactly Gidney's controlled-multiplier construction. -/
def cPhysMeasModNLookupAddStep (cq w bits N : Nat) (T : Nat → Nat)
    (q_start flagPos dim : Nat) : BaseCom dim :=
  Com.useq (Com.embedU (Gate.toUCom dim (lookupReadAt w (addendIdx q_start) bits T)))
    (Com.useq (Com.embedU (FormalRV.Framework.BaseUCom.control cq
          (Gate.toUCom dim (cuccaro_n_bit_adder_full bits q_start))))
      (Com.useq (measWordUncompute dim (addendIdx q_start)
          (fun j => phaseLookup dim w (fun v => (T v).testBit j)) bits)
        (Com.useq (Com.embedU (Gate.toUCom dim (modNReduceFlag bits q_start N flagPos)))
          (Com.useq (Com.embedU (Gate.toUCom dim (lookupReadAt w (addendIdx q_start) bits T)))
            (Com.useq (Com.embedU (Gate.toUCom dim (regCompareXor bits q_start flagPos)))
              (measWordUncompute dim (addendIdx q_start)
                (fun j => phaseLookup dim w (fun v => (T v).testBit j)) bits))))))

/-- **The CONTROLLED reversible mod-N lookup-add step** — the same 7-block reversible
    `WindowedCircuit.modNLookupAddStep` with its Cuccaro adder block replaced by
    `control cq (toUCom cuccaro)`, written as the corresponding `BaseUCom` sequence (the other six
    blocks remain `toUCom`'d `Gate`s; only the adder picks up the control). -/
def cModNLookupAddStepUCom (cq w bits N : Nat) (T : Nat → Nat)
    (q_start flagPos dim : Nat) : BaseUCom dim :=
  UCom.seq (Gate.toUCom dim (lookupReadAt w (addendIdx q_start) bits T))
    (UCom.seq (FormalRV.Framework.BaseUCom.control cq
        (Gate.toUCom dim (cuccaro_n_bit_adder_full bits q_start)))
      (UCom.seq (Gate.toUCom dim (lookupReadAt w (addendIdx q_start) bits T))
        (UCom.seq (Gate.toUCom dim (modNReduceFlag bits q_start N flagPos))
          (UCom.seq (Gate.toUCom dim (lookupReadAt w (addendIdx q_start) bits T))
            (UCom.seq (Gate.toUCom dim (regCompareXor bits q_start flagPos))
              (Gate.toUCom dim (lookupReadAt w (addendIdx q_start) bits T)))))))

/-- **★ CONTROLLED COHERENCE-LEVEL STEP TRANSPORT ★** — the controlled physical measured mod-N
    lookup-add step, as a density channel on an encoded superposition `∑ᵢ αᵢ|eᵢ⟩` of clean inputs,
    equals the CONTROLLED reversible step's unitary conjugation, coefficients and ALL coherences
    intact.  Same hypotheses as `physMeasStep_channel` PLUS the control qubit `cq` placed above the
    arithmetic register (`q_start + 2*bits + 1 ≤ cq`), which makes `cq` fresh in / preserved by the
    Cuccaro adder, so the brick-1 re-read bridge fires UNIFORMLY on both control branches. -/
theorem cPhysMeasStep_channel
    {dim : Nat} {ι : Type*} (cq w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat)
    (s : Finset ι) (α : ι → ℂ) (e : ι → Nat → Bool) (v : ι → Nat) (sacc : ι → Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hq : 2 * w < q_start)
    (hflag_hi : q_start + 2 * bits + 1 ≤ flagPos)
    (hdim : q_start + 2 * bits + 1 ≤ dim) (hflag_lt : flagPos < dim)
    (hcq_lt : cq < dim) (hcq_above : q_start + 2 * bits + 1 ≤ cq)
    (hv : ∀ i ∈ s, v i < 2 ^ w) (hs : ∀ i ∈ s, sacc i < N) (hTv : ∀ i ∈ s, T (v i) < N)
    (hctrl : ∀ i ∈ s, e i ulookup_ctrl_idx = true)
    (haddr : ∀ i ∈ s, ∀ k, k < w → e i (ulookup_address_idx k) = (v i).testBit k)
    (hand : ∀ i ∈ s, ∀ k, k < w → e i (ulookup_and_idx k) = false)
    (h_clean : ∀ i ∈ s, ∀ j, j < bits → e i (addendIdx q_start j) = false)
    (h_acc : ∀ i ∈ s, ∀ k, k < bits → e i (q_start + 2 * k + 1) = (sacc i).testBit k)
    (h_cin : ∀ i ∈ s, e i q_start = false)
    (h_flag : ∀ i ∈ s, e i flagPos = false) :
    c_eval (cPhysMeasModNLookupAddStep cq w bits N T q_start flagPos dim)
        ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
      = uc_eval (cModNLookupAddStepUCom cq w bits N T q_start flagPos dim)
          * ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
          * (uc_eval (cModNLookupAddStepUCom cq w bits N T q_start flagPos dim))ᴴ := by
  -- ════ position / injectivity facts (shared with the value template) ════
  have hread_pos : ∀ j, j < bits → addendIdx q_start j < dim := fun j hj => by
    unfold addendIdx; omega
  have hread_high : ∀ j, j < bits → 2 * w < addendIdx q_start j := fun j _ => by
    unfold addendIdx; omega
  have hread_inj : ∀ j, j < bits → ∀ k, k < bits → j ≠ k →
      addendIdx q_start j ≠ addendIdx q_start k := fun j _ k _ hjk h => by
    unfold addendIdx at h; omega
  have hph : ∀ k, k < bits → 2 * w < addendIdx q_start k := fun k _ => by unfold addendIdx; omega
  have hpi : ∀ k l, k < bits → l < bits → addendIdx q_start k = addendIdx q_start l → k = l :=
    fun k l _ _ h => by unfold addendIdx at h; omega
  have hctrl_ne : ∀ k, k < bits → ulookup_ctrl_idx ≠ addendIdx q_start k :=
    fun k _ => by unfold ulookup_ctrl_idx addendIdx; omega
  have haddr_ne : ∀ i, i < w → ∀ k, k < bits → ulookup_address_idx i ≠ addendIdx q_start k :=
    fun i hi k _ => by unfold ulookup_address_idx addendIdx; omega
  have hand_ne : ∀ i, i < w → ∀ k, k < bits → ulookup_and_idx i ≠ addendIdx q_start k :=
    fun i hi k _ => by unfold ulookup_and_idx addendIdx; omega
  have hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos := Or.inr hflag_hi
  -- ════ well-typedness of the component gates ════
  have hwt_read : Gate.WellTyped dim (lookupReadAt w (addendIdx q_start) bits T) := by
    apply lookupReadAt_wellTyped w bits (addendIdx q_start) T dim hw (by omega)
    intro j hj; refine ⟨hread_pos j hj, ?_⟩
    unfold ulookup_and_idx addendIdx; omega
  have hwt_add : Gate.WellTyped dim (cuccaro_n_bit_adder_full bits q_start) :=
    cuccaro_n_bit_adder_full_wellTyped bits q_start dim (by omega)
  have hwt_reduce : Gate.WellTyped dim (modNReduceFlag bits q_start N flagPos) := by
    apply modNReduceFlag_wellTyped bits q_start N flagPos dim (by omega) hflag_lt
    · omega
    · intro i hi; omega
  have hwt_reg : Gate.WellTyped dim (regCompareXor bits q_start flagPos) :=
    regCompareXor_wellTyped bits q_start flagPos dim (by omega) hflag_lt (by omega)
  -- ════ control-qubit freshness / preservation w.r.t. the Cuccaro adder ════
  have hcq_fresh : is_fresh cq (Gate.toUCom dim (cuccaro_n_bit_adder_full bits q_start)) :=
    is_fresh_cuccaro_of_above cq bits q_start hcq_above
  have hcq_pres : ∀ f, Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) f cq = f cq :=
    fun f => cuccaro_n_bit_adder_full_frame_above bits q_start f cq (by omega)
  -- ════ per-component intermediate states (mirroring the value template) ════
  set g1 : ι → Nat → Bool := fun i =>
    Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (e i) with hg1
  -- the CONTROLLED cuccaro stage: bifurcates on the control bit at `cq`
  set g2 : ι → Nat → Bool := fun i =>
    if (g1 i) cq then Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) (g1 i) else g1 i
    with hg2
  set g3 : ι → Nat → Bool := fun i =>
    Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (g2 i) with hg3
  set g4 : ι → Nat → Bool := fun i =>
    Gate.applyNat (modNReduceFlag bits q_start N flagPos) (g3 i) with hg4
  set g5 : ι → Nat → Bool := fun i =>
    Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (g4 i) with hg5
  set g6 : ι → Nat → Bool := fun i =>
    Gate.applyNat (regCompareXor bits q_start flagPos) (g5 i) with hg6
  set g7 : ι → Nat → Bool := fun i =>
    Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (g6 i) with hg7
  -- ── g1 register facts ──
  have hsel1 : ∀ i ∈ s,
      (∀ j, j < bits → g1 i (addendIdx q_start j)
        = xor (e i (addendIdx q_start j)) ((T (v i)).testBit j))
      ∧ (∀ p, (∀ j, j < bits → p ≠ addendIdx q_start j) → g1 i p = e i p) := fun i hi =>
    lookupReadAt_selects w bits T (addendIdx q_start) (e i) (v i) hw (hv i hi)
      (hctrl i hi) (haddr i hi) (hand i hi) hph hpi
  have hg1_ctrl : ∀ i ∈ s, g1 i ulookup_ctrl_idx = true := fun i hi => by
    rw [(hsel1 i hi).2 _ (fun k hk => hctrl_ne k hk)]; exact hctrl i hi
  have hg1_addr : ∀ i ∈ s, ∀ k, k < w → g1 i (ulookup_address_idx k) = (v i).testBit k :=
    fun i hi k hk => by
      rw [(hsel1 i hi).2 _ (fun l hl => haddr_ne k hk l hl)]; exact haddr i hi k hk
  have hg1_and : ∀ i ∈ s, ∀ k, k < w → g1 i (ulookup_and_idx k) = false := fun i hi k hk => by
    rw [(hsel1 i hi).2 _ (fun l hl => hand_ne k hk l hl)]; exact hand i hi k hk
  have hg1_addend : ∀ i ∈ s, ∀ j, j < bits → g1 i (addendIdx q_start j) = (T (v i)).testBit j :=
    fun i hi j hj => by rw [(hsel1 i hi).1 j hj, h_clean i hi j hj, Bool.false_xor]
  have hg1_acc : ∀ i ∈ s, ∀ k, k < bits → g1 i (q_start + 2 * k + 1) = (sacc i).testBit k :=
    fun i hi k hk => by
      rw [(hsel1 i hi).2 _ (fun l hl => by unfold addendIdx; omega)]; exact h_acc i hi k hk
  have hg1_cin : ∀ i ∈ s, g1 i q_start = false := fun i hi => by
    rw [(hsel1 i hi).2 _ (fun l hl => by unfold addendIdx; omega)]; exact h_cin i hi
  have hg1_flag : ∀ i ∈ s, g1 i flagPos = false := fun i hi => by
    rw [(hsel1 i hi).2 _ (fun l hl => by unfold addendIdx; omega)]; exact h_flag i hi
  -- ── g2 register facts: discharge BOTH control branches.  TRUE branch = template cuccaro facts;
  --    FALSE branch = the g1 facts directly (the load already framed the lookup regs / addend). ──
  have hg2_ctrl : ∀ i ∈ s, g2 i ulookup_ctrl_idx = true := fun i hi => by
    simp only [hg2]; split
    · rw [cuccaro_n_bit_adder_full_frame_below bits q_start (g1 i) _
        (by unfold ulookup_ctrl_idx; omega)]
      exact hg1_ctrl i hi
    · exact hg1_ctrl i hi
  have hg2_addr : ∀ i ∈ s, ∀ k, k < w → g2 i (ulookup_address_idx k) = (v i).testBit k :=
    fun i hi k hk => by
      simp only [hg2]; split
      · rw [cuccaro_n_bit_adder_full_frame_below bits q_start (g1 i) _
          (by unfold ulookup_address_idx; omega)]
        exact hg1_addr i hi k hk
      · exact hg1_addr i hi k hk
  have hg2_and : ∀ i ∈ s, ∀ k, k < w → g2 i (ulookup_and_idx k) = false := fun i hi k hk => by
    simp only [hg2]; split
    · rw [cuccaro_n_bit_adder_full_frame_below bits q_start (g1 i) _
        (by unfold ulookup_and_idx; omega)]
      exact hg1_and i hi k hk
    · exact hg1_and i hi k hk
  have hg2_addend : ∀ i ∈ s, ∀ j, j < bits → g2 i (addendIdx q_start j) = (T (v i)).testBit j :=
    fun i hi j hj => by
      simp only [hg2]; split
      · show Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) (g1 i) (q_start + 2 * j + 2) = _
        rw [(cuccaro_n_bit_adder_full_correct bits q_start (g1 i)).2.2 j hj]
        exact hg1_addend i hi j hj
      · exact hg1_addend i hi j hj
  have hgood2 : ∀ i ∈ s, GoodState w (g2 i) := fun i hi => ⟨hg2_ctrl i hi, hg2_and i hi⟩
  -- the control bit at `cq` is unchanged by the (controlled) cuccaro stage, so we may always read
  -- the branch condition off `g1` (cuccaro preserves `cq` since `cq` is above its register).
  have hg2_cq : ∀ i, (g2 i) cq = (g1 i) cq := fun i => by
    simp only [hg2]; split
    · exact hcq_pres (g1 i)
    · rfl
  -- g2 in the TRUE branch is the bare cuccaro; in the FALSE branch it is g1.
  have hg2_set : ∀ i, (g1 i) cq = true →
      g2 i = Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) (g1 i) := fun i hb => by
    show (if (g1 i) cq = true then Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) (g1 i)
      else g1 i) = _
    rw [if_pos (by rw [hb])]
  have hg2_clear : ∀ i, (g1 i) cq = false → g2 i = g1 i := fun i hb => by
    show (if (g1 i) cq = true then Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) (g1 i)
      else g1 i) = _
    rw [if_neg (by rw [hb]; simp)]
  -- ── g3 register facts (re-read clears addend, frames lookup regs / acc / carry / flag) ──
  have hsel2 : ∀ i ∈ s,
      (∀ j, j < bits → g3 i (addendIdx q_start j)
        = xor (g2 i (addendIdx q_start j)) ((T (v i)).testBit j))
      ∧ (∀ p, (∀ j, j < bits → p ≠ addendIdx q_start j) → g3 i p = g2 i p) := fun i hi =>
    lookupReadAt_selects w bits T (addendIdx q_start) (g2 i) (v i) hw (hv i hi)
      (hg2_ctrl i hi) (hg2_addr i hi) (hg2_and i hi) hph hpi
  have hg3_ctrl : ∀ i ∈ s, g3 i ulookup_ctrl_idx = true := fun i hi => by
    rw [(hsel2 i hi).2 _ (fun k hk => hctrl_ne k hk)]; exact hg2_ctrl i hi
  have hg3_addr : ∀ i ∈ s, ∀ k, k < w → g3 i (ulookup_address_idx k) = (v i).testBit k :=
    fun i hi k hk => by
      rw [(hsel2 i hi).2 _ (fun l hl => haddr_ne k hk l hl)]; exact hg2_addr i hi k hk
  have hg3_and : ∀ i ∈ s, ∀ k, k < w → g3 i (ulookup_and_idx k) = false := fun i hi k hk => by
    rw [(hsel2 i hi).2 _ (fun l hl => hand_ne k hk l hl)]; exact hg2_and i hi k hk
  have hg3_addend : ∀ i ∈ s, ∀ j, j < bits → g3 i (addendIdx q_start j) = false :=
    fun i hi j hj => by rw [(hsel2 i hi).1 j hj, hg2_addend i hi j hj, Bool.xor_self]
  -- the acc / carry / flag facts for g3 are NOT needed by the measured-uncompute bridge (brick 1
  -- only uses the lookup-register frame + the addend = T v), and the controlled cuccaro changes the
  -- accumulator VALUE between branches, so we do not assert a single accumulator value for g3.
  have hg3_cin : ∀ i ∈ s, g3 i q_start = false := fun i hi => by
    rw [(hsel2 i hi).2 _ (fun l hl => by unfold addendIdx; omega)]
    -- g2 carry: both branches clear (cuccaro restores carry-in to its input; input was clear)
    simp only [hg2]; split
    · rw [(cuccaro_n_bit_adder_full_correct bits q_start (g1 i)).1]; exact hg1_cin i hi
    · exact hg1_cin i hi
  have hg3_flag : ∀ i ∈ s, g3 i flagPos = false := fun i hi => by
    rw [(hsel2 i hi).2 _ (fun l hl => by unfold addendIdx; omega)]
    simp only [hg2]; split
    · rw [cuccaro_n_bit_adder_full_frame_above bits q_start (g1 i) _ hflag_hi]
      exact hg1_flag i hi
    · exact hg1_flag i hi
  -- ── g4 register facts (mod-N reduce: addend stays clean, lookup regs framed below q_start) ──
  -- the reduce gate needs the accumulator value to be `< 2*N`; with the controlled cuccaro it is
  -- either `sacc + T v` (control set, `< 2N` by hs/hTv) or `sacc` (control clear, `< N < 2N`).
  -- We only need that the reduce frames the lookup regs and keeps the addend clean — both
  -- hold for ANY accumulator value, via `modNReduceFlag_frame_outside` style facts derived per
  -- branch.  Establish the acc value per branch first.
  have hg3_acc_set : ∀ i ∈ s, (g1 i) cq = true →
      ∀ k, k < bits → g3 i (q_start + 2 * k + 1) = ((sacc i) + T (v i)).testBit k :=
    fun i hi hbit k hk => by
      rw [(hsel2 i hi).2 _ (fun l hl => by unfold addendIdx; omega), hg2_set i hbit]
      exact cuccaro_adder_sum_bits_general bits q_start (sacc i) (T (v i)) (g1 i)
        (hg1_cin i hi) (hg1_acc i hi) (hg1_addend i hi) k hk
  have hg3_acc_clear : ∀ i ∈ s, (g1 i) cq = false →
      ∀ k, k < bits → g3 i (q_start + 2 * k + 1) = (sacc i).testBit k :=
    fun i hi hbit k hk => by
      rw [(hsel2 i hi).2 _ (fun l hl => by unfold addendIdx; omega), hg2_clear i hbit]
      exact hg1_acc i hi k hk
  -- reduce frames + addend-clean, established per accumulator-value branch
  have hred_read : ∀ i ∈ s, ∀ j, j < bits → g4 i (addendIdx q_start j) = false := fun i hi j hj => by
    simp only [hg4]
    show Gate.applyNat (modNReduceFlag bits q_start N flagPos) (g3 i) (q_start + 2 * j + 2) = _
    by_cases hcset : (g1 i) cq
    · exact (modNReduceFlag_state_general bits q_start N flagPos ((sacc i) + T (v i)) (g3 i)
        hN_pos hN2 (by have := hs i hi; have := hTv i hi; omega) hflag_out (hg3_cin i hi)
        (hg3_flag i hi) (hg3_acc_set i hi hcset) (hg3_addend i hi)).2.1 j hj
    · exact (modNReduceFlag_state_general bits q_start N flagPos (sacc i) (g3 i)
        hN_pos hN2 (by have := hs i hi; omega) hflag_out (hg3_cin i hi)
        (hg3_flag i hi) (hg3_acc_clear i hi (by simpa using hcset)) (hg3_addend i hi)).2.1 j hj
  have hred_frame : ∀ i ∈ s, ∀ p, p ≠ flagPos → (p < q_start ∨ q_start + 2 * bits + 1 ≤ p) →
      g4 i p = g3 i p := fun i hi p hpf hpo => by
    simp only [hg4]
    by_cases hcset : (g1 i) cq
    · exact (modNReduceFlag_state_general bits q_start N flagPos ((sacc i) + T (v i)) (g3 i)
        hN_pos hN2 (by have := hs i hi; have := hTv i hi; omega) hflag_out (hg3_cin i hi)
        (hg3_flag i hi) (hg3_acc_set i hi hcset) (hg3_addend i hi)).2.2.2.2 p hpf hpo
    · exact (modNReduceFlag_state_general bits q_start N flagPos (sacc i) (g3 i)
        hN_pos hN2 (by have := hs i hi; omega) hflag_out (hg3_cin i hi)
        (hg3_flag i hi) (hg3_acc_clear i hi (by simpa using hcset)) (hg3_addend i hi)).2.2.2.2 p hpf hpo
  have hg4_ctrl : ∀ i ∈ s, g4 i ulookup_ctrl_idx = true := fun i hi => by
    rw [hred_frame i hi ulookup_ctrl_idx (by unfold ulookup_ctrl_idx; omega)
      (Or.inl (by unfold ulookup_ctrl_idx; omega))]
    exact hg3_ctrl i hi
  have hg4_addr : ∀ i ∈ s, ∀ k, k < w → g4 i (ulookup_address_idx k) = (v i).testBit k :=
    fun i hi k hk => by
      rw [hred_frame i hi (ulookup_address_idx k) (by unfold ulookup_address_idx; omega)
        (Or.inl (by unfold ulookup_address_idx; omega))]
      exact hg3_addr i hi k hk
  have hg4_and : ∀ i ∈ s, ∀ k, k < w → g4 i (ulookup_and_idx k) = false := fun i hi k hk => by
    rw [hred_frame i hi (ulookup_and_idx k) (by unfold ulookup_and_idx; omega)
      (Or.inl (by unfold ulookup_and_idx; omega))]
    exact hg3_and i hi k hk
  have hg4_addend : ∀ i ∈ s, ∀ j, j < bits → g4 i (addendIdx q_start j) = false := hred_read
  -- ── g5 register facts (re-read reloads addend to T v, frames lookup regs) ──
  have hsel3 : ∀ i ∈ s,
      (∀ j, j < bits → g5 i (addendIdx q_start j)
        = xor (g4 i (addendIdx q_start j)) ((T (v i)).testBit j))
      ∧ (∀ p, (∀ j, j < bits → p ≠ addendIdx q_start j) → g5 i p = g4 i p) := fun i hi =>
    lookupReadAt_selects w bits T (addendIdx q_start) (g4 i) (v i) hw (hv i hi)
      (hg4_ctrl i hi) (hg4_addr i hi) (hg4_and i hi) hph hpi
  have hg5_ctrl : ∀ i ∈ s, g5 i ulookup_ctrl_idx = true := fun i hi => by
    rw [(hsel3 i hi).2 _ (fun k hk => hctrl_ne k hk)]; exact hg4_ctrl i hi
  have hg5_addr : ∀ i ∈ s, ∀ k, k < w → g5 i (ulookup_address_idx k) = (v i).testBit k :=
    fun i hi k hk => by
      rw [(hsel3 i hi).2 _ (fun l hl => haddr_ne k hk l hl)]; exact hg4_addr i hi k hk
  have hg5_and : ∀ i ∈ s, ∀ k, k < w → g5 i (ulookup_and_idx k) = false := fun i hi k hk => by
    rw [(hsel3 i hi).2 _ (fun l hl => hand_ne k hk l hl)]; exact hg4_and i hi k hk
  have hg5_addend : ∀ i ∈ s, ∀ j, j < bits → g5 i (addendIdx q_start j) = (T (v i)).testBit j :=
    fun i hi j hj => by rw [(hsel3 i hi).1 j hj, hg4_addend i hi j hj, Bool.false_xor]
  -- ── g6 register facts (regCompare frames lookup regs, restores addend workspace) ──
  have hg6_ctrl : ∀ i ∈ s, g6 i ulookup_ctrl_idx = true := fun i hi => by
    simp only [hg6]
    rw [regCompareXor_frame_outside bits q_start flagPos (g5 i) ulookup_ctrl_idx
      (by unfold ulookup_ctrl_idx; omega) (Or.inl (by unfold ulookup_ctrl_idx; omega))]
    exact hg5_ctrl i hi
  have hg6_addr : ∀ i ∈ s, ∀ k, k < w → g6 i (ulookup_address_idx k) = (v i).testBit k :=
    fun i hi k hk => by
      simp only [hg6]
      rw [regCompareXor_frame_outside bits q_start flagPos (g5 i) (ulookup_address_idx k)
        (by unfold ulookup_address_idx; omega) (Or.inl (by unfold ulookup_address_idx; omega))]
      exact hg5_addr i hi k hk
  have hg6_and : ∀ i ∈ s, ∀ k, k < w → g6 i (ulookup_and_idx k) = false := fun i hi k hk => by
    simp only [hg6]
    rw [regCompareXor_frame_outside bits q_start flagPos (g5 i) (ulookup_and_idx k)
      (by unfold ulookup_and_idx; omega) (Or.inl (by unfold ulookup_and_idx; omega))]
    exact hg5_and i hi k hk
  have hg6_addend : ∀ i ∈ s, ∀ j, j < bits → g6 i (addendIdx q_start j) = (T (v i)).testBit j :=
    fun i hi j hj => by
      simp only [hg6]
      show Gate.applyNat (regCompareXor bits q_start flagPos) (g5 i) (q_start + 2 * j + 2) = _
      rw [regCompareXor_workspace_restored_at bits q_start flagPos (g5 i) hflag_out
        (q_start + 2 * j + 2) (by omega) (by omega)]
      exact hg5_addend i hi j hj
  have hgood6 : ∀ i ∈ s, GoodState w (g6 i) := fun i hi => ⟨hg6_ctrl i hi, hg6_and i hi⟩
  -- pointwise fold equalities (each is `rfl` by definition of the `set` variables).
  have f1 : ∀ i, Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (e i) = g1 i :=
    fun _ => rfl
  have f2 : ∀ i,
      (if (g1 i) cq then Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) (g1 i) else g1 i)
        = g2 i := fun _ => rfl
  have f3 : ∀ i, Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (g2 i) = g3 i :=
    fun _ => rfl
  have f4 : ∀ i, Gate.applyNat (modNReduceFlag bits q_start N flagPos) (g3 i) = g4 i := fun _ => rfl
  have f5 : ∀ i, Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (g4 i) = g5 i :=
    fun _ => rfl
  have f6 : ∀ i, Gate.applyNat (regCompareXor bits q_start flagPos) (g5 i) = g6 i := fun _ => rfl
  have f7 : ∀ i, Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (g6 i) = g7 i :=
    fun _ => rfl
  -- ════ THE FOLD: push the superposition through the channel, block by block ════
  unfold cPhysMeasModNLookupAddStep
  -- read
  rw [c_eval_useq, embedU_gate_on_superposition (lookupReadAt w (addendIdx q_start) bits T) hwt_read
        s α e]
  simp only [f1]
  -- CONTROLLED add
  rw [c_eval_useq, embedU_control_gate_on_superposition cq
        (cuccaro_n_bit_adder_full bits q_start) (by omega) hcq_fresh hwt_add hcq_pres s α g1]
  simp only [f2]
  -- measWord #1 = re-read (bridge), then the embedded read
  rw [c_eval_useq,
      measWord_eq_embedRead_on_loaded w bits (addendIdx q_start) T hw (by omega)
        hread_pos hread_high hread_inj s α g2 v hv hgood2 hg2_addr hg2_addend,
      embedU_gate_on_superposition (lookupReadAt w (addendIdx q_start) bits T) hwt_read s α g2]
  simp only [f3]
  -- reduce
  rw [c_eval_useq, embedU_gate_on_superposition (modNReduceFlag bits q_start N flagPos) hwt_reduce
        s α g3]
  simp only [f4]
  -- read
  rw [c_eval_useq, embedU_gate_on_superposition (lookupReadAt w (addendIdx q_start) bits T) hwt_read
        s α g4]
  simp only [f5]
  -- regCompare
  rw [c_eval_useq, embedU_gate_on_superposition (regCompareXor bits q_start flagPos) hwt_reg
        s α g5]
  simp only [f6]
  -- measWord #2 = re-read (bridge), then the embedded read
  rw [measWord_eq_embedRead_on_loaded w bits (addendIdx q_start) T hw (by omega)
        hread_pos hread_high hread_inj s α g6 v hv hgood6 hg6_addr hg6_addend,
      embedU_gate_on_superposition (lookupReadAt w (addendIdx q_start) bits T) hwt_read s α g6]
  simp only [f7]
  -- LHS is now `(∑ α • f_to_vec (g7 i)) * (…)ᴴ`.
  -- ════ REPACKAGE: the RHS conjugation by `cModNLookupAddStepUCom` = the SAME final superposition ═
  rw [conj_outer_product (uc_eval (cModNLookupAddStepUCom cq w bits N T q_start flagPos dim))
        (∑ i ∈ s, α i • f_to_vec dim (e i))]
  -- the controlled reversible step sends each basis state `e i` to `g7 i` (single-vector push)
  have hcV_apply : ∀ i,
      uc_eval (cModNLookupAddStepUCom cq w bits N T q_start flagPos dim) * f_to_vec dim (e i)
        = f_to_vec dim (g7 i) := fun i => by
    -- unfold all the staged `set` variables so both sides are bare `applyNat` towers, then push.
    -- `g2` is the controlled `if`; the control-lemma push produces exactly that `if`.
    have hg2def : g2 i = (if (Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (e i)) cq
        then Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
              (Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (e i))
        else Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (e i)) := rfl
    simp only [hg7, hg6, hg5, hg4, hg3, hg2def, cModNLookupAddStepUCom, uc_eval_seq_mul,
      uc_eval_toUCom_acts_on_basis dim _ hwt_read,
      uc_eval_control_toUCom_on_basis cq (cuccaro_n_bit_adder_full bits q_start)
        (by omega) hcq_fresh hwt_add hcq_pres]
    -- both sides now differ only in the `if`; the `f_to_vec` of the controlled image matches.
    split <;> simp only [uc_eval_toUCom_acts_on_basis dim _ hwt_read,
      uc_eval_toUCom_acts_on_basis dim _ hwt_reduce, uc_eval_toUCom_acts_on_basis dim _ hwt_reg]
  have hpush : uc_eval (cModNLookupAddStepUCom cq w bits N T q_start flagPos dim)
        * (∑ i ∈ s, α i • f_to_vec dim (e i))
      = ∑ i ∈ s, α i • f_to_vec dim (g7 i) := by
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_smul, hcV_apply i]
  rw [hpush]

end

end FormalRV.Shor.ControlledMeasuredStep
