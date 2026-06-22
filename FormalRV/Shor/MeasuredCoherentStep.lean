/-
  FormalRV.Shor.MeasuredCoherentStep — GAP ① brick 2: the PHYSICAL measured mod-N
  lookup-add STEP, as a density channel, equals its reversible unitary counterpart's
  conjugation on encoded superpositions.
  ════════════════════════════════════════════════════════════════════════════════════════════

  `MeasuredWindowedModN.measModNLookupAddStep_applyNat_eq` proves the measured mod-N lookup-add
  step equals the reversible `WindowedCircuit.modNLookupAddStep` at the VALUE (single-basis-state)
  level — both clear the addend word at the two uncompute points.  This file lifts that to the
  AMPLITUDE/SUPERPOSITION level: on a superposition `∑ᵢ αᵢ|eᵢ⟩` of clean encoded inputs, the
  PHYSICAL measured step (the two uncompute reads done by Gidney's X-basis measurement +
  CZ-phase-fixup `measWordUncompute`) acts EXACTLY as the reversible step's unitary conjugation —
  coefficients and ALL coherences `|eᵢ⟩⟨eⱼ|` intact.

  This is the density/coherence analog of the value-level transport.  It is built by folding the
  brick-1 keystone `MeasuredCoherentUncompute.measUncompute_eq_reread_on_loaded` (measurement-
  uncompute = re-read, AS CHANNELS, on loaded superpositions) at the two divergence points, and
  pushing the unitary blocks through with `embedU_gate_on_superposition`, reusing the EXACT
  register-fact derivations of the value-level template.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.MeasuredCoherentUncompute
import FormalRV.Shor.MeasuredWindowedModN

namespace FormalRV.Shor.MeasuredCoherentStep

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
open Matrix

noncomputable section

/-- **The PHYSICAL measured mod-N lookup-add step as a density program.**  The reversible
    `WindowedCircuit.modNLookupAddStep` is
    `read · add · read⁻¹ · reduce · read · regCompare · read⁻¹` (the 2nd and 4th reads uncompute);
    here those two uncompute reads become Gidney's measurement-based uncompute `measWordUncompute`
    (the X-basis measure + CZ phase fixup, density-modeled), the other five blocks embedded as
    unitaries.  This is the density-level companion of the `EGate`
    `MeasuredWindowedModN.measModNLookupAddStep`. -/
def physMeasModNLookupAddStep (w bits N : Nat) (T : Nat → Nat)
    (q_start flagPos dim : Nat) : BaseCom dim :=
  Com.useq (Com.embedU (Gate.toUCom dim (lookupReadAt w (addendIdx q_start) bits T)))
    (Com.useq (Com.embedU (Gate.toUCom dim (cuccaro_n_bit_adder_full bits q_start)))
      (Com.useq (measWordUncompute dim (addendIdx q_start)
          (fun j => phaseLookup dim w (fun v => (T v).testBit j)) bits)
        (Com.useq (Com.embedU (Gate.toUCom dim (modNReduceFlag bits q_start N flagPos)))
          (Com.useq (Com.embedU (Gate.toUCom dim (lookupReadAt w (addendIdx q_start) bits T)))
            (Com.useq (Com.embedU (Gate.toUCom dim (regCompareXor bits q_start flagPos)))
              (measWordUncompute dim (addendIdx q_start)
                (fun j => phaseLookup dim w (fun v => (T v).testBit j)) bits))))))

/-- **The measurement-uncompute IS the re-read embedding, on a loaded superposition.**  On a
    superposition of loaded states, Gidney's measurement-uncompute channel `measWordUncompute` and
    the embedded reversible re-read `embedU (toUCom (lookupReadAt …))` have the SAME density action
    (both equal the re-read's conjugation, by brick 1).  This is the per-divergence-point rewrite
    that turns the measured channel into the fully reversible one. -/
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

/-- **★ COHERENCE-LEVEL STEP TRANSPORT ★** — the physical measured mod-N lookup-add step, as a
    density channel on an encoded superposition `∑ᵢ αᵢ|eᵢ⟩` of clean inputs, equals the reversible
    `modNLookupAddStep`'s unitary conjugation, coefficients and ALL coherences intact.  The
    amplitude-level lift of `MeasuredWindowedModN.measModNLookupAddStep_applyNat_eq`. -/
theorem physMeasStep_channel
    {dim : Nat} {ι : Type*} (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat)
    (s : Finset ι) (α : ι → ℂ) (e : ι → Nat → Bool) (v : ι → Nat) (sacc : ι → Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hq : 2 * w < q_start)
    (hflag_hi : q_start + 2 * bits + 1 ≤ flagPos)
    (hdim : q_start + 2 * bits + 1 ≤ dim) (hflag_lt : flagPos < dim)
    (hv : ∀ i ∈ s, v i < 2 ^ w) (hs : ∀ i ∈ s, sacc i < N) (hTv : ∀ i ∈ s, T (v i) < N)
    (hctrl : ∀ i ∈ s, e i ulookup_ctrl_idx = true)
    (haddr : ∀ i ∈ s, ∀ k, k < w → e i (ulookup_address_idx k) = (v i).testBit k)
    (hand : ∀ i ∈ s, ∀ k, k < w → e i (ulookup_and_idx k) = false)
    (h_clean : ∀ i ∈ s, ∀ j, j < bits → e i (addendIdx q_start j) = false)
    (h_acc : ∀ i ∈ s, ∀ k, k < bits → e i (q_start + 2 * k + 1) = (sacc i).testBit k)
    (h_cin : ∀ i ∈ s, e i q_start = false)
    (h_flag : ∀ i ∈ s, e i flagPos = false) :
    c_eval (physMeasModNLookupAddStep w bits N T q_start flagPos dim)
        ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
      = uc_eval (Gate.toUCom dim (modNLookupAddStep w bits N T q_start flagPos))
          * ((∑ i ∈ s, α i • f_to_vec dim (e i)) * (∑ i ∈ s, α i • f_to_vec dim (e i))ᴴ)
          * (uc_eval (Gate.toUCom dim (modNLookupAddStep w bits N T q_start flagPos)))ᴴ := by
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
  -- well-typedness of the whole reversible step (its 7-fold seq)
  have hwt_step : Gate.WellTyped dim (modNLookupAddStep w bits N T q_start flagPos) :=
    ⟨hwt_read, hwt_add, hwt_read, hwt_reduce, hwt_read, hwt_reg, hwt_read⟩
  -- ════ per-component intermediate states (mirroring the value template) ════
  set g1 : ι → Nat → Bool := fun i =>
    Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (e i) with hg1
  set g2 : ι → Nat → Bool := fun i =>
    Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) (g1 i) with hg2
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
  -- ── g2 register facts (cuccaro frames lookup regs, preserves addend, sums accumulator) ──
  have hg2_ctrl : ∀ i ∈ s, g2 i ulookup_ctrl_idx = true := fun i hi => by
    simp only [hg2]
    rw [cuccaro_n_bit_adder_full_frame_below bits q_start (g1 i) _
      (by unfold ulookup_ctrl_idx; omega)]
    exact hg1_ctrl i hi
  have hg2_addr : ∀ i ∈ s, ∀ k, k < w → g2 i (ulookup_address_idx k) = (v i).testBit k :=
    fun i hi k hk => by
      simp only [hg2]
      rw [cuccaro_n_bit_adder_full_frame_below bits q_start (g1 i) _
        (by unfold ulookup_address_idx; omega)]
      exact hg1_addr i hi k hk
  have hg2_and : ∀ i ∈ s, ∀ k, k < w → g2 i (ulookup_and_idx k) = false := fun i hi k hk => by
    simp only [hg2]
    rw [cuccaro_n_bit_adder_full_frame_below bits q_start (g1 i) _
      (by unfold ulookup_and_idx; omega)]
    exact hg1_and i hi k hk
  have hg2_addend : ∀ i ∈ s, ∀ j, j < bits → g2 i (addendIdx q_start j) = (T (v i)).testBit j :=
    fun i hi j hj => by
      simp only [hg2]
      show Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) (g1 i) (q_start + 2 * j + 2) = _
      rw [(cuccaro_n_bit_adder_full_correct bits q_start (g1 i)).2.2 j hj]
      exact hg1_addend i hi j hj
  have hg2_acc : ∀ i ∈ s, ∀ k, k < bits → g2 i (q_start + 2 * k + 1) = ((sacc i) + T (v i)).testBit k :=
    fun i hi k hk => by
      simp only [hg2]
      exact cuccaro_adder_sum_bits_general bits q_start (sacc i) (T (v i)) (g1 i)
        (hg1_cin i hi) (hg1_acc i hi) (hg1_addend i hi) k hk
  have hg2_cin : ∀ i ∈ s, g2 i q_start = false := fun i hi => by
    simp only [hg2]
    rw [(cuccaro_n_bit_adder_full_correct bits q_start (g1 i)).1]; exact hg1_cin i hi
  have hg2_flag : ∀ i ∈ s, g2 i flagPos = false := fun i hi => by
    simp only [hg2]
    rw [cuccaro_n_bit_adder_full_frame_above bits q_start (g1 i) _ hflag_hi]
    exact hg1_flag i hi
  have hgood2 : ∀ i ∈ s, GoodState w (g2 i) := fun i hi => ⟨hg2_ctrl i hi, hg2_and i hi⟩
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
  -- (g2 addend = T v ; xor (T v) (T v) = false)
  have hg3_acc : ∀ i ∈ s, ∀ k, k < bits → g3 i (q_start + 2 * k + 1) = ((sacc i) + T (v i)).testBit k :=
    fun i hi k hk => by
      rw [(hsel2 i hi).2 _ (fun l hl => by unfold addendIdx; omega)]; exact hg2_acc i hi k hk
  have hg3_cin : ∀ i ∈ s, g3 i q_start = false := fun i hi => by
    rw [(hsel2 i hi).2 _ (fun l hl => by unfold addendIdx; omega)]; exact hg2_cin i hi
  have hg3_flag : ∀ i ∈ s, g3 i flagPos = false := fun i hi => by
    rw [(hsel2 i hi).2 _ (fun l hl => by unfold addendIdx; omega)]; exact hg2_flag i hi
  -- ── g4 register facts (mod-N reduce: addend stays clean, lookup regs framed below q_start) ──
  have hred_read : ∀ i ∈ s, ∀ j, j < bits → g4 i (addendIdx q_start j) = false := fun i hi j hj => by
    simp only [hg4]
    show Gate.applyNat (modNReduceFlag bits q_start N flagPos) (g3 i) (q_start + 2 * j + 2) = _
    exact (modNReduceFlag_state_general bits q_start N flagPos ((sacc i) + T (v i)) (g3 i)
      hN_pos hN2 (by have := hs i hi; have := hTv i hi; omega) hflag_out (hg3_cin i hi)
      (hg3_flag i hi) (hg3_acc i hi) (hg3_addend i hi)).2.1 j hj
  have hred_frame : ∀ i ∈ s, ∀ p, p ≠ flagPos → (p < q_start ∨ q_start + 2 * bits + 1 ≤ p) →
      g4 i p = g3 i p := fun i hi p hpf hpo => by
    simp only [hg4]
    exact (modNReduceFlag_state_general bits q_start N flagPos ((sacc i) + T (v i)) (g3 i)
      hN_pos hN2 (by have := hs i hi; have := hTv i hi; omega) hflag_out (hg3_cin i hi)
      (hg3_flag i hi) (hg3_acc i hi) (hg3_addend i hi)).2.2.2.2 p hpf hpo
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
  -- pointwise fold equalities (each is `rfl` by definition of the `set` variables); used to keep
  -- each stage's superposition in `gₖ i` form so the next brick/embed rewrite fires syntactically.
  have f1 : ∀ i, Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (e i) = g1 i :=
    fun _ => rfl
  have f2 : ∀ i, Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) (g1 i) = g2 i := fun _ => rfl
  have f3 : ∀ i, Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (g2 i) = g3 i :=
    fun _ => rfl
  have f4 : ∀ i, Gate.applyNat (modNReduceFlag bits q_start N flagPos) (g3 i) = g4 i := fun _ => rfl
  have f5 : ∀ i, Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (g4 i) = g5 i :=
    fun _ => rfl
  have f6 : ∀ i, Gate.applyNat (regCompareXor bits q_start flagPos) (g5 i) = g6 i := fun _ => rfl
  have f7 : ∀ i, Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) (g6 i) = g7 i :=
    fun _ => rfl
  -- ════ THE FOLD: push the superposition through the channel, block by block ════
  unfold physMeasModNLookupAddStep
  -- read
  rw [c_eval_useq, embedU_gate_on_superposition (lookupReadAt w (addendIdx q_start) bits T) hwt_read
        s α e]
  simp only [f1]
  -- add
  rw [c_eval_useq, embedU_gate_on_superposition (cuccaro_n_bit_adder_full bits q_start) hwt_add
        s α g1]
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
  -- LHS is now `(∑ α • f_to_vec (g7 i)) * (…)ᴴ` with g7 i = applyNat (read) (g6 i).
  -- ════ REPACKAGE: the RHS conjugation = the SAME final superposition ════
  -- the whole reversible step sends each `e i` to `g7 i`
  have hstep_apply : ∀ i ∈ s,
      Gate.applyNat (modNLookupAddStep w bits N T q_start flagPos) (e i) = g7 i := fun i hi => by
    simp only [modNLookupAddStep, Gate.applyNat_seq]
    rfl
  rw [conj_outer_product (uc_eval (Gate.toUCom dim (modNLookupAddStep w bits N T q_start flagPos)))
        (∑ i ∈ s, α i • f_to_vec dim (e i))]
  have hpush : uc_eval (Gate.toUCom dim (modNLookupAddStep w bits N T q_start flagPos))
        * (∑ i ∈ s, α i • f_to_vec dim (e i))
      = ∑ i ∈ s, α i • f_to_vec dim (g7 i) := by
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Matrix.mul_smul, uc_eval_toUCom_acts_on_basis dim _ hwt_step (e i), hstep_apply i hi]
  rw [hpush]

end

end FormalRV.Shor.MeasuredCoherentStep
