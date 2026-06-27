/- WindowedModN — §8-9 window-step invariant + preservation proof.
   Part of `WindowedModN` (the `WindowedModN.lean` shim re-exports all parts). -/
import FormalRV.Arithmetic.Windowed.WindowedModN.Step

namespace FormalRV.Shor.WindowedCircuit
open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §8. The mod-N window-step invariant. -/

/-- **The mod-N window-step invariant.**  After some window-steps starting
    from `mulInputOf cuccaroAdder w bits numWin y`, the state `g` satisfies:
    (F) frame off the Cuccaro block and the flag;
    (D) the addend register is clean;
    (C) the carry-in is clean;
    (G) the flag is clean;
    (V) the accumulator holds the bits of the running mod-N sum `s`. -/
def ModNStepInv (w bits numWin y s : Nat) (g : Nat → Bool) : Prop :=
  (∀ p, ¬ inBlock (1 + 2 * w) (2 * bits + 1) p →
      p ≠ 1 + 2 * w + (2 * bits + 1) + numWin * w →
      g p = mulInputOf cuccaroAdder w bits numWin y p)
  ∧ (∀ i, i < bits → g (1 + 2 * w + 2 * i + 2) = false)
  ∧ g (1 + 2 * w) = false
  ∧ g (1 + 2 * w + (2 * bits + 1) + numWin * w) = false
  ∧ (∀ i, i < bits → g (1 + 2 * w + 2 * i + 1) = s.testBit i)

/-- Invariant initialization: the clean input satisfies the invariant at `0`. -/
theorem modNStepInv_init (w bits numWin y : Nat) :
    ModNStepInv w bits numWin y 0 (mulInputOf cuccaroAdder w bits numWin y) := by
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  refine ⟨fun p _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega) (by rw [hspan]; omega)
  · exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega) (by rw [hspan]; omega)
  · show mulInputOf cuccaroAdder w bits numWin y
        (1 + 2 * w + (2 * bits + 1) + numWin * w) = false
    unfold mulInputOf encodeReg
    rw [if_neg (by unfold ulookup_ctrl_idx; omega), if_neg (by rw [hspan]; omega)]
  · intro i hi
    rw [Nat.zero_testBit]
    exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega) (by rw [hspan]; omega)

/-! ## §9. The mod-N window step preserves the invariant. -/

theorem modNStepInv_step (w bits a N numWin y : Nat) (hw : 0 < w)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (j : Nat) (hj : j < numWin) (s : Nat) (hs : s < N) (g : Nat → Bool)
    (hg : ModNStepInv w bits numWin y s g) :
    ModNStepInv w bits numWin y
      ((s + WindowedArith.tableValue a N w j (WindowedArith.window w y j)) % N)
      (Gate.applyNat
        (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) j) g) := by
  obtain ⟨hF, hD, hC, hG, hV⟩ := hg
  -- ── Values ─────────────────────────────────────────────────────────────
  have hv : WindowedArith.window w y j < 2 ^ w := WindowedArith.window_lt w y j
  have ht_lt : WindowedArith.tableValue a N w j (WindowedArith.window w y j) < N := by
    unfold WindowedArith.tableValue
    exact Nat.mod_lt _ hN_pos
  -- ── Standing position facts ────────────────────────────────────────────
  have hjw_le : j * w + w ≤ numWin * w := by
    have h1 : (j + 1) * w ≤ numWin * w := Nat.mul_le_mul_right w (by omega)
    have h2 : (j + 1) * w = j * w + w := by ring
    omega
  have hctrl_addr : ∀ i k, i < w → k < w →
      (1 + 2 * w + (2 * bits + 1)) + j * w + i ≠ ulookup_address_idx k :=
    ctrl_ne_addr_of_le_yBase w (1 + 2 * w + (2 * bits + 1)) j (by omega)
  have hpos_high : ∀ k, k < bits → 2 * w < addendIdx (1 + 2 * w) k := by
    intro k hk
    unfold addendIdx
    omega
  have hpos_inj : ∀ k l, k < bits → l < bits →
      addendIdx (1 + 2 * w) k = addendIdx (1 + 2 * w) l → k = l := by
    intro k l _ _ h
    unfold addendIdx at h
    omega
  have hflag_out : 1 + 2 * w + (2 * bits + 1) + numWin * w < 1 + 2 * w ∨
      1 + 2 * w + 2 * bits + 1 ≤ 1 + 2 * w + (2 * bits + 1) + numWin * w := by
    right
    omega
  -- ── Pre-step register values, from the invariant ───────────────────────
  have hg_ctrl : g ulookup_ctrl_idx = true := by
    rw [hF ulookup_ctrl_idx (by unfold inBlock ulookup_ctrl_idx; omega)
          (by unfold ulookup_ctrl_idx; omega)]
    exact mulInputOf_ctrl cuccaroAdder w bits numWin y
  have hg_addr : ∀ i, i < w → g (ulookup_address_idx i) = false := by
    intro i hi
    rw [hF _ (by unfold inBlock ulookup_address_idx; omega)
          (by unfold ulookup_address_idx; omega)]
    exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx ulookup_address_idx; omega)
      (by unfold ulookup_address_idx; omega)
  have hg_and : ∀ i, i < w → g (ulookup_and_idx i) = false := by
    intro i hi
    rw [hF _ (by unfold inBlock ulookup_and_idx; omega)
          (by unfold ulookup_and_idx; omega)]
    exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx ulookup_and_idx; omega)
      (by unfold ulookup_and_idx; omega)
  have hg_y : ∀ i, i < w →
      g ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hF _ (by unfold inBlock; omega) (by omega)]
    exact mulInputOf_eq_encodeReg cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega)
  -- ── Expose the nine-fold composition ───────────────────────────────────
  simp only [windowedModNStep, modNLookupAddStep, Gate.applyNat_seq]
  set g1 : Nat → Bool :=
    Gate.applyNat (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) g with hg1def
  set g2 : Nat → Bool :=
    Gate.applyNat (lookupReadAt w (addendIdx (1 + 2 * w)) bits
      (WindowedArith.tableValue a N w j)) g1 with hg2def
  set g3 : Nat → Bool :=
    Gate.applyNat (cuccaro_n_bit_adder_full bits (1 + 2 * w)) g2 with hg3def
  set g4 : Nat → Bool :=
    Gate.applyNat (lookupReadAt w (addendIdx (1 + 2 * w)) bits
      (WindowedArith.tableValue a N w j)) g3 with hg4def
  set g5 : Nat → Bool :=
    Gate.applyNat (modNReduceFlag bits (1 + 2 * w) N
      (1 + 2 * w + (2 * bits + 1) + numWin * w)) g4 with hg5def
  set g6 : Nat → Bool :=
    Gate.applyNat (lookupReadAt w (addendIdx (1 + 2 * w)) bits
      (WindowedArith.tableValue a N w j)) g5 with hg6def
  set g7 : Nat → Bool :=
    Gate.applyNat (regCompareXor bits (1 + 2 * w)
      (1 + 2 * w + (2 * bits + 1) + numWin * w)) g6 with hg7def
  set g8 : Nat → Bool :=
    Gate.applyNat (lookupReadAt w (addendIdx (1 + 2 * w)) bits
      (WindowedArith.tableValue a N w j)) g7 with hg8def
  -- ── g₁ = copyWindow: the address register receives the window digit ────
  have hg1_frame : ∀ p, (∀ i, i < w → p ≠ ulookup_address_idx i) → g1 p = g p :=
    fun p hp => copyWindow_frame w (1 + 2 * w + (2 * bits + 1)) j g p hp
  have hg1_addr : ∀ i, i < w →
      g1 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i :=
    fun i hi => copyWindow_loads_window w (1 + 2 * w + (2 * bits + 1)) numWin y j g
      hctrl_addr hg_addr hg_y hj i hi
  have hg1_ctrl : g1 ulookup_ctrl_idx = true := by
    rw [hg1_frame _ (fun i hi => by unfold ulookup_ctrl_idx ulookup_address_idx; omega)]
    exact hg_ctrl
  have hg1_and : ∀ i, i < w → g1 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg1_frame _ (fun k hk => by unfold ulookup_and_idx ulookup_address_idx; omega)]
    exact hg_and i hi
  have hg1_read : ∀ i, i < bits → g1 (addendIdx (1 + 2 * w) i) = false := by
    intro i hi
    rw [hg1_frame _ (fun k hk => by unfold addendIdx ulookup_address_idx; omega)]
    exact hD i hi
  have hg1_tgt : ∀ i, i < bits → g1 (1 + 2 * w + 2 * i + 1) = s.testBit i := by
    intro i hi
    rw [hg1_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hV i hi
  have hg1_cin : g1 (1 + 2 * w) = false := by
    rw [hg1_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hC
  have hg1_flag : g1 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hg1_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hG
  have hg1_y : ∀ i, i < w →
      g1 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg1_frame _ (fun k hk => hctrl_addr i k hi hk)]
    exact hg_y i hi
  -- ── g₂ = QROM read: the table row lands in the addend register ─────────
  have hg2_frame : ∀ p, (∀ k, k < bits → p ≠ addendIdx (1 + 2 * w) k) → g2 p = g1 p :=
    fun p hp => lookupReadAt_frame w bits (WindowedArith.tableValue a N w j)
      (addendIdx (1 + 2 * w)) g1 hpos_high p hp
  have hg2_read : ∀ i, i < bits →
      g2 (addendIdx (1 + 2 * w) i)
        = (WindowedArith.tableValue a N w j (WindowedArith.window w y j)).testBit i := by
    intro i hi
    rw [hg2def,
        lookupReadAt_selects_word w bits (WindowedArith.tableValue a N w j)
          (addendIdx (1 + 2 * w)) g1 (WindowedArith.window w y j)
          hw hv hg1_ctrl hg1_addr hg1_and hpos_high hpos_inj i hi,
        hg1_read i hi, Bool.false_xor]
  have hg2_ctrl : g2 ulookup_ctrl_idx = true := by
    rw [hg2_frame _ (fun k hk => by unfold ulookup_ctrl_idx addendIdx; omega)]
    exact hg1_ctrl
  have hg2_addr : ∀ i, i < w →
      g2 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg2_frame _ (fun k hk => by unfold ulookup_address_idx addendIdx; omega)]
    exact hg1_addr i hi
  have hg2_and : ∀ i, i < w → g2 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg2_frame _ (fun k hk => by unfold ulookup_and_idx addendIdx; omega)]
    exact hg1_and i hi
  have hg2_tgt : ∀ i, i < bits → g2 (1 + 2 * w + 2 * i + 1) = s.testBit i := by
    intro i hi
    rw [hg2_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg1_tgt i hi
  have hg2_cin : g2 (1 + 2 * w) = false := by
    rw [hg2_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg1_cin
  have hg2_flag : g2 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hg2_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg1_flag
  have hg2_y : ∀ i, i < w →
      g2 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg2_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg1_y i hi
  -- ── g₃ = the adder: acc ← s + t (no overflow: s + t < 2N ≤ 2^bits) ─────
  have hg3_frame : ∀ p, p < 1 + 2 * w ∨ 1 + 2 * w + 2 * bits + 1 ≤ p →
      g3 p = g2 p := by
    intro p hp
    rcases hp with h | h
    · exact cuccaro_n_bit_adder_full_frame_below bits (1 + 2 * w) g2 p h
    · exact cuccaro_n_bit_adder_full_frame_above bits (1 + 2 * w) g2 p h
  have hg3_tgt : ∀ i, i < bits →
      g3 (1 + 2 * w + 2 * i + 1)
        = (s + WindowedArith.tableValue a N w j
            (WindowedArith.window w y j)).testBit i := by
    intro i hi
    show Gate.applyNat (cuccaro_n_bit_adder_full bits (1 + 2 * w)) g2
        (1 + 2 * w + 2 * i + 1) = _
    exact cuccaro_adder_sum_bits_general bits (1 + 2 * w) s
      (WindowedArith.tableValue a N w j (WindowedArith.window w y j)) g2
      hg2_cin hg2_tgt hg2_read i hi
  have hg3_read : ∀ i, i < bits →
      g3 (addendIdx (1 + 2 * w) i)
        = (WindowedArith.tableValue a N w j (WindowedArith.window w y j)).testBit i := by
    intro i hi
    show Gate.applyNat (cuccaro_n_bit_adder_full bits (1 + 2 * w)) g2
        (1 + 2 * w + 2 * i + 2) = _
    rw [(cuccaro_n_bit_adder_full_correct bits (1 + 2 * w) g2).2.2 i hi]
    exact hg2_read i hi
  have hg3_cin : g3 (1 + 2 * w) = false := by
    show Gate.applyNat (cuccaro_n_bit_adder_full bits (1 + 2 * w)) g2 (1 + 2 * w) = _
    rw [(cuccaro_n_bit_adder_full_correct bits (1 + 2 * w) g2).1]
    exact hg2_cin
  have hg3_ctrl : g3 ulookup_ctrl_idx = true := by
    rw [hg3_frame _ (by unfold ulookup_ctrl_idx; omega)]
    exact hg2_ctrl
  have hg3_addr : ∀ i, i < w →
      g3 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg3_frame _ (by unfold ulookup_address_idx; omega)]
    exact hg2_addr i hi
  have hg3_and : ∀ i, i < w → g3 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg3_frame _ (by unfold ulookup_and_idx; omega)]
    exact hg2_and i hi
  have hg3_flag : g3 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hg3_frame _ (by omega)]
    exact hg2_flag
  have hg3_y : ∀ i, i < w →
      g3 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg3_frame _ (by omega)]
    exact hg2_y i hi
  -- ── g₄ = QROM read again: the addend register is cleared ───────────────
  have hg4_frame : ∀ p, (∀ k, k < bits → p ≠ addendIdx (1 + 2 * w) k) → g4 p = g3 p :=
    fun p hp => lookupReadAt_frame w bits (WindowedArith.tableValue a N w j)
      (addendIdx (1 + 2 * w)) g3 hpos_high p hp
  have hg4_read : ∀ i, i < bits → g4 (addendIdx (1 + 2 * w) i) = false := by
    intro i hi
    rw [hg4def,
        lookupReadAt_selects_word w bits (WindowedArith.tableValue a N w j)
          (addendIdx (1 + 2 * w)) g3 (WindowedArith.window w y j)
          hw hv hg3_ctrl hg3_addr hg3_and hpos_high hpos_inj i hi,
        hg3_read i hi, Bool.xor_self]
  have hg4_tgt : ∀ i, i < bits →
      g4 (1 + 2 * w + 2 * i + 1)
        = (s + WindowedArith.tableValue a N w j
            (WindowedArith.window w y j)).testBit i := by
    intro i hi
    rw [hg4_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg3_tgt i hi
  have hg4_cin : g4 (1 + 2 * w) = false := by
    rw [hg4_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg3_cin
  have hg4_flag : g4 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hg4_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg3_flag
  have hg4_ctrl : g4 ulookup_ctrl_idx = true := by
    rw [hg4_frame _ (fun k hk => by unfold ulookup_ctrl_idx addendIdx; omega)]
    exact hg3_ctrl
  have hg4_addr : ∀ i, i < w →
      g4 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg4_frame _ (fun k hk => by unfold ulookup_address_idx addendIdx; omega)]
    exact hg3_addr i hi
  have hg4_and : ∀ i, i < w → g4 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg4_frame _ (fun k hk => by unfold ulookup_and_idx addendIdx; omega)]
    exact hg3_and i hi
  have hg4_y : ∀ i, i < w →
      g4 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg4_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg3_y i hi
  -- ── g₅ = mod-N reduction: acc ← (s+t) mod N, flag ← [N ≤ s+t] ──────────
  have hred := modNReduceFlag_state_general bits (1 + 2 * w) N
    (1 + 2 * w + (2 * bits + 1) + numWin * w)
    (s + WindowedArith.tableValue a N w j (WindowedArith.window w y j)) g4
    hN_pos hN2 (by omega) hflag_out hg4_cin hg4_flag hg4_tgt hg4_read
  have hg5_tgt : ∀ i, i < bits →
      g5 (1 + 2 * w + 2 * i + 1)
        = ((s + WindowedArith.tableValue a N w j
            (WindowedArith.window w y j)) % N).testBit i :=
    fun i hi => hred.1 i hi
  have hg5_read : ∀ i, i < bits → g5 (addendIdx (1 + 2 * w) i) = false :=
    fun i hi => hred.2.1 i hi
  have hg5_cin : g5 (1 + 2 * w) = false := hred.2.2.1
  have hg5_flag : g5 (1 + 2 * w + (2 * bits + 1) + numWin * w)
      = decide (N ≤ s + WindowedArith.tableValue a N w j
          (WindowedArith.window w y j)) := hred.2.2.2.1
  have hg5_frame : ∀ p, p ≠ 1 + 2 * w + (2 * bits + 1) + numWin * w →
      p < 1 + 2 * w ∨ 1 + 2 * w + 2 * bits + 1 ≤ p → g5 p = g4 p :=
    fun p hp hout => hred.2.2.2.2 p hp hout
  have hg5_ctrl : g5 ulookup_ctrl_idx = true := by
    rw [hg5_frame _ (by unfold ulookup_ctrl_idx; omega)
          (by unfold ulookup_ctrl_idx; omega)]
    exact hg4_ctrl
  have hg5_addr : ∀ i, i < w →
      g5 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg5_frame _ (by unfold ulookup_address_idx; omega)
          (by unfold ulookup_address_idx; omega)]
    exact hg4_addr i hi
  have hg5_and : ∀ i, i < w → g5 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg5_frame _ (by unfold ulookup_and_idx; omega)
          (by unfold ulookup_and_idx; omega)]
    exact hg4_and i hi
  have hg5_y : ∀ i, i < w →
      g5 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg5_frame _ (by omega) (by omega)]
    exact hg4_y i hi
  -- ── g₆ = QROM read: the addend register reloads the table row ──────────
  have hg6_frame : ∀ p, (∀ k, k < bits → p ≠ addendIdx (1 + 2 * w) k) → g6 p = g5 p :=
    fun p hp => lookupReadAt_frame w bits (WindowedArith.tableValue a N w j)
      (addendIdx (1 + 2 * w)) g5 hpos_high p hp
  have hg6_read : ∀ i, i < bits →
      g6 (addendIdx (1 + 2 * w) i)
        = (WindowedArith.tableValue a N w j (WindowedArith.window w y j)).testBit i := by
    intro i hi
    rw [hg6def,
        lookupReadAt_selects_word w bits (WindowedArith.tableValue a N w j)
          (addendIdx (1 + 2 * w)) g5 (WindowedArith.window w y j)
          hw hv hg5_ctrl hg5_addr hg5_and hpos_high hpos_inj i hi,
        hg5_read i hi, Bool.false_xor]
  have hg6_tgt : ∀ i, i < bits →
      g6 (1 + 2 * w + 2 * i + 1)
        = ((s + WindowedArith.tableValue a N w j
            (WindowedArith.window w y j)) % N).testBit i := by
    intro i hi
    rw [hg6_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg5_tgt i hi
  have hg6_cin : g6 (1 + 2 * w) = false := by
    rw [hg6_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg5_cin
  have hg6_flag : g6 (1 + 2 * w + (2 * bits + 1) + numWin * w)
      = decide (N ≤ s + WindowedArith.tableValue a N w j
          (WindowedArith.window w y j)) := by
    rw [hg6_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg5_flag
  have hg6_ctrl : g6 ulookup_ctrl_idx = true := by
    rw [hg6_frame _ (fun k hk => by unfold ulookup_ctrl_idx addendIdx; omega)]
    exact hg5_ctrl
  have hg6_addr : ∀ i, i < w →
      g6 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg6_frame _ (fun k hk => by unfold ulookup_address_idx addendIdx; omega)]
    exact hg5_addr i hi
  have hg6_and : ∀ i, i < w → g6 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg6_frame _ (fun k hk => by unfold ulookup_and_idx addendIdx; omega)]
    exact hg5_and i hi
  have hg6_y : ∀ i, i < w →
      g6 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg6_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg5_y i hi
  -- ── g₇ = register-compare: the flag is uncomputed ──────────────────────
  have happ7 : Gate.applyNat (regCompareXor bits (1 + 2 * w)
      (1 + 2 * w + (2 * bits + 1) + numWin * w)) g6
      = update g6 (1 + 2 * w + (2 * bits + 1) + numWin * w) false := by
    rw [regCompareXor_state_general bits (1 + 2 * w)
          (1 + 2 * w + (2 * bits + 1) + numWin * w)
          ((s + WindowedArith.tableValue a N w j (WindowedArith.window w y j)) % N)
          (WindowedArith.tableValue a N w j (WindowedArith.window w y j)) g6
          (by have := Nat.mod_lt (s + WindowedArith.tableValue a N w j
                (WindowedArith.window w y j)) hN_pos; omega)
          (by omega) hflag_out hg6_cin hg6_tgt hg6_read]
    rw [hg6_flag,
        modReduce_lt_decide N s
          (WindowedArith.tableValue a N w j (WindowedArith.window w y j)) hs ht_lt,
        Bool.xor_self]
  have hg7_other : ∀ p, p ≠ 1 + 2 * w + (2 * bits + 1) + numWin * w →
      g7 p = g6 p := by
    intro p hp
    show Gate.applyNat (regCompareXor bits (1 + 2 * w)
        (1 + 2 * w + (2 * bits + 1) + numWin * w)) g6 p = _
    rw [happ7]
    exact update_neq _ _ _ _ hp
  have hg7_flag : g7 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    show Gate.applyNat (regCompareXor bits (1 + 2 * w)
        (1 + 2 * w + (2 * bits + 1) + numWin * w)) g6
        (1 + 2 * w + (2 * bits + 1) + numWin * w) = _
    rw [happ7]
    exact update_eq _ _ _
  have hg7_ctrl : g7 ulookup_ctrl_idx = true := by
    rw [hg7_other _ (by unfold ulookup_ctrl_idx; omega)]
    exact hg6_ctrl
  have hg7_addr : ∀ i, i < w →
      g7 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg7_other _ (by unfold ulookup_address_idx; omega)]
    exact hg6_addr i hi
  have hg7_and : ∀ i, i < w → g7 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg7_other _ (by unfold ulookup_and_idx; omega)]
    exact hg6_and i hi
  have hg7_read : ∀ i, i < bits →
      g7 (addendIdx (1 + 2 * w) i)
        = (WindowedArith.tableValue a N w j (WindowedArith.window w y j)).testBit i := by
    intro i hi
    rw [hg7_other _ (by unfold addendIdx; omega)]
    exact hg6_read i hi
  have hg7_tgt : ∀ i, i < bits →
      g7 (1 + 2 * w + 2 * i + 1)
        = ((s + WindowedArith.tableValue a N w j
            (WindowedArith.window w y j)) % N).testBit i := by
    intro i hi
    rw [hg7_other _ (by omega)]
    exact hg6_tgt i hi
  have hg7_cin : g7 (1 + 2 * w) = false := by
    rw [hg7_other _ (by omega)]
    exact hg6_cin
  have hg7_y : ∀ i, i < w →
      g7 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg7_other _ (by omega)]
    exact hg6_y i hi
  -- ── g₈ = QROM read: the addend register is cleared again ───────────────
  have hg8_frame : ∀ p, (∀ k, k < bits → p ≠ addendIdx (1 + 2 * w) k) → g8 p = g7 p :=
    fun p hp => lookupReadAt_frame w bits (WindowedArith.tableValue a N w j)
      (addendIdx (1 + 2 * w)) g7 hpos_high p hp
  have hg8_read : ∀ i, i < bits → g8 (addendIdx (1 + 2 * w) i) = false := by
    intro i hi
    rw [hg8def,
        lookupReadAt_selects_word w bits (WindowedArith.tableValue a N w j)
          (addendIdx (1 + 2 * w)) g7 (WindowedArith.window w y j)
          hw hv hg7_ctrl hg7_addr hg7_and hpos_high hpos_inj i hi,
        hg7_read i hi, Bool.xor_self]
  have hg8_addr : ∀ i, i < w →
      g8 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg8_frame _ (fun k hk => by unfold ulookup_address_idx addendIdx; omega)]
    exact hg7_addr i hi
  have hg8_tgt : ∀ i, i < bits →
      g8 (1 + 2 * w + 2 * i + 1)
        = ((s + WindowedArith.tableValue a N w j
            (WindowedArith.window w y j)) % N).testBit i := by
    intro i hi
    rw [hg8_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg7_tgt i hi
  have hg8_cin : g8 (1 + 2 * w) = false := by
    rw [hg8_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg7_cin
  have hg8_flag : g8 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hg8_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg7_flag
  have hg8_y : ∀ i, i < w →
      g8 ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := by
    intro i hi
    rw [hg8_frame _ (fun k hk => by unfold addendIdx; omega)]
    exact hg7_y i hi
  -- ── g₉ = copyWindow again: the address register is cleared ─────────────
  have hg9_frame : ∀ p, (∀ i, i < w → p ≠ ulookup_address_idx i) →
      Gate.applyNat (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) g8 p = g8 p :=
    fun p hp => copyWindow_frame w (1 + 2 * w + (2 * bits + 1)) j g8 p hp
  have hg9_addr : ∀ i, i < w →
      Gate.applyNat (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) g8
        (ulookup_address_idx i) = false := by
    intro i hi
    rw [copyWindow_at_addr w (1 + 2 * w + (2 * bits + 1)) j g8 hctrl_addr i hi,
        hg8_addr i hi, hg8_y i hi,
        encodeReg_window_bit (1 + 2 * w + (2 * bits + 1)) w numWin y j i hi hj,
        Bool.xor_self]
  -- ── Reassemble the invariant ───────────────────────────────────────────
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (F) frame off the block and the flag.
    intro p hpb hpf
    by_cases hpaddr : ∃ i, i < w ∧ p = ulookup_address_idx i
    · obtain ⟨i, hi, rfl⟩ := hpaddr
      rw [hg9_addr i hi]
      exact (mulInputOf_low cuccaroAdder w bits numWin y _
        (by unfold ulookup_ctrl_idx ulookup_address_idx; omega)
        (by unfold ulookup_address_idx; omega)).symm
    · push Not at hpaddr
      have hp_not_addr : ∀ i, i < w → p ≠ ulookup_address_idx i :=
        fun i hi => hpaddr i hi
      have hp_not_pos : ∀ k, k < bits → p ≠ addendIdx (1 + 2 * w) k := by
        intro k hk heq
        apply hpb
        unfold addendIdx at heq
        unfold inBlock
        omega
      have hp_out : p < 1 + 2 * w ∨ 1 + 2 * w + 2 * bits + 1 ≤ p := by
        unfold inBlock at hpb
        omega
      rw [hg9_frame p hp_not_addr, hg8_frame p hp_not_pos, hg7_other p hpf,
          hg6_frame p hp_not_pos, hg5_frame p hpf hp_out, hg4_frame p hp_not_pos,
          hg3_frame p hp_out, hg2_frame p hp_not_pos, hg1_frame p hp_not_addr]
      exact hF p hpb hpf
  · -- (D) the addend register is clean again.
    intro i hi
    rw [hg9_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hg8_read i hi
  · -- (C) the carry-in is clean.
    rw [hg9_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hg8_cin
  · -- (G) the flag is clean again (uncomputed by the register-compare).
    rw [hg9_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hg8_flag
  · -- (V) the accumulator holds the new mod-N partial sum.
    intro i hi
    rw [hg9_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]
    exact hg8_tgt i hi


end FormalRV.Shor.WindowedCircuit
