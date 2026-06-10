/-
  FormalRV.Arithmetic.Windowed.WindowedGrayLookup — the **Gray-code-read
  windowed multiplier**: the adder-generic windowed multiplier with the QROM
  lookup slot filled by the gate-level Gray-code/sawtooth read
  (`grayLookupReadAt`, FormalRV/Arithmetic/UnaryLookup/UnaryLookupGrayCode.lean)
  instead of the faithful per-row read (`lookupReadAt`).

  ## Why this file exists (audit grade: Gidney–Ekerå 2021)

  The faithful windowed multiplier (`windowedMulCircuitOf`,
  Windowed/WindowedCircuit.lean) charges `14·w·2^w` T per table read — the
  no-optimization unary cascade re-run per row.  Gidney–Ekerå 2021 (and
  qianxu p. 23) charge the Gray-code-amortized cost.  This file builds the SAME
  windowed multiplier with the Gray-code read dropped into the lookup slot,
  closing the factor `w` at the gate level:

      per read:   14·w·2^w   →   14·(2^w − 1)
      per window: 28·w·2^w + adder   →   28·(2^w − 1) + adder

  The residual ×2 against the papers' `2^w` Toffolis per lookup is the
  measurement-based uncompute (EXIT Toffolis replaced by X-basis measurements
  + classically-controlled Cliffords), which is not expressible in the pure
  X/CX/CCX `Gate` IR — see the UnaryLookupGrayCode module docstring and
  `FormalRV/Shor/MeasUncompute.lean`.

  ## Headlines

  * `grayWindowedMulCircuitOf_correct` — VALUE: for ANY adder `A`, the
    Gray-code windowed multiplier leaves `(a·y) mod 2^bits` in the
    accumulator.  Same statement (same hypotheses, same input `mulInputOf`)
    as the faithful `windowedMulCircuitOf_correct`; instances
    `grayWindowedMulCircuit_correct_cuccaro` / `_gidney`.
  * `tcount_grayWindowedMulCircuitOf` — RESOURCE:
    `numWin · (2·(14·(2^w − 1)) + tcount (A.circuit bits (1+2w)))`; Cuccaro
    closed form `numWin · (28·(2^w − 1) + 14·bits)` and Toffoli count
    `numWin · (4·(2^w − 1) + 2·bits)` — versus the faithful
    `numWin · (4·w·2^w + 2·bits)`: the factor `w` is GONE.
  * `tcount_grayWindowedMulCircuitOf_le_faithful` — the Gray-code multiplier
    never costs more than the faithful one (any adder, `0 < w`).

  ## Which file to import when auditing

  Import THIS file when auditing the optimized (Gray-code) lookup counts that
  Gidney–Ekerå-style resource estimates charge; import the faithful
  `Windowed/WindowedCircuit(Correct)` when auditing the no-optimization
  baseline.  Both expose the same value theorem, so the choice only moves the
  resource count.

  Proof reuse: `StepInv`, `stepInv_init`, `mulInputOf` and all the
  copy-window/adder-contract lemmas are circuit-independent and are REUSED
  from WindowedCircuitCorrect; only the step/fold/headline are cloned, with
  `grayLookupReadAt_selects_word` / `grayLookupReadAt_frame` consumed as
  black boxes exactly where the faithful proof consumed
  `lookupReadAt_selects_word` / `lookupReadAt_frame` (the contracts are
  statement-identical).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.UnaryLookup.UnaryLookupGrayCode
import FormalRV.Arithmetic.Windowed.WindowedCircuitCorrect

namespace FormalRV.Shor.WindowedCircuit

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §1. The circuit: the windowed multiplier with the Gray-code read in the
lookup slot.  Mirrors `lookupAddAtOf` / `windowStepOf` / `windowedMulOf` /
`windowedMulCircuitOf` (Windowed/WindowedCircuit.lean) with `lookupReadAt`
replaced by `grayLookupReadAt`; layout unchanged. -/

/-- **Gray-code lookup-ADDITION.**  Gidney l.276 read·add·unread with the
    Gray-code/sawtooth QROM read, word register laid out AS adder `A`'s addend
    register.  (Mirror of `lookupAddAtOf`.) -/
def grayLookupAddAtOf (A : Adder) (w W : Nat) (T : Nat → Nat) (bits q_start : Nat) : Gate :=
  Gate.seq (Gate.seq (grayLookupReadAt w (A.addendIdx q_start) W T)
                     (A.circuit bits q_start))
           (grayLookupReadAt w (A.addendIdx q_start) W T)

/-- **Gray-code window step.**  Copy window `j` into the lookup address,
    Gray-code-lookup-add the entry `T_j[v] = a·(2^w)^j·v` into adder `A`, then
    uncopy.  (Mirror of `windowStepOf`.) -/
def grayWindowStepOf (A : Adder) (w W a : Nat) (bits q_start yBase j : Nat) : Gate :=
  Gate.seq (Gate.seq (copyWindow w yBase j)
                     (grayLookupAddAtOf A w W (fun v => a * (2 ^ w) ^ j * v) bits q_start))
           (copyWindow w yBase j)

/-- **Gray-code windowed multiplier**, a fold of Gray-code window-steps over
    adder `A`.  (Mirror of `windowedMulOf`.) -/
def grayWindowedMulOf (A : Adder) (w W a : Nat) (bits q_start yBase numWin : Nat) : Gate :=
  (List.range numWin).foldl
    (fun g j => Gate.seq g (grayWindowStepOf A w W a bits q_start yBase j)) Gate.I

/-- **The full Gray-code windowed-multiplier circuit over an arbitrary adder
    `A`.**  Same layout as the faithful `windowedMulCircuitOf`: ctrl=0; address
    bits `1,3,…,2w−1`; AND-ancillas `2,4,…,2w`; the adder region at
    `q_start = 1+2w`; the `y`-register at `yBase = q_start + A.span bits`. -/
def grayWindowedMulCircuitOf (A : Adder) (w bits a numWin : Nat) : Gate :=
  grayWindowedMulOf A w bits a bits (1 + 2 * w) (1 + 2 * w + A.span bits) numWin

/-! ## §2. The Gray-code window step preserves the invariant.

`StepInv` (WindowedCircuitCorrect §3) is a predicate on STATES — it never
mentions the circuit — so it is reused as-is, together with `stepInv_init`.
Only the step lemma is cloned: the faithful proof consumed
`lookupReadAt_selects_word` / `lookupReadAt_frame` as black boxes at exactly
two points (the read and the unread); here the Gray-code contracts — which are
statement-identical — are consumed at the same two points. -/

/-- One Gray-code window step preserves `StepInv`, adding
    `a·(2^w)^j·windowⱼ(y)` to the partial sum.  (Clone of `stepInv_step` with
    the Gray-code read lemmas swapped in.) -/
theorem grayStepInv_step (A : Adder) (w bits a numWin y : Nat) (hw : 0 < w)
    (j : Nat) (hj : j < numWin) (s : Nat) (g : Nat → Bool)
    (hg : StepInv A w bits numWin y s g) :
    StepInv A w bits numWin y (s + a * (2 ^ w) ^ j * WindowedArith.window w y j)
      (Gate.applyNat
        (grayWindowStepOf A w bits a bits (1 + 2 * w) (1 + 2 * w + A.span bits) j)
        g) := by
  obtain ⟨hF, hD, hC, hV⟩ := hg
  -- Expose the five-fold composition.
  simp only [grayWindowStepOf, grayLookupAddAtOf, Gate.applyNat_seq]
  set g1 : Nat → Bool :=
    Gate.applyNat (copyWindow w (1 + 2 * w + A.span bits) j) g with hg1def
  set g2 : Nat → Bool :=
    Gate.applyNat (grayLookupReadAt w (A.addendIdx (1 + 2 * w)) bits
      (fun v => a * (2 ^ w) ^ j * v)) g1 with hg2def
  set g3 : Nat → Bool := Gate.applyNat (A.circuit bits (1 + 2 * w)) g2 with hg3def
  set g4 : Nat → Bool :=
    Gate.applyNat (grayLookupReadAt w (A.addendIdx (1 + 2 * w)) bits
      (fun v => a * (2 ^ w) ^ j * v)) g3 with hg4def
  set g5 : Nat → Bool :=
    Gate.applyNat (copyWindow w (1 + 2 * w + A.span bits) j) g4 with hg5def
  -- ── Standing zone facts ────────────────────────────────────────────────
  -- CX controls (y-wires) are never address wires.
  have hctrl_addr : ∀ i k, i < w → k < w →
      (1 + 2 * w + A.span bits) + j * w + i ≠ ulookup_address_idx k :=
    ctrl_ne_addr_of_le_yBase w (1 + 2 * w + A.span bits) j (by omega)
  -- The addend positions sit above the lookup zone and are injective.
  have hpos_high : ∀ k, k < bits → 2 * w < A.addendIdx (1 + 2 * w) k := by
    intro k hk
    have hblk := A.addendIdx_inBlock bits (1 + 2 * w) k hk
    unfold inBlock at hblk
    omega
  have hpos_inj : ∀ k l, k < bits → l < bits →
      A.addendIdx (1 + 2 * w) k = A.addendIdx (1 + 2 * w) l → k = l :=
    fun k l _ _ h => A.addendIdx_inj (1 + 2 * w) k l h
  -- The ctrl / address / AND wires are never addend positions.
  have hctrl_ne_pos : ∀ k, k < bits →
      ulookup_ctrl_idx ≠ A.addendIdx (1 + 2 * w) k := by
    intro k hk
    have := hpos_high k hk
    unfold ulookup_ctrl_idx
    omega
  have haddr_ne_pos : ∀ i, i < w → ∀ k, k < bits →
      ulookup_address_idx i ≠ A.addendIdx (1 + 2 * w) k := by
    intro i hi k hk
    have := hpos_high k hk
    unfold ulookup_address_idx
    omega
  have hand_ne_pos : ∀ i, i < w → ∀ k, k < bits →
      ulookup_and_idx i ≠ A.addendIdx (1 + 2 * w) k := by
    intro i hi k hk
    have := hpos_high k hk
    unfold ulookup_and_idx
    omega
  -- The lookup zone lies below the block; the y-register lies above it.
  have hctrl_out : ¬ inBlock (1 + 2 * w) (A.span bits) ulookup_ctrl_idx := by
    unfold inBlock ulookup_ctrl_idx
    omega
  have haddr_out : ∀ i, i < w →
      ¬ inBlock (1 + 2 * w) (A.span bits) (ulookup_address_idx i) := by
    intro i hi
    unfold inBlock ulookup_address_idx
    omega
  have hand_out : ∀ i, i < w →
      ¬ inBlock (1 + 2 * w) (A.span bits) (ulookup_and_idx i) := by
    intro i hi
    unfold inBlock ulookup_and_idx
    omega
  have hy_out : ∀ i, i < w →
      ¬ inBlock (1 + 2 * w) (A.span bits) ((1 + 2 * w + A.span bits) + j * w + i) := by
    intro i hi
    unfold inBlock
    omega
  -- The y-wires are never addend positions (addend is in-block, y is above).
  have hy_ne_pos : ∀ i, i < w → ∀ k, k < bits →
      (1 + 2 * w + A.span bits) + j * w + i ≠ A.addendIdx (1 + 2 * w) k := by
    intro i hi k hk
    have hblk := A.addendIdx_inBlock bits (1 + 2 * w) k hk
    unfold inBlock at hblk
    omega
  -- The augend positions are never address wires (they sit at/above the base).
  have haug_ne_addr : ∀ i, i < bits → ∀ k, k < w →
      A.augendIdx (1 + 2 * w) i ≠ ulookup_address_idx k := by
    intro i hi k hk
    have hblk := A.augendIdx_inBlock bits (1 + 2 * w) i hi
    unfold inBlock at hblk
    unfold ulookup_address_idx
    omega
  -- The addend positions are never address wires.
  have hadd_ne_addr : ∀ i, i < bits → ∀ k, k < w →
      A.addendIdx (1 + 2 * w) i ≠ ulookup_address_idx k := by
    intro i hi k hk
    have := hpos_high i hi
    unfold ulookup_address_idx
    omega
  -- ── g (pre-step) register values, from the frame conjunct ─────────────
  have hg_addr_clean : ∀ i, i < w → g (ulookup_address_idx i) = false := by
    intro i hi
    rw [hF _ (haddr_out i hi)]
    exact mulInputOf_low A w bits numWin y _
      (by unfold ulookup_ctrl_idx ulookup_address_idx; omega)
      (by unfold ulookup_address_idx; omega)
  have hg_y : ∀ i, i < w →
      g ((1 + 2 * w + A.span bits) + j * w + i)
        = encodeReg (1 + 2 * w + A.span bits) (numWin * w) y
            ((1 + 2 * w + A.span bits) + j * w + i) := by
    intro i hi
    rw [hF _ (hy_out i hi)]
    exact mulInputOf_eq_encodeReg A w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega)
  -- ── g₁ = copyWindow: the address register receives the window digit ───
  have hg1_addr : ∀ i, i < w →
      g1 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i :=
    fun i hi => copyWindow_loads_window w (1 + 2 * w + A.span bits) numWin y j g
      hctrl_addr hg_addr_clean hg_y hj i hi
  have hg1_frame : ∀ p, (∀ i, i < w → p ≠ ulookup_address_idx i) → g1 p = g p :=
    fun p hp => copyWindow_frame w (1 + 2 * w + A.span bits) j g p hp
  have hg1_ctrl : g1 ulookup_ctrl_idx = true := by
    rw [hg1_frame _ (fun i hi => by unfold ulookup_ctrl_idx ulookup_address_idx; omega),
        hF _ hctrl_out]
    exact mulInputOf_ctrl A w bits numWin y
  have hg1_and : ∀ i, i < w → g1 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg1_frame _ (fun k hk => by unfold ulookup_and_idx ulookup_address_idx; omega),
        hF _ (hand_out i hi)]
    exact mulInputOf_low A w bits numWin y _
      (by unfold ulookup_ctrl_idx ulookup_and_idx; omega)
      (by unfold ulookup_and_idx; omega)
  have hg1_addend : ∀ i, i < bits → g1 (A.addendIdx (1 + 2 * w) i) = false := by
    intro i hi
    rw [hg1_frame _ (fun k hk => (hadd_ne_addr i hi k hk)),
        hD i hi]
  have hg1_aug : ∀ i, i < bits →
      g1 (A.augendIdx (1 + 2 * w) i) = g (A.augendIdx (1 + 2 * w) i) :=
    fun i hi => hg1_frame _ (fun k hk => haug_ne_addr i hi k hk)
  -- ── g₂ = GRAY-CODE read: the table row lands in the addend register ───
  have hvlt : WindowedArith.window w y j < 2 ^ w := WindowedArith.window_lt w y j
  have hg2_addend : ∀ i, i < bits →
      g2 (A.addendIdx (1 + 2 * w) i)
        = (a * (2 ^ w) ^ j * WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg2def,
        grayLookupReadAt_selects_word w bits (fun v => a * (2 ^ w) ^ j * v)
          (A.addendIdx (1 + 2 * w)) g1 (WindowedArith.window w y j)
          hw hvlt hg1_ctrl hg1_addr hg1_and hpos_high hpos_inj i hi,
        hg1_addend i hi, Bool.false_xor]
  have hg2_frame : ∀ p, (∀ k, k < bits → p ≠ A.addendIdx (1 + 2 * w) k) →
      g2 p = g1 p :=
    fun p hp => grayLookupReadAt_frame w bits (fun v => a * (2 ^ w) ^ j * v)
      (A.addendIdx (1 + 2 * w)) g1 hpos_high p hp
  have hg2_ctrl : g2 ulookup_ctrl_idx = true := by
    rw [hg2_frame _ hctrl_ne_pos]
    exact hg1_ctrl
  have hg2_addr : ∀ i, i < w →
      g2 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg2_frame _ (haddr_ne_pos i hi)]
    exact hg1_addr i hi
  have hg2_and : ∀ i, i < w → g2 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg2_frame _ (hand_ne_pos i hi)]
    exact hg1_and i hi
  have hg2_aug : ∀ i, i < bits →
      g2 (A.augendIdx (1 + 2 * w) i) = g (A.augendIdx (1 + 2 * w) i) := by
    intro i hi
    rw [hg2_frame _ (fun k _ => A.augend_addend_disjoint (1 + 2 * w) i k)]
    exact hg1_aug i hi
  -- The read/copy only touched out-of-block wires and the addend, so the
  -- ancilla block is still clean.
  have hg2_clean : A.ancClean g2 bits (1 + 2 * w) := by
    refine A.ancClean_ext bits (1 + 2 * w) g g2 ?_ hC
    intro p hin hoff
    rw [hg2_frame p (fun k hk => (hoff k hk).2),
        hg1_frame p (fun k hk => by
          unfold inBlock at hin
          unfold ulookup_address_idx
          omega)]
  -- ── g₃ = the adder: augend ← augend + row, addend restored ────────────
  have hg3_dec : decodeReg (A.augendIdx (1 + 2 * w)) bits g3
      = (s + a * (2 ^ w) ^ j * WindowedArith.window w y j) % 2 ^ bits := by
    rw [hg3def, A.sumCorrect bits (1 + 2 * w) g2 hg2_clean,
        decodeReg_ext (A.augendIdx (1 + 2 * w)) bits g2 g hg2_aug, hV,
        decodeReg_eq_mod_of_testBit (A.addendIdx (1 + 2 * w)) bits
          (a * (2 ^ w) ^ j * WindowedArith.window w y j) g2 hg2_addend,
        ← Nat.add_mod]
  have hg3_addend : ∀ i, i < bits →
      g3 (A.addendIdx (1 + 2 * w) i)
        = (a * (2 ^ w) ^ j * WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg3def, A.addendRestored bits (1 + 2 * w) g2 hg2_clean i hi]
    exact hg2_addend i hi
  have hg3_clean : A.ancClean g3 bits (1 + 2 * w) :=
    A.ancRestored bits (1 + 2 * w) g2 hg2_clean
  have hg3_frame : ∀ p, ¬ inBlock (1 + 2 * w) (A.span bits) p → g3 p = g2 p :=
    fun p hp => A.frame bits (1 + 2 * w) g2 p hp
  have hg3_ctrl : g3 ulookup_ctrl_idx = true := by
    rw [hg3_frame _ hctrl_out]
    exact hg2_ctrl
  have hg3_addr : ∀ i, i < w →
      g3 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg3_frame _ (haddr_out i hi)]
    exact hg2_addr i hi
  have hg3_and : ∀ i, i < w → g3 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg3_frame _ (hand_out i hi)]
    exact hg2_and i hi
  -- ── g₄ = GRAY-CODE read again: the addend register is cleared ─────────
  have hg4_addend : ∀ i, i < bits → g4 (A.addendIdx (1 + 2 * w) i) = false := by
    intro i hi
    rw [hg4def,
        grayLookupReadAt_selects_word w bits (fun v => a * (2 ^ w) ^ j * v)
          (A.addendIdx (1 + 2 * w)) g3 (WindowedArith.window w y j)
          hw hvlt hg3_ctrl hg3_addr hg3_and hpos_high hpos_inj i hi,
        hg3_addend i hi, Bool.xor_self]
  have hg4_frame : ∀ p, (∀ k, k < bits → p ≠ A.addendIdx (1 + 2 * w) k) →
      g4 p = g3 p :=
    fun p hp => grayLookupReadAt_frame w bits (fun v => a * (2 ^ w) ^ j * v)
      (A.addendIdx (1 + 2 * w)) g3 hpos_high p hp
  have hg4_clean : A.ancClean g4 bits (1 + 2 * w) := by
    refine A.ancClean_ext bits (1 + 2 * w) g3 g4 ?_ hg3_clean
    intro p _ hoff
    exact (hg4_frame p (fun k hk => (hoff k hk).2)).symm
  have hg4_aug : ∀ i, i < bits →
      g4 (A.augendIdx (1 + 2 * w) i) = g3 (A.augendIdx (1 + 2 * w) i) :=
    fun i hi => hg4_frame _ (fun k _ => A.augend_addend_disjoint (1 + 2 * w) i k)
  have hg4_addr : ∀ i, i < w →
      g4 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg4_frame _ (haddr_ne_pos i hi)]
    exact hg3_addr i hi
  have hg4_y : ∀ i, i < w →
      g4 ((1 + 2 * w + A.span bits) + j * w + i)
        = encodeReg (1 + 2 * w + A.span bits) (numWin * w) y
            ((1 + 2 * w + A.span bits) + j * w + i) := by
    intro i hi
    rw [hg4_frame _ (hy_ne_pos i hi), hg3_frame _ (hy_out i hi),
        hg2_frame _ (hy_ne_pos i hi),
        hg1_frame _ (fun k hk => hctrl_addr i k hi hk)]
    exact hg_y i hi
  -- ── g₅ = copyWindow again: the address register is cleared ────────────
  have hg5_addr : ∀ i, i < w → g5 (ulookup_address_idx i) = false := by
    intro i hi
    rw [hg5def,
        copyWindow_at_addr w (1 + 2 * w + A.span bits) j g4 hctrl_addr i hi,
        hg4_addr i hi, hg4_y i hi,
        encodeReg_window_bit (1 + 2 * w + A.span bits) w numWin y j i hi hj,
        Bool.xor_self]
  have hg5_frame : ∀ p, (∀ i, i < w → p ≠ ulookup_address_idx i) → g5 p = g4 p :=
    fun p hp => copyWindow_frame w (1 + 2 * w + A.span bits) j g4 p hp
  -- ── Reassemble the invariant for g₅ ───────────────────────────────────
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (F) frame off the block.
    intro p hp
    by_cases hpaddr : ∃ i, i < w ∧ p = ulookup_address_idx i
    · obtain ⟨i, hi, rfl⟩ := hpaddr
      rw [hg5_addr i hi]
      exact (mulInputOf_low A w bits numWin y _
        (by unfold ulookup_ctrl_idx ulookup_address_idx; omega)
        (by unfold ulookup_address_idx; omega)).symm
    · push Not at hpaddr
      have hp_ne_pos : ∀ k, k < bits → p ≠ A.addendIdx (1 + 2 * w) k :=
        fun k hk heq => hp (heq ▸ A.addendIdx_inBlock bits (1 + 2 * w) k hk)
      rw [hg5_frame p hpaddr, hg4_frame p hp_ne_pos, hg3_frame p hp,
          hg2_frame p hp_ne_pos, hg1_frame p hpaddr]
      exact hF p hp
  · -- (D) the addend register is clean again.
    intro i hi
    rw [hg5_frame _ (fun k hk => hadd_ne_addr i hi k hk)]
    exact hg4_addend i hi
  · -- (C) the ancilla block is clean again.
    refine A.ancClean_ext bits (1 + 2 * w) g4 g5 ?_ hg4_clean
    intro p hin _
    exact (hg5_frame p (fun k hk => by
      unfold inBlock at hin
      unfold ulookup_address_idx
      omega)).symm
  · -- (V) the augend register decodes to the new partial sum.
    rw [decodeReg_ext (A.augendIdx (1 + 2 * w)) bits g5 g4
          (fun i hi => hg5_frame _ (fun k hk => haug_ne_addr i hi k hk)),
        decodeReg_ext (A.augendIdx (1 + 2 * w)) bits g4 g3 hg4_aug]
    exact hg3_dec

/-! ## §3. The fold and the headline value theorem. -/

/-- Running the first `n` Gray-code window-steps (`n ≤ numWin`) establishes the
    invariant with partial sum `Σ_{k<n} a·(2^w)^k·windowₖ(y)`.
    (Clone of `stepInv_fold`; `stepInv_init` is reused as-is.) -/
theorem grayStepInv_fold (A : Adder) (w bits a numWin y : Nat) (hw : 0 < w)
    (hclean : A.ancClean (mulInputOf A w bits numWin y) bits (1 + 2 * w)) :
    ∀ n, n ≤ numWin →
      StepInv A w bits numWin y
        (∑ k ∈ Finset.range n, a * (2 ^ w) ^ k * WindowedArith.window w y k)
        (Gate.applyNat
          (grayWindowedMulOf A w bits a bits (1 + 2 * w) (1 + 2 * w + A.span bits) n)
          (mulInputOf A w bits numWin y)) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Finset.sum_range_zero]
    show StepInv A w bits numWin y 0
      (Gate.applyNat Gate.I (mulInputOf A w bits numWin y))
    rw [Gate.applyNat_I]
    exact stepInv_init A w bits numWin y hclean
  | succ n ih =>
    intro hn
    have hsplit : grayWindowedMulOf A w bits a bits (1 + 2 * w)
          (1 + 2 * w + A.span bits) (n + 1)
        = Gate.seq
            (grayWindowedMulOf A w bits a bits (1 + 2 * w)
              (1 + 2 * w + A.span bits) n)
            (grayWindowStepOf A w bits a bits (1 + 2 * w)
              (1 + 2 * w + A.span bits) n) := by
      unfold grayWindowedMulOf
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq, Finset.sum_range_succ]
    exact grayStepInv_step A w bits a numWin y hw n (by omega) _ _ (ih (by omega))

/-- **HEADLINE — Gray-code windowed-multiplier VALUE theorem.**
    For ANY adder `A` (Cuccaro, Gidney, …), the Gray-code windowed multiplier
    `grayWindowedMulCircuitOf A w bits a numWin`, run on the encoded input
    `mulInputOf A w bits numWin y` (ctrl set, `y` in the y-register,
    everything else clean), leaves `(a·y) mod 2^bits` in the accumulator —
    provided `0 < w`, `y < 2^(w·numWin)`, and the adder's ancilla block starts
    clean.  Same statement as the faithful `windowedMulCircuitOf_correct`. -/
theorem grayWindowedMulCircuitOf_correct (A : Adder) (w bits a numWin y : Nat)
    (hw : 0 < w) (hy : y < 2 ^ (w * numWin))
    (hclean : A.ancClean (mulInputOf A w bits numWin y) bits (1 + 2 * w)) :
    decodeAccOf A (Gate.applyNat (grayWindowedMulCircuitOf A w bits a numWin)
        (mulInputOf A w bits numWin y)) (1 + 2 * w) bits
      = (a * y) % 2 ^ bits := by
  have hfold := (grayStepInv_fold A w bits a numWin y hw hclean numWin
    (le_refl numWin)).2.2.2
  have hy' : y < (2 ^ w) ^ numWin := by rw [← pow_mul]; exact hy
  have hsum : (∑ k ∈ Finset.range numWin,
        a * (2 ^ w) ^ k * WindowedArith.window w y k) = a * y := by
    rw [WindowedArith.windowed_mul w numWin a y hy']
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hsum] at hfold
  show decodeReg (A.augendIdx (1 + 2 * w)) bits
      (Gate.applyNat (grayWindowedMulCircuitOf A w bits a numWin)
        (mulInputOf A w bits numWin y)) = (a * y) % 2 ^ bits
  unfold grayWindowedMulCircuitOf
  exact hfold

/-- **Cuccaro instance.**  `cuccaroAdder.ancClean` is `f (1+2w) = false` — the
    carry-in qubit sits at the block base, below the y-register, so the input
    state reads it `false`. -/
theorem grayWindowedMulCircuit_correct_cuccaro (w bits a numWin y : Nat)
    (hw : 0 < w) (hy : y < 2 ^ (w * numWin)) :
    decodeAccOf cuccaroAdder
        (Gate.applyNat (grayWindowedMulCircuitOf cuccaroAdder w bits a numWin)
          (mulInputOf cuccaroAdder w bits numWin y)) (1 + 2 * w) bits
      = (a * y) % 2 ^ bits := by
  refine grayWindowedMulCircuitOf_correct cuccaroAdder w bits a numWin y hw hy ?_
  show mulInputOf cuccaroAdder w bits numWin y (1 + 2 * w) = false
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  exact mulInputOf_low cuccaroAdder w bits numWin y _
    (by unfold ulookup_ctrl_idx; omega) (by omega)

/-- **Gidney instance.**  `gidneyAdder.ancClean` is
    `∀ i < bits, f ((1+2w) + 3i + 2) = false` — every carry qubit lies inside
    the block, below the y-register, so the input state reads it `false`. -/
theorem grayWindowedMulCircuit_correct_gidney (w bits a numWin y : Nat)
    (hw : 0 < w) (hy : y < 2 ^ (w * numWin)) :
    decodeAccOf gidneyAdder
        (Gate.applyNat (grayWindowedMulCircuitOf gidneyAdder w bits a numWin)
          (mulInputOf gidneyAdder w bits numWin y)) (1 + 2 * w) bits
      = (a * y) % 2 ^ bits := by
  refine grayWindowedMulCircuitOf_correct gidneyAdder w bits a numWin y hw hy ?_
  show ∀ i, i < bits →
    mulInputOf gidneyAdder w bits numWin y (1 + 2 * w + 3 * i + 2) = false
  intro i hi
  have hspan : gidneyAdder.span bits = 3 * bits + 2 := rfl
  exact mulInputOf_low gidneyAdder w bits numWin y _
    (by unfold ulookup_ctrl_idx; omega) (by omega)

/-! ## §4. Resource counts: the factor `w` is gone. -/

/-- **Gray-code lookup-add T-count.**  Two Gray-code table reads plus one
    adder application: `2·(14·(2^w − 1)) + tcount (A.circuit bits q_start)`
    (vs the faithful `2·(14·w·2^w) + adder`, `tcount_lookupAddAtOf`). -/
theorem tcount_grayLookupAddAtOf (A : Adder) (w W : Nat) (T : Nat → Nat) (bits q_start : Nat) :
    tcount (grayLookupAddAtOf A w W T bits q_start)
      = 2 * (14 * (2 ^ w - 1)) + tcount (A.circuit bits q_start) := by
  simp only [grayLookupAddAtOf, tcount, tcount_grayLookupReadAt]
  ring

/-- **Gray-code window-step T-count.**  The window copy/uncopy are
    Toffoli-free, so the cost is exactly the per-step lookup-add cost. -/
theorem tcount_grayWindowStepOf (A : Adder) (w W a bits q_start yBase j : Nat) :
    tcount (grayWindowStepOf A w W a bits q_start yBase j)
      = 2 * (14 * (2 ^ w - 1)) + tcount (A.circuit bits q_start) := by
  simp only [grayWindowStepOf, tcount, tcount_copyWindow, tcount_grayLookupAddAtOf]
  ring

/-- **Gray-code windowed-multiplier T-count.**  `numWin` identical steps. -/
theorem tcount_grayWindowedMulOf (A : Adder) (w W a bits q_start yBase numWin : Nat) :
    tcount (grayWindowedMulOf A w W a bits q_start yBase numWin)
      = numWin * (2 * (14 * (2 ^ w - 1)) + tcount (A.circuit bits q_start)) := by
  rw [grayWindowedMulOf, tcount_foldl_seq_const
        (fun j => grayWindowStepOf A w W a bits q_start yBase j) _
        (fun j => tcount_grayWindowStepOf A w W a bits q_start yBase j)]
  simp [tcount, List.length_range]

/-- **RESOURCE HEADLINE — generic closed-form T-count of the Gray-code
    windowed multiplier.**  Per window: two `14·(2^w − 1)`-T Gray-code reads
    plus the adder at base `1+2w`.  Versus the faithful
    `tcount_windowedMulCircuitOf` = `numWin·(28·w·2^w + adder)`: the factor
    `w` in the lookup term is gone. -/
theorem tcount_grayWindowedMulCircuitOf (A : Adder) (w bits a numWin : Nat) :
    tcount (grayWindowedMulCircuitOf A w bits a numWin)
      = numWin * (2 * (14 * (2 ^ w - 1)) + tcount (A.circuit bits (1 + 2 * w))) := by
  rw [grayWindowedMulCircuitOf, tcount_grayWindowedMulOf]

/-- **Cuccaro closed form**: `numWin · (28·(2^w − 1) + 14·bits)` T
    (vs the faithful `numWin · (28·w·2^w + 14·bits)`,
    `tcount_windowedMulCircuit`). -/
theorem tcount_grayWindowedMulCircuit_cuccaro (w bits a numWin : Nat) :
    tcount (grayWindowedMulCircuitOf cuccaroAdder w bits a numWin)
      = numWin * (28 * (2 ^ w - 1) + 14 * bits) := by
  rw [tcount_grayWindowedMulCircuitOf]
  show numWin * (2 * (14 * (2 ^ w - 1))
        + tcount (cuccaro_n_bit_adder_full bits (1 + 2 * w))) = _
  rw [tcount_cuccaro_n_bit_adder_full]
  ring

/-- **Cuccaro Toffoli count**: `numWin · (4·(2^w − 1) + 2·bits)` — versus the
    faithful `numWin · (4·w·2^w + 2·bits)` (`windowedMulCircuit_toffoli`):
    the factor `w` on the lookup term is GONE; the remaining ×2 against the
    papers' `2^w` per lookup is the measurement-uncompute leg (module
    docstring). -/
theorem grayWindowedMulCircuit_toffoli_cuccaro (w bits a numWin : Nat) :
    toffoliCount (grayWindowedMulCircuitOf cuccaroAdder w bits a numWin)
      = numWin * (4 * (2 ^ w - 1) + 2 * bits) := by
  rw [toffoliCount, tcount_grayWindowedMulCircuit_cuccaro,
      show numWin * (28 * (2 ^ w - 1) + 14 * bits)
            = numWin * (4 * (2 ^ w - 1) + 2 * bits) * 7 from by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **Audit bridge**: for any adder and any `0 < w`, the Gray-code windowed
    multiplier never costs more T than the faithful one
    (`28·(2^w − 1) ≤ 28·2^w ≤ 28·w·2^w` per window, adder term identical). -/
theorem tcount_grayWindowedMulCircuitOf_le_faithful
    (A : Adder) (w bits a numWin : Nat) (hw : 0 < w) :
    tcount (grayWindowedMulCircuitOf A w bits a numWin)
      ≤ tcount (windowedMulCircuitOf A w bits a numWin) := by
  rw [tcount_grayWindowedMulCircuitOf, tcount_windowedMulCircuitOf]
  refine Nat.mul_le_mul_left numWin (Nat.add_le_add_right ?_ _)
  calc 2 * (14 * (2 ^ w - 1)) = 28 * (2 ^ w - 1) := by ring
    _ ≤ 28 * 2 ^ w := Nat.mul_le_mul_left 28 (Nat.sub_le _ _)
    _ ≤ 28 * (w * 2 ^ w) := Nat.mul_le_mul_left 28 (Nat.le_mul_of_pos_left _ hw)
    _ = 28 * w * 2 ^ w := by ring

end FormalRV.Shor.WindowedCircuit
