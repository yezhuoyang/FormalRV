/-
  FormalRV.Shor.WindowedCircuit.WindowedCircuitCorrect — the adder-generic
  windowed-multiplier VALUE theorem.

  HEADLINE (`windowedMulCircuitOf_correct`): for ANY adder `A` satisfying the
  layout-parametric `Adder` interface, the full windowed multiplier
  `windowedMulCircuitOf A w bits a numWin`, run on the input state
  `mulInputOf A w bits numWin y` (ctrl set, integer `y` encoded in the
  y-register, everything else clean), leaves

      (a · y) mod 2^bits

  in the accumulator (`decodeAccOf A · (1+2w) bits`), provided `0 < w`,
  `y < 2^(w·numWin)` and the adder's ancilla block starts clean.

  Proof: invariant induction over the window-steps.  After `j` steps the state
  `g` satisfies the four-part invariant `StepInv`:
    (F)  frame: `g` agrees with the input off the adder block;
    (D)  the addend register is clean (all `false`);
    (C)  the adder's ancilla block is clean (`A.ancClean`);
    (V)  the augend register decodes to `(Σ_{k<j} a·(2^w)^k·windowₖ(y)) mod 2^bits`.
  Each window-step is tracked through its five sub-gates
  (copy · read · add · unread · uncopy) using the proven selection/frame lemmas
  of `WindowedLookupSelect` / `WindowedCopySemantics` and the `Adder` contract.
  The final bridge to `a·y` is `WindowedArith.windowed_mul`.

  Corollaries: the Cuccaro and Gidney instances with the `ancClean`
  precondition discharged concretely.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Windowed.WindowedLookupSelect
import FormalRV.Arithmetic.Windowed.WindowedCopySemantics
import FormalRV.Arithmetic.Adder.Cuccaro
import FormalRV.Arithmetic.Adder.Gidney

namespace FormalRV.Shor.WindowedCircuit

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §1. The generic input state. -/

/-- The input store for the generic windowed multiplier over adder `A`:
    control qubit set, integer `y` encoded in the y-register at
    `yBase = 1 + 2w + A.span bits`, everything else clean.
    (Generic version of the Cuccaro-shaped `mulInput`.) -/
def mulInputOf (A : Adder) (w bits numWin y : Nat) : Nat → Bool := fun p =>
  if p = ulookup_ctrl_idx then true
  else encodeReg (1 + 2 * w + A.span bits) (numWin * w) y p

/-- `mulInputOf` reads `true` at the control qubit. -/
theorem mulInputOf_ctrl (A : Adder) (w bits numWin y : Nat) :
    mulInputOf A w bits numWin y ulookup_ctrl_idx = true := by
  unfold mulInputOf
  rw [if_pos rfl]

/-- `mulInputOf` reads `false` at every non-control position below the
    y-register (`p < yBase = 1 + 2w + A.span bits`). -/
theorem mulInputOf_low (A : Adder) (w bits numWin y p : Nat)
    (hp0 : p ≠ ulookup_ctrl_idx) (hpy : p < 1 + 2 * w + A.span bits) :
    mulInputOf A w bits numWin y p = false := by
  unfold mulInputOf encodeReg
  rw [if_neg hp0, if_neg (by omega)]

/-- Off the control qubit, `mulInputOf` is the `encodeReg` encoding of `y`. -/
theorem mulInputOf_eq_encodeReg (A : Adder) (w bits numWin y p : Nat)
    (hp : p ≠ ulookup_ctrl_idx) :
    mulInputOf A w bits numWin y p
      = encodeReg (1 + 2 * w + A.span bits) (numWin * w) y p := by
  unfold mulInputOf
  rw [if_neg hp]

/-! ## §2. Decoding a register holding the bits of `M`: `decodeReg = M % 2^n`. -/

/-- **Register decode of a bit-pattern.**  If the register at `idx` holds the
    binary digits of `M` (bit `i` at `idx i`), it decodes to `M % 2^n`. -/
theorem decodeReg_eq_mod_of_testBit (idx : Nat → Nat) (n M : Nat) (f : Nat → Bool)
    (h : ∀ i, i < n → f (idx i) = M.testBit i) :
    decodeReg idx n f = M % 2 ^ n := by
  induction n with
  | zero => simp [decodeReg, Nat.mod_one]
  | succ k ih =>
    have hk := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    unfold decodeReg at hk ⊢
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [hk, h k (Nat.lt_succ_self k)]
    -- ⊢ M % 2 ^ k + (if M.testBit k then 2 ^ k else 0) = M % 2 ^ (k + 1)
    have hsplit : M % 2 ^ (k + 1) = M % 2 ^ k + 2 ^ k * (M / 2 ^ k % 2) := by
      rw [pow_succ, Nat.mod_mul]
    have hbit : M.testBit k = decide (M / 2 ^ k % 2 = 1) :=
      Nat.testBit_eq_decide_div_mod_eq
    have hr : M / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases hb : M.testBit k
    · rw [if_pos hb]
      rw [hb] at hbit
      have h1 : M / 2 ^ k % 2 = 1 := of_decide_eq_true hbit.symm
      rw [h1, Nat.mul_one] at hsplit
      omega
    · rw [if_neg hb]
      have hbf : M.testBit k = false := by
        cases hM : M.testBit k
        · rfl
        · exact absurd hM hb
      rw [hbf] at hbit
      have h1 : ¬ (M / 2 ^ k % 2 = 1) := of_decide_eq_false hbit.symm
      have h0 : M / 2 ^ k % 2 = 0 := by omega
      rw [h0, Nat.mul_zero, Nat.add_zero] at hsplit
      omega

/-- A register reading all-`false` decodes to `0`. -/
theorem decodeReg_eq_zero (idx : Nat → Nat) (n : Nat) (f : Nat → Bool)
    (h : ∀ i, i < n → f (idx i) = false) :
    decodeReg idx n f = 0 := by
  rw [decodeReg_eq_mod_of_testBit idx n 0 f
        (fun i hi => by rw [h i hi, Nat.zero_testBit]),
      Nat.zero_mod]

/-! ## §3. The window-step invariant. -/

/-- **The window-step invariant.**  After some number of window-steps starting
    from `mulInputOf A w bits numWin y`, the state `g` satisfies:
    * (F) frame: `g` agrees with the input off the adder block
      `[1+2w, 1+2w + A.span bits)` — in particular ctrl is set, the lookup's
      address/AND registers are clean, and the y-register still encodes `y`;
    * (D) the addend register is clean;
    * (C) the adder's ancilla block is clean;
    * (V) the augend register decodes to `s % 2^bits` (the partial sum so far). -/
def StepInv (A : Adder) (w bits numWin y s : Nat) (g : Nat → Bool) : Prop :=
  (∀ p, ¬ inBlock (1 + 2 * w) (A.span bits) p →
      g p = mulInputOf A w bits numWin y p)
  ∧ (∀ i, i < bits → g (A.addendIdx (1 + 2 * w) i) = false)
  ∧ A.ancClean g bits (1 + 2 * w)
  ∧ decodeReg (A.augendIdx (1 + 2 * w)) bits g = s % 2 ^ bits

/-- **Invariant initialization.**  The input state satisfies the invariant with
    partial sum `0`. -/
theorem stepInv_init (A : Adder) (w bits numWin y : Nat)
    (hclean : A.ancClean (mulInputOf A w bits numWin y) bits (1 + 2 * w)) :
    StepInv A w bits numWin y 0 (mulInputOf A w bits numWin y) := by
  refine ⟨fun p _ => rfl, ?_, hclean, ?_⟩
  · -- (D): the addend register reads false (in-block, below the y-register).
    intro i hi
    have hblk := A.addendIdx_inBlock bits (1 + 2 * w) i hi
    unfold inBlock at hblk
    exact mulInputOf_low A w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega) (by omega)
  · -- (V): the augend register reads false, so it decodes to 0 = 0 % 2^bits.
    rw [decodeReg_eq_zero _ bits _ (fun i hi => by
      have hblk := A.augendIdx_inBlock bits (1 + 2 * w) i hi
      unfold inBlock at hblk
      exact mulInputOf_low A w bits numWin y _
        (by unfold ulookup_ctrl_idx; omega) (by omega)),
      Nat.zero_mod]

/-! ## §4. The window step preserves the invariant.

One step `windowStepOf` is five sub-gates: copy the window into the address
register, QROM-read the table row into the addend, run the adder, QROM-read
again (clearing the addend), uncopy the window.  We track the state through
`g₁ … g₅` and re-establish all four invariant conjuncts. -/

theorem stepInv_step (A : Adder) (w bits a numWin y : Nat) (hw : 0 < w)
    (j : Nat) (hj : j < numWin) (s : Nat) (g : Nat → Bool)
    (hg : StepInv A w bits numWin y s g) :
    StepInv A w bits numWin y (s + a * (2 ^ w) ^ j * WindowedArith.window w y j)
      (Gate.applyNat
        (windowStepOf A w bits a bits (1 + 2 * w) (1 + 2 * w + A.span bits) j)
        g) := by
  obtain ⟨hF, hD, hC, hV⟩ := hg
  -- Expose the five-fold composition.
  simp only [windowStepOf, lookupAddAtOf, Gate.applyNat_seq]
  set g1 : Nat → Bool :=
    Gate.applyNat (copyWindow w (1 + 2 * w + A.span bits) j) g with hg1def
  set g2 : Nat → Bool :=
    Gate.applyNat (lookupReadAt w (A.addendIdx (1 + 2 * w)) bits
      (fun v => a * (2 ^ w) ^ j * v)) g1 with hg2def
  set g3 : Nat → Bool := Gate.applyNat (A.circuit bits (1 + 2 * w)) g2 with hg3def
  set g4 : Nat → Bool :=
    Gate.applyNat (lookupReadAt w (A.addendIdx (1 + 2 * w)) bits
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
  -- ── g₂ = QROM read: the table row lands in the addend register ────────
  have hvlt : WindowedArith.window w y j < 2 ^ w := WindowedArith.window_lt w y j
  have hg2_addend : ∀ i, i < bits →
      g2 (A.addendIdx (1 + 2 * w) i)
        = (a * (2 ^ w) ^ j * WindowedArith.window w y j).testBit i := by
    intro i hi
    rw [hg2def,
        lookupReadAt_selects_word w bits (fun v => a * (2 ^ w) ^ j * v)
          (A.addendIdx (1 + 2 * w)) g1 (WindowedArith.window w y j)
          hw hvlt hg1_ctrl hg1_addr hg1_and hpos_high hpos_inj i hi,
        hg1_addend i hi, Bool.false_xor]
  have hg2_frame : ∀ p, (∀ k, k < bits → p ≠ A.addendIdx (1 + 2 * w) k) →
      g2 p = g1 p :=
    fun p hp => lookupReadAt_frame w bits (fun v => a * (2 ^ w) ^ j * v)
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
  -- ── g₄ = QROM read again: the addend register is cleared ──────────────
  have hg4_addend : ∀ i, i < bits → g4 (A.addendIdx (1 + 2 * w) i) = false := by
    intro i hi
    rw [hg4def,
        lookupReadAt_selects_word w bits (fun v => a * (2 ^ w) ^ j * v)
          (A.addendIdx (1 + 2 * w)) g3 (WindowedArith.window w y j)
          hw hvlt hg3_ctrl hg3_addr hg3_and hpos_high hpos_inj i hi,
        hg3_addend i hi, Bool.xor_self]
  have hg4_frame : ∀ p, (∀ k, k < bits → p ≠ A.addendIdx (1 + 2 * w) k) →
      g4 p = g3 p :=
    fun p hp => lookupReadAt_frame w bits (fun v => a * (2 ^ w) ^ j * v)
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

/-! ## §5. The fold: the invariant holds after every prefix of window-steps. -/

/-- Running the first `n` window-steps (`n ≤ numWin`) of the windowed
    multiplier establishes the invariant with partial sum
    `Σ_{k<n} a·(2^w)^k·windowₖ(y)`. -/
theorem stepInv_fold (A : Adder) (w bits a numWin y : Nat) (hw : 0 < w)
    (hclean : A.ancClean (mulInputOf A w bits numWin y) bits (1 + 2 * w)) :
    ∀ n, n ≤ numWin →
      StepInv A w bits numWin y
        (∑ k ∈ Finset.range n, a * (2 ^ w) ^ k * WindowedArith.window w y k)
        (Gate.applyNat
          (windowedMulOf A w bits a bits (1 + 2 * w) (1 + 2 * w + A.span bits) n)
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
    have hsplit : windowedMulOf A w bits a bits (1 + 2 * w)
          (1 + 2 * w + A.span bits) (n + 1)
        = Gate.seq
            (windowedMulOf A w bits a bits (1 + 2 * w)
              (1 + 2 * w + A.span bits) n)
            (windowStepOf A w bits a bits (1 + 2 * w)
              (1 + 2 * w + A.span bits) n) := by
      unfold windowedMulOf
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq, Finset.sum_range_succ]
    exact stepInv_step A w bits a numWin y hw n (by omega) _ _ (ih (by omega))

/-! ## §6. The headline: adder-generic windowed-multiplier value correctness. -/

/-- **HEADLINE — adder-generic windowed-multiplier VALUE theorem.**
    For ANY adder `A` (Cuccaro, Gidney, …), the full windowed multiplier
    `windowedMulCircuitOf A w bits a numWin`, run on the encoded input
    `mulInputOf A w bits numWin y` (ctrl set, `y` in the y-register,
    everything else clean), leaves `(a·y) mod 2^bits` in the accumulator —
    provided `0 < w`, `y < 2^(w·numWin)`, and the adder's ancilla block
    starts clean. -/
theorem windowedMulCircuitOf_correct (A : Adder) (w bits a numWin y : Nat)
    (hw : 0 < w) (hy : y < 2 ^ (w * numWin))
    (hclean : A.ancClean (mulInputOf A w bits numWin y) bits (1 + 2 * w)) :
    decodeAccOf A (Gate.applyNat (windowedMulCircuitOf A w bits a numWin)
        (mulInputOf A w bits numWin y)) (1 + 2 * w) bits
      = (a * y) % 2 ^ bits := by
  have hfold := (stepInv_fold A w bits a numWin y hw hclean numWin
    (le_refl numWin)).2.2.2
  have hy' : y < (2 ^ w) ^ numWin := by rw [← pow_mul]; exact hy
  have hsum : (∑ k ∈ Finset.range numWin,
        a * (2 ^ w) ^ k * WindowedArith.window w y k) = a * y := by
    rw [WindowedArith.windowed_mul w numWin a y hy']
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hsum] at hfold
  show decodeReg (A.augendIdx (1 + 2 * w)) bits
      (Gate.applyNat (windowedMulCircuitOf A w bits a numWin)
        (mulInputOf A w bits numWin y)) = (a * y) % 2 ^ bits
  unfold windowedMulCircuitOf
  exact hfold

/-! ## §7. Instance corollaries: the `ancClean` precondition holds concretely. -/

/-- **Cuccaro instance.**  `cuccaroAdder.ancClean` is `f (1+2w) = false` — the
    carry-in qubit sits at the block base, below the y-register, so the input
    state reads it `false`. -/
theorem windowedMulCircuit_correct_cuccaro (w bits a numWin y : Nat)
    (hw : 0 < w) (hy : y < 2 ^ (w * numWin)) :
    decodeAccOf cuccaroAdder
        (Gate.applyNat (windowedMulCircuitOf cuccaroAdder w bits a numWin)
          (mulInputOf cuccaroAdder w bits numWin y)) (1 + 2 * w) bits
      = (a * y) % 2 ^ bits := by
  refine windowedMulCircuitOf_correct cuccaroAdder w bits a numWin y hw hy ?_
  show mulInputOf cuccaroAdder w bits numWin y (1 + 2 * w) = false
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  exact mulInputOf_low cuccaroAdder w bits numWin y _
    (by unfold ulookup_ctrl_idx; omega) (by omega)

/-- **Gidney instance.**  `gidneyAdder.ancClean` is
    `∀ i < bits, f ((1+2w) + 3i + 2) = false` — every carry qubit lies inside
    the block, below the y-register, so the input state reads it `false`. -/
theorem windowedMulCircuit_correct_gidney (w bits a numWin y : Nat)
    (hw : 0 < w) (hy : y < 2 ^ (w * numWin)) :
    decodeAccOf gidneyAdder
        (Gate.applyNat (windowedMulCircuitOf gidneyAdder w bits a numWin)
          (mulInputOf gidneyAdder w bits numWin y)) (1 + 2 * w) bits
      = (a * y) % 2 ^ bits := by
  refine windowedMulCircuitOf_correct gidneyAdder w bits a numWin y hw hy ?_
  show ∀ i, i < bits →
    mulInputOf gidneyAdder w bits numWin y (1 + 2 * w + 3 * i + 2) = false
  intro i hi
  have hspan : gidneyAdder.span bits = 3 * bits + 2 := rfl
  exact mulInputOf_low gidneyAdder w bits numWin y _
    (by unfold ulookup_ctrl_idx; omega) (by omega)

end FormalRV.Shor.WindowedCircuit
