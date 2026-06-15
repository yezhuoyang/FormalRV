/-
  FormalRV.Arithmetic.Windowed.WindowedExpInPlaceQ — the QUANTUM-SELECTED
  in-place windowed exponentiation: per-window in-place multiplication by the
  exponent-window-SELECTED constant `g_k^{e_k}` (windows read from a quantum
  exponent REGISTER), discharging the named next-stage obligation of
  `WindowedInPlace`.

  Composes the two proven engines:
  * the OUT-OF-PLACE quantum-selected pass (`WindowedExpStep`):
    `expWindowPassOf` with the two-level table `expTable g_k wM` reads the
    exponent window `e_k` from the exponent register (concatenated address =
    exp-window ++ mul-window) and multiply-accumulates by `g_k^{e_k}`;
  * the in-place composition pattern (`WindowedInPlace`):
    pass(table) ; acc↔y swap ; pass(inverse table).

  Contents:
  * **§1 — the generic-table step.**  `expStepInvT_step`: the exponent-window
    step advances `ExpStepInv` from ANY partial sum, for ANY table whose row
    at the touched concatenated address evaluates to `c·(2^wM)^j·windowⱼ(y)` —
    the common engine behind the forward table `expTable g_k wM` AND the
    inverse table `expTableInv g_kinv wM bits` (whose row constant
    `2^bits − g_kinv^{e_k} mod 2^bits` is NOT of the form `h^{e_k}`, so the
    step must be generic in the table; the proof is `expStepInv_step`'s,
    with the two `expTable_row` evaluations abstracted into `hrow`).
  * **§2–§4 — the generalized pass at any `acc₀`.**  `expStepInvT_fold_acc`,
    `expStepInvT_full_pass`, and the Stage-1 headline
    `expWindowPassOf_correct_acc` (mirror of `windowedMulCircuitOf_correct_acc`):
    the quantum-selected pass run from an invariant state with partial sum
    `acc₀` leaves `(acc₀ + g_k^{e_k}·y) mod 2^bits` in the accumulator.
  * **§5 — the inverse table.**  `expTableInv` and the selected-exponent
    inverse: `g_k·g_kinv ≡ 1 (mod 2^bits)` lifts to every selected power
    (`pow_mod_inv_one`, by `mul_pow`), so the pass-2 constant
    `2^bits − g_kinv^{e_k} mod 2^bits` cancels via `mod_inv_cancel_identity`
    at the SELECTED exponent.
  * **§6–§7 — the in-place quantum-selected pass.**  `ExpReady` (the
    `MulReady` analogue INCLUDING the exponent register's content, through
    the off-block frame) and the Stage-3 headline `expWindowInPlace_correct`:
    `pass(expTable g_k) ; acc↔y swap ; pass(expTableInv g_kinv)` maps the
    `ExpReady` state with y-value `y` and exponent-register value `e` to the
    `ExpReady` state with `y ← g_k^{windowₖ(e)}·y mod 2^bits` and the exponent
    register PRESERVED.  This is the per-basis-state `e` statement — exactly
    what lifts to superposed exponents at the unitary level via the
    basis-action bridge, because the circuit is one FIXED gate (the tables,
    not the gate, depend on the classical constants; nothing depends on `e`).
  * **§8 — the chain.**  `windowedExpInPlaceQ`, the `numExpWin`-fold chain of
    in-place quantum-selected passes with constants `g^((2^wE)^k)` (inverses
    `ginv^((2^wE)^k)`), and its headline `windowedExpInPlaceQ_correct`:
    `y ← g^e·y mod 2^bits` for the QUANTUM (basis-state) exponent `e`,
    exponent register preserved — the product collapses by the windowed
    digit expansion (`Finset.prod_pow_eq_pow_sum` + `windowed_mul`).
  * **§9 — Cuccaro instance** (`ancClean` discharged concretely).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Windowed.WindowedExpStep
import FormalRV.Arithmetic.Windowed.WindowedInPlace

namespace FormalRV.Shor.WindowedCircuit

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §1. The generic-table exponent-window step.

`expStepInv_step` (WindowedExpStep §6) is start-agnostic in the partial sum
but SPECIFIC to the forward table `expTable g_k wM`.  The in-place clear pass
needs the same step for the INVERSE table, whose selected constant
`2^bits − g_kinv^{e_k} mod 2^bits` cannot be realized by any `expTable h wM`
(at `e_k = 0` the forward row constant is forced to `h^0 = 1`).  So we replay
the step proof once, generic in the table `T`: the ONLY facts consumed about
`T` are its two row evaluations at the touched concatenated address, both
abstracted into the single hypothesis `hrow`. -/

/-- **The generic-table exponent-window step.**  One `expWindowStepOf A wE wM T`
    step at mul-window `j`, exp-window `k`, advances the invariant from ANY
    partial sum `s` to `s + c·(2^wM)^j·windowⱼ(y)`, provided table `T`'s row
    at the touched concatenated address `windowⱼ(y) + 2^wM·windowₖ(e)`
    evaluates to `c·(2^wM)^j·windowⱼ(y)` (hypothesis `hrow`).
    Proof: `expStepInv_step`'s, verbatim, with the two `expTable_row`
    evaluations replaced by `hrow`. -/
theorem expStepInvT_step (A : Adder) (wE wM bits c numWin numExpWin y e k : Nat)
    (T : Nat → Nat) (hwM : 0 < wM) (hk : k < numExpWin)
    (j : Nat) (hj : j < numWin)
    (hrow : T (WindowedArith.window wM y j + 2 ^ wM * WindowedArith.window wE e k)
      = c * (2 ^ wM) ^ j * WindowedArith.window wM y j)
    (s : Nat) (g : Nat → Bool)
    (hg : ExpStepInv A wE wM bits numWin numExpWin y e s g) :
    ExpStepInv A wE wM bits numWin numExpWin y e
      (s + c * (2 ^ wM) ^ j * WindowedArith.window wM y j)
      (Gate.applyNat
        (expWindowStepOf A wE wM T bits (1 + 2 * (wE + wM))
          (1 + 2 * (wE + wM) + A.span bits)
          (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k j)
        g) := by
  obtain ⟨hF, hD, hC, hV⟩ := hg
  -- Expose the seven-fold composition.
  simp only [expWindowStepOf, lookupAddAtOf, Gate.applyNat_seq]
  set g1 : Nat → Bool :=
    Gate.applyNat (copyWindowAt wM (1 + 2 * (wE + wM) + A.span bits) j 0) g
    with hg1def
  set g2 : Nat → Bool :=
    Gate.applyNat (copyWindowAt wE
      (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k wM) g1 with hg2def
  set g3 : Nat → Bool :=
    Gate.applyNat (lookupReadAt (wE + wM) (A.addendIdx (1 + 2 * (wE + wM))) bits
      T) g2 with hg3def
  set g4 : Nat → Bool :=
    Gate.applyNat (A.circuit bits (1 + 2 * (wE + wM))) g3 with hg4def
  set g5 : Nat → Bool :=
    Gate.applyNat (lookupReadAt (wE + wM) (A.addendIdx (1 + 2 * (wE + wM))) bits
      T) g4 with hg5def
  set g6 : Nat → Bool :=
    Gate.applyNat (copyWindowAt wE
      (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k wM) g5 with hg6def
  set g7 : Nat → Bool :=
    Gate.applyNat (copyWindowAt wM (1 + 2 * (wE + wM) + A.span bits) j 0) g6
    with hg7def
  -- ── Standing zone facts ────────────────────────────────────────────────
  -- Copy controls (y-/e-wires) are never targeted address wires.
  have hctrlM : ∀ i k', i < wM → k' < wM →
      (1 + 2 * (wE + wM) + A.span bits) + j * wM + i
        ≠ ulookup_address_idx (0 + k') :=
    copyWindowAt_ctrl_ne wM (1 + 2 * (wE + wM) + A.span bits) j 0 (by omega)
  have hctrlE : ∀ i k', i < wE → k' < wE →
      (1 + 2 * (wE + wM) + A.span bits + numWin * wM) + k * wE + i
        ≠ ulookup_address_idx (wM + k') :=
    copyWindowAt_ctrl_ne wE (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k wM
      (by omega)
  -- The addend positions sit above the lookup zone and are injective.
  have hpos_high : ∀ l, l < bits →
      2 * (wE + wM) < A.addendIdx (1 + 2 * (wE + wM)) l := by
    intro l hl
    have hblk := A.addendIdx_inBlock bits (1 + 2 * (wE + wM)) l hl
    unfold inBlock at hblk
    omega
  have hpos_inj : ∀ l m, l < bits → m < bits →
      A.addendIdx (1 + 2 * (wE + wM)) l = A.addendIdx (1 + 2 * (wE + wM)) m →
      l = m :=
    fun l m _ _ h => A.addendIdx_inj (1 + 2 * (wE + wM)) l m h
  -- The ctrl / address / AND wires are never addend positions.
  have hctrl_ne_pos : ∀ l, l < bits →
      ulookup_ctrl_idx ≠ A.addendIdx (1 + 2 * (wE + wM)) l := by
    intro l hl
    have := hpos_high l hl
    unfold ulookup_ctrl_idx
    omega
  have haddr_ne_pos : ∀ i, i < wE + wM → ∀ l, l < bits →
      ulookup_address_idx i ≠ A.addendIdx (1 + 2 * (wE + wM)) l := by
    intro i hi l hl
    have := hpos_high l hl
    unfold ulookup_address_idx
    omega
  have hand_ne_pos : ∀ i, i < wE + wM → ∀ l, l < bits →
      ulookup_and_idx i ≠ A.addendIdx (1 + 2 * (wE + wM)) l := by
    intro i hi l hl
    have := hpos_high l hl
    unfold ulookup_and_idx
    omega
  -- The lookup zone lies below the block; the y-/e-registers lie above it.
  have hctrl_out : ¬ inBlock (1 + 2 * (wE + wM)) (A.span bits) ulookup_ctrl_idx := by
    unfold inBlock ulookup_ctrl_idx
    omega
  have haddr_out : ∀ i, i < wE + wM →
      ¬ inBlock (1 + 2 * (wE + wM)) (A.span bits) (ulookup_address_idx i) := by
    intro i hi
    unfold inBlock ulookup_address_idx
    omega
  have hand_out : ∀ i, i < wE + wM →
      ¬ inBlock (1 + 2 * (wE + wM)) (A.span bits) (ulookup_and_idx i) := by
    intro i hi
    unfold inBlock ulookup_and_idx
    omega
  have hy_out : ∀ i, i < wM →
      ¬ inBlock (1 + 2 * (wE + wM)) (A.span bits)
        ((1 + 2 * (wE + wM) + A.span bits) + j * wM + i) := by
    intro i hi
    unfold inBlock
    omega
  have he_out : ∀ i, i < wE →
      ¬ inBlock (1 + 2 * (wE + wM)) (A.span bits)
        ((1 + 2 * (wE + wM) + A.span bits + numWin * wM) + k * wE + i) := by
    intro i hi
    unfold inBlock
    omega
  -- The y-/e-wires are never addend positions (the addend is in-block).
  have hy_ne_pos : ∀ i, i < wM → ∀ l, l < bits →
      (1 + 2 * (wE + wM) + A.span bits) + j * wM + i
        ≠ A.addendIdx (1 + 2 * (wE + wM)) l := by
    intro i hi l hl
    have hblk := A.addendIdx_inBlock bits (1 + 2 * (wE + wM)) l hl
    unfold inBlock at hblk
    omega
  have he_ne_pos : ∀ i, i < wE → ∀ l, l < bits →
      (1 + 2 * (wE + wM) + A.span bits + numWin * wM) + k * wE + i
        ≠ A.addendIdx (1 + 2 * (wE + wM)) l := by
    intro i hi l hl
    have hblk := A.addendIdx_inBlock bits (1 + 2 * (wE + wM)) l hl
    unfold inBlock at hblk
    omega
  -- The augend/addend positions are never address wires.
  have haug_ne_addr : ∀ l, l < bits → ∀ i, i < wE + wM →
      A.augendIdx (1 + 2 * (wE + wM)) l ≠ ulookup_address_idx i := by
    intro l hl i hi
    have hblk := A.augendIdx_inBlock bits (1 + 2 * (wE + wM)) l hl
    unfold inBlock at hblk
    unfold ulookup_address_idx
    omega
  have hadd_ne_addr : ∀ l, l < bits → ∀ i, i < wE + wM →
      A.addendIdx (1 + 2 * (wE + wM)) l ≠ ulookup_address_idx i := by
    intro l hl i hi
    have := hpos_high l hl
    unfold ulookup_address_idx
    omega
  -- ── g (pre-step) register values, from the frame conjunct ─────────────
  have hg_addr_clean : ∀ i, i < wE + wM → g (ulookup_address_idx i) = false := by
    intro i hi
    rw [hF _ (haddr_out i hi)]
    exact expMulInputOf_low A wE wM bits numWin numExpWin y e _
      (by unfold ulookup_ctrl_idx ulookup_address_idx; omega)
      (by unfold ulookup_address_idx; omega)
  have hg_y : ∀ i, i < wM →
      g ((1 + 2 * (wE + wM) + A.span bits) + j * wM + i)
        = encodeReg (1 + 2 * (wE + wM) + A.span bits) (numWin * wM) y
            ((1 + 2 * (wE + wM) + A.span bits) + j * wM + i) := by
    intro i hi
    rw [hF _ (hy_out i hi)]
    refine expMulInputOf_y A wE wM bits numWin numExpWin y e _
      (by unfold ulookup_ctrl_idx; omega) ?_
    have h3 : j * wM + i < (j + 1) * wM := by
      have h4 : (j + 1) * wM = j * wM + wM := by ring
      omega
    have h2 : (j + 1) * wM ≤ numWin * wM := Nat.mul_le_mul_right wM (by omega)
    omega
  have hg_e : ∀ i, i < wE →
      g ((1 + 2 * (wE + wM) + A.span bits + numWin * wM) + k * wE + i)
        = encodeReg (1 + 2 * (wE + wM) + A.span bits + numWin * wM)
            (numExpWin * wE) e
            ((1 + 2 * (wE + wM) + A.span bits + numWin * wM) + k * wE + i) := by
    intro i hi
    rw [hF _ (he_out i hi)]
    exact expMulInputOf_e A wE wM bits numWin numExpWin y e _ (by omega)
  -- ── g₁ = copy mul-window: address[0,wM) receives the mul-window digit ──
  have hg1_frame : ∀ p, (∀ i, i < wM → p ≠ ulookup_address_idx i) → g1 p = g p := by
    intro p hp
    rw [hg1def]
    exact copyWindowAt_frame wM (1 + 2 * (wE + wM) + A.span bits) j 0 g p
      (fun i hi => by rw [Nat.zero_add]; exact hp i hi)
  have hg1_addr_lo : ∀ i, i < wM →
      g1 (ulookup_address_idx i) = (WindowedArith.window wM y j).testBit i := by
    intro i hi
    have h := copyWindowAt_copies wM (1 + 2 * (wE + wM) + A.span bits) j 0 g hctrlM
      (fun i' hi' => by rw [Nat.zero_add]; exact hg_addr_clean i' (by omega)) i hi
    rw [Nat.zero_add] at h
    rw [hg1def, h, hg_y i hi,
        encodeReg_window_bit (1 + 2 * (wE + wM) + A.span bits) wM numWin y j i hi hj]
  have hg1_addr_hi : ∀ i, i < wE →
      g1 (ulookup_address_idx (wM + i)) = false := by
    intro i hi
    rw [hg1_frame _ (fun i' hi' => by unfold ulookup_address_idx; omega)]
    exact hg_addr_clean (wM + i) (by omega)
  have hg1_ctrl : g1 ulookup_ctrl_idx = true := by
    rw [hg1_frame _ (fun i hi => by unfold ulookup_ctrl_idx ulookup_address_idx; omega),
        hF _ hctrl_out]
    exact expMulInputOf_ctrl A wE wM bits numWin numExpWin y e
  have hg1_and : ∀ i, i < wE + wM → g1 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg1_frame _ (fun i' hi' => by unfold ulookup_and_idx ulookup_address_idx; omega),
        hF _ (hand_out i hi)]
    exact expMulInputOf_low A wE wM bits numWin numExpWin y e _
      (by unfold ulookup_ctrl_idx ulookup_and_idx; omega)
      (by unfold ulookup_and_idx; omega)
  have hg1_addend : ∀ l, l < bits →
      g1 (A.addendIdx (1 + 2 * (wE + wM)) l) = false := by
    intro l hl
    rw [hg1_frame _ (fun i hi => hadd_ne_addr l hl i (by omega))]
    exact hD l hl
  have hg1_aug : ∀ l, l < bits →
      g1 (A.augendIdx (1 + 2 * (wE + wM)) l)
        = g (A.augendIdx (1 + 2 * (wE + wM)) l) :=
    fun l hl => hg1_frame _ (fun i hi => haug_ne_addr l hl i (by omega))
  have hg1_e : ∀ i, i < wE →
      g1 ((1 + 2 * (wE + wM) + A.span bits + numWin * wM) + k * wE + i)
        = g ((1 + 2 * (wE + wM) + A.span bits + numWin * wM) + k * wE + i) :=
    fun i hi => hg1_frame _ (fun i' hi' => by unfold ulookup_address_idx; omega)
  -- ── g₂ = copy exp-window: address[wM,wM+wE) receives the exp-window digit ──
  have hg2_frame : ∀ p, (∀ i, i < wE → p ≠ ulookup_address_idx (wM + i)) →
      g2 p = g1 p := by
    intro p hp
    rw [hg2def]
    exact copyWindowAt_frame wE (1 + 2 * (wE + wM) + A.span bits + numWin * wM)
      k wM g1 p hp
  have hg2_addr_hi : ∀ i, i < wE →
      g2 (ulookup_address_idx (wM + i))
        = (WindowedArith.window wE e k).testBit i := by
    intro i hi
    rw [hg2def,
        copyWindowAt_copies wE (1 + 2 * (wE + wM) + A.span bits + numWin * wM)
          k wM g1 hctrlE (fun i' hi' => hg1_addr_hi i' hi') i hi,
        hg1_e i hi, hg_e i hi,
        encodeReg_window_bit (1 + 2 * (wE + wM) + A.span bits + numWin * wM)
          wE numExpWin e k i hi hk]
  have hg2_addr_lo : ∀ i, i < wM →
      g2 (ulookup_address_idx i) = (WindowedArith.window wM y j).testBit i := by
    intro i hi
    rw [hg2_frame _ (fun i' hi' => by unfold ulookup_address_idx; omega)]
    exact hg1_addr_lo i hi
  -- The widened address register now holds the CONCATENATED value.
  have hg2_addr : ∀ i, i < wE + wM →
      g2 (ulookup_address_idx i)
        = (WindowedArith.window wM y j
            + 2 ^ wM * WindowedArith.window wE e k).testBit i := by
    intro i hi
    rw [concat_testBit wM (WindowedArith.window wM y j)
          (WindowedArith.window wE e k) i (WindowedArith.window_lt wM y j)]
    by_cases hilo : i < wM
    · rw [if_pos hilo]
      exact hg2_addr_lo i hilo
    · rw [if_neg hilo]
      have h := hg2_addr_hi (i - wM) (by omega)
      rw [show wM + (i - wM) = i by omega] at h
      exact h
  have hg2_ctrl : g2 ulookup_ctrl_idx = true := by
    rw [hg2_frame _
        (fun i hi => by unfold ulookup_ctrl_idx ulookup_address_idx; omega)]
    exact hg1_ctrl
  have hg2_and : ∀ i, i < wE + wM → g2 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg2_frame _
        (fun i' hi' => by unfold ulookup_and_idx ulookup_address_idx; omega)]
    exact hg1_and i hi
  have hg2_addend : ∀ l, l < bits →
      g2 (A.addendIdx (1 + 2 * (wE + wM)) l) = false := by
    intro l hl
    rw [hg2_frame _ (fun i hi => hadd_ne_addr l hl (wM + i) (by omega))]
    exact hg1_addend l hl
  have hg2_aug : ∀ l, l < bits →
      g2 (A.augendIdx (1 + 2 * (wE + wM)) l)
        = g (A.augendIdx (1 + 2 * (wE + wM)) l) := by
    intro l hl
    rw [hg2_frame _ (fun i hi => haug_ne_addr l hl (wM + i) (by omega))]
    exact hg1_aug l hl
  -- ── g₃ = QROM read: table `T`'s row lands in the addend ───────────────
  have hwT : 0 < wE + wM := by omega
  have hvconcat : WindowedArith.window wM y j
      + 2 ^ wM * WindowedArith.window wE e k < 2 ^ (wE + wM) :=
    concat_lt wE wM _ _ (WindowedArith.window_lt wM y j)
      (WindowedArith.window_lt wE e k)
  have hg3_addend : ∀ l, l < bits →
      g3 (A.addendIdx (1 + 2 * (wE + wM)) l)
        = (c * (2 ^ wM) ^ j * WindowedArith.window wM y j).testBit l := by
    intro l hl
    rw [hg3def,
        lookupReadAt_selects_word (wE + wM) bits T
          (A.addendIdx (1 + 2 * (wE + wM))) g2
          (WindowedArith.window wM y j + 2 ^ wM * WindowedArith.window wE e k)
          hwT hvconcat hg2_ctrl hg2_addr hg2_and hpos_high hpos_inj l hl,
        hg2_addend l hl, Bool.false_xor, hrow]
  have hg3_frame : ∀ p, (∀ l, l < bits → p ≠ A.addendIdx (1 + 2 * (wE + wM)) l) →
      g3 p = g2 p := by
    intro p hp
    rw [hg3def]
    exact lookupReadAt_frame (wE + wM) bits T
      (A.addendIdx (1 + 2 * (wE + wM))) g2 hpos_high p hp
  have hg3_ctrl : g3 ulookup_ctrl_idx = true := by
    rw [hg3_frame _ hctrl_ne_pos]
    exact hg2_ctrl
  have hg3_addr : ∀ i, i < wE + wM →
      g3 (ulookup_address_idx i)
        = (WindowedArith.window wM y j
            + 2 ^ wM * WindowedArith.window wE e k).testBit i := by
    intro i hi
    rw [hg3_frame _ (haddr_ne_pos i hi)]
    exact hg2_addr i hi
  have hg3_and : ∀ i, i < wE + wM → g3 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg3_frame _ (hand_ne_pos i hi)]
    exact hg2_and i hi
  have hg3_aug : ∀ l, l < bits →
      g3 (A.augendIdx (1 + 2 * (wE + wM)) l)
        = g (A.augendIdx (1 + 2 * (wE + wM)) l) := by
    intro l hl
    rw [hg3_frame _ (fun m _ => A.augend_addend_disjoint (1 + 2 * (wE + wM)) l m)]
    exact hg2_aug l hl
  -- The copies/read only touched out-of-block wires and the addend, so the
  -- ancilla block is still clean.
  have hg3_clean : A.ancClean g3 bits (1 + 2 * (wE + wM)) := by
    refine A.ancClean_ext bits (1 + 2 * (wE + wM)) g g3 ?_ hC
    intro p hin hoff
    rw [hg3_frame p (fun l hl => (hoff l hl).2),
        hg2_frame p (fun i hi => by
          unfold inBlock at hin
          unfold ulookup_address_idx
          omega),
        hg1_frame p (fun i hi => by
          unfold inBlock at hin
          unfold ulookup_address_idx
          omega)]
  -- ── g₄ = the adder: augend ← augend + row, addend restored ────────────
  have hg4_dec : decodeReg (A.augendIdx (1 + 2 * (wE + wM))) bits g4
      = (s + c * (2 ^ wM) ^ j * WindowedArith.window wM y j) % 2 ^ bits := by
    rw [hg4def, A.sumCorrect bits (1 + 2 * (wE + wM)) g3 hg3_clean,
        decodeReg_ext (A.augendIdx (1 + 2 * (wE + wM))) bits g3 g hg3_aug, hV,
        decodeReg_eq_mod_of_testBit (A.addendIdx (1 + 2 * (wE + wM))) bits
          (c * (2 ^ wM) ^ j * WindowedArith.window wM y j) g3 hg3_addend,
        ← Nat.add_mod]
  have hg4_addend : ∀ l, l < bits →
      g4 (A.addendIdx (1 + 2 * (wE + wM)) l)
        = (c * (2 ^ wM) ^ j * WindowedArith.window wM y j).testBit l := by
    intro l hl
    rw [hg4def, A.addendRestored bits (1 + 2 * (wE + wM)) g3 hg3_clean l hl]
    exact hg3_addend l hl
  have hg4_clean : A.ancClean g4 bits (1 + 2 * (wE + wM)) :=
    A.ancRestored bits (1 + 2 * (wE + wM)) g3 hg3_clean
  have hg4_frame : ∀ p, ¬ inBlock (1 + 2 * (wE + wM)) (A.span bits) p →
      g4 p = g3 p := by
    intro p hp
    rw [hg4def]
    exact A.frame bits (1 + 2 * (wE + wM)) g3 p hp
  have hg4_ctrl : g4 ulookup_ctrl_idx = true := by
    rw [hg4_frame _ hctrl_out]
    exact hg3_ctrl
  have hg4_addr : ∀ i, i < wE + wM →
      g4 (ulookup_address_idx i)
        = (WindowedArith.window wM y j
            + 2 ^ wM * WindowedArith.window wE e k).testBit i := by
    intro i hi
    rw [hg4_frame _ (haddr_out i hi)]
    exact hg3_addr i hi
  have hg4_and : ∀ i, i < wE + wM → g4 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg4_frame _ (hand_out i hi)]
    exact hg3_and i hi
  -- ── g₅ = QROM read again: the addend register is cleared ──────────────
  have hg5_addend : ∀ l, l < bits →
      g5 (A.addendIdx (1 + 2 * (wE + wM)) l) = false := by
    intro l hl
    rw [hg5def,
        lookupReadAt_selects_word (wE + wM) bits T
          (A.addendIdx (1 + 2 * (wE + wM))) g4
          (WindowedArith.window wM y j + 2 ^ wM * WindowedArith.window wE e k)
          hwT hvconcat hg4_ctrl hg4_addr hg4_and hpos_high hpos_inj l hl,
        hg4_addend l hl, hrow, Bool.xor_self]
  have hg5_frame : ∀ p, (∀ l, l < bits → p ≠ A.addendIdx (1 + 2 * (wE + wM)) l) →
      g5 p = g4 p := by
    intro p hp
    rw [hg5def]
    exact lookupReadAt_frame (wE + wM) bits T
      (A.addendIdx (1 + 2 * (wE + wM))) g4 hpos_high p hp
  have hg5_clean : A.ancClean g5 bits (1 + 2 * (wE + wM)) := by
    refine A.ancClean_ext bits (1 + 2 * (wE + wM)) g4 g5 ?_ hg4_clean
    intro p _ hoff
    exact (hg5_frame p (fun l hl => (hoff l hl).2)).symm
  have hg5_aug : ∀ l, l < bits →
      g5 (A.augendIdx (1 + 2 * (wE + wM)) l)
        = g4 (A.augendIdx (1 + 2 * (wE + wM)) l) :=
    fun l hl => hg5_frame _
      (fun m _ => A.augend_addend_disjoint (1 + 2 * (wE + wM)) l m)
  have hg5_addr : ∀ i, i < wE + wM →
      g5 (ulookup_address_idx i)
        = (WindowedArith.window wM y j
            + 2 ^ wM * WindowedArith.window wE e k).testBit i := by
    intro i hi
    rw [hg5_frame _ (haddr_ne_pos i hi)]
    exact hg4_addr i hi
  -- The y-/e-registers rode through untouched (controls only, never targets).
  have hg5_e : ∀ i, i < wE →
      g5 ((1 + 2 * (wE + wM) + A.span bits + numWin * wM) + k * wE + i)
        = encodeReg (1 + 2 * (wE + wM) + A.span bits + numWin * wM)
            (numExpWin * wE) e
            ((1 + 2 * (wE + wM) + A.span bits + numWin * wM) + k * wE + i) := by
    intro i hi
    rw [hg5_frame _ (he_ne_pos i hi), hg4_frame _ (he_out i hi),
        hg3_frame _ (he_ne_pos i hi),
        hg2_frame _ (fun i' hi' => hctrlE i i' hi hi'),
        hg1_e i hi]
    exact hg_e i hi
  have hg5_y : ∀ i, i < wM →
      g5 ((1 + 2 * (wE + wM) + A.span bits) + j * wM + i)
        = encodeReg (1 + 2 * (wE + wM) + A.span bits) (numWin * wM) y
            ((1 + 2 * (wE + wM) + A.span bits) + j * wM + i) := by
    intro i hi
    rw [hg5_frame _ (hy_ne_pos i hi), hg4_frame _ (hy_out i hi),
        hg3_frame _ (hy_ne_pos i hi),
        hg2_frame _ (fun i' hi' => by unfold ulookup_address_idx; omega),
        hg1_frame _ (fun i' hi' => by
          have h := hctrlM i i' hi hi'
          rwa [Nat.zero_add] at h)]
    exact hg_y i hi
  -- ── g₆ = uncopy exp-window: address[wM,wM+wE) is cleared ──────────────
  have hg6_frame : ∀ p, (∀ i, i < wE → p ≠ ulookup_address_idx (wM + i)) →
      g6 p = g5 p := by
    intro p hp
    rw [hg6def]
    exact copyWindowAt_frame wE (1 + 2 * (wE + wM) + A.span bits + numWin * wM)
      k wM g5 p hp
  have hg6_addr_hi : ∀ i, i < wE → g6 (ulookup_address_idx (wM + i)) = false := by
    intro i hi
    rw [hg6def,
        copyWindowAt_at_addr wE (1 + 2 * (wE + wM) + A.span bits + numWin * wM)
          k wM g5 hctrlE i hi,
        hg5_e i hi,
        encodeReg_window_bit (1 + 2 * (wE + wM) + A.span bits + numWin * wM)
          wE numExpWin e k i hi hk]
    have h := hg5_addr (wM + i) (by omega)
    rw [concat_testBit wM (WindowedArith.window wM y j)
          (WindowedArith.window wE e k) (wM + i)
          (WindowedArith.window_lt wM y j), if_neg (by omega),
        show wM + i - wM = i by omega] at h
    rw [h, Bool.xor_self]
  have hg6_addr_lo : ∀ i, i < wM →
      g6 (ulookup_address_idx i) = (WindowedArith.window wM y j).testBit i := by
    intro i hi
    rw [hg6_frame _ (fun i' hi' => by unfold ulookup_address_idx; omega)]
    have h := hg5_addr i (by omega)
    rw [concat_testBit wM (WindowedArith.window wM y j)
          (WindowedArith.window wE e k) i (WindowedArith.window_lt wM y j),
        if_pos hi] at h
    exact h
  have hg6_y : ∀ i, i < wM →
      g6 ((1 + 2 * (wE + wM) + A.span bits) + j * wM + i)
        = encodeReg (1 + 2 * (wE + wM) + A.span bits) (numWin * wM) y
            ((1 + 2 * (wE + wM) + A.span bits) + j * wM + i) := by
    intro i hi
    rw [hg6_frame _ (fun i' hi' => by unfold ulookup_address_idx; omega)]
    exact hg5_y i hi
  -- ── g₇ = uncopy mul-window: address[0,wM) is cleared ──────────────────
  have hg7_frame : ∀ p, (∀ i, i < wM → p ≠ ulookup_address_idx i) →
      g7 p = g6 p := by
    intro p hp
    rw [hg7def]
    exact copyWindowAt_frame wM (1 + 2 * (wE + wM) + A.span bits) j 0 g6 p
      (fun i hi => by rw [Nat.zero_add]; exact hp i hi)
  have hg7_addr_lo : ∀ i, i < wM → g7 (ulookup_address_idx i) = false := by
    intro i hi
    have h := copyWindowAt_at_addr wM (1 + 2 * (wE + wM) + A.span bits) j 0 g6
      hctrlM i hi
    rw [Nat.zero_add] at h
    rw [hg7def, h, hg6_addr_lo i hi, hg6_y i hi,
        encodeReg_window_bit (1 + 2 * (wE + wM) + A.span bits) wM numWin y j
          i hi hj,
        Bool.xor_self]
  -- ── Reassemble the invariant for g₇ ───────────────────────────────────
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (F) frame off the block.
    intro p hp
    by_cases hplo : ∃ i, i < wM ∧ p = ulookup_address_idx i
    · obtain ⟨i, hi, rfl⟩ := hplo
      rw [hg7_addr_lo i hi]
      exact (expMulInputOf_low A wE wM bits numWin numExpWin y e _
        (by unfold ulookup_ctrl_idx ulookup_address_idx; omega)
        (by unfold ulookup_address_idx; omega)).symm
    · push Not at hplo
      by_cases hphi : ∃ i, i < wE ∧ p = ulookup_address_idx (wM + i)
      · obtain ⟨i, hi, rfl⟩ := hphi
        rw [hg7_frame _ (fun i' hi' => by unfold ulookup_address_idx; omega),
            hg6_addr_hi i hi]
        exact (expMulInputOf_low A wE wM bits numWin numExpWin y e _
          (by unfold ulookup_ctrl_idx ulookup_address_idx; omega)
          (by unfold ulookup_address_idx; omega)).symm
      · push Not at hphi
        have hp_ne_pos : ∀ l, l < bits →
            p ≠ A.addendIdx (1 + 2 * (wE + wM)) l :=
          fun l hl heq =>
            hp (heq ▸ A.addendIdx_inBlock bits (1 + 2 * (wE + wM)) l hl)
        rw [hg7_frame p hplo, hg6_frame p hphi, hg5_frame p hp_ne_pos,
            hg4_frame p hp, hg3_frame p hp_ne_pos, hg2_frame p hphi,
            hg1_frame p hplo]
        exact hF p hp
  · -- (D) the addend register is clean again.
    intro l hl
    rw [hg7_frame _ (fun i hi => hadd_ne_addr l hl i (by omega)),
        hg6_frame _ (fun i hi => hadd_ne_addr l hl (wM + i) (by omega))]
    exact hg5_addend l hl
  · -- (C) the ancilla block is clean again.
    refine A.ancClean_ext bits (1 + 2 * (wE + wM)) g5 g7 ?_ hg5_clean
    intro p hin _
    rw [hg7_frame p (fun i hi => by
          unfold inBlock at hin
          unfold ulookup_address_idx
          omega),
        hg6_frame p (fun i hi => by
          unfold inBlock at hin
          unfold ulookup_address_idx
          omega)]
  · -- (V) the augend register decodes to the new partial sum.
    rw [decodeReg_ext (A.augendIdx (1 + 2 * (wE + wM))) bits g7 g5
          (fun l hl => by
            rw [hg7_frame _ (fun i hi => haug_ne_addr l hl i (by omega)),
                hg6_frame _ (fun i hi => haug_ne_addr l hl (wM + i) (by omega))]),
        decodeReg_ext (A.augendIdx (1 + 2 * (wE + wM))) bits g5 g4 hg5_aug]
    exact hg4_dec

/-! ## §2. The generic fold at any initial accumulator.

`expStepInvT_step` is start-agnostic (it advances the invariant from ANY
partial sum `s`), so — exactly as `stepInv_fold_acc` generalized
`stepInv_fold` — the fold from ANY invariant state with partial sum `acc₀`
needs only a replayed induction. -/

/-- **The generic fold.**  From ANY state `g` satisfying the invariant with
    partial sum `acc₀`, running the first `n ≤ numWin` exponent-window steps
    of the pass with table family `Tfam` (each row evaluating to constant `c`,
    hypothesis `hrow`) yields the invariant with partial sum
    `acc₀ + Σ_{l<n} c·(2^wM)^l·windowₗ(y)`. -/
theorem expStepInvT_fold_acc (A : Adder)
    (wE wM bits c numWin numExpWin y e k acc₀ : Nat)
    (Tfam : Nat → Nat → Nat)
    (hrow : ∀ j, j < numWin →
      Tfam j (WindowedArith.window wM y j + 2 ^ wM * WindowedArith.window wE e k)
        = c * (2 ^ wM) ^ j * WindowedArith.window wM y j)
    (hwM : 0 < wM) (hk : k < numExpWin)
    (g : Nat → Bool) (hg : ExpStepInv A wE wM bits numWin numExpWin y e acc₀ g) :
    ∀ n, n ≤ numWin →
      ExpStepInv A wE wM bits numWin numExpWin y e
        (acc₀ + ∑ l ∈ Finset.range n,
          c * (2 ^ wM) ^ l * WindowedArith.window wM y l)
        (Gate.applyNat
          (expWindowPassOf A wE wM Tfam bits (1 + 2 * (wE + wM))
            (1 + 2 * (wE + wM) + A.span bits)
            (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k n)
          g) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Finset.sum_range_zero, Nat.add_zero]
    show ExpStepInv A wE wM bits numWin numExpWin y e acc₀
      (Gate.applyNat Gate.I g)
    rw [Gate.applyNat_I]
    exact hg
  | succ n ih =>
    intro hn
    have hsplit : expWindowPassOf A wE wM Tfam bits (1 + 2 * (wE + wM))
          (1 + 2 * (wE + wM) + A.span bits)
          (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k (n + 1)
        = Gate.seq
            (expWindowPassOf A wE wM Tfam bits (1 + 2 * (wE + wM))
              (1 + 2 * (wE + wM) + A.span bits)
              (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k n)
            (expWindowStepOf A wE wM (Tfam n) bits (1 + 2 * (wE + wM))
              (1 + 2 * (wE + wM) + A.span bits)
              (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k n) := by
      unfold expWindowPassOf
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq, Finset.sum_range_succ, ← Nat.add_assoc]
    exact expStepInvT_step A wE wM bits c numWin numExpWin y e k (Tfam n)
      hwM hk n (by omega) (hrow n (by omega)) _ _ (ih (by omega))

/-! ## §3. The full generic pass, invariant form. -/

/-- **The full generic pass.**  One complete pass (all `numWin` steps) from an
    invariant state with partial sum `acc₀` re-establishes the invariant with
    partial sum `acc₀ + c·y` — the form the in-place composition consumes. -/
theorem expStepInvT_full_pass (A : Adder)
    (wE wM bits c numWin numExpWin y e k acc₀ : Nat)
    (Tfam : Nat → Nat → Nat)
    (hrow : ∀ j, j < numWin →
      Tfam j (WindowedArith.window wM y j + 2 ^ wM * WindowedArith.window wE e k)
        = c * (2 ^ wM) ^ j * WindowedArith.window wM y j)
    (hwM : 0 < wM) (hk : k < numExpWin) (hy : y < 2 ^ (wM * numWin))
    (g : Nat → Bool) (hg : ExpStepInv A wE wM bits numWin numExpWin y e acc₀ g) :
    ExpStepInv A wE wM bits numWin numExpWin y e (acc₀ + c * y)
      (Gate.applyNat
        (expWindowPassOf A wE wM Tfam bits (1 + 2 * (wE + wM))
          (1 + 2 * (wE + wM) + A.span bits)
          (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k numWin)
        g) := by
  have hfold := expStepInvT_fold_acc A wE wM bits c numWin numExpWin y e k acc₀
    Tfam hrow hwM hk g hg numWin le_rfl
  have hy' : y < (2 ^ wM) ^ numWin := by rw [← pow_mul]; exact hy
  have hsum : (∑ l ∈ Finset.range numWin,
        c * (2 ^ wM) ^ l * WindowedArith.window wM y l) = c * y := by
    rw [WindowedArith.windowed_mul wM numWin c y hy']
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hsum] at hfold
  exact hfold

/-! ## §4. Stage 1 — the generalized quantum-selected pass at any `acc₀`. -/

/-- **Stage 1 HEADLINE — generalized quantum-selected pass VALUE theorem**
    (mirror of `windowedMulCircuitOf_correct_acc`).  For ANY adder `A`, the
    two-level pass with forward table `expTable g_k wM`, run from an invariant
    state whose accumulator holds partial sum `acc₀` (exponent register
    holding `e`), leaves `(acc₀ + g_k^{windowₖ(e)}·y) mod 2^bits` in the
    accumulator — the multiplication constant is SELECTED by the exponent
    window read from the quantum exponent register. -/
theorem expWindowPassOf_correct_acc (A : Adder)
    (wE wM bits g_k numWin numExpWin y e k acc₀ : Nat)
    (hwM : 0 < wM) (hk : k < numExpWin) (hy : y < 2 ^ (wM * numWin))
    (g : Nat → Bool) (hg : ExpStepInv A wE wM bits numWin numExpWin y e acc₀ g) :
    decodeAccOf A (Gate.applyNat
        (expWindowPassOf A wE wM (expTable g_k wM) bits (1 + 2 * (wE + wM))
          (1 + 2 * (wE + wM) + A.span bits)
          (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k numWin)
        g)
        (1 + 2 * (wE + wM)) bits
      = (acc₀ + g_k ^ WindowedArith.window wE e k * y) % 2 ^ bits := by
  show decodeReg (A.augendIdx (1 + 2 * (wE + wM))) bits _
    = (acc₀ + g_k ^ WindowedArith.window wE e k * y) % 2 ^ bits
  exact (expStepInvT_full_pass A wE wM bits
    (g_k ^ WindowedArith.window wE e k) numWin numExpWin y e k acc₀
    (expTable g_k wM)
    (fun j _ => expTable_row g_k wM j _ _ (WindowedArith.window_lt wM y j))
    hwM hk hy g hg).2.2.2

/-- **The nonzero-accumulator input** for the exponent-window pass:
    `expMulInputOf` with `acc₀` additionally encoded at the accumulator
    (augend) positions of adder `A`. -/
def expMulInputAccOf (A : Adder) (wE wM bits numWin numExpWin acc₀ y e : Nat) :
    Nat → Bool :=
  writeReg (A.augendIdx (1 + 2 * (wE + wM))) bits acc₀
    (expMulInputOf A wE wM bits numWin numExpWin y e)

/-- **Invariant initialization at `acc₀`.**  `expMulInputAccOf` satisfies the
    exponent-window-step invariant with partial sum `acc₀`. -/
theorem expStepInv_init_acc (A : Adder)
    (wE wM bits numWin numExpWin acc₀ y e : Nat)
    (hinj : ∀ i j, i < bits → j < bits →
      A.augendIdx (1 + 2 * (wE + wM)) i = A.augendIdx (1 + 2 * (wE + wM)) j →
      i = j)
    (hclean : A.ancClean (expMulInputAccOf A wE wM bits numWin numExpWin acc₀ y e)
      bits (1 + 2 * (wE + wM))) :
    ExpStepInv A wE wM bits numWin numExpWin y e acc₀
      (expMulInputAccOf A wE wM bits numWin numExpWin acc₀ y e) := by
  unfold expMulInputAccOf
  refine ⟨?_, ?_, hclean, ?_⟩
  · -- (F): off-block positions are untouched by the accumulator write.
    intro p hp
    exact writeReg_frame _ _ _ _ _
      (fun i hi heq => hp (heq ▸ A.augendIdx_inBlock bits (1 + 2 * (wE + wM)) i hi))
  · -- (D): the addend register is clean (augend and addend never collide).
    intro i hi
    rw [writeReg_frame _ _ _ _ _
          (fun l hl => Ne.symm (A.augend_addend_disjoint (1 + 2 * (wE + wM)) l i))]
    have hblk := A.addendIdx_inBlock bits (1 + 2 * (wE + wM)) i hi
    unfold inBlock at hblk
    exact expMulInputOf_low A wE wM bits numWin numExpWin y e _
      (by unfold ulookup_ctrl_idx; omega) (by omega)
  · -- (V): the accumulator decodes to `acc₀ % 2^bits`.
    exact decodeReg_eq_mod_of_testBit _ bits acc₀ _
      (fun i hi => writeReg_at _ bits acc₀ _ hinj i hi)

/-- **Stage 1, concrete input.**  On `expMulInputAccOf` (ctrl set, `y` in the
    y-register, `e` in the exponent register, `acc₀` in the accumulator), the
    quantum-selected pass leaves `(acc₀ + g_k^{windowₖ(e)}·y) mod 2^bits` in
    the accumulator. -/
theorem expMulInputAccOf_correct (A : Adder)
    (wE wM bits g_k numWin numExpWin acc₀ y e k : Nat)
    (hwM : 0 < wM) (hk : k < numExpWin) (hy : y < 2 ^ (wM * numWin))
    (hinj : ∀ i j, i < bits → j < bits →
      A.augendIdx (1 + 2 * (wE + wM)) i = A.augendIdx (1 + 2 * (wE + wM)) j →
      i = j)
    (hclean : A.ancClean (expMulInputAccOf A wE wM bits numWin numExpWin acc₀ y e)
      bits (1 + 2 * (wE + wM))) :
    decodeAccOf A (Gate.applyNat
        (expWindowPassOf A wE wM (expTable g_k wM) bits (1 + 2 * (wE + wM))
          (1 + 2 * (wE + wM) + A.span bits)
          (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k numWin)
        (expMulInputAccOf A wE wM bits numWin numExpWin acc₀ y e))
        (1 + 2 * (wE + wM)) bits
      = (acc₀ + g_k ^ WindowedArith.window wE e k * y) % 2 ^ bits :=
  expWindowPassOf_correct_acc A wE wM bits g_k numWin numExpWin y e k acc₀
    hwM hk hy _
    (expStepInv_init_acc A wE wM bits numWin numExpWin acc₀ y e hinj hclean)

/-! ## §5. The inverse table and the selected-exponent cancellation.

Pass 2 of the in-place round must multiply-accumulate by the NEGATED INVERSE
of the selected constant: for exponent-window value `ek`, the constant
`2^bits − (g_kinv^{ek} mod 2^bits)`, so that with `c = g_k^{ek}` and
`g_k·g_kinv ≡ 1 (mod 2^bits)` the accumulator clears:
`y + (2^bits − cinv)·(c·y mod 2^bits) ≡ 0 (mod 2^bits)`
(`mod_inv_cancel_identity` at the SELECTED exponent). -/

/-- **The two-level INVERSE table**: at concatenated address
    `addr = v + 2^wM·ek`, row `j` provides
    `(2^bits − g_kinv^ek mod 2^bits) · (2^wM)^j · v` — the negated inverse of
    the exponent-window-selected constant.  (Not of the form `expTable h wM`:
    at `ek = 0` a forward table's constant is pinned to `h^0 = 1`.) -/
def expTableInv (g_kinv wM bits : Nat) (j addr : Nat) : Nat :=
  (2 ^ bits - g_kinv ^ (addr / 2 ^ wM) % 2 ^ bits) * (2 ^ wM) ^ j
    * (addr % 2 ^ wM)

/-- **Inverse-table row decode at a concatenated address.** -/
theorem expTableInv_row (g_kinv wM bits j v ek : Nat) (hv : v < 2 ^ wM) :
    expTableInv g_kinv wM bits j (v + 2 ^ wM * ek)
      = (2 ^ bits - g_kinv ^ ek % 2 ^ bits) * (2 ^ wM) ^ j * v := by
  have hdm := WindowedArith.address_concat wM ek v hv
  rw [show ek * 2 ^ wM + v = v + 2 ^ wM * ek by ring] at hdm
  unfold expTableInv
  rw [hdm.1, hdm.2]

/-- A modular unit forces `1 % m = 1` (`m = 1` would make the residue `0`;
    `m = 0` is the identity modulus). -/
theorem one_mod_of_mul_mod_one (g ginv m : Nat) (h : g * ginv % m = 1) :
    1 % m = 1 := by
  have hm1 : m ≠ 1 := by
    intro hm1
    rw [hm1, Nat.mod_one] at h
    exact absurd h (by omega)
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · rw [hm0]
  · exact Nat.mod_eq_of_lt (by omega)

/-- **Inverses lift to powers** (`mul_pow`): if `g·ginv ≡ 1 (mod m)` then
    `g^n · ginv^n ≡ 1 (mod m)` — the selected constant `g_k^{ek}` is
    invertible with inverse `g_kinv^{ek}`. -/
theorem mul_pow_mod_one (g ginv m n : Nat) (h : g * ginv % m = 1) :
    g ^ n * ginv ^ n % m = 1 := by
  rw [← mul_pow, Nat.pow_mod, h, one_pow]
  exact one_mod_of_mul_mod_one g ginv m h

/-- The reduced form `g^n · (ginv^n mod m) ≡ 1 (mod m)` — the inverse witness
    the cancellation lemma consumes (it requires its inverse `< m`). -/
theorem pow_mod_inv_one (g ginv m n : Nat) (h : g * ginv % m = 1) :
    g ^ n * (ginv ^ n % m) % m = 1 := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  exact mul_pow_mod_one g ginv m n h

/-! ## §6. The composable I/O shape: `ExpReady`.

The `MulReady` analogue for the quantum-selected setting: off the adder block
the state IS `expMulInputOf` — ctrl set, lookup zone clean, `y` in the
y-register AND `e` in the exponent register (the exponent content is part of
the contract, so preservation through each round is part of the conclusion) —
and inside the block the addend register, the accumulator, and the adder
ancillas are all clean.  Output shape = input shape, so in-place
quantum-selected rounds compose. -/

/-- The in-place quantum-selected round's input/output contract: an
    `expMulInputOf`-shaped state with y-register value `y`, exponent-register
    value `e`, and a CLEAN adder block. -/
def ExpReady (A : Adder) (wE wM bits numWin numExpWin y e : Nat)
    (f : Nat → Bool) : Prop :=
  (∀ p, ¬ inBlock (1 + 2 * (wE + wM)) (A.span bits) p →
      f p = expMulInputOf A wE wM bits numWin numExpWin y e p)
  ∧ (∀ i, i < bits → f (A.addendIdx (1 + 2 * (wE + wM)) i) = false)
  ∧ A.ancClean f bits (1 + 2 * (wE + wM))
  ∧ (∀ i, i < bits → f (A.augendIdx (1 + 2 * (wE + wM)) i) = false)

/-- An `ExpReady` state satisfies the exponent-window-step invariant with
    partial sum 0 (a bitwise-clean accumulator decodes to 0). -/
theorem ExpReady.toExpStepInv {A : Adder} {wE wM bits numWin numExpWin y e : Nat}
    {f : Nat → Bool} (h : ExpReady A wE wM bits numWin numExpWin y e f) :
    ExpStepInv A wE wM bits numWin numExpWin y e 0 f :=
  ⟨h.1, h.2.1, h.2.2.1,
    by rw [decodeReg_eq_zero _ bits f h.2.2.2, Nat.zero_mod]⟩

/-- The clean input `expMulInputOf` is `ExpReady` (given the adder's abstract
    ancilla-cleanliness, discharged concretely per instance). -/
theorem expReady_expMulInputOf (A : Adder) (wE wM bits numWin numExpWin y e : Nat)
    (hclean : A.ancClean (expMulInputOf A wE wM bits numWin numExpWin y e)
      bits (1 + 2 * (wE + wM))) :
    ExpReady A wE wM bits numWin numExpWin y e
      (expMulInputOf A wE wM bits numWin numExpWin y e) := by
  refine ⟨fun p _ => rfl, ?_, hclean, ?_⟩
  · intro i hi
    have hblk := A.addendIdx_inBlock bits (1 + 2 * (wE + wM)) i hi
    unfold inBlock at hblk
    exact expMulInputOf_low A wE wM bits numWin numExpWin y e _
      (by unfold ulookup_ctrl_idx; omega) (by omega)
  · intro i hi
    have hblk := A.augendIdx_inBlock bits (1 + 2 * (wE + wM)) i hi
    unfold inBlock at hblk
    exact expMulInputOf_low A wE wM bits numWin numExpWin y e _
      (by unfold ulookup_ctrl_idx; omega) (by omega)

/-! ## §7. Stage 3 — the in-place quantum-selected pass.

The Gidney `modMultInPlace` pattern with the constant SELECTED by the quantum
exponent register, mod `2^bits`:

    pass(expTable g_k) ; acc↔y swap ; pass(expTableInv g_kinv)

On an `ExpReady` state with y-value `y` and exponent-register value `e`
(write `c = g_k^{windowₖ(e)}`): pass 1 puts `c·y mod 2^bits` in the
accumulator; the swap (`accYSwap A (wE+wM) bits` — the WindowedInPlace swap at
the widened layout; it touches only acc/y wires, so the exponent register is
framed) moves it into the y-register, leaving `y` in the accumulator; pass 2 —
the §3 generalized pass, initial accumulator `y`, y-register `c·y mod 2^bits` —
adds `(2^bits − g_kinv^{windowₖ(e)} mod 2^bits)·(c·y mod 2^bits)`, and the
selected-exponent cancellation clears the accumulator. -/

/-- **The in-place quantum-selected window round** at exp-window `k`, by the
    classical constant `g_k` with inverse `g_kinv` (`g_k·g_kinv ≡ 1 mod
    2^bits`): the multiplication constant `g_k^{e_k}` and its inverse are
    SELECTED by the exponent window living in the quantum exponent register.
    The gate is FIXED — only the tables depend on `g_k`/`g_kinv`; nothing
    depends on the exponent value. -/
def expWindowInPlaceOf (A : Adder) (wE wM bits numWin g_k g_kinv k : Nat) :
    Gate :=
  Gate.seq
    (Gate.seq
      (expWindowPassOf A wE wM (expTable g_k wM) bits (1 + 2 * (wE + wM))
        (1 + 2 * (wE + wM) + A.span bits)
        (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k numWin)
      (accYSwap A (wE + wM) bits))
    (expWindowPassOf A wE wM (expTableInv g_kinv wM bits) bits
      (1 + 2 * (wE + wM))
      (1 + 2 * (wE + wM) + A.span bits)
      (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k numWin)

/-- **Stage 3 HEADLINE — in-place QUANTUM-SELECTED windowed multiplication,
    full state restoration.**  For ANY adder `A` with pairwise-distinct
    accumulator positions, `numWin·wM = bits`, and `g_k·g_kinv ≡ 1 (mod
    2^bits)`: on an `ExpReady` state whose exponent register holds basis value
    `e` and whose y-register holds `y < 2^bits`, the round produces the
    `ExpReady` state with

        y ← g_k^{windowₖ(e)} · y  mod 2^bits

    and the EXPONENT REGISTER PRESERVED — accumulator, addend register, and
    ancillas all returned CLEAN.  Output shape = input shape, so rounds
    compose (§8).

    This is the per-basis-state `e` statement (for EVERY `e`; only the
    windows `windowₖ(e)`, automatically `< 2^wE`, enter) — exactly the form
    that lifts to superposed exponent registers at the unitary level via the
    basis-action bridge, since `expWindowInPlaceOf` is one fixed gate
    independent of `e`. -/
theorem expWindowInPlace_correct (A : Adder)
    (wE wM bits numWin numExpWin g_k g_kinv y e k : Nat)
    (hwM : 0 < wM) (hbits : numWin * wM = bits) (hk : k < numExpWin)
    (hy : y < 2 ^ bits) (hgk : g_k * g_kinv % 2 ^ bits = 1)
    (hinj : ∀ i j, i < bits → j < bits →
      A.augendIdx (1 + 2 * (wE + wM)) i = A.augendIdx (1 + 2 * (wE + wM)) j →
      i = j)
    (f : Nat → Bool) (hf : ExpReady A wE wM bits numWin numExpWin y e f) :
    ExpReady A wE wM bits numWin numExpWin
      (g_k ^ WindowedArith.window wE e k * y % 2 ^ bits) e
      (Gate.applyNat (expWindowInPlaceOf A wE wM bits numWin g_k g_kinv k) f) := by
  have hpow : (2 : Nat) ^ (wM * numWin) = 2 ^ bits := by
    rw [Nat.mul_comm wM numWin, hbits]
  -- The selected constant's reduced inverse and its unit equation.
  have hainv : g_kinv ^ WindowedArith.window wE e k % 2 ^ bits < 2 ^ bits :=
    Nat.mod_lt _ (Nat.two_pow_pos bits)
  have hinv : g_k ^ WindowedArith.window wE e k
      * (g_kinv ^ WindowedArith.window wE e k % 2 ^ bits) % 2 ^ bits = 1 :=
    pow_mod_inv_one g_k g_kinv (2 ^ bits) (WindowedArith.window wE e k) hgk
  -- Standing zone facts.
  have hadd_lt : ∀ i, i < bits →
      A.addendIdx (1 + 2 * (wE + wM)) i < 1 + 2 * (wE + wM) + A.span bits := by
    intro i hi
    have hblk := A.addendIdx_inBlock bits (1 + 2 * (wE + wM)) i hi
    unfold inBlock at hblk
    omega
  have hy_off : ∀ i : Nat,
      ¬ inBlock (1 + 2 * (wE + wM)) (A.span bits)
        (1 + 2 * (wE + wM) + A.span bits + i) := by
    intro i
    unfold inBlock
    omega
  -- Expose the three stages.
  unfold expWindowInPlaceOf
  simp only [Gate.applyNat_seq]
  set s1 : Nat → Bool :=
    Gate.applyNat (expWindowPassOf A wE wM (expTable g_k wM) bits
      (1 + 2 * (wE + wM)) (1 + 2 * (wE + wM) + A.span bits)
      (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k numWin) f with hs1def
  set s2 : Nat → Bool := Gate.applyNat (accYSwap A (wE + wM) bits) s1 with hs2def
  -- ── Pass 1: accumulator ← g_k^{windowₖ(e)}·y mod 2^bits ───────────────
  have hy1 : y < 2 ^ (wM * numWin) := by rw [hpow]; exact hy
  have h1 := expStepInvT_full_pass A wE wM bits
    (g_k ^ WindowedArith.window wE e k) numWin numExpWin y e k 0
    (expTable g_k wM)
    (fun j _ => expTable_row g_k wM j _ _ (WindowedArith.window_lt wM y j))
    hwM hk hy1 f hf.toExpStepInv
  rw [Nat.zero_add] at h1
  obtain ⟨h1F, h1D, h1C, h1V⟩ := h1
  rw [← hs1def] at h1F h1D h1C h1V
  -- Bitwise content after pass 1: the accumulator holds the digits of
  -- g_k^{windowₖ(e)}·y mod 2^bits, the y-register still holds the digits of y.
  have h1aug : ∀ i, i < bits →
      s1 (A.augendIdx (1 + 2 * (wE + wM)) i)
        = (g_k ^ WindowedArith.window wE e k * y % 2 ^ bits).testBit i := by
    intro i hi
    rw [← decodeReg_testBit (A.augendIdx (1 + 2 * (wE + wM))) bits s1 i hi, h1V]
  have h1y : ∀ i, i < bits →
      s1 (1 + 2 * (wE + wM) + A.span bits + i) = y.testBit i := by
    intro i hi
    rw [h1F _ (hy_off i),
        expMulInputOf_y A wE wM bits numWin numExpWin y e _
          (by unfold ulookup_ctrl_idx; omega) (by omega),
        encodeReg_at _ _ _ i (by omega)]
  -- ── The swap: accumulator ↔ y-register (exponent register framed) ─────
  obtain ⟨hsw_acc, hsw_y, hsw_fr⟩ := accYSwap_apply A (wE + wM) bits s1 hinj
  rw [← hs2def] at hsw_acc hsw_y hsw_fr
  -- s2 is an invariant state for the SECOND pass: y-register value
  -- g_k^{windowₖ(e)}·y mod 2^bits, exponent register still e, partial sum y.
  have h2 : ExpStepInv A wE wM bits numWin numExpWin
      (g_k ^ WindowedArith.window wE e k * y % 2 ^ bits) e y s2 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (F): off-block, s2 IS the fresh input with the new y-value and the
      -- SAME exponent value e.
      intro p hp
      by_cases hpy : ∃ i, i < bits ∧ p = 1 + 2 * (wE + wM) + A.span bits + i
      · obtain ⟨i, hi, rfl⟩ := hpy
        rw [hsw_y i hi, h1aug i hi,
            expMulInputOf_y A wE wM bits numWin numExpWin _ e _
              (by unfold ulookup_ctrl_idx; omega) (by omega),
            encodeReg_at _ _ _ i (by omega)]
      · push Not at hpy
        have hpa : ∀ i, i < bits → p ≠ A.augendIdx (1 + 2 * (wE + wM)) i :=
          fun i hi heq =>
            hp (heq ▸ A.augendIdx_inBlock bits (1 + 2 * (wE + wM)) i hi)
        rw [hsw_fr p (fun i hi => ⟨hpa i hi, hpy i hi⟩), h1F p hp]
        by_cases hpc : p = ulookup_ctrl_idx
        · rw [hpc, expMulInputOf_ctrl, expMulInputOf_ctrl]
        · unfold inBlock at hp
          push Not at hp
          by_cases hplow : p < 1 + 2 * (wE + wM) + A.span bits
          · have hlow : p < 1 + 2 * (wE + wM) := by
              by_contra hcon
              have := hp (by omega)
              omega
            rw [expMulInputOf_low A wE wM bits numWin numExpWin y e p hpc
                  (by omega),
                expMulInputOf_low A wE wM bits numWin numExpWin _ e p hpc
                  (by omega)]
          · have hphigh : 1 + 2 * (wE + wM) + A.span bits + numWin * wM ≤ p := by
              by_contra hcon
              exact hpy (p - (1 + 2 * (wE + wM) + A.span bits)) (by omega)
                (by omega)
            rw [expMulInputOf_e A wE wM bits numWin numExpWin y e p hphigh,
                expMulInputOf_e A wE wM bits numWin numExpWin _ e p hphigh]
    · -- (D): the addend register is untouched by the swap.
      intro i hi
      rw [hsw_fr _ (fun l hl =>
            ⟨Ne.symm (A.augend_addend_disjoint (1 + 2 * (wE + wM)) l i),
             by have := hadd_lt i hi; omega⟩)]
      exact h1D i hi
    · -- (C): the swap only touches data wires, so cleanliness transfers.
      refine A.ancClean_ext bits (1 + 2 * (wE + wM)) s1 s2 ?_ h1C
      intro p hin hoff
      exact (hsw_fr p (fun l hl =>
        ⟨(hoff l hl).1, by unfold inBlock at hin; omega⟩)).symm
    · -- (V): the accumulator now holds the digits of y.
      exact decodeReg_eq_mod_of_testBit _ bits y s2
        (fun i hi => by rw [hsw_acc i hi, h1y i hi])
  -- ── Pass 2: accumulator ← y + (2^bits − cinv)·(c·y mod 2^bits) ≡ 0 ────
  have hy2 : g_k ^ WindowedArith.window wE e k * y % 2 ^ bits
      < 2 ^ (wM * numWin) := by
    rw [hpow]
    exact Nat.mod_lt _ (Nat.two_pow_pos bits)
  set s3 : Nat → Bool :=
    Gate.applyNat (expWindowPassOf A wE wM (expTableInv g_kinv wM bits) bits
      (1 + 2 * (wE + wM)) (1 + 2 * (wE + wM) + A.span bits)
      (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k numWin) s2 with hs3def
  have h3 := expStepInvT_full_pass A wE wM bits
    (2 ^ bits - g_kinv ^ WindowedArith.window wE e k % 2 ^ bits) numWin
    numExpWin (g_k ^ WindowedArith.window wE e k * y % 2 ^ bits) e k y
    (expTableInv g_kinv wM bits)
    (fun j _ => expTableInv_row g_kinv wM bits j _ _
      (WindowedArith.window_lt wM
        (g_k ^ WindowedArith.window wE e k * y % 2 ^ bits) j))
    hwM hk hy2 s2 h2
  obtain ⟨h3F, h3D, h3C, h3V⟩ := h3
  rw [← hs3def] at h3F h3D h3C h3V
  -- The SELECTED-exponent modular-inverse cancellation clears the accumulator.
  have hzero : (y + (2 ^ bits - g_kinv ^ WindowedArith.window wE e k % 2 ^ bits)
        * (g_k ^ WindowedArith.window wE e k * y % 2 ^ bits)) % 2 ^ bits = 0 :=
    mod_inv_cancel_identity (g_k ^ WindowedArith.window wE e k)
      (g_kinv ^ WindowedArith.window wE e k % 2 ^ bits) (2 ^ bits) y
      (Nat.two_pow_pos bits) hy hainv hinv
  rw [hzero] at h3V
  refine ⟨h3F, h3D, h3C, ?_⟩
  intro i hi
  rw [← decodeReg_testBit (A.augendIdx (1 + 2 * (wE + wM))) bits s3 i hi, h3V,
      Nat.zero_testBit]

/-! ## §8. Stage 4 — the chain: quantum-selected in-place windowed MODEXP.

Because Stage 3 returns the state to the `ExpReady` shape (same exponent
value!), in-place quantum-selected rounds compose by induction: round `k`
uses the classical constants `g_k = g^((2^wE)^k)` (inverse `ginv^((2^wE)^k)`),
so round `k` multiplies the y-register by `g^((2^wE)^k·windowₖ(e))`, and the
`numExpWin` rounds multiply out to `g^e` by the base-`2^wE` digit expansion
of the QUANTUM (basis-state) exponent `e`. -/

/-- **The quantum-selected in-place windowed modular exponentiation**: the
    `nE`-fold chain of in-place quantum-selected window rounds, round `k`
    with constants `g^((2^wE)^k)` / `ginv^((2^wE)^k)`.  One FIXED gate —
    the exponent enters only through the quantum exponent register. -/
def windowedExpInPlaceQ (A : Adder) (wE wM bits numWin g ginv nE : Nat) : Gate :=
  (List.range nE).foldl
    (fun gate k => Gate.seq gate
      (expWindowInPlaceOf A wE wM bits numWin
        (g ^ (2 ^ wE) ^ k) (ginv ^ (2 ^ wE) ^ k) k))
    Gate.I

/-- **The chain fold.**  After the first `n ≤ numExpWin` rounds, the state is
    `ExpReady` with y-value `(Π_{k<n} g^((2^wE)^k·windowₖ(e)))·y mod 2^bits`
    and the exponent register STILL holding `e` — by induction, using
    Stage 3's full state restoration (the per-round inverse constants are
    units by `mul_pow_mod_one`). -/
theorem windowedExpInPlaceQ_fold (A : Adder)
    (wE wM bits numWin numExpWin g ginv y e : Nat)
    (hwM : 0 < wM) (hbits : numWin * wM = bits) (hy : y < 2 ^ bits)
    (hg : g * ginv % 2 ^ bits = 1)
    (hinj : ∀ i j, i < bits → j < bits →
      A.augendIdx (1 + 2 * (wE + wM)) i = A.augendIdx (1 + 2 * (wE + wM)) j →
      i = j)
    (f : Nat → Bool) (hf : ExpReady A wE wM bits numWin numExpWin y e f) :
    ∀ n, n ≤ numExpWin →
      ExpReady A wE wM bits numWin numExpWin
        ((∏ k ∈ Finset.range n,
            g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k)) * y % 2 ^ bits) e
        (Gate.applyNat (windowedExpInPlaceQ A wE wM bits numWin g ginv n) f) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Finset.prod_range_zero, Nat.one_mul, Nat.mod_eq_of_lt hy]
    show ExpReady A wE wM bits numWin numExpWin y e (Gate.applyNat Gate.I f)
    rw [Gate.applyNat_I]
    exact hf
  | succ n ih =>
    intro hn
    have hsplit : windowedExpInPlaceQ A wE wM bits numWin g ginv (n + 1)
        = Gate.seq (windowedExpInPlaceQ A wE wM bits numWin g ginv n)
            (expWindowInPlaceOf A wE wM bits numWin
              (g ^ (2 ^ wE) ^ n) (ginv ^ (2 ^ wE) ^ n) n) := by
      unfold windowedExpInPlaceQ
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq]
    -- After `n` rounds: an `ExpReady` state with the running-product y-value.
    have ihn := ih (by omega)
    have hyn : (∏ k ∈ Finset.range n,
          g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k)) * y % 2 ^ bits
        < 2 ^ bits := Nat.mod_lt _ (Nat.two_pow_pos bits)
    -- Round n's constants are a unit pair mod 2^bits.
    have hgn : (g ^ (2 ^ wE) ^ n) * (ginv ^ (2 ^ wE) ^ n) % 2 ^ bits = 1 :=
      mul_pow_mod_one g ginv (2 ^ bits) ((2 ^ wE) ^ n) hg
    -- Round n+1: one more in-place quantum-selected round, by Stage 3.
    have hstep := expWindowInPlace_correct A wE wM bits numWin numExpWin
      (g ^ (2 ^ wE) ^ n) (ginv ^ (2 ^ wE) ^ n)
      ((∏ k ∈ Finset.range n,
        g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k)) * y % 2 ^ bits)
      e n hwM hbits (by omega) hyn hgn hinj _ ihn
    -- Fold the new selected factor into the running product.
    have hval : (g ^ (2 ^ wE) ^ n) ^ WindowedArith.window wE e n
          * ((∏ k ∈ Finset.range n,
              g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k)) * y % 2 ^ bits)
          % 2 ^ bits
        = (∏ k ∈ Finset.range (n + 1),
            g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k)) * y % 2 ^ bits := by
      rw [← pow_mul, Finset.prod_range_succ, Nat.mul_mod, Nat.mod_mod,
          ← Nat.mul_mod,
          show g ^ ((2 ^ wE) ^ n * WindowedArith.window wE e n)
              * ((∏ k ∈ Finset.range n,
                  g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k)) * y)
            = (∏ k ∈ Finset.range n,
                g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k))
              * g ^ ((2 ^ wE) ^ n * WindowedArith.window wE e n) * y from by
            ring]
    rw [← hval]
    exact hstep

/-- **Stage 4 HEADLINE — QUANTUM-SELECTED in-place windowed MODEXP value
    theorem.**  For ANY adder `A`, `numWin·wM = bits`, `g·ginv ≡ 1 (mod
    2^bits)`, and ANY basis exponent `e < 2^(wE·numExpWin)` held in the
    quantum exponent register: the fixed gate `windowedExpInPlaceQ` maps the
    `ExpReady` state with y-value `y < 2^bits` to the `ExpReady` state with

        y ← g^e · y  mod 2^bits

    and the exponent register PRESERVED — the windowed factors multiply out
    to `g^e` by the base-`2^wE` digit expansion of `e`.  Holding for every
    basis `e` with one fixed gate, this is the statement that lifts to
    superposed exponent registers at the unitary level. -/
theorem windowedExpInPlaceQ_correct (A : Adder)
    (wE wM bits numWin numExpWin g ginv y e : Nat)
    (hwM : 0 < wM) (hbits : numWin * wM = bits) (hy : y < 2 ^ bits)
    (he : e < (2 ^ wE) ^ numExpWin) (hg : g * ginv % 2 ^ bits = 1)
    (hinj : ∀ i j, i < bits → j < bits →
      A.augendIdx (1 + 2 * (wE + wM)) i = A.augendIdx (1 + 2 * (wE + wM)) j →
      i = j)
    (f : Nat → Bool) (hf : ExpReady A wE wM bits numWin numExpWin y e f) :
    ExpReady A wE wM bits numWin numExpWin (g ^ e * y % 2 ^ bits) e
      (Gate.applyNat (windowedExpInPlaceQ A wE wM bits numWin g ginv numExpWin)
        f) := by
  have h := windowedExpInPlaceQ_fold A wE wM bits numWin numExpWin g ginv y e
    hwM hbits hy hg hinj f hf numExpWin le_rfl
  -- Σ_{k<numExpWin} (2^wE)^k · windowₖ(e) = e — the windowed digit expansion.
  have hexp : (∑ k ∈ Finset.range numExpWin,
        (2 ^ wE) ^ k * WindowedArith.window wE e k) = e := by
    have hm := (WindowedArith.windowed_mul wE numExpWin 1 e he).symm
    simp only [Nat.one_mul] at hm
    calc (∑ k ∈ Finset.range numExpWin,
          (2 ^ wE) ^ k * WindowedArith.window wE e k)
        = ∑ k ∈ Finset.range numExpWin,
            WindowedArith.window wE e k * (2 ^ wE) ^ k :=
          Finset.sum_congr rfl (fun k _ => Nat.mul_comm _ _)
      _ = e := hm
  -- Π_{k<numExpWin} g^((2^wE)^k · windowₖ(e)) = g^e.
  have hprod : (∏ k ∈ Finset.range numExpWin,
        g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k)) = g ^ e := by
    rw [Finset.prod_pow_eq_pow_sum, hexp]
  rw [← hprod]
  exact h

/-! ## §9. Cuccaro instance: the `ancClean` precondition discharged. -/

/-- **Cuccaro instance.**  The full quantum-selected in-place windowed modular
    exponentiation over the Cuccaro adder, run on the clean encoded input
    (`y` in the y-register, basis exponent `e` in the exponent register):
    the output is the `ExpReady` state with y-value `g^e·y mod 2^bits` and
    the exponent register preserved.  Cuccaro's `ancClean` — the carry-in
    qubit at the block base — is discharged concretely. -/
theorem windowedExpInPlaceQ_correct_cuccaro
    (wE wM bits numWin numExpWin g ginv y e : Nat)
    (hwM : 0 < wM) (hbits : numWin * wM = bits) (hy : y < 2 ^ bits)
    (he : e < (2 ^ wE) ^ numExpWin) (hg : g * ginv % 2 ^ bits = 1) :
    ExpReady cuccaroAdder wE wM bits numWin numExpWin (g ^ e * y % 2 ^ bits) e
      (Gate.applyNat
        (windowedExpInPlaceQ cuccaroAdder wE wM bits numWin g ginv numExpWin)
        (expMulInputOf cuccaroAdder wE wM bits numWin numExpWin y e)) := by
  refine windowedExpInPlaceQ_correct cuccaroAdder wE wM bits numWin numExpWin
    g ginv y e hwM hbits hy he hg
    (fun i j _ _ h => cuccaroAdder_augendIdx_inj (1 + 2 * (wE + wM)) i j h)
    _ (expReady_expMulInputOf cuccaroAdder wE wM bits numWin numExpWin y e ?_)
  show expMulInputOf cuccaroAdder wE wM bits numWin numExpWin y e
    (1 + 2 * (wE + wM)) = false
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  exact expMulInputOf_low cuccaroAdder wE wM bits numWin numExpWin y e _
    (by unfold ulookup_ctrl_idx; omega) (by omega)

end FormalRV.Shor.WindowedCircuit
