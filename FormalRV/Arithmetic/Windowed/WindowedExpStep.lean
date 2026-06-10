/-
  FormalRV.Shor.WindowedCircuit.WindowedExpStep — the windowed-EXPONENT
  multiply-add pass (Gidney–Ekerå two-level lookup), adder-generic.

  One pass of the windowed modular-exponentiation inner loop (Gidney 1905.07682
  l.694–697): the lookup address CONCATENATES an exponent window (high bits)
  with a multiplier window (low bits), so a single QROM read over the widened
  `wE + wM`-bit address realizes the two-argument table
  `T[ek, v] = g_k^ek · (2^wM)^j · v` — i.e. one pass multiply-accumulates by
  the exponent-window-SELECTED constant `g_k^{e_k}`.

  HEADLINE (`expWindowPassOf_correct`): for ANY adder `A` satisfying the
  `Adder` interface, the pass `expWindowPassOf A wE wM (expTable g_k wM) …`,
  run on the input `expMulInputOf …` (ctrl set, `y` in the y-register, `e` in
  the exponent register, everything else clean), leaves

      (g_k ^ window wE e k · y) mod 2^bits

  in the accumulator.  Structural sibling of `windowedMulCircuitOf_correct`
  (same StepInv technique), with the wider `wTot = wE + wM` lookup register
  and the concatenated-address decode.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Windowed.WindowedCircuitCorrect

namespace FormalRV.Shor.WindowedCircuit

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §1. Offset window copy: `copyWindowAt`.

`copyWindow` always writes address wires `0 … w−1`.  The two-level lookup
needs to load TWO windows side by side into one widened address register, so
`copyWindowAt` adds an address OFFSET `aOff`: it CX-copies the `w`-bit window
`j` of the register at `srcBase` into address wires `aOff … aOff+w−1`.
Semantics are corollaries of the generic parallel-CX cascade engine. -/

/-- CX-copy window `j` of the `w`-bit-windowed register at `srcBase` into the
    lookup address wires `ulookup_address_idx (aOff) … (aOff+w−1)`.
    Self-inverse (`copyWindowAt_involutive_apply`).  `copyWindow w yBase j`
    is the `aOff = 0` instance (definitionally up to `0 + i = i`). -/
def copyWindowAt (w srcBase j aOff : Nat) : Gate :=
  (List.range w).foldl
    (fun g i => Gate.seq g
      (Gate.CX (srcBase + j * w + i) (ulookup_address_idx (aOff + i)))) Gate.I

/-- The standing control-vs-target disjointness: the CX controls (source wires
    `srcBase + j·w + i`) are never the targeted address wires whenever the
    source register sits above the targeted address segment. -/
theorem copyWindowAt_ctrl_ne (w srcBase j aOff : Nat)
    (hsrc : 2 * (aOff + w) ≤ srcBase) :
    ∀ i k, i < w → k < w → srcBase + j * w + i ≠ ulookup_address_idx (aOff + k) := by
  intro i k _ hk
  unfold ulookup_address_idx
  omega

/-- **`copyWindowAt` frame.**  Any wire that is not a targeted address wire
    `ulookup_address_idx (aOff + i)` (`i < w`) is untouched. -/
theorem copyWindowAt_frame (w srcBase j aOff : Nat) (f : Nat → Bool) (p : Nat)
    (hp : ∀ i, i < w → p ≠ ulookup_address_idx (aOff + i)) :
    Gate.applyNat (copyWindowAt w srcBase j aOff) f p = f p := by
  unfold copyWindowAt
  exact applyNat_cx_cascade_frame (fun i => srcBase + j * w + i)
    (fun i => ulookup_address_idx (aOff + i)) f w p hp

/-- **`copyWindowAt` post-state at a target.**  Targeted address wire `aOff + i`
    ends as the XOR of its original value with source bit `srcBase + j·w + i`. -/
theorem copyWindowAt_at_addr (w srcBase j aOff : Nat) (f : Nat → Bool)
    (hctrl : ∀ i k, i < w → k < w →
      srcBase + j * w + i ≠ ulookup_address_idx (aOff + k))
    (i : Nat) (hi : i < w) :
    Gate.applyNat (copyWindowAt w srcBase j aOff) f (ulookup_address_idx (aOff + i))
      = xor (f (ulookup_address_idx (aOff + i))) (f (srcBase + j * w + i)) := by
  unfold copyWindowAt
  exact applyNat_cx_cascade_at (fun i => srcBase + j * w + i)
    (fun i => ulookup_address_idx (aOff + i)) f w
    (fun a b _ _ hne => ulookup_address_idx_ne (aOff + a) (aOff + b) (by omega))
    hctrl i hi

/-- **`copyWindowAt` copies.**  On clean targeted address wires the copy writes
    the source bits verbatim. -/
theorem copyWindowAt_copies (w srcBase j aOff : Nat) (f : Nat → Bool)
    (hctrl : ∀ i k, i < w → k < w →
      srcBase + j * w + i ≠ ulookup_address_idx (aOff + k))
    (hclean : ∀ i, i < w → f (ulookup_address_idx (aOff + i)) = false)
    (i : Nat) (hi : i < w) :
    Gate.applyNat (copyWindowAt w srcBase j aOff) f (ulookup_address_idx (aOff + i))
      = f (srcBase + j * w + i) := by
  rw [copyWindowAt_at_addr w srcBase j aOff f hctrl i hi, hclean i hi, Bool.false_xor]

/-- **`copyWindowAt` is self-inverse (pointwise).** -/
theorem copyWindowAt_involutive_apply (w srcBase j aOff : Nat) (f : Nat → Bool)
    (hctrl : ∀ i k, i < w → k < w →
      srcBase + j * w + i ≠ ulookup_address_idx (aOff + k))
    (p : Nat) :
    Gate.applyNat (copyWindowAt w srcBase j aOff)
        (Gate.applyNat (copyWindowAt w srcBase j aOff) f) p = f p := by
  by_cases hp : ∃ i, i < w ∧ p = ulookup_address_idx (aOff + i)
  · obtain ⟨i, hi, rfl⟩ := hp
    rw [copyWindowAt_at_addr w srcBase j aOff _ hctrl i hi,
        copyWindowAt_at_addr w srcBase j aOff f hctrl i hi,
        copyWindowAt_frame w srcBase j aOff f (srcBase + j * w + i)
          (fun k hk => hctrl i k hi hk)]
    cases f (ulookup_address_idx (aOff + i)) <;> cases f (srcBase + j * w + i) <;> rfl
  · push Not at hp
    rw [copyWindowAt_frame w srcBase j aOff _ p hp,
        copyWindowAt_frame w srcBase j aOff f p hp]

/-! ## §2. Concatenated-address arithmetic.

The two-level address is `v + 2^wM · ek` (multiplier window `v` in the low
`wM` bits, exponent window `ek` in the high bits).  Its bits, its bound, and
the table-row decode at a concatenated address. -/

/-- **Concatenated-address bits.**  For `v < 2^wM`, bit `i` of `v + 2^wM·ek`
    is bit `i` of `v` below the split and bit `i − wM` of `ek` above it. -/
theorem concat_testBit (wM v ek i : Nat) (hv : v < 2 ^ wM) :
    (v + 2 ^ wM * ek).testBit i
      = if i < wM then v.testBit i else ek.testBit (i - wM) := by
  have hdm := WindowedArith.address_concat wM ek v hv
  rw [show ek * 2 ^ wM + v = v + 2 ^ wM * ek by ring] at hdm
  by_cases hi : i < wM
  · rw [if_pos hi]
    conv_rhs => rw [← hdm.2]
    rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
  · rw [if_neg hi]
    conv_rhs => rw [← hdm.1]
    rw [Nat.testBit_div_two_pow]
    congr 1
    omega

/-- **Concatenated-address bound.**  The concatenation of a `wM`-bit and a
    `wE`-bit window fits in the widened `wE + wM`-bit address space. -/
theorem concat_lt (wE wM v ek : Nat) (hv : v < 2 ^ wM) (hek : ek < 2 ^ wE) :
    v + 2 ^ wM * ek < 2 ^ (wE + wM) := by
  have h1 : v + 2 ^ wM * ek < 2 ^ wM * (ek + 1) := by
    rw [Nat.mul_succ]
    omega
  calc v + 2 ^ wM * ek < 2 ^ wM * (ek + 1) := h1
    _ ≤ 2 ^ wM * 2 ^ wE := Nat.mul_le_mul_left _ (by omega)
    _ = 2 ^ (wE + wM) := by rw [← pow_add, Nat.add_comm]

/-- **The two-level table** (Gidney 1905.07682 l.694–697): at concatenated
    address `addr = v + 2^wM·ek`, row `j` provides
    `g_k^ek · (2^wM)^j · v` — the multiplicand is SELECTED by the exponent
    window sitting in the high address bits. -/
def expTable (g_k wM : Nat) (j addr : Nat) : Nat :=
  g_k ^ (addr / 2 ^ wM) * (2 ^ wM) ^ j * (addr % 2 ^ wM)

/-- **Table-row decode at a concatenated address.**  Splitting the address
    back into its two windows (`address_concat`) evaluates the row. -/
theorem expTable_row (g_k wM j v ek : Nat) (hv : v < 2 ^ wM) :
    expTable g_k wM j (v + 2 ^ wM * ek) = g_k ^ ek * (2 ^ wM) ^ j * v := by
  have hdm := WindowedArith.address_concat wM ek v hv
  rw [show ek * 2 ^ wM + v = v + 2 ^ wM * ek by ring] at hdm
  unfold expTable
  rw [hdm.1, hdm.2]

/-! ## §3. The circuit.

Layout (as `windowedMulCircuitOf`, with the WIDER `wTot = wE + wM` lookup):
ctrl `0`; address wires `1+2i` (`i < wTot`); AND-ancillas `2+2i`; the adder
block at `q_start = 1 + 2·wTot`; the y-register (`numWin·wM` bits) at
`yBase = q_start + A.span bits`; the EXPONENT register (`numExpWin·wE` bits)
at `eBase = yBase + numWin·wM`. -/

/-- **One exponent-window step** at mul-window `j`, exp-window `k`: copy the
    mul-window into address bits `[0, wM)`, copy the exp-window into address
    bits `[wM, wM+wE)`, lookup-add the two-argument table row over the widened
    address, then uncopy both (reverse order). -/
def expWindowStepOf (A : Adder) (wE wM : Nat) (T : Nat → Nat)
    (bits q_start yBase eBase k j : Nat) : Gate :=
  Gate.seq (Gate.seq (Gate.seq (Gate.seq
    (copyWindowAt wM yBase j 0)
    (copyWindowAt wE eBase k wM))
    (lookupAddAtOf A (wE + wM) bits T bits q_start))
    (copyWindowAt wE eBase k wM))
    (copyWindowAt wM yBase j 0)

/-- **The windowed-exponent multiply-add pass**: fold the exponent-window step
    over the mul-windows `j < numWin`, with per-`j` table `Tfam j`. -/
def expWindowPassOf (A : Adder) (wE wM : Nat) (Tfam : Nat → Nat → Nat)
    (bits q_start yBase eBase k numWin : Nat) : Gate :=
  (List.range numWin).foldl
    (fun g j => Gate.seq g
      (expWindowStepOf A wE wM (Tfam j) bits q_start yBase eBase k j)) Gate.I

/-! ## §4. The input state. -/

/-- The input store for the exponent-window pass over adder `A`: control set,
    `y` encoded in the y-register at `yBase = 1+2(wE+wM) + A.span bits`, the
    exponent `e` encoded at `eBase = yBase + numWin·wM`, everything else clean. -/
def expMulInputOf (A : Adder) (wE wM bits numWin numExpWin y e : Nat) :
    Nat → Bool := fun p =>
  if p = ulookup_ctrl_idx then true
  else if p < 1 + 2 * (wE + wM) + A.span bits + numWin * wM then
    encodeReg (1 + 2 * (wE + wM) + A.span bits) (numWin * wM) y p
  else encodeReg (1 + 2 * (wE + wM) + A.span bits + numWin * wM) (numExpWin * wE) e p

/-- `expMulInputOf` reads `true` at the control qubit. -/
theorem expMulInputOf_ctrl (A : Adder) (wE wM bits numWin numExpWin y e : Nat) :
    expMulInputOf A wE wM bits numWin numExpWin y e ulookup_ctrl_idx = true := by
  unfold expMulInputOf
  rw [if_pos rfl]

/-- `expMulInputOf` reads `false` at every non-control position below the
    y-register. -/
theorem expMulInputOf_low (A : Adder) (wE wM bits numWin numExpWin y e p : Nat)
    (hp0 : p ≠ ulookup_ctrl_idx) (hpy : p < 1 + 2 * (wE + wM) + A.span bits) :
    expMulInputOf A wE wM bits numWin numExpWin y e p = false := by
  unfold expMulInputOf encodeReg
  rw [if_neg hp0, if_pos (by omega), if_neg (by omega)]

/-- Below the exponent register (and off the control), `expMulInputOf` is the
    `encodeReg` encoding of `y`. -/
theorem expMulInputOf_y (A : Adder) (wE wM bits numWin numExpWin y e p : Nat)
    (hp0 : p ≠ ulookup_ctrl_idx)
    (hp : p < 1 + 2 * (wE + wM) + A.span bits + numWin * wM) :
    expMulInputOf A wE wM bits numWin numExpWin y e p
      = encodeReg (1 + 2 * (wE + wM) + A.span bits) (numWin * wM) y p := by
  unfold expMulInputOf
  rw [if_neg hp0, if_pos hp]

/-- At and above the exponent register, `expMulInputOf` is the `encodeReg`
    encoding of `e`. -/
theorem expMulInputOf_e (A : Adder) (wE wM bits numWin numExpWin y e p : Nat)
    (hp : 1 + 2 * (wE + wM) + A.span bits + numWin * wM ≤ p) :
    expMulInputOf A wE wM bits numWin numExpWin y e p
      = encodeReg (1 + 2 * (wE + wM) + A.span bits + numWin * wM)
          (numExpWin * wE) e p := by
  unfold expMulInputOf
  rw [if_neg (by unfold ulookup_ctrl_idx; omega), if_neg (by omega)]

/-! ## §5. The exponent-window step invariant. -/

/-- **The pass invariant** (the `StepInv` of the two-level pass).  After some
    number of exponent-window steps starting from `expMulInputOf …`:
    * (F) frame: `g` agrees with the input off the adder block — in particular
      ctrl is set, the widened address/AND registers are clean, and the y- and
      exponent-registers still encode `y` and `e`;
    * (D) the addend register is clean;
    * (C) the adder's ancilla block is clean;
    * (V) the augend register decodes to `s % 2^bits` (the partial sum so far). -/
def ExpStepInv (A : Adder) (wE wM bits numWin numExpWin y e s : Nat)
    (g : Nat → Bool) : Prop :=
  (∀ p, ¬ inBlock (1 + 2 * (wE + wM)) (A.span bits) p →
      g p = expMulInputOf A wE wM bits numWin numExpWin y e p)
  ∧ (∀ i, i < bits → g (A.addendIdx (1 + 2 * (wE + wM)) i) = false)
  ∧ A.ancClean g bits (1 + 2 * (wE + wM))
  ∧ decodeReg (A.augendIdx (1 + 2 * (wE + wM))) bits g = s % 2 ^ bits

/-- **Invariant initialization.**  The input state satisfies the invariant
    with partial sum `0`. -/
theorem expStepInv_init (A : Adder) (wE wM bits numWin numExpWin y e : Nat)
    (hclean : A.ancClean (expMulInputOf A wE wM bits numWin numExpWin y e)
      bits (1 + 2 * (wE + wM))) :
    ExpStepInv A wE wM bits numWin numExpWin y e 0
      (expMulInputOf A wE wM bits numWin numExpWin y e) := by
  refine ⟨fun p _ => rfl, ?_, hclean, ?_⟩
  · -- (D): the addend register reads false (in-block, below the y-register).
    intro i hi
    have hblk := A.addendIdx_inBlock bits (1 + 2 * (wE + wM)) i hi
    unfold inBlock at hblk
    exact expMulInputOf_low A wE wM bits numWin numExpWin y e _
      (by unfold ulookup_ctrl_idx; omega) (by omega)
  · -- (V): the augend register reads false, so it decodes to 0 = 0 % 2^bits.
    rw [decodeReg_eq_zero _ bits _ (fun i hi => by
      have hblk := A.augendIdx_inBlock bits (1 + 2 * (wE + wM)) i hi
      unfold inBlock at hblk
      exact expMulInputOf_low A wE wM bits numWin numExpWin y e _
        (by unfold ulookup_ctrl_idx; omega) (by omega)),
      Nat.zero_mod]

/-! ## §6. The exponent-window step preserves the invariant.

One step is seven sub-gates: copy the mul-window into address `[0, wM)`, copy
the exp-window into address `[wM, wM+wE)`, QROM-read the two-argument table
row into the addend, run the adder, QROM-read again (clearing the addend),
uncopy the exp-window, uncopy the mul-window.  We track the state through
`g₁ … g₇` and re-establish all four invariant conjuncts. -/

theorem expStepInv_step (A : Adder) (wE wM bits g_k numWin numExpWin y e k : Nat)
    (hwM : 0 < wM) (hk : k < numExpWin)
    (j : Nat) (hj : j < numWin) (s : Nat) (g : Nat → Bool)
    (hg : ExpStepInv A wE wM bits numWin numExpWin y e s g) :
    ExpStepInv A wE wM bits numWin numExpWin y e
      (s + g_k ^ WindowedArith.window wE e k * (2 ^ wM) ^ j
            * WindowedArith.window wM y j)
      (Gate.applyNat
        (expWindowStepOf A wE wM (expTable g_k wM j) bits (1 + 2 * (wE + wM))
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
      (expTable g_k wM j)) g2 with hg3def
  set g4 : Nat → Bool :=
    Gate.applyNat (A.circuit bits (1 + 2 * (wE + wM))) g3 with hg4def
  set g5 : Nat → Bool :=
    Gate.applyNat (lookupReadAt (wE + wM) (A.addendIdx (1 + 2 * (wE + wM))) bits
      (expTable g_k wM j)) g4 with hg5def
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
  -- ── g₃ = QROM read: the two-argument table row lands in the addend ────
  have hwT : 0 < wE + wM := by omega
  have hvconcat : WindowedArith.window wM y j
      + 2 ^ wM * WindowedArith.window wE e k < 2 ^ (wE + wM) :=
    concat_lt wE wM _ _ (WindowedArith.window_lt wM y j)
      (WindowedArith.window_lt wE e k)
  have hg3_addend : ∀ l, l < bits →
      g3 (A.addendIdx (1 + 2 * (wE + wM)) l)
        = (g_k ^ WindowedArith.window wE e k * (2 ^ wM) ^ j
            * WindowedArith.window wM y j).testBit l := by
    intro l hl
    rw [hg3def,
        lookupReadAt_selects_word (wE + wM) bits (expTable g_k wM j)
          (A.addendIdx (1 + 2 * (wE + wM))) g2
          (WindowedArith.window wM y j + 2 ^ wM * WindowedArith.window wE e k)
          hwT hvconcat hg2_ctrl hg2_addr hg2_and hpos_high hpos_inj l hl,
        hg2_addend l hl, Bool.false_xor,
        expTable_row g_k wM j _ _ (WindowedArith.window_lt wM y j)]
  have hg3_frame : ∀ p, (∀ l, l < bits → p ≠ A.addendIdx (1 + 2 * (wE + wM)) l) →
      g3 p = g2 p := by
    intro p hp
    rw [hg3def]
    exact lookupReadAt_frame (wE + wM) bits (expTable g_k wM j)
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
      = (s + g_k ^ WindowedArith.window wE e k * (2 ^ wM) ^ j
            * WindowedArith.window wM y j) % 2 ^ bits := by
    rw [hg4def, A.sumCorrect bits (1 + 2 * (wE + wM)) g3 hg3_clean,
        decodeReg_ext (A.augendIdx (1 + 2 * (wE + wM))) bits g3 g hg3_aug, hV,
        decodeReg_eq_mod_of_testBit (A.addendIdx (1 + 2 * (wE + wM))) bits
          (g_k ^ WindowedArith.window wE e k * (2 ^ wM) ^ j
            * WindowedArith.window wM y j) g3 hg3_addend,
        ← Nat.add_mod]
  have hg4_addend : ∀ l, l < bits →
      g4 (A.addendIdx (1 + 2 * (wE + wM)) l)
        = (g_k ^ WindowedArith.window wE e k * (2 ^ wM) ^ j
            * WindowedArith.window wM y j).testBit l := by
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
        lookupReadAt_selects_word (wE + wM) bits (expTable g_k wM j)
          (A.addendIdx (1 + 2 * (wE + wM))) g4
          (WindowedArith.window wM y j + 2 ^ wM * WindowedArith.window wE e k)
          hwT hvconcat hg4_ctrl hg4_addr hg4_and hpos_high hpos_inj l hl,
        hg4_addend l hl,
        expTable_row g_k wM j _ _ (WindowedArith.window_lt wM y j),
        Bool.xor_self]
  have hg5_frame : ∀ p, (∀ l, l < bits → p ≠ A.addendIdx (1 + 2 * (wE + wM)) l) →
      g5 p = g4 p := by
    intro p hp
    rw [hg5def]
    exact lookupReadAt_frame (wE + wM) bits (expTable g_k wM j)
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

/-! ## §7. The fold and the headline. -/

/-- Running the first `n` exponent-window steps (`n ≤ numWin`) of the pass
    establishes the invariant with partial sum
    `Σ_{l<n} g_k^{windowₖ(e)}·(2^wM)^l·windowₗ(y)`. -/
theorem expStepInv_fold (A : Adder) (wE wM bits g_k numWin numExpWin y e k : Nat)
    (hwM : 0 < wM) (hk : k < numExpWin)
    (hclean : A.ancClean (expMulInputOf A wE wM bits numWin numExpWin y e)
      bits (1 + 2 * (wE + wM))) :
    ∀ n, n ≤ numWin →
      ExpStepInv A wE wM bits numWin numExpWin y e
        (∑ l ∈ Finset.range n,
          g_k ^ WindowedArith.window wE e k * (2 ^ wM) ^ l
            * WindowedArith.window wM y l)
        (Gate.applyNat
          (expWindowPassOf A wE wM (expTable g_k wM) bits (1 + 2 * (wE + wM))
            (1 + 2 * (wE + wM) + A.span bits)
            (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k n)
          (expMulInputOf A wE wM bits numWin numExpWin y e)) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Finset.sum_range_zero]
    show ExpStepInv A wE wM bits numWin numExpWin y e 0
      (Gate.applyNat Gate.I (expMulInputOf A wE wM bits numWin numExpWin y e))
    rw [Gate.applyNat_I]
    exact expStepInv_init A wE wM bits numWin numExpWin y e hclean
  | succ n ih =>
    intro hn
    have hsplit : expWindowPassOf A wE wM (expTable g_k wM) bits
          (1 + 2 * (wE + wM)) (1 + 2 * (wE + wM) + A.span bits)
          (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k (n + 1)
        = Gate.seq
            (expWindowPassOf A wE wM (expTable g_k wM) bits (1 + 2 * (wE + wM))
              (1 + 2 * (wE + wM) + A.span bits)
              (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k n)
            (expWindowStepOf A wE wM (expTable g_k wM n) bits (1 + 2 * (wE + wM))
              (1 + 2 * (wE + wM) + A.span bits)
              (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k n) := by
      unfold expWindowPassOf
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq, Finset.sum_range_succ]
    exact expStepInv_step A wE wM bits g_k numWin numExpWin y e k hwM hk
      n (by omega) _ _ (ih (by omega))

set_option linter.unusedVariables false in
/-- **HEADLINE — the windowed-EXPONENT multiply-add pass VALUE theorem.**
    For ANY adder `A`, the two-level pass (Gidney 1905.07682 l.694–697:
    concatenated address = exponent-window ++ multiplier-window), run on the
    encoded input (ctrl set, `y` in the y-register, `e` in the exponent
    register, everything else clean), multiply-accumulates by the
    exponent-window-SELECTED constant `g_k^{e_k}`: the accumulator ends at

        (g_k ^ window wE e k · y) mod 2^bits.

    One pass = one exponent-window step of the windowed modular
    exponentiation, adder-generic.

    (`hwE`/`he` are part of the well-formedness contract — the exponent
    register genuinely holds `numExpWin` nonempty windows — though the proof
    only consumes the per-window bounds, which hold definitionally.) -/
theorem expWindowPassOf_correct (A : Adder)
    (wE wM bits g_k numWin numExpWin y e k : Nat)
    (hwE : 0 < wE) (hwM : 0 < wM) (hk : k < numExpWin)
    (hy : y < 2 ^ (wM * numWin)) (he : e < 2 ^ (wE * numExpWin))
    (hclean : A.ancClean (expMulInputOf A wE wM bits numWin numExpWin y e)
      bits (1 + 2 * (wE + wM))) :
    decodeAccOf A (Gate.applyNat
        (expWindowPassOf A wE wM (expTable g_k wM) bits (1 + 2 * (wE + wM))
          (1 + 2 * (wE + wM) + A.span bits)
          (1 + 2 * (wE + wM) + A.span bits + numWin * wM) k numWin)
        (expMulInputOf A wE wM bits numWin numExpWin y e))
        (1 + 2 * (wE + wM)) bits
      = (g_k ^ WindowedArith.window wE e k * y) % 2 ^ bits := by
  have hfold := (expStepInv_fold A wE wM bits g_k numWin numExpWin y e k hwM hk
    hclean numWin (le_refl numWin)).2.2.2
  have hy' : y < (2 ^ wM) ^ numWin := by rw [← pow_mul]; exact hy
  have hsum : (∑ l ∈ Finset.range numWin,
        g_k ^ WindowedArith.window wE e k * (2 ^ wM) ^ l
          * WindowedArith.window wM y l)
      = g_k ^ WindowedArith.window wE e k * y := by
    rw [WindowedArith.windowed_mul wM numWin
          (g_k ^ WindowedArith.window wE e k) y hy']
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hsum] at hfold
  exact hfold

/-! ## §8. Cuccaro instance: the `ancClean` precondition discharged. -/

/-- **Cuccaro instance.**  `cuccaroAdder.ancClean` is the carry-in qubit at the
    block base reading `false` — below the y-register, so the input state
    provides it. -/
theorem expWindowPass_correct_cuccaro (wE wM bits g_k numWin numExpWin y e k : Nat)
    (hwE : 0 < wE) (hwM : 0 < wM) (hk : k < numExpWin)
    (hy : y < 2 ^ (wM * numWin)) (he : e < 2 ^ (wE * numExpWin)) :
    decodeAccOf cuccaroAdder (Gate.applyNat
        (expWindowPassOf cuccaroAdder wE wM (expTable g_k wM) bits
          (1 + 2 * (wE + wM)) (1 + 2 * (wE + wM) + cuccaroAdder.span bits)
          (1 + 2 * (wE + wM) + cuccaroAdder.span bits + numWin * wM) k numWin)
        (expMulInputOf cuccaroAdder wE wM bits numWin numExpWin y e))
        (1 + 2 * (wE + wM)) bits
      = (g_k ^ WindowedArith.window wE e k * y) % 2 ^ bits := by
  refine expWindowPassOf_correct cuccaroAdder wE wM bits g_k numWin numExpWin
    y e k hwE hwM hk hy he ?_
  show expMulInputOf cuccaroAdder wE wM bits numWin numExpWin y e
    (1 + 2 * (wE + wM)) = false
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  exact expMulInputOf_low cuccaroAdder wE wM bits numWin numExpWin y e _
    (by unfold ulookup_ctrl_idx; omega) (by omega)

/-- **Gidney instance.**  `gidneyAdder.ancClean` is
    `∀ i < bits, f ((1+2(wE+wM)) + 3i + 2) = false` — every carry qubit lies
    inside the adder block, below the y-register, so the input state reads it
    `false`. -/
theorem expWindowPass_correct_gidney (wE wM bits g_k numWin numExpWin y e k : Nat)
    (hwE : 0 < wE) (hwM : 0 < wM) (hk : k < numExpWin)
    (hy : y < 2 ^ (wM * numWin)) (he : e < 2 ^ (wE * numExpWin)) :
    decodeAccOf gidneyAdder (Gate.applyNat
        (expWindowPassOf gidneyAdder wE wM (expTable g_k wM) bits
          (1 + 2 * (wE + wM)) (1 + 2 * (wE + wM) + gidneyAdder.span bits)
          (1 + 2 * (wE + wM) + gidneyAdder.span bits + numWin * wM) k numWin)
        (expMulInputOf gidneyAdder wE wM bits numWin numExpWin y e))
        (1 + 2 * (wE + wM)) bits
      = (g_k ^ WindowedArith.window wE e k * y) % 2 ^ bits := by
  refine expWindowPassOf_correct gidneyAdder wE wM bits g_k numWin numExpWin
    y e k hwE hwM hk hy he ?_
  show ∀ i, i < bits →
    expMulInputOf gidneyAdder wE wM bits numWin numExpWin y e
      (1 + 2 * (wE + wM) + 3 * i + 2) = false
  intro i hi
  have hspan : gidneyAdder.span bits = 3 * bits + 2 := rfl
  exact expMulInputOf_low gidneyAdder wE wM bits numWin numExpWin y e _
    (by unfold ulookup_ctrl_idx; omega) (by omega)

end FormalRV.Shor.WindowedCircuit
