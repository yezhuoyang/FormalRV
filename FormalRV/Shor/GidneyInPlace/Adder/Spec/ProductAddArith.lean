/-
  FormalRV.Shor.GidneyInPlace.ProductAddArith
  ──────────────────────────────────────────────
  ARITHMETIC of the two-register windowed product-add `gidneyProductAddTOf`
  (ProductAddWrapper): it accumulates `Σₖ Tₖ[window(y,k)]` into the accumulator,
  using the relocated two-base adder.  NO in-place composition, NO coset/deviation.

  Mirrors `WindowedCircuitCorrect.stepInv_stepT`/`stepInv_foldT`, but on the two-base
  layout: accumulator `[accBase, accBase+bits)`, addend-temp `[tempBase, tempBase+bits)`,
  carry `tempBase+bits`, multiplicand `y` read from `yBase` (the SOURCE is explicit via
  `WindowedArith.window` + `encodeReg yBase`).  The multiplicand SOURCE being `yBase`
  (not `accBase`/`tempBase`) is visible in `RelocStepInv`'s `y`-conjunct and the
  `WindowedArith.window w y j` advance.
-/
import FormalRV.Shor.GidneyInPlace.Adder.Def.ProductAddWrapper
import FormalRV.Arithmetic.Windowed.WindowedLookupSelect
import FormalRV.Arithmetic.Windowed.WindowedCopySemantics
import FormalRV.Arithmetic.Windowed.WindowedCircuitCorrect

namespace FormalRV.Shor.GidneyInPlace.ProductAddArith

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.GidneyInPlace.ProductAddWrapper

/-- The per-step invariant for the two-base product-add: control set; address/AND/temp
    clean; carry clean; the multiplicand `y` still encoded at `yBase`; the accumulator
    decodes to the partial sum `s`. -/
def RelocStepInv (w bits numWin y accBase tempBase yBase s : Nat) (g : Nat → Bool) : Prop :=
  (g ulookup_ctrl_idx = true)
  ∧ (∀ i, i < w → g (ulookup_address_idx i) = false)
  ∧ (∀ i, i < w → g (ulookup_and_idx i) = false)
  ∧ (∀ i, i < bits → g (tempBase + i) = false)
  ∧ (g (tempBase + bits) = false)
  ∧ (∀ i, i < numWin * w → g (yBase + i) = encodeReg yBase (numWin * w) y (yBase + i))
  ∧ decodeReg (fun i => accBase + i) bits g = s % 2 ^ bits

/-- **One window step preserves the invariant, advancing the accumulator by
    `T (window w y j)`** — the literal `j`-th window of the multiplicand at `yBase`. -/
theorem relocatedProductAddStep_inv (w bits numWin : Nat) (T : Nat → Nat)
    (y accBase tempBase yBase j s : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin)
    (hv : accBase + bits ≤ tempBase) (hacc : 2 * w < accBase) (hyy : 2 * w < yBase)
    (hytemp : yBase + bits ≤ tempBase)
    (hpresY : ∀ (f' : Nat → Bool) i, i < numWin * w →
      Gate.applyNat (relocatedAdderCircuit accBase tempBase bits) f' (yBase + i) = f' (yBase + i))
    (g : Nat → Bool) (hg : RelocStepInv w bits numWin y accBase tempBase yBase s g) :
    RelocStepInv w bits numWin y accBase tempBase yBase (s + T (WindowedArith.window w y j))
      (Gate.applyNat (relocatedProductAddStep w bits T accBase tempBase yBase j) g) := by
  obtain ⟨hgctrl, hgaddr, hgand, hgtemp, hgcarry, hgy, hgV⟩ := hg
  have htemp : 2 * w < tempBase := by omega
  have hvw : WindowedArith.window w y j < 2 ^ w := WindowedArith.window_lt w y j
  -- reusable side conditions
  have hctrl_addr : ∀ i k, i < w → k < w → yBase + j * w + i ≠ ulookup_address_idx k :=
    fun i k _ _ => by unfold ulookup_address_idx; omega
  have hpos_high : ∀ k, k < bits → 2 * w < (fun k => tempBase + k) k :=
    fun k hk => by show 2 * w < tempBase + k; omega
  have hpos_inj : ∀ a b, a < bits → b < bits →
      (fun k => tempBase + k) a = (fun k => tempBase + k) b → a = b :=
    fun a b _ _ h => by simp only at h; omega
  -- expose the 5 sub-gates
  simp only [relocatedProductAddStep, relocatedLookupAdd, Gate.applyNat_seq]
  set g1 := Gate.applyNat (copyWindow w yBase j) g with hg1def
  set g2 := Gate.applyNat (lookupReadAt w (fun k => tempBase + k) bits T) g1 with hg2def
  set g3 := Gate.applyNat (relocatedAdderCircuit accBase tempBase bits) g2 with hg3def
  set g4 := Gate.applyNat (lookupReadAt w (fun k => tempBase + k) bits T) g3 with hg4def
  set g5 := Gate.applyNat (copyWindow w yBase j) g4 with hg5def
  -- y-conjunct, in the (yBase + j*w + i) form copyWindow_loads_window wants
  have hgy' : ∀ i, i < w →
      g (yBase + j * w + i) = encodeReg yBase (numWin * w) y (yBase + j * w + i) := by
    intro i hi
    have hlt : j * w + i < numWin * w := by
      calc j * w + i < j * w + w := by omega
        _ = (j + 1) * w := by ring
        _ ≤ numWin * w := Nat.mul_le_mul_right w hj
    have := hgy (j * w + i) hlt
    simpa [Nat.add_assoc] using this
  -- ── g1 = copyWindow: address ← window digit; rest framed ──
  have hg1_addr : ∀ i, i < w → g1 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i :=
    fun i hi => copyWindow_loads_window w yBase numWin y j g hctrl_addr hgaddr hgy' hj i hi
  have hg1_frame : ∀ p, (∀ i, i < w → p ≠ ulookup_address_idx i) → g1 p = g p :=
    fun p hp => copyWindow_frame w yBase j g p hp
  have hg1_ctrl : g1 ulookup_ctrl_idx = true := by
    rw [hg1_frame _ (fun i _ => by unfold ulookup_ctrl_idx ulookup_address_idx; omega)]; exact hgctrl
  have hg1_and : ∀ i, i < w → g1 (ulookup_and_idx i) = false := fun i hi => by
    rw [hg1_frame _ (fun k hk => by unfold ulookup_and_idx ulookup_address_idx; omega)]; exact hgand i hi
  have hg1_temp : ∀ i, i < bits → g1 (tempBase + i) = false := fun i hi => by
    rw [hg1_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]; exact hgtemp i hi
  have hg1_carry : g1 (tempBase + bits) = false := by
    rw [hg1_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]; exact hgcarry
  have hg1_acc : ∀ i, i < bits → g1 (accBase + i) = g (accBase + i) :=
    fun i hi => hg1_frame _ (fun k hk => by unfold ulookup_address_idx; omega)
  have hg1_y : ∀ i, i < numWin * w → g1 (yBase + i) = g (yBase + i) :=
    fun i hi => hg1_frame _ (fun k hk => by unfold ulookup_address_idx; omega)
  -- ── g2 = lookup read: temp ← T[window] row; rest framed ──
  have hg2_temp : ∀ i, i < bits → g2 (tempBase + i) = (T (WindowedArith.window w y j)).testBit i := by
    intro i hi
    rw [hg2def, lookupReadAt_selects_word w bits T (fun k => tempBase + k) g1
          (WindowedArith.window w y j) hw hvw hg1_ctrl hg1_addr hg1_and hpos_high hpos_inj i hi]
    show xor (g1 (tempBase + i)) _ = _
    rw [hg1_temp i hi, Bool.false_xor]
  have hg2_frame : ∀ p, (∀ k, k < bits → p ≠ tempBase + k) → g2 p = g1 p :=
    fun p hp => lookupReadAt_frame w bits T (fun k => tempBase + k) g1 hpos_high p hp
  have hg2_ctrl : g2 ulookup_ctrl_idx = true := by
    rw [hg2_frame _ (fun k hk => by unfold ulookup_ctrl_idx; omega)]; exact hg1_ctrl
  have hg2_addr : ∀ i, i < w → g2 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi; rw [hg2_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]; exact hg1_addr i hi
  have hg2_and : ∀ i, i < w → g2 (ulookup_and_idx i) = false := by
    intro i hi; rw [hg2_frame _ (fun k hk => by unfold ulookup_and_idx; omega)]; exact hg1_and i hi
  have hg2_carry : g2 (tempBase + bits) = false := by
    rw [hg2_frame _ (fun k hk => by omega)]; exact hg1_carry
  have hg2_acc : ∀ i, i < bits → g2 (accBase + i) = g (accBase + i) := by
    intro i hi; rw [hg2_frame _ (fun k hk => by omega)]; exact hg1_acc i hi
  have hg2_y : ∀ i, i < numWin * w → g2 (yBase + i) = g (yBase + i) := by
    intro i hi; rw [hg2_frame _ (fun k hk => by omega)]; exact hg1_y i hi
  -- carry-clean (the relocated adder's ancClean) for g2
  have hg2_anc : g2 (tempBase + bits) = false := hg2_carry
  -- ── g3 = relocated adder: acc += T[window]; temp restored; carry clean ──
  have hg3_acc : decodeReg (fun i => accBase + i) bits g3
      = (s + T (WindowedArith.window w y j)) % 2 ^ bits := by
    rw [hg3def, relocated_sumCorrect bits accBase tempBase g2 hv hg2_anc,
        decodeReg_ext (fun i => accBase + i) bits g2 g hg2_acc, hgV,
        decodeReg_eq_mod_of_testBit (fun i => tempBase + i) bits
          (T (WindowedArith.window w y j)) g2 hg2_temp, ← Nat.add_mod]
  have hg3_temp : ∀ i, i < bits → g3 (tempBase + i) = (T (WindowedArith.window w y j)).testBit i := by
    intro i hi
    rw [hg3def, relocated_addendRestored bits accBase tempBase g2 hv i hi]; exact hg2_temp i hi
  have hg3_carry : g3 (tempBase + bits) = false := by
    rw [hg3def]; exact relocated_ancRestored bits accBase tempBase g2 hv hg2_anc
  have hg3_frame : ∀ p, ¬ inBlock accBase (tempBase + bits + 1 - accBase) p → g3 p = g2 p :=
    fun p hp => by rw [hg3def]; exact relocated_frame bits accBase tempBase g2 p hv hp
  have hg3_ctrl : g3 ulookup_ctrl_idx = true := by
    rw [hg3_frame _ (by unfold inBlock ulookup_ctrl_idx; omega)]; exact hg2_ctrl
  have hg3_addr : ∀ i, i < w → g3 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi; rw [hg3_frame _ (by unfold inBlock ulookup_address_idx; omega)]; exact hg2_addr i hi
  have hg3_and : ∀ i, i < w → g3 (ulookup_and_idx i) = false := by
    intro i hi; rw [hg3_frame _ (by unfold inBlock ulookup_and_idx; omega)]; exact hg2_and i hi
  have hg3_y : ∀ i, i < numWin * w → g3 (yBase + i) = g (yBase + i) := by
    intro i hi; rw [hg3def, hpresY g2 i hi]; exact hg2_y i hi
  -- ── g4 = lookup read again: temp cleared; rest framed ──
  have hg4_temp : ∀ i, i < bits → g4 (tempBase + i) = false := by
    intro i hi
    rw [hg4def, lookupReadAt_selects_word w bits T (fun k => tempBase + k) g3
          (WindowedArith.window w y j) hw hvw hg3_ctrl hg3_addr hg3_and hpos_high hpos_inj i hi]
    show xor (g3 (tempBase + i)) _ = _
    rw [hg3_temp i hi, Bool.xor_self]
  have hg4_frame : ∀ p, (∀ k, k < bits → p ≠ tempBase + k) → g4 p = g3 p :=
    fun p hp => lookupReadAt_frame w bits T (fun k => tempBase + k) g3 hpos_high p hp
  have hg4_ctrl : g4 ulookup_ctrl_idx = true := by
    rw [hg4_frame _ (fun k hk => by unfold ulookup_ctrl_idx; omega)]; exact hg3_ctrl
  have hg4_addr : ∀ i, i < w → g4 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i := by
    intro i hi; rw [hg4_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]; exact hg3_addr i hi
  have hg4_carry : g4 (tempBase + bits) = false := by
    rw [hg4_frame _ (fun k hk => by omega)]; exact hg3_carry
  have hg4_acc : ∀ i, i < bits → g4 (accBase + i) = g3 (accBase + i) :=
    fun i hi => hg4_frame _ (fun k hk => by omega)
  have hg4_y : ∀ i, i < numWin * w → g4 (yBase + i) = g (yBase + i) := by
    intro i hi; rw [hg4_frame _ (fun k hk => by omega)]; exact hg3_y i hi
  -- y in the j*w+i form (for copyWindow_at_addr clearing)
  have hg4_y' : ∀ i, i < w →
      g4 (yBase + j * w + i) = encodeReg yBase (numWin * w) y (yBase + j * w + i) := by
    intro i hi
    have hlt : j * w + i < numWin * w := by
      calc j * w + i < j * w + w := by omega
        _ = (j + 1) * w := by ring
        _ ≤ numWin * w := Nat.mul_le_mul_right w hj
    have h := hg4_y (j * w + i) hlt
    rw [show yBase + (j * w + i) = yBase + j * w + i from by ring] at h
    rw [h]; exact hgy' i hi
  -- ── g5 = copyWindow again: address cleared; rest framed ──
  have hg5_addr : ∀ i, i < w → g5 (ulookup_address_idx i) = false := by
    intro i hi
    rw [hg5def, copyWindow_at_addr w yBase j g4 hctrl_addr i hi, hg4_addr i hi, hg4_y' i hi,
        encodeReg_window_bit yBase w numWin y j i hi hj, Bool.xor_self]
  have hg5_frame : ∀ p, (∀ i, i < w → p ≠ ulookup_address_idx i) → g5 p = g4 p :=
    fun p hp => copyWindow_frame w yBase j g4 p hp
  -- ── reassemble the invariant for g5 ──
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg5_frame _ (fun i _ => by unfold ulookup_ctrl_idx ulookup_address_idx; omega)]; exact hg4_ctrl
  · exact hg5_addr
  · intro i hi
    rw [hg5_frame _ (fun k hk => by unfold ulookup_and_idx ulookup_address_idx; omega),
        hg4_frame _ (fun k hk => by unfold ulookup_and_idx; omega)]
    rw [hg3_frame _ (by unfold inBlock ulookup_and_idx; omega), hg2_frame _ (fun k hk => by unfold ulookup_and_idx; omega)]
    exact hg1_and i hi
  · intro i hi
    rw [hg5_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]; exact hg4_temp i hi
  · rw [hg5_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]; exact hg4_carry
  · intro i hi
    rw [hg5_frame _ (fun k hk => by unfold ulookup_address_idx; omega), hg4_y i hi]
    exact hgy i hi
  · -- accumulator decodes to (s + T(window)) % 2^bits
    have hg5_acc : ∀ i, i < bits → g5 (accBase + i) = g4 (accBase + i) :=
      fun i hi => hg5_frame _ (fun k hk => by unfold ulookup_address_idx; omega)
    rw [decodeReg_ext (fun i => accBase + i) bits g5 g4 hg5_acc,
        decodeReg_ext (fun i => accBase + i) bits g4 g3 hg4_acc, hg3_acc]

/-- **The fold: after the first `n` window steps, the accumulator carries the partial
    sum `Σ_{k<n} Tfam k (window w y k)`** (and the invariant — temp/carry clean,
    multiplicand `y` preserved — still holds). -/
theorem relocatedProductAdd_fold (w bits numWin : Nat) (Tfam : Nat → Nat → Nat)
    (y accBase tempBase yBase : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hv : accBase + bits ≤ tempBase) (hacc : 2 * w < accBase) (hyy : 2 * w < yBase)
    (hytemp : yBase + bits ≤ tempBase)
    (hpresY : ∀ (f' : Nat → Bool) i, i < numWin * w →
      Gate.applyNat (relocatedAdderCircuit accBase tempBase bits) f' (yBase + i) = f' (yBase + i))
    (g : Nat → Bool) (hg : RelocStepInv w bits numWin y accBase tempBase yBase 0 g) :
    ∀ n, n ≤ numWin →
      RelocStepInv w bits numWin y accBase tempBase yBase
        (∑ k ∈ Finset.range n, Tfam k (WindowedArith.window w y k))
        (Gate.applyNat (gidneyProductAddTOf w bits Tfam accBase tempBase yBase n) g) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Finset.sum_range_zero,
        show gidneyProductAddTOf w bits Tfam accBase tempBase yBase 0 = Gate.I from rfl,
        Gate.applyNat_I]
    exact hg
  | succ n ih =>
    intro hn
    have hsplit : gidneyProductAddTOf w bits Tfam accBase tempBase yBase (n + 1)
        = Gate.seq (gidneyProductAddTOf w bits Tfam accBase tempBase yBase n)
            (relocatedProductAddStep w bits (Tfam n) accBase tempBase yBase n) := by
      unfold gidneyProductAddTOf
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq, Finset.sum_range_succ]
    exact relocatedProductAddStep_inv w bits numWin (Tfam n) y accBase tempBase yBase n _
      hw hbits (by omega) hv hacc hyy hytemp hpresY _ (ih (by omega))

/-- **Decode corollary: the accumulator value after the full product-add.** -/
theorem gidneyProductAddTOf_decode (w bits numWin : Nat) (Tfam : Nat → Nat → Nat)
    (y accBase tempBase yBase : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hv : accBase + bits ≤ tempBase) (hacc : 2 * w < accBase) (hyy : 2 * w < yBase)
    (hytemp : yBase + bits ≤ tempBase)
    (hpresY : ∀ (f' : Nat → Bool) i, i < numWin * w →
      Gate.applyNat (relocatedAdderCircuit accBase tempBase bits) f' (yBase + i) = f' (yBase + i))
    (g : Nat → Bool) (hg : RelocStepInv w bits numWin y accBase tempBase yBase 0 g) :
    decodeReg (fun i => accBase + i) bits
        (Gate.applyNat (gidneyProductAddTOf w bits Tfam accBase tempBase yBase numWin) g)
      = (∑ k ∈ Finset.range numWin, Tfam k (WindowedArith.window w y k)) % 2 ^ bits :=
  (relocatedProductAdd_fold w bits numWin Tfam y accBase tempBase yBase hw hbits hv hacc hyy hytemp
    hpresY g hg numWin (le_refl _)).2.2.2.2.2.2

/-! ## §3. Faithful-layout decode corollaries (multiplicand SOURCE = yBase visible). -/

/-- Pass 1 (`b += a·k`): accumulator `b @ 1+2w+bits`, multiplicand `a @ 1+2w`.  The
    accumulated value is `Σₖ Tfamₖ(window w a k) mod 2^bits` — the multiplicand windows
    are read from `yBase = 1+2w` (the `a` register). `hpresY` discharged by
    `relocated_pass1_multiplicand_preserved`. -/
theorem gidneyProductAdd_pass1_decode (w bits numWin : Nat) (Tfam : Nat → Nat → Nat)
    (y : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (g : Nat → Bool)
    (hg : RelocStepInv w bits numWin y (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) 0 g) :
    decodeReg (fun i => 1 + 2 * w + bits + i) bits
        (Gate.applyNat (gidneyProductAddTOf w bits Tfam (1 + 2 * w + bits) (1 + 2 * w + 2 * bits)
          (1 + 2 * w) numWin) g)
      = (∑ k ∈ Finset.range numWin, Tfam k (WindowedArith.window w y k)) % 2 ^ bits :=
  gidneyProductAddTOf_decode w bits numWin Tfam y (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w)
    hw hbits (by omega) (by omega) (by omega) (by omega)
    (fun f' i hi => relocated_pass1_multiplicand_preserved w bits f' i (by omega)) g hg

/-- Pass 2 (`a -= b·kInv`): accumulator `a @ 1+2w`, multiplicand `b @ 1+2w+bits` (the
    GAP).  `hpresY` discharged by `relocated_pass2_multiplicand_preserved` (the
    gap-frame fact): `b` is read as the multiplicand and left intact. -/
theorem gidneyProductAdd_pass2_decode (w bits numWin : Nat) (Tfam : Nat → Nat → Nat)
    (y : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (g : Nat → Bool)
    (hg : RelocStepInv w bits numWin y (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) 0 g) :
    decodeReg (fun i => 1 + 2 * w + i) bits
        (Gate.applyNat (gidneyProductAddTOf w bits Tfam (1 + 2 * w) (1 + 2 * w + 2 * bits)
          (1 + 2 * w + bits) numWin) g)
      = (∑ k ∈ Finset.range numWin, Tfam k (WindowedArith.window w y k)) % 2 ^ bits :=
  gidneyProductAddTOf_decode w bits numWin Tfam y (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits)
    hw hbits (by omega) (by omega) (by omega) (by omega)
    (fun f' i hi => relocated_pass2_multiplicand_preserved w bits f' i (by omega)) g hg

/-! ## §4. Frame: unrelated positions are untouched by the whole product-add.

A position `p` that is neither a lookup ADDRESS wire nor inside the adder bounding
`[accBase, tempBase+bits+1)` (which contains the accumulator, the gap, the addend-temp
and the carry) is left UNCHANGED by the full gate — for ANY input state `g` (no
cleanliness assumption).  Combined with the `RelocStepInv` corollaries (address/AND/temp/
carry restored, multiplicand `y` preserved, accumulator ← sum), this gives the complete
"only the accumulator is net-modified" picture the in-place composition needs:
the AND wires, ctrl, and any register OUTSIDE the bounding (incl. the multiplicand when
it sits below `accBase`, e.g. pass 1) are untouched here; the multiplicand inside the
gap (pass 2) is handled by the `RelocStepInv` `y`-conjunct / `relocated_gap_frame`. -/

/-- One window step leaves untouched any `p` off the address wires and off the adder
    bounding `[accBase, tempBase+bits+1)`. -/
theorem relocatedProductAddStep_frame (w bits : Nat) (T : Nat → Nat)
    (accBase tempBase yBase j : Nat) (hv : accBase + bits ≤ tempBase) (htemp : 2 * w < tempBase)
    (p : Nat) (haddr : ∀ i, i < w → p ≠ ulookup_address_idx i)
    (hbound : ¬ inBlock accBase (tempBase + bits + 1 - accBase) p) (g : Nat → Bool) :
    Gate.applyNat (relocatedProductAddStep w bits T accBase tempBase yBase j) g p = g p := by
  have hpos_high : ∀ k, k < bits → 2 * w < (fun k => tempBase + k) k :=
    fun k _ => by show 2 * w < tempBase + k; omega
  have hp_ne_pos : ∀ k, k < bits → p ≠ (fun k => tempBase + k) k :=
    fun k _ => by show p ≠ tempBase + k; unfold inBlock at hbound; omega
  simp only [relocatedProductAddStep, relocatedLookupAdd, Gate.applyNat_seq]
  rw [copyWindow_frame w yBase j _ p haddr,
      lookupReadAt_frame w bits T (fun k => tempBase + k) _ hpos_high p hp_ne_pos,
      relocated_frame bits accBase tempBase _ p hv hbound,
      lookupReadAt_frame w bits T (fun k => tempBase + k) _ hpos_high p hp_ne_pos,
      copyWindow_frame w yBase j _ p haddr]

/-- **The full product-add frame.**  `p` off the address wires and off the adder
    bounding is unchanged by `gidneyProductAddTOf`, for any `g`. -/
theorem gidneyProductAddTOf_frame (w bits : Nat) (Tfam : Nat → Nat → Nat)
    (accBase tempBase yBase numWin : Nat) (hv : accBase + bits ≤ tempBase) (htemp : 2 * w < tempBase)
    (p : Nat) (haddr : ∀ i, i < w → p ≠ ulookup_address_idx i)
    (hbound : ¬ inBlock accBase (tempBase + bits + 1 - accBase) p) (g : Nat → Bool) :
    Gate.applyNat (gidneyProductAddTOf w bits Tfam accBase tempBase yBase numWin) g p = g p := by
  induction numWin with
  | zero =>
    rw [show gidneyProductAddTOf w bits Tfam accBase tempBase yBase 0 = Gate.I from rfl,
        Gate.applyNat_I]
  | succ n ih =>
    have hsplit : gidneyProductAddTOf w bits Tfam accBase tempBase yBase (n + 1)
        = Gate.seq (gidneyProductAddTOf w bits Tfam accBase tempBase yBase n)
            (relocatedProductAddStep w bits (Tfam n) accBase tempBase yBase n) := by
      unfold gidneyProductAddTOf
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq,
        relocatedProductAddStep_frame w bits (Tfam n) accBase tempBase yBase n hv htemp p haddr hbound,
        ih]

/-! ## §5. Off-accumulator characterization: the gate changes ONLY the accumulator.

For an input `g` satisfying the invariant (fresh accumulator, clean scratch, `y` at
`yBase`), the product-add leaves EVERY position off the accumulator block unchanged —
the addend-temp, carry, lookup wires are restored; the multiplicand `y` is preserved;
everything unrelated is framed.  This is the "forward-pass" full-state fact the
in-place composition needs (combined with the decode of the accumulator itself). -/

/-- The gate restores every non-accumulator position.  `hcover` says the adder bounding
    decomposes into accumulator ∪ addend-temp ∪ carry ∪ multiplicand (true for the
    faithful pass-1/pass-2 wirings, discharged by `omega`). -/
theorem gidneyProductAddTOf_offAcc (w bits numWin : Nat) (Tfam : Nat → Nat → Nat)
    (y accBase tempBase yBase : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hv : accBase + bits ≤ tempBase) (hacc : 2 * w < accBase) (hyy : 2 * w < yBase)
    (hytemp : yBase + bits ≤ tempBase)
    (hpresY : ∀ (f' : Nat → Bool) i, i < numWin * w →
      Gate.applyNat (relocatedAdderCircuit accBase tempBase bits) f' (yBase + i) = f' (yBase + i))
    (hcover : ∀ q, accBase ≤ q → q < tempBase + bits + 1 →
      (∃ i, i < bits ∧ q = accBase + i) ∨ (∃ i, i < bits ∧ q = tempBase + i)
        ∨ q = tempBase + bits ∨ (∃ i, i < numWin * w ∧ q = yBase + i))
    (g : Nat → Bool) (hg : RelocStepInv w bits numWin y accBase tempBase yBase 0 g)
    (p : Nat) (hp_acc : ∀ i, i < bits → p ≠ accBase + i) :
    Gate.applyNat (gidneyProductAddTOf w bits Tfam accBase tempBase yBase numWin) g p = g p := by
  have hafter := relocatedProductAdd_fold w bits numWin Tfam y accBase tempBase yBase
    hw hbits hv hacc hyy hytemp hpresY g hg numWin (le_refl _)
  obtain ⟨hgc, hg1, hg2, hg3, hg4, hg5, _⟩ := hg
  obtain ⟨hac, ha1, ha2, ha3, ha4, ha5, _⟩ := hafter
  by_cases hctrl : p = ulookup_ctrl_idx
  · rw [hctrl, hac, hgc]
  by_cases haddr : ∃ i, i < w ∧ p = ulookup_address_idx i
  · obtain ⟨i, hi, rfl⟩ := haddr; rw [ha1 i hi, hg1 i hi]
  by_cases hand : ∃ i, i < w ∧ p = ulookup_and_idx i
  · obtain ⟨i, hi, rfl⟩ := hand; rw [ha2 i hi, hg2 i hi]
  by_cases htmp : ∃ i, i < bits ∧ p = tempBase + i
  · obtain ⟨i, hi, rfl⟩ := htmp; rw [ha3 i hi, hg3 i hi]
  by_cases hcry : p = tempBase + bits
  · rw [hcry, ha4, hg4]
  by_cases hyb : ∃ i, i < numWin * w ∧ p = yBase + i
  · obtain ⟨i, hi, rfl⟩ := hyb; rw [ha5 i hi, hg5 i hi]
  -- else: p is unrelated — show p ∉ bounding, then frame.
  have hbound : ¬ inBlock accBase (tempBase + bits + 1 - accBase) p := by
    intro hin
    unfold inBlock at hin
    rcases hcover p hin.1 (by omega) with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl | ⟨i, hi, rfl⟩
    · exact hp_acc i hi rfl
    · exact htmp ⟨i, hi, rfl⟩
    · exact hcry rfl
    · exact hyb ⟨i, hi, rfl⟩
  exact gidneyProductAddTOf_frame w bits Tfam accBase tempBase yBase numWin hv (by omega) p
    (fun i hi h => haddr ⟨i, hi, h⟩) hbound g

/-- **Full-state characterization.**  The gate output equals `g` EVERYWHERE except the
    accumulator block, where it holds the bits of `(Σₖ Tfam k (window w y k)) mod 2^bits`. -/
theorem gidneyProductAddTOf_state (w bits numWin : Nat) (Tfam : Nat → Nat → Nat)
    (y accBase tempBase yBase : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hv : accBase + bits ≤ tempBase) (hacc : 2 * w < accBase) (hyy : 2 * w < yBase)
    (hytemp : yBase + bits ≤ tempBase)
    (hpresY : ∀ (f' : Nat → Bool) i, i < numWin * w →
      Gate.applyNat (relocatedAdderCircuit accBase tempBase bits) f' (yBase + i) = f' (yBase + i))
    (hcover : ∀ q, accBase ≤ q → q < tempBase + bits + 1 →
      (∃ i, i < bits ∧ q = accBase + i) ∨ (∃ i, i < bits ∧ q = tempBase + i)
        ∨ q = tempBase + bits ∨ (∃ i, i < numWin * w ∧ q = yBase + i))
    (g : Nat → Bool) (hg : RelocStepInv w bits numWin y accBase tempBase yBase 0 g) (p : Nat) :
    Gate.applyNat (gidneyProductAddTOf w bits Tfam accBase tempBase yBase numWin) g p
      = if accBase ≤ p ∧ p < accBase + bits
        then ((∑ k ∈ Finset.range numWin, Tfam k (WindowedArith.window w y k)) % 2 ^ bits).testBit (p - accBase)
        else g p := by
  by_cases hpacc : accBase ≤ p ∧ p < accBase + bits
  · obtain ⟨h1, h2⟩ := hpacc
    rw [if_pos ⟨h1, h2⟩]
    have hdt := decodeReg_testBit (fun i => accBase + i) bits
      (Gate.applyNat (gidneyProductAddTOf w bits Tfam accBase tempBase yBase numWin) g)
      (p - accBase) (by omega)
    rw [gidneyProductAddTOf_decode w bits numWin Tfam y accBase tempBase yBase
          hw hbits hv hacc hyy hytemp hpresY g hg] at hdt
    have hpe : (fun i => accBase + i) (p - accBase) = p := by show accBase + (p - accBase) = p; omega
    rw [hpe] at hdt; exact hdt.symm
  · rw [if_neg hpacc]
    exact gidneyProductAddTOf_offAcc w bits numWin Tfam y accBase tempBase yBase
      hw hbits hv hacc hyy hytemp hpresY hcover g hg p
      (fun i hi heq => hpacc ⟨by omega, by omega⟩)

end FormalRV.Shor.GidneyInPlace.ProductAddArith
