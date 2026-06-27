/-
  Audit · Gidney–Ekerå 2021 · `InPlaceMulData` — the reusable core for the
  literal `multiplyAddAt`-reduction read-out (bridge-reuse route).
  ════════════════════════════════════════════════════════════════════════════
  GOAL.  A verified gate that performs an IN-PLACE modular multiply
  `x ↦ (c·x) % N` on the canonical BIG-ENDIAN data band `[0, bits)` of an
  `encodeDataZeroAnc`-style state, by BRIDGING to the already-proven in-place
  multiplier `windowedModNMulInPlace` (which works in the `ModNMulReady`
  Cuccaro layout) and BACK.  This REUSES `windowedModNMulInPlace_correct`
  VERBATIM rather than rebuilding an inverse multiply.

  ────────────────────────────────────────────────────────────────────────────
  THE TWO ENDIANNESS/POSITION CONVENTIONS BEING RECONCILED
  ────────────────────────────────────────────────────────────────────────────
  • BIG-ENDIAN data band (`encodeDataZeroAnc`): data wire `i` (`i < bits`)
    carries `x.testBit (bits-1-i)`  (`encodeDataZeroAnc_data` ∘
    `nat_to_funbool_eq_testBit`).
  • `ModNMulReady`'s VALUE band (`mulInputOf cuccaroAdder`): the y-register wire
    `yBase + j` carries `x.testBit j` LSB-first, where
    `yBase = 1 + 2·w + cuccaroAdder.span bits = 1 + 2·w + (2·bits+1)`; AND the
    control qubit `ulookup_ctrl_idx = 0` must be SET (`= true`); AND the Cuccaro
    block (addend `1+2w+2i+2`, carry-in `1+2w`, augend `1+2w+2i+1`), the flag
    `yBase + numWin·w`, are all CLEAN.

  The bit-reversal `dataSrc j := bits-1-j` (the big-endian wire holding y-bit
  `j`) ↔ `yDst j := yBase + j` (the LSB-first y-register wire of weight `2^j`)
  is exactly the mover `transcodeBand` (`TranscodeBand.lean`).  The extra X on
  qubit 0 SETS the `ModNMulReady` control.

  ────────────────────────────────────────────────────────────────────────────
  THE POSITION-0 / BLOCK COLLISION (honest scope statement)
  ────────────────────────────────────────────────────────────────────────────
  `ModNMulReady` anchors its control at qubit 0 and its Cuccaro block at
  `[1+2w, 1+2w+(2·bits+1))`, while the big-endian data band is literally
  `[0, bits)`.  Position 0 is therefore SHARED (it is data wire 0 in the input
  and the control in the output — resolved: the SWAP empties wire 0, then X
  sets the control).  The Cuccaro block `[1+2w, …)` overlaps the data band
  `[0, bits)` precisely on `[1+2w, bits)`, which is empty IFF `bits ≤ 1+2w`.
  We therefore carry the explicit, SOUND separation hypothesis `hsep :
  bits ≤ 1 + 2·w` (it makes "data band = x" and "Cuccaro block clean"
  simultaneously satisfiable).  With `numWin·w = bits` this restricts
  `numWin ≤ 2`; the gate, the bridge, and the resource counts are nonetheless
  the reusable core (the multiply itself is reused verbatim at any `numWin`).

  ────────────────────────────────────────────────────────────────────────────
  WHAT IS PROVEN HERE (no `sorry`, no `native_decide`, kernel-clean)
  ────────────────────────────────────────────────────────────────────────────
  • `readyBridge` / `readyBridge_tcount` (T-free) / `readyBridge_wellTyped`.
  • `readyBridge_establishes_ModNMulReady` — forward bridge:
        data band `[0,bits)` = x  ⟹  `ModNMulReady w bits numWin x` after bridge.
  • `inPlaceMulData` — the round trip `readyBridge ; multiply ; reverse bridge`.
  • `inPlaceMulData_tcount` = `tcount (windowedModNMulInPlace …)` (bridges free).
  • `inPlaceMulData_wellTyped`.
  • `inPlaceMulData_apply` — FULL round trip: data band `[0,bits)` ends decoding
        to `(c·x) % N` in the SAME big-endian convention, the `ModNMulReady`
        scratch band restored clean, frame off the two bands.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Audit.GidneyEkera2021.TranscodeBand
import FormalRV.Arithmetic.Windowed.WindowedModNInPlace
import FormalRV.Shor.GidneyInPlace.Gate.Def.GateReversible

namespace FormalRV.Audit.GidneyEkera2021.InPlaceMulData

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open FormalRV.Audit.GidneyEkera2021.TranscodeBand (transcodeBand transcodeBand_tcount
  transcodeBand_wellTyped transcodeBand_apply)
open FormalRV.Shor.GidneyInPlace.GateReversible (Gate.reverse applyNat_reverse_cancel)
open VerifiedShor.Windowed (nat_to_funbool_eq_testBit)

/-! ## §0. Position abbreviations.

`yBase w bits = 1 + 2·w + (2·bits+1)` is the y-register base of `ModNMulReady`
(`= 1 + 2·w + cuccaroAdder.span bits`).  `dataSrc bits j = bits-1-j` is the
big-endian data wire carrying y-bit `j`; `yDst w bits j = yBase + j` is the
LSB-first y-register wire of weight `2^j`. -/

/-- The y-register base of the `ModNMulReady` layout. -/
def yBase (w bits : Nat) : Nat := 1 + 2 * w + (2 * bits + 1)

/-- The big-endian data wire of `[0,bits)` holding y-bit `j` (`encodeDataZeroAnc`
    convention: data wire `bits-1-j` carries `x.testBit j`). -/
def dataSrc (bits j : Nat) : Nat := bits - 1 - j

/-- The LSB-first `ModNMulReady` y-register wire of weight `2^j`. -/
def yDst (w bits j : Nat) : Nat := yBase w bits + j

/-! ### Local `mulInputOf` accessors (the originals in `WindowedModNInPlace` are
private; we restate them via the public `mulInputOf_eq_encodeReg` + `encodeReg_*`). -/

/-- Off the control qubit, `mulInputOf cuccaroAdder` is the `encodeReg` encoding
    of `v` (literal Cuccaro base). -/
private theorem mulInputOf_cuc_encodeReg (w bits numWin v p : Nat)
    (hp : p ≠ ulookup_ctrl_idx) :
    mulInputOf cuccaroAdder w bits numWin v p
      = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) v p :=
  mulInputOf_eq_encodeReg cuccaroAdder w bits numWin v p hp

/-- `mulInputOf cuccaroAdder` reads bit `i` of `v` at y-wire `yBase + i`. -/
private theorem mulInputOf_cuc_y_bit (w bits numWin v i : Nat)
    (hi : i < numWin * w) :
    mulInputOf cuccaroAdder w bits numWin v (1 + 2 * w + (2 * bits + 1) + i)
      = v.testBit i := by
  rw [mulInputOf_cuc_encodeReg w bits numWin v _ (by unfold ulookup_ctrl_idx; omega)]
  exact encodeReg_at _ _ _ i hi

/-! ## §1. The forward bridge `readyBridge`.

`readyBridge` = bit-reversal mover of `[0,bits)` → y-register, then X on the
control qubit 0.  T-free (the mover is a SWAP cascade, X is Clifford). -/

/-- **The forward bridge.**  Transcodes the big-endian data band `[0,bits)` into
    the `ModNMulReady` y-register (bit-reversing the order), then SETS the
    control qubit 0. -/
def readyBridge (w bits : Nat) : Gate :=
  Gate.seq (transcodeBand (dataSrc bits) (yDst w bits) bits) (Gate.X 0)

/-- The bridge is T-free (a SWAP cascade + an X gate). -/
theorem readyBridge_tcount (w bits : Nat) :
    (readyBridge w bits).tcount = 0 := by
  show (transcodeBand (dataSrc bits) (yDst w bits) bits).tcount + (Gate.X 0).tcount = 0
  rw [transcodeBand_tcount]
  rfl

/-- The bridge is well-typed at any `D` covering the whole `ModNMulReady` layout
    (`yBase + bits < D`, so both the data band `[0,bits)` and the y-register fit,
    and `bits ≤ 1+2w` keeps the data band below the y-register). -/
theorem readyBridge_wellTyped (w bits D : Nat)
    (hbits : 0 < bits) (_hsep : bits ≤ 1 + 2 * w) (hD : yBase w bits + bits < D) :
    Gate.WellTyped D (readyBridge w bits) := by
  refine ⟨?_, ?_⟩
  · refine transcodeBand_wellTyped _ _ bits D (by omega) ?_ ?_
    · intro k hk
      refine ⟨?_, ?_⟩
      · show dataSrc bits k < D; unfold dataSrc; omega
      · show yDst w bits k < D; unfold yDst; omega
    · intro k hk
      show dataSrc bits k ≠ yDst w bits k
      unfold dataSrc yDst yBase; omega
  · show 0 < D; omega

/-! ## §2. The `ModNMulReady`-input convention on the data band.

`DataBandReady w bits anc x f` packages the input contract for the bridge:
the big-endian data band `[0,bits)` carries `x` (`encodeDataZeroAnc` order), and
EVERYTHING above the data band (`p ≥ bits` — the Cuccaro block, the y-register,
the carry/flag, the low/high clean positions) is clean.  With `hsep : bits ≤
1+2w` this makes the `ModNMulReady` region clean while the data band holds `x`. -/

/-- The bridge-input contract: data band `[0,bits)` = `x` (big-endian); clean
    above. -/
def DataBandReady (bits anc x : Nat) (f : Nat → Bool) : Prop :=
  (∀ i, i < bits → f i = encodeDataZeroAnc bits anc x i)
  ∧ (∀ p, bits ≤ p → f p = false)

/-! ## §3. HEADLINE forward bridge — `readyBridge` establishes `ModNMulReady`. -/

/-- **HEADLINE (forward bridge).**  Given `f` whose big-endian data band `[0,bits)`
    decodes to `x` in the `encodeDataZeroAnc` convention (`DataBandReady`), with
    `x < N`, `x < 2^bits`, the y-register exactly the accumulator width
    (`numWin·w = bits`), and the data band below the Cuccaro block
    (`hsep : bits ≤ 1+2w`):  `ModNMulReady w bits numWin x` holds of
    `Gate.applyNat (readyBridge w bits) f`.  (The SWAP moves `x` from the
    big-endian band into the LSB-first y-register; the X sets the control.) -/
theorem readyBridge_establishes_ModNMulReady
    (w bits numWin anc x : Nat)
    (hbits : 0 < bits) (hsep : bits ≤ 1 + 2 * w) (hbw : numWin * w = bits)
    (hxbits : x < 2 ^ bits)
    (f : Nat → Bool) (hf : DataBandReady bits anc x f) :
    ModNMulReady w bits numWin x (Gate.applyNat (readyBridge w bits) f) := by
  obtain ⟨hdata, hclean⟩ := hf
  -- Abbreviations.
  set src : Nat → Nat := dataSrc bits with hsrc
  set dst : Nat → Nat := yDst w bits with hdst
  -- Injectivity / disjointness of the two index maps on `[0,bits)`.
  have hsrc_inj : ∀ i k, i < bits → k < bits → i ≠ k → src i ≠ src k := by
    intro i k _ _ hik; simp only [hsrc, dataSrc]; omega
  have hdst_inj : ∀ i k, i < bits → k < bits → i ≠ k → dst i ≠ dst k := by
    intro i k _ _ hik; simp only [hdst, yDst]; omega
  have hdisj : ∀ i k, i < bits → k < bits → src i ≠ dst k := by
    intro i k _ _; simp only [hsrc, hdst, dataSrc, yDst, yBase]; omega
  -- The y-register (`dst`-range) is all-false in `f` (it sits above the band).
  have hdst_false : ∀ k, k < bits → f (dst k) = false := by
    intro k hk; simp only [hdst, yDst, yBase]; exact hclean _ (by omega)
  -- Generic mover semantics.
  obtain ⟨h_read, h_clear, h_frame⟩ :=
    transcodeBand_apply src dst bits f hsrc_inj hdst_inj hdisj hdst_false
  -- The mover output (before the X).
  set m : Nat → Bool := Gate.applyNat (transcodeBand src dst bits) f with hmdef
  -- `readyBridge` output = `update m 0 (!(m 0))` (the X on qubit 0).
  have hbridge : Gate.applyNat (readyBridge w bits) f = update m 0 (!(m 0)) := by
    show Gate.applyNat (Gate.X 0) (Gate.applyNat (transcodeBand src dst bits) f)
        = update m 0 (!(m 0))
    rw [Gate.applyNat_X, ← hmdef]
  -- The control qubit 0 ends `true`: `dst k ≥ yBase > 0`, `src k = bits-1-k`,
  -- so `0 = src (bits-1)`; the mover CLEARS it (false), then X flips to true.
  have hm0 : m 0 = false := by
    have h0 : src (bits - 1) = 0 := by simp only [hsrc, dataSrc]; omega
    have hc := h_clear (bits - 1) (by omega)
    rw [h0] at hc
    exact hc
  -- y-register: `m (dst j) = f (src j) = x.testBit j` for `j < bits`.
  have hy : ∀ j, j < bits → m (dst j) = x.testBit j := by
    intro j hj
    rw [h_read j hj]
    have hsrclt : src j < bits := by simp only [hsrc, dataSrc]; omega
    rw [hdata _ hsrclt]
    -- `encodeDataZeroAnc bits anc x (src j) = x.testBit j` (big-endian readout).
    rw [encodeDataZeroAnc_data hxbits hsrclt, nat_to_funbool_eq_testBit]
    congr 1
    simp only [hsrc, dataSrc]; omega
  -- frame: positions off `[0,bits) ∪ y-register` are untouched by the mover.
  have hfr : ∀ p, (∀ k, k < bits → p ≠ src k ∧ p ≠ dst k) → m p = f p := by
    intro p hp; exact h_frame p hp
  -- Now assemble `ModNMulReady`.  Goal positions: y-register, addend, carry,
  -- flag, augend — plus the frame conjunct.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (F) off-block, off-flag, non-y, non-ctrl → `mulInputOf cuccaroAdder x p`.
    intro p hpb hpf
    rw [hbridge]
    by_cases hp0 : p = 0
    · -- control qubit: X set it `true = mulInputOf … ctrl`.
      subst hp0
      rw [update_eq, hm0]
      simp only [Bool.not_false]
      -- `mulInputOf cuccaroAdder w bits numWin x 0 = true` (ctrl = `ulookup_ctrl_idx`).
      exact (mulInputOf_ctrl cuccaroAdder w bits numWin x).symm
    · rw [update_neq m 0 p (!(m 0)) hp0]
      by_cases hpy : ∃ j, j < bits ∧ p = dst j
      · -- y-register wire: holds `x.testBit j` = `mulInputOf` y-bit.
        obtain ⟨j, hj, rfl⟩ := hpy
        rw [hy j hj]
        -- `mulInputOf cuccaroAdder w bits numWin x (yBase + j) = x.testBit j`.
        have : dst j = 1 + 2 * w + (2 * bits + 1) + j := by
          simp only [hdst, yDst, yBase]
        rw [this]
        exact (mulInputOf_cuc_y_bit w bits numWin x j (by omega)).symm
      · -- elsewhere: `p ≠ 0`, not a y-register wire.
        push Not at hpy
        have hpne : p ≠ ulookup_ctrl_idx := by show p ≠ 0; exact hp0
        by_cases hplt : p < bits
        · -- p in the data band `[1,bits)`: it is `src (bits-1-p)`; the SWAP
          -- CLEARED it (false); `mulInputOf x p = false` (low).
          have hpsrc : p = src (bits - 1 - p) := by simp only [hsrc, dataSrc]; omega
          have hclr : m p = false := by
            rw [hpsrc]; exact h_clear (bits - 1 - p) (by omega)
          rw [hclr]
          -- `p < bits ≤ 1+2w < yBase`, so `mulInputOf x p = false` (low).
          exact (mulInputOf_low cuccaroAdder w bits numWin x p hpne (by
            show p < 1 + 2 * w + cuccaroAdder.span bits
            show p < 1 + 2 * w + (2 * bits + 1); omega)).symm
        · -- p ≥ bits: framed → `f p = false` (clean above the data band).
          push Not at hplt
          have hpsrc' : ∀ k, k < bits → p ≠ src k := by
            intro k hk; simp only [hsrc, dataSrc]; omega
          rw [hfr p (fun k hk => ⟨hpsrc' k hk, hpy k hk⟩), hclean p hplt]
          -- `mulInputOf x p = false`: low (`p < yBase`) or high (`p ≥ yBase+bits`).
          by_cases hplow : p < 1 + 2 * w + (2 * bits + 1)
          · exact (mulInputOf_low cuccaroAdder w bits numWin x p hpne (by
              show p < 1 + 2 * w + cuccaroAdder.span bits
              show p < 1 + 2 * w + (2 * bits + 1); exact hplow)).symm
          · -- `p ≥ yBase`; not in y-register (hpy) ⟹ `p ≥ yBase+bits` (high).
            have hphigh : 1 + 2 * w + (2 * bits + 1) + bits ≤ p := by
              by_contra hcon
              push Not at hcon
              exact hpy (p - (1 + 2 * w + (2 * bits + 1)))
                (by omega)
                (by simp only [hdst, yDst, yBase]; omega)
            rw [mulInputOf_cuc_encodeReg w bits numWin x p hpne,
                encodeReg_high _ _ _ _ (by rw [hbw]; omega)]
  · -- (D) addend register clean: `1+2w+2i+2`, framed → `f = false`.
    intro i hi
    rw [hbridge]
    have hne0 : (1 + 2 * w + 2 * i + 2) ≠ 0 := by omega
    rw [update_neq m 0 _ (!(m 0)) hne0]
    rw [hfr _ (fun k hk => ⟨by simp only [hsrc, dataSrc]; omega,
                            by simp only [hdst, yDst, yBase]; omega⟩)]
    exact hclean _ (by omega)
  · -- (C) carry-in `1+2w` clean.
    rw [hbridge]
    have hne0 : (1 + 2 * w) ≠ 0 := by omega
    rw [update_neq m 0 _ (!(m 0)) hne0]
    rw [hfr _ (fun k hk => ⟨by simp only [hsrc, dataSrc]; omega,
                            by simp only [hdst, yDst, yBase]; omega⟩)]
    exact hclean _ (by omega)
  · -- (G) flag `yBase + numWin·w` clean.
    rw [hbridge]
    have hne0 : (1 + 2 * w + (2 * bits + 1) + numWin * w) ≠ 0 := by omega
    rw [update_neq m 0 _ (!(m 0)) hne0]
    rw [hfr _ (fun k hk => ⟨by simp only [hsrc, dataSrc]; omega,
                            by simp only [hdst, yDst, yBase]; rw [hbw]; omega⟩)]
    exact hclean _ (by rw [hbw]; omega)
  · -- (V) augend register clean: `1+2w+2i+1`, framed → `f = false`.
    intro i hi
    rw [hbridge]
    have hne0 : (1 + 2 * w + 2 * i + 1) ≠ 0 := by omega
    rw [update_neq m 0 _ (!(m 0)) hne0]
    rw [hfr _ (fun k hk => ⟨by simp only [hsrc, dataSrc]; omega,
                            by simp only [hdst, yDst, yBase]; omega⟩)]
    exact hclean _ (by omega)

/-! ## §4. The full round trip `inPlaceMulData`. -/

/-- **The in-place modular multiply on the big-endian data band.**
    `readyBridge ; windowedModNMulInPlace(c, cinv) ; reverse readyBridge`. -/
def inPlaceMulData (w bits N numWin c cinv : Nat) : Gate :=
  Gate.seq
    (Gate.seq (readyBridge w bits)
      (windowedModNMulInPlace w bits c cinv N numWin))
    (Gate.reverse (readyBridge w bits))

/-- **Round-trip T-count** = the multiply's T-count (both bridges are T-free). -/
theorem inPlaceMulData_tcount (w bits N numWin c cinv : Nat) :
    (inPlaceMulData w bits N numWin c cinv).tcount
      = (windowedModNMulInPlace w bits c cinv N numWin).tcount := by
  show (readyBridge w bits).tcount
      + (windowedModNMulInPlace w bits c cinv N numWin).tcount
      + (Gate.reverse (readyBridge w bits)).tcount
    = (windowedModNMulInPlace w bits c cinv N numWin).tcount
  -- `reverse` preserves tcount (each generator fixed; seq reverses order).
  have hrev : ∀ g : Gate, (Gate.reverse g).tcount = g.tcount := by
    intro g
    induction g with
    | I => rfl
    | X _ => rfl
    | CX _ _ => rfl
    | CCX _ _ _ => rfl
    | seq g₁ g₂ ih₁ ih₂ =>
        show (Gate.reverse g₂).tcount + (Gate.reverse g₁).tcount
            = g₁.tcount + g₂.tcount
        rw [ih₁, ih₂]; ring
  rw [readyBridge_tcount, hrev, readyBridge_tcount]
  omega

/-- **Round-trip well-typedness** at any `D` covering the whole layout. -/
theorem inPlaceMulData_wellTyped (w bits N numWin c cinv D : Nat)
    (hbits : 0 < bits) (hsep : bits ≤ 1 + 2 * w)
    (hD : yBase w bits + bits < D)
    (hmul : Gate.WellTyped D (windowedModNMulInPlace w bits c cinv N numWin)) :
    Gate.WellTyped D (inPlaceMulData w bits N numWin c cinv) := by
  -- `reverse` preserves well-typedness (generators fixed, seq order reversed).
  have hrev : ∀ g : Gate, Gate.WellTyped D g → Gate.WellTyped D (Gate.reverse g) := by
    intro g
    induction g with
    | I => intro h; exact h
    | X _ => intro h; exact h
    | CX _ _ => intro h; exact h
    | CCX _ _ _ => intro h; exact h
    | seq g₁ g₂ ih₁ ih₂ =>
        intro h; exact ⟨ih₂ h.2, ih₁ h.1⟩
  have hbr : Gate.WellTyped D (readyBridge w bits) :=
    readyBridge_wellTyped w bits D hbits hsep hD
  exact ⟨⟨hbr, hmul⟩, hrev _ hbr⟩

/-! ## §4½. `ModNMulReady` is RIGID (it pins the whole function).

`ModNMulReady w bits numWin v` constrains EVERY position: the Cuccaro block
`[1+2w, 1+2w+2bits+1)` is pinned to `false` by the carry/augend/addend conjuncts
(carry `1+2w`, augend `1+2w+2i+1`, addend `1+2w+2i+2`, `i<bits` — exactly the
`2·bits+1` block positions); the flag is pinned by the flag conjunct; everything
else is pinned to `mulInputOf cuccaroAdder w bits numWin v` by the frame
conjunct.  Hence any two `ModNMulReady`-states with the SAME value are equal. -/

/-- **`ModNMulReady` is rigid.**  Two states satisfying `ModNMulReady w bits
    numWin v` for the same `v` are equal as functions. -/
theorem ModNMulReady_rigid {w bits numWin v : Nat} {f g : Nat → Bool}
    (hf : ModNMulReady w bits numWin v f) (hg : ModNMulReady w bits numWin v g) :
    f = g := by
  obtain ⟨hfF, hfD, hfC, hfG, hfV⟩ := hf
  obtain ⟨hgF, hgD, hgC, hgG, hgV⟩ := hg
  funext p
  -- Case: flag position.
  by_cases hpflag : p = 1 + 2 * w + (2 * bits + 1) + numWin * w
  · subst hpflag; rw [hfG, hgG]
  -- Case: inside the Cuccaro block `[1+2w, 1+2w+2bits+1)`.
  by_cases hpblock : inBlock (1 + 2 * w) (2 * bits + 1) p
  · -- `p ∈ [1+2w, 1+2w+2bits+1)`: carry, augend, or addend.
    obtain ⟨hlo, hhi⟩ := hpblock
    by_cases hpcarry : p = 1 + 2 * w
    · subst hpcarry; rw [hfC, hgC]
    · -- `p = 1+2w + r` with `1 ≤ r ≤ 2bits`; odd r → augend `i=(r-1)/2`,
      -- even r → addend `i=(r-2)/2`.
      have hr : ∃ r, 1 ≤ r ∧ r ≤ 2 * bits ∧ p = 1 + 2 * w + r := by
        exact ⟨p - (1 + 2 * w), by omega, by omega, by omega⟩
      obtain ⟨r, hr1, hr2, hrp⟩ := hr
      rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- r = 2k even, `k ≥ 1`, addend index `k-1`: `p = 1+2w+2(k-1)+2`.
        have hkrange : k - 1 < bits := by omega
        have hpeq : p = 1 + 2 * w + 2 * (k - 1) + 2 := by omega
        rw [hpeq, hfD (k - 1) hkrange, hgD (k - 1) hkrange]
      · -- r = 2k+1 odd, augend index `k`: `p = 1+2w+2k+1`.
        have hkrange : k < bits := by omega
        have hpeq : p = 1 + 2 * w + 2 * k + 1 := by omega
        rw [hpeq, hfV k hkrange, hgV k hkrange]
  · -- Otherwise: frame conjunct pins both to `mulInputOf`.
    rw [hfF p hpblock hpflag, hgF p hpblock hpflag]

/-! ## §5. HEADLINE — the full round trip on the data band. -/

/-- **HEADLINE — in-place modular multiply on the big-endian data band.**
    For `f` whose big-endian data band `[0,bits)` decodes to `x` (the
    `encodeDataZeroAnc` convention, `DataBandReady`), with `x < N`,
    `numWin·w = bits`, the data band below the Cuccaro block (`bits ≤ 1+2w`),
    `0 < N`, `2·N ≤ 2^bits`, and `c` invertible mod `N` (`cinv < N`,
    `c·cinv ≡ 1`):  after `inPlaceMulData`, the data band `[0,bits)` decodes to
    `(c·x) % N` in the SAME big-endian convention, the `ModNMulReady` scratch
    band is restored clean, and positions off the data band are framed.

    PROOF.  `readyBridge` establishes `ModNMulReady x`
    (`readyBridge_establishes_ModNMulReady`); `windowedModNMulInPlace_correct`
    upgrades that to `ModNMulReady ((c·x)%N)`; `reverse readyBridge` CANCELS the
    bridge (`applyNat_reverse_cancel`), which by injectivity is exactly the
    `DataBandReady` state at `(c·x)%N` — i.e. the data band carries `(c·x)%N`
    big-endian and the scratch band is clean again. -/
theorem inPlaceMulData_apply
    (w bits N numWin c cinv anc x D : Nat)
    (hw : 0 < w) (hbits : 0 < bits) (hsep : bits ≤ 1 + 2 * w)
    (hbw : numWin * w = bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hx : x < N) (hcinv : cinv < N) (hinv : c * cinv % N = 1)
    (hD : yBase w bits + bits < D)
    (f : Nat → Bool) (hf : DataBandReady bits anc x f) :
    DataBandReady bits anc ((c * x) % N)
      (Gate.applyNat (inPlaceMulData w bits N numWin c cinv) f) := by
  have hN_le : N ≤ 2 ^ bits := by omega
  have hxbits : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN_le
  have hcxlt : (c * x) % N < N := Nat.mod_lt _ hN_pos
  have hcxbits : (c * x) % N < 2 ^ bits := Nat.lt_of_lt_of_le hcxlt hN_le
  set cx : Nat := (c * x) % N with hcxdef
  -- Step 1: bridge establishes `ModNMulReady x`.
  have hready_x :
      ModNMulReady w bits numWin x (Gate.applyNat (readyBridge w bits) f) :=
    readyBridge_establishes_ModNMulReady w bits numWin anc x hbits hsep hbw
      hxbits f hf
  -- Step 2: the multiply upgrades to `ModNMulReady cx` of the multiply output `g'`.
  set g' : Nat → Bool :=
    Gate.applyNat (windowedModNMulInPlace w bits c cinv N numWin)
      (Gate.applyNat (readyBridge w bits) f) with hg'def
  have hready_cx : ModNMulReady w bits numWin cx g' :=
    windowedModNMulInPlace_correct w bits c cinv N numWin x hw hbw hN_pos hN2
      hx hcinv hinv _ hready_x
  -- The canonical `DataBandReady` witness for `cx` (data band = `cx`, clean above).
  set wcx : Nat → Bool :=
    (fun p => if p < bits then encodeDataZeroAnc bits anc cx p else false) with hwcxdef
  have hwcx_ready : DataBandReady bits anc cx wcx := by
    refine ⟨?_, ?_⟩
    · intro i hi; simp only [hwcxdef, if_pos hi]
    · intro p hp; simp only [hwcxdef, if_neg (by omega : ¬ p < bits)]
  -- Forward lemma on the witness: `readyBridge wcx` is `ModNMulReady cx`.
  have hready_wcx :
      ModNMulReady w bits numWin cx (Gate.applyNat (readyBridge w bits) wcx) :=
    readyBridge_establishes_ModNMulReady w bits numWin anc cx hbits hsep hbw
      hcxbits wcx hwcx_ready
  -- RIGIDITY: both `g'` and `readyBridge wcx` are `ModNMulReady cx`, hence equal.
  have heq : Gate.applyNat (readyBridge w bits) wcx = g' :=
    ModNMulReady_rigid hready_wcx hready_cx
  -- The bridge is well-typed (needed for the cancel identity).
  have hbr_wt : Gate.WellTyped D (readyBridge w bits) :=
    readyBridge_wellTyped w bits D hbits hsep hD
  -- The whole `inPlaceMulData f` is `reverse readyBridge` applied to `g'`.
  have hunfold :
      Gate.applyNat (inPlaceMulData w bits N numWin c cinv) f
        = Gate.applyNat (Gate.reverse (readyBridge w bits)) g' := by
    show Gate.applyNat (Gate.reverse (readyBridge w bits))
          (Gate.applyNat (windowedModNMulInPlace w bits c cinv N numWin)
            (Gate.applyNat (readyBridge w bits) f))
        = Gate.applyNat (Gate.reverse (readyBridge w bits)) g'
    rw [hg'def]
  -- reverse readyBridge g' = reverse readyBridge (readyBridge wcx) = wcx (cancel).
  rw [hunfold, ← heq, applyNat_reverse_cancel (readyBridge w bits) D hbr_wt wcx]
  exact hwcx_ready

end FormalRV.Audit.GidneyEkera2021.InPlaceMulData
