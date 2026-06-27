/-
  Audit · Gidney–Ekerå 2021 · THE FULL OUTPUT STATE OF `multiplyAddAt`
  ════════════════════════════════════════════════════════════════════════════
  Characterizing the WHOLE post-state of `WindowedComposedAt.multiplyAddAt` (the
  count-bearing GE2021 per-multiply block) on a `CountGateMulInput` — not merely
  its data band.  The data-band readout
  (`ShorModExpAt.multiplyAddAt_block_isCosetRep` /
  `ShorComposed.countOptimal_multiplyAdd_value`) already records that the shared
  Cuccaro accumulator at `q_start + 2·i + 1` holds the windowed modular product.
  This file adds the THREE structural facts the reduction read-out needs:

    M1  ADDRESS-PRESERVED.    Each window-`k` address register `addrBaseOf` still
        decodes to `window w y k` — the multiply-ADD READS the addresses (the
        babbush QROM only reads them) but never consumes them, so every window's
        `y`-digit survives the whole block.

    M2  PER-WINDOW-ANCILLA-CLEARED.  Each window's `w`-qubit AND-ancilla
        `ancBaseOf` reads `false` afterwards — every `babbushLookupAddAt` measure-
        resets its own QROM ancilla (`unaryQROMAt_anc_cleared`), and neither the
        Cuccaro adder (frame) nor the addend measure-clear touches it.

    M3  FRAME.  Every position strictly BELOW the accumulator block (`p < q_start`)
        and every position at-or-ABOVE the whole stacked region
        (`p ≥ q_start + 2·bits + 1 + numWin·(2·w)`) is preserved bit-for-bit — so
        the data positions `[0, q_start)` and the high anc are untouched.

  PROOF SHAPE.  We mirror `WindowedComposedAt.multiplyAddAt_fold` but carry the
  CONSUMED-window facts (`k < n`) alongside its un-consumed facts (`n ≤ k`): every
  step's `babbushLookupAddAt_frame` (with the ancilla-cleared add-on
  `babbushLookupAddAt_anc_cleared`) preserves the already-processed windows'
  addresses and re-establishes their cleared ancillas, and the frame over a generic
  out-of-region position folds trivially.

  ALSO (S2): `decodeReg_eq_cuccaro_target_val` bridges the GE2021 `decodeReg`
  accumulator read to the Cuccaro `cuccaro_target_val` form (both LSB-first, same
  wires `q_start + 2·i + 1`, weight `2^i`) — used to feed `divModN`'s cuccaro
  output into the `decodeReg`-shaped value chain.

  This chain is dimension/anc-free (everything is `Nat → Bool` + `decodeReg`, no
  upper-wire bound), so no anc parameter is needed.

  Kernel-clean: no `sorry`, no `native_decide`; axioms exactly
  `[propext, Classical.choice, Quot.sound]`.  ADDITIVE.
-/
import FormalRV.Audit.GidneyEkera2021.ShorComposed
import FormalRV.Arithmetic.Cuccaro.CuccaroDecoded

namespace FormalRV.Audit.GidneyEkera2021.ModExpAtFullOutput

open FormalRV.Framework FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute FormalRV.Shor.MeasUncomputeAt
open FormalRV.Shor.WindowedCircuit (addendIdx)
open FormalRV.Shor.WindowedComposed (seqAll)
open FormalRV.Shor.WindowedComposedAt
open FormalRV.Shor.WindowedArith (window)
open FormalRV.Audit.GidneyEkera2021.ShorComposed (CountGateMulInput)

/-! ## §0. S2 — the `decodeReg` ↔ `cuccaro_target_val` bridge.

The GE2021 value chain reads the shared accumulator with
`decodeReg (fun i => q_start + 2·i + 1) bits`; `divModN`'s Cuccaro output is stated
with `cuccaro_target_val bits q_start`.  Both are LSB-first over the SAME wires
`q_start + 2·i + 1` with weight `2^i`, so they are pointwise equal. -/

/-- **S2 — `decodeReg` of the accumulator equals the Cuccaro target decode.**  By
    induction on `bits`: both are LSB-first sums over `q_start + 2·i + 1` with
    weight `2^i`, so they coincide on every `f`. -/
theorem decodeReg_eq_cuccaro_target_val (bits q_start : Nat) (f : Nat → Bool) :
    decodeReg (fun i => q_start + 2 * i + 1) bits f
      = cuccaro_target_val bits q_start f := by
  induction bits with
  | zero => simp [decodeReg, cuccaro_target_val]
  | succ k ih =>
    rw [show decodeReg (fun i => q_start + 2 * i + 1) (k + 1) f
          = decodeReg (fun i => q_start + 2 * i + 1) k f
            + (if f (q_start + 2 * k + 1) then 2 ^ k else 0) from ?_]
    · rw [ih]; rfl
    · unfold decodeReg
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]

/-! ## §1. M2-support — one `babbushLookupAddAt` clears its own AND-ancilla.

The full measured lookup-add `mzList ∘ cuccaro ∘ unaryQROMAt` returns its QROM
AND-ancilla register `[ancBase, ancBase + w)` cleared: `unaryQROMAt_anc_cleared`
clears it, the Cuccaro adder leaves it alone (frame: it is off the accumulator
block `[q_start, q_start + 2·bits + 1)`), and the addend measure-clear does not
hit it (it clears only the addend positions `q_start + 2·j + 2`). -/

/-- **One lookup-add clears its AND-ancilla.**  After `babbushLookupAddAt`, every
    ancilla position `ancBase + i` (`i < w`) reads `false`, PROVIDED the ancilla
    register sits off the accumulator block and off the addend positions
    (`ancBase + i > q_start + 2·bits` suffices for both). -/
theorem babbushLookupAddAt_anc_cleared
    (w W bits : Nat) (T : Nat → Nat) (addrBase ancBase q_start : Nat) (f : Nat → Bool)
    (i : Nat) (hi : i < w) (hWb : W ≤ bits)
    (hanc_hi : q_start + 2 * bits < ancBase + i) :
    EGate.applyNat (babbushLookupAddAt w W T bits addrBase ancBase q_start) f
        (ancBase + i) = false := by
  -- `babbushLookupAddAt = mzList ∘ cuccaro ∘ unaryQROMAt`.
  show EGate.applyNat (mzList ((List.range W).map (addendIdx q_start)))
      (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f))
      (ancBase + i) = false
  -- (1) the addend measure-clear does NOT touch `ancBase + i` (addends `< q_start+2·W ≤ q_start+2·bits`)
  rw [applyNat_mzList_preserves _ _
        (by simp only [List.mem_map, List.mem_range, addendIdx]
            rintro ⟨j, hj, hjeq⟩; omega)]
  -- (2) the Cuccaro adder frame leaves `ancBase + i` (off the block) untouched
  rw [show Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
          (EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f)
          (ancBase + i)
        = EGate.applyNat (unaryQROMAt (addendIdx q_start) W T addrBase ancBase w 0 0) f
            (ancBase + i) from
      cuccaroAdder.frame bits q_start _ (ancBase + i)
        (by intro h
            have hlt : ancBase + i < q_start + (2 * bits + 1) :=
              show ancBase + i < q_start + cuccaroAdder.span bits from h.2
            omega)]
  -- (3) the QROM measure-resets its AND-ancilla
  exact unaryQROMAt_anc_cleared (addendIdx q_start) W T addrBase ancBase w 0 0 f i hi

/-! ## §2. The full-output fold — mirroring `multiplyAddAt_fold` with CONSUMED facts.

We run the first `n` windowed lookup-adds and carry, in addition to the data-band
invariant (already in `multiplyAddAt_fold`), the THREE structural facts for the
CONSUMED windows (`k < n`):

  • the address register of every consumed window still decodes to `window w y k`;
  • the AND-ancilla of every consumed window reads `false`;
  • every out-of-region position is preserved.

Each succ step uses `babbushLookupAddAt_frame` (address preserved, since the step's
gate touches only its OWN window-`n` registers + the accumulator) and
`babbushLookupAddAt_anc_cleared` (the just-processed window `n`'s ancilla cleared).
-/

set_option linter.unusedVariables false in
/-- **The consumed-window fold.**  After the first `n` windowed lookup-adds of
    multiply-add `m`, started from a `CountGateMulInput`:

      (1) every ALREADY-PROCESSED window (`k < n`) has its address register intact;
      (2) every NOT-YET-PROCESSED window (`n ≤ k < numWin`) ALSO has its address
          register intact (no later-window step has touched it yet) — this is the
          fact M1's `k = n` step consumes;
      (3) every consumed window (`k < n`) has its AND-ancilla cleared;
      (4) every out-of-region position (`p < q_start` or
          `p ≥ q_start + 2·bits + 1 + numWin·(2·w)`) is preserved.

    The hypotheses `hw : 0 < w`, `hq : 0 < q_start` are carried for API consistency
    with the data-band lemmas (`countOptimal_multiplyAdd_*`); the structural fold
    itself derives every disjointness purely from the layout offsets, so they are
    not consumed here. -/
theorem multiplyAddAt_consumed_fold
    (w bits numWin y m q_start : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (hw : 0 < w) (hq : 0 < q_start)
    (g0 : Nat → Bool)
    (haddr0 : ∀ k, k < numWin →
      decodeReg (fun i => addrBaseOf w bits q_start k + i) w g0 = window w y k) :
    ∀ n, n ≤ numWin →
      (∀ k, k < n →
          decodeReg (fun i => addrBaseOf w bits q_start k + i) w
            (EGate.applyNat (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0)
          = window w y k)
      ∧ (∀ k, n ≤ k → k < numWin →
          decodeReg (fun i => addrBaseOf w bits q_start k + i) w
            (EGate.applyNat (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0)
          = window w y k)
      ∧ (∀ k, k < n → ∀ t, t < w → EGate.applyNat
          (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0
          (ancBaseOf w bits q_start k + t) = false)
      ∧ (∀ p, (p < q_start ∨ p ≥ q_start + 2 * bits + 1 + numWin * (2 * w)) →
          EGate.applyNat (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0 p
          = g0 p) := by
  intro n hn
  induction n with
  | zero =>
    have hg : EGate.applyNat (seqAll ((List.range 0).map (laAt w bits bits Tfam q_start m))) g0
        = g0 := by simp [seqAll, EGate.applyNat]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk; omega
    · intro k _ hk; rw [decodeReg_ext _ _ _ g0 (fun i _ => by rw [hg])]; exact haddr0 k hk
    · intro k hk; omega
    · intro p _; rw [hg]
  | succ n ih =>
    have hn' : n ≤ numWin := by omega
    have hnW : n < numWin := by omega
    obtain ⟨hAddr, hAddrUn, hAnc, hFrame⟩ := ih hn'
    -- abbreviations for the depth-`n` state and the lookup-add gate
    set gn := EGate.applyNat (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0
      with hgn
    set la := laAt w bits bits Tfam q_start m n with hla
    have hla_def : la = babbushLookupAddAt w bits (Tfam m n) bits
        (addrBaseOf w bits q_start n) (ancBaseOf w bits q_start n) q_start := rfl
    rw [applyNat_seqAll_range_succ, ← hgn, ← hla]
    refine ⟨?_, ?_, ?_, ?_⟩
    -- (1) each consumed window `k < n+1` keeps its address register.
    · intro k hk
      by_cases hkn : k < n
      · -- window `k < n`: untouched by `la` (frame off window-`n` registers + accumulator).
        have hkt : k * (2 * w) + 2 * w ≤ n * (2 * w) :=
          le_trans (le_of_eq (by ring)) (Nat.mul_le_mul_right (2 * w) (by omega : k + 1 ≤ n))
        rw [decodeReg_ext _ _ _ gn (fun i hi => by
          rw [hla_def, babbushLookupAddAt_frame w bits bits (Tfam m n) _ _ q_start gn _
                (le_refl bits) (by simp only [addrBaseOf]; omega)
                (fun i' hi' => by simp only [ancBaseOf, addrBaseOf]; omega)])]
        exact hAddr k hkn
      · -- window `k = n`: just-processed; `la` READS but does not WRITE its address.
        have hkeq : k = n := by omega
        subst hkeq
        rw [decodeReg_ext _ _ _ gn (fun i hi => by
          rw [hla_def, babbushLookupAddAt_frame w bits bits (Tfam m k) _ _ q_start gn _
                (le_refl bits) (by simp only [addrBaseOf]; omega)
                (fun i' hi' => by simp only [ancBaseOf, addrBaseOf]; omega)])]
        -- at depth `n`, window `k = n` is STILL un-consumed, so its address = `window w y k`.
        exact hAddrUn k (le_refl k) hnW
    -- (2) each not-yet-processed window `n+1 ≤ k < numWin` keeps its address register.
    · intro k hk hkW
      have hkt : n * (2 * w) + 2 * w ≤ k * (2 * w) :=
        le_trans (le_of_eq (by ring)) (Nat.mul_le_mul_right (2 * w) (by omega : n + 1 ≤ k))
      rw [decodeReg_ext _ _ _ gn (fun i hi => by
        rw [hla_def, babbushLookupAddAt_frame w bits bits (Tfam m n) _ _ q_start gn _
              (le_refl bits) (by simp only [addrBaseOf]; omega)
              (fun i' hi' => by simp only [ancBaseOf, addrBaseOf]; omega)])]
      exact hAddrUn k (by omega) hkW
    -- (3) each consumed window `k < n+1` has its ancilla cleared.
    · intro k hk t ht
      by_cases hkn : k < n
      · -- window `k < n`: untouched by `la`.
        have hkt : k * (2 * w) + 2 * w ≤ n * (2 * w) :=
          le_trans (le_of_eq (by ring)) (Nat.mul_le_mul_right (2 * w) (by omega : k + 1 ≤ n))
        rw [hla_def, babbushLookupAddAt_frame w bits bits (Tfam m n) _ _ q_start gn _
              (le_refl bits) (by simp only [ancBaseOf, addrBaseOf]; omega)
              (fun i' hi' => by simp only [ancBaseOf, addrBaseOf]; omega)]
        exact hAnc k hkn t ht
      · -- window `k = n`: just-processed; `la` clears its OWN ancilla.
        have hkeq : k = n := by omega
        subst hkeq
        rw [hla_def]
        exact babbushLookupAddAt_anc_cleared w bits bits (Tfam m k) _ _ q_start gn t ht
          (le_refl bits) (by simp only [ancBaseOf, addrBaseOf]; omega)
    -- (4) every out-of-region position is preserved.
    · intro p hp
      -- `window n` sits inside the stacked region: `n·(2w) + 2w ≤ numWin·(2w)`.
      have hnstep : n * (2 * w) + 2 * w ≤ numWin * (2 * w) :=
        le_trans (le_of_eq (by ring)) (Nat.mul_le_mul_right (2 * w) (by omega : n + 1 ≤ numWin))
      rw [hla_def, babbushLookupAddAt_frame w bits bits (Tfam m n) _ _ q_start gn p
            (le_refl bits)
            (by -- `p` is off the accumulator block `[q_start, q_start + 2·bits + 1)`
                rcases hp with hlo | hhi
                · omega
                · omega)
            (by -- `p` is off window `n`'s ancilla register `[ancBaseOf n, ancBaseOf n + w)`
                intro i hi
                rcases hp with hlo | hhi
                · simp only [ancBaseOf, addrBaseOf]; omega
                · simp only [ancBaseOf, addrBaseOf]; omega)]
      exact hFrame p hp

/-! ## §3. The headline M1 / M2 / M3 on the full `multiplyAddAt` block. -/

/-- **M1 — ADDRESS-PRESERVED.**  After the full `multiplyAddAt`, every window-`k`
    address register (`k < numWin`) still decodes to `window w y k`: the multiply-
    ADD reads the addresses (babbush QROM read) but never consumes them. -/
theorem multiplyAddAt_full_M1_address_preserved
    (w bits numWin y m q_start : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (hw : 0 < w) (hq : 0 < q_start)
    (g0 : Nat → Bool)
    (haddr0 : ∀ k, k < numWin →
      decodeReg (fun i => addrBaseOf w bits q_start k + i) w g0 = window w y k)
    (k : Nat) (hk : k < numWin) :
    decodeReg (fun t => addrBaseOf w bits q_start k + t) w
        (EGate.applyNat (multiplyAddAt w bits bits Tfam q_start m numWin) g0)
      = window w y k := by
  rw [show multiplyAddAt w bits bits Tfam q_start m numWin
        = seqAll ((List.range numWin).map (laAt w bits bits Tfam q_start m)) from rfl]
  exact (multiplyAddAt_consumed_fold w bits numWin y m q_start Tfam hw hq g0 haddr0
    numWin (le_refl numWin)).1 k hk

/-- **M2 — PER-WINDOW-ANCILLA-CLEARED.**  After the full `multiplyAddAt`, every
    window's `w`-qubit AND-ancilla register reads `false`. -/
theorem multiplyAddAt_full_M2_anc_cleared
    (w bits numWin y m q_start : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (hw : 0 < w) (hq : 0 < q_start)
    (g0 : Nat → Bool)
    (haddr0 : ∀ k, k < numWin →
      decodeReg (fun i => addrBaseOf w bits q_start k + i) w g0 = window w y k)
    (k : Nat) (hk : k < numWin) (t : Nat) (ht : t < w) :
    EGate.applyNat (multiplyAddAt w bits bits Tfam q_start m numWin) g0
        (ancBaseOf w bits q_start k + t) = false := by
  rw [show multiplyAddAt w bits bits Tfam q_start m numWin
        = seqAll ((List.range numWin).map (laAt w bits bits Tfam q_start m)) from rfl]
  exact (multiplyAddAt_consumed_fold w bits numWin y m q_start Tfam hw hq g0 haddr0
    numWin (le_refl numWin)).2.2.1 k hk t ht

/-- **M3 — FRAME.**  After the full `multiplyAddAt`, every position strictly below
    the accumulator block (`p < q_start`) and every position at-or-above the whole
    stacked region (`p ≥ q_start + 2·bits + 1 + numWin·(2·w)`) is preserved. -/
theorem multiplyAddAt_full_M3_frame
    (w bits numWin y m q_start : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (hw : 0 < w) (hq : 0 < q_start)
    (g0 : Nat → Bool)
    (haddr0 : ∀ k, k < numWin →
      decodeReg (fun i => addrBaseOf w bits q_start k + i) w g0 = window w y k)
    (p : Nat)
    (hp : p < q_start ∨ p ≥ q_start + 2 * bits + 1 + numWin * (2 * w)) :
    EGate.applyNat (multiplyAddAt w bits bits Tfam q_start m numWin) g0 p = g0 p := by
  rw [show multiplyAddAt w bits bits Tfam q_start m numWin
        = seqAll ((List.range numWin).map (laAt w bits bits Tfam q_start m)) from rfl]
  exact (multiplyAddAt_consumed_fold w bits numWin y m q_start Tfam hw hq g0 haddr0
    numWin (le_refl numWin)).2.2.2 p hp

/-! ## §4. The packaged full-output characterization on a `CountGateMulInput`.

Bundling M1/M2/M3 on the native clean family the count gate consumes.  (The
DATA-band result `decodeReg (q_start + 2·i + 1) bits out = coset rep` already lives
in `ShorModExpAt.multiplyAddAt_block_isCosetRep` /
`ShorComposed.countOptimal_multiplyAdd_value`; this file does NOT reprove it.) -/

/-- **★ FULL OUTPUT of `multiplyAddAt` on a `CountGateMulInput` ★.**  On the native
    clean family with the windows of `y` pre-loaded, the count-bearing
    `multiplyAddAt` block leaves: (M1) every window's address register holding its
    `y`-digit; (M2) every window's AND-ancilla cleared; (M3) everything below the
    accumulator block and above the whole stacked region untouched.  Together with
    the existing data-band coset readout, this is the complete post-state the
    reduction read-out consumes. -/
theorem multiplyAddAt_full_output
    (w bits numWin y m q_start : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (hw : 0 < w) (hq : 0 < q_start)
    (g0 : Nat → Bool) (hg0 : CountGateMulInput w bits numWin y q_start g0)
    (out : Nat → Bool)
    (hout : out = EGate.applyNat (multiplyAddAt w bits bits Tfam q_start m numWin) g0) :
    -- M1 ADDRESS-PRESERVED
    (∀ k, k < numWin →
        decodeReg (fun t => addrBaseOf w bits q_start k + t) w out = window w y k)
    -- M2 PER-WINDOW-ANCILLA-CLEARED
    ∧ (∀ k, k < numWin → ∀ t, t < w → out (ancBaseOf w bits q_start k + t) = false)
    -- M3 FRAME
    ∧ (∀ p, (p < q_start ∨ p ≥ q_start + 2 * bits + 1 + numWin * (2 * w)) →
        out p = g0 p) := by
  subst hout
  refine ⟨?_, ?_, ?_⟩
  · exact fun k hk =>
      multiplyAddAt_full_M1_address_preserved w bits numWin y m q_start Tfam hw hq g0
        hg0.addr0 k hk
  · exact fun k hk t ht =>
      multiplyAddAt_full_M2_anc_cleared w bits numWin y m q_start Tfam hw hq g0
        hg0.addr0 k hk t ht
  · exact fun p hp =>
      multiplyAddAt_full_M3_frame w bits numWin y m q_start Tfam hw hq g0
        hg0.addr0 p hp

end FormalRV.Audit.GidneyEkera2021.ModExpAtFullOutput
