/-
  FormalRV.Shor.RunwayWindowed.RunwayMulCorrect — M3 core: the runway add at base.
  ════════════════════════════════════════════════════════════════════════════

  The single-add correctness of the re-based runway adder, pulled through the
  `runwayAddKAt_downshift` bridge from the base-0 `runwayAddK_contiguous`.  A
  single runway add needs only input-cleanliness (`kClean`) — the 1-bit runway
  absorbs the single carry, and the contiguous reading folds it by place value —
  so NO no-overflow hypothesis is needed here (that enters only for the windowed
  FOLD, where the accumulator grows; M4).

  REUSE: `runwayAddKAt_downshift` (RunwayShift), `runwayAddK_contiguous` +
  `contiguousDecode`/`contiguousAugend`/`contiguousAddend`/`kClean` (the verified
  base-0 runway adder).  NEW: only the one-line transport.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.RunwayWindowed.RunwayShift
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderContiguous
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd

namespace FormalRV.Shor.RunwayWindowed.RunwayMulCorrect

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.RunwayWindowed.RunwayLayout
  (runwayAddKAt runwayAddendIdx runwayWindowStep runwayLookupAdd)
open FormalRV.Shor.RunwayWindowed.RunwayShift (runwayAddKAt_downshift)
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
  (runwayAddK kClean segStride segBase segReg)
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderContiguous
  (contiguousDecode contiguousAugend contiguousAddend runwayAddK_contiguous)
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd
  (IterReady iterGate runwayAddK_iter_contiguous)
open FormalRV.Shor.WindowedCircuit
  (copyWindow lookupReadAt encodeReg copyWindow_loads_window copyWindow_frame
   lookupReadAt_selects_word lookupReadAt_frame decodeReg_eq_mod_of_testBit)

/-- **The runway add at base.**  Reading the re-based runway adder's output via
    the base-shifted contiguous decode (= the base-0 contiguous decode of the
    down-shifted state) yields `augend + addend`, exactly the base-0
    `runwayAddK_contiguous` — transported through `runwayAddKAt_downshift`.  Only
    `kClean` (down-shifted) is required; a single add never overflows the runway. -/
theorem runwayAddKAt_contiguous_at_base (gSep base k : Nat) (f : Nat → Bool)
    (hclean : kClean gSep k (fun q => f (q + base))) :
    contiguousDecode gSep k
        (fun q => Gate.applyNat (runwayAddKAt gSep base k) f (q + base))
      = contiguousAugend gSep k (fun q => f (q + base))
        + contiguousAddend gSep k (fun q => f (q + base)) := by
  rw [runwayAddKAt_downshift]
  exact runwayAddK_contiguous gSep k (fun q => f (q + base)) hclean

/-- **The runway add at base, from an `IterReady` state (the fold's add).**  This
    is the version the windowed FOLD needs: between windows the runways CARRY the
    deferred carries (`IterReady`, not clean), and each window adds a fresh word
    (single add, `t = 1`).  Transports `runwayAddK_iter_contiguous` (`t = 1`)
    through `runwayAddKAt_downshift`; needs the per-segment no-overflow `hno`
    (the M2/R4 hypothesis, discharged from the padding by the fold). -/
theorem runwayAddKAt_iter_at_base (gSep base k : Nat) (f : Nat → Bool)
    (hready : IterReady gSep k (fun q => f (q + base)))
    (hno : ∀ m, m < k →
      segReg gSep m (fun q => f (q + base))
        + 1 * decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep
            (fun q => f (q + base))
        < 2 ^ (gSep + 1)) :
    contiguousDecode gSep k
        (fun q => Gate.applyNat (runwayAddKAt gSep base k) f (q + base))
      = contiguousDecode gSep k (fun q => f (q + base))
        + contiguousAddend gSep k (fun q => f (q + base)) := by
  rw [runwayAddKAt_downshift]
  have h := runwayAddK_iter_contiguous gSep k 1 (fun q => f (q + base)) hready hno
  simpa using h

/-! ## M3 window-step prerequisites — the segment-major addend index facts. -/

/-- The segment-major addend positions sit strictly above the lookup zone
    (`> 2w`), as `lookupReadAt_selects_word`/`_frame` require. -/
theorem runwayAddendIdx_gt_two_w (gSep w i : Nat) :
    2 * w < runwayAddendIdx gSep (1 + 2 * w) i := by
  unfold runwayAddendIdx
  show 2 * w < 1 + 2 * w + segBase gSep (i / gSep) + 2 * (i % gSep) + 2
  omega

/-- The segment-major addend index is injective: it determines the segment
    `i / gSep` and the within-segment offset `i % gSep`, hence `i`. -/
theorem runwayAddendIdx_inj (gSep base : Nat) (hgSep : 0 < gSep) (i i' : Nat)
    (h : runwayAddendIdx gSep base i = runwayAddendIdx gSep base i') : i = i' := by
  have hr : i % gSep < gSep := Nat.mod_lt _ hgSep
  have hr' : i' % gSep < gSep := Nat.mod_lt _ hgSep
  have hE : (i / gSep) * (2 * gSep + 3) + 2 * (i % gSep)
      = (i' / gSep) * (2 * gSep + 3) + 2 * (i' % gSep) := by
    have h' : 1 + 2 * base + (i / gSep) * (2 * gSep + 3) + 2 * (i % gSep) + 2
        = 1 + 2 * base + (i' / gSep) * (2 * gSep + 3) + 2 * (i' % gSep) + 2 := by
      have : base + (i / gSep) * (2 * gSep + 3) + 2 * (i % gSep) + 2
          = base + (i' / gSep) * (2 * gSep + 3) + 2 * (i' % gSep) + 2 := h
      omega
    omega
  -- The quotient `i/gSep` is determined (the `2·(i%gSep)` term is `< 2gSep+3`).
  have hq : i / gSep = i' / gSep := by
    have h1 : (i / gSep) * (2 * gSep + 3) < (i' / gSep + 1) * (2 * gSep + 3) := by
      calc (i / gSep) * (2 * gSep + 3)
          ≤ (i / gSep) * (2 * gSep + 3) + 2 * (i % gSep) := Nat.le_add_right _ _
        _ = (i' / gSep) * (2 * gSep + 3) + 2 * (i' % gSep) := hE
        _ < (i' / gSep) * (2 * gSep + 3) + (2 * gSep + 3) := by omega
        _ = (i' / gSep + 1) * (2 * gSep + 3) := by ring
    have h2 : (i' / gSep) * (2 * gSep + 3) < (i / gSep + 1) * (2 * gSep + 3) := by
      calc (i' / gSep) * (2 * gSep + 3)
          ≤ (i' / gSep) * (2 * gSep + 3) + 2 * (i' % gSep) := Nat.le_add_right _ _
        _ = (i / gSep) * (2 * gSep + 3) + 2 * (i % gSep) := hE.symm
        _ < (i / gSep) * (2 * gSep + 3) + (2 * gSep + 3) := by omega
        _ = (i / gSep + 1) * (2 * gSep + 3) := by ring
    have hlt1 : i / gSep < i' / gSep + 1 :=
      Nat.lt_of_mul_lt_mul_right h1
    have hlt2 : i' / gSep < i / gSep + 1 :=
      Nat.lt_of_mul_lt_mul_right h2
    omega
  have hrmod : i % gSep = i' % gSep := by rw [hq] at hE; omega
  calc i = gSep * (i / gSep) + i % gSep := (Nat.div_add_mod i gSep).symm
    _ = gSep * (i' / gSep) + i' % gSep := by rw [hq, hrmod]
    _ = i' := Nat.div_add_mod i' gSep

/-! ## M3 window-step — the lookup-write half.

`yBaseR w gSep k = 1 + 2w + k·segStride` is the runway multiplier's y-register
base (above the runway accumulator).  The lookup-write half (`copyWindow ;
lookupReadAt`) loads window `j` of `y` into the address and writes the residue
word `(a·(2^w)^j·window) mod N` into the segment-major addend register. -/

/-- The runway multiplier's y-register base: above ctrl(0), lookup `[1,2w]`, and
    the `k`-segment runway accumulator at `[1+2w, 1+2w+k·segStride)`. -/
def yBaseR (w gSep k : Nat) : Nat := 1 + 2 * w + k * segStride gSep

/-- **The lookup-write writes the residue word into the segment-major addend.**
    After `copyWindow` loads window `j` of `y` into the address (reusing
    `copyWindow_loads_window`), `lookupReadAt` writes `(a·(2^w)^j·window_j) mod N`
    into the addend (reusing `lookupReadAt_selects_word` with the segment-major
    `pos = runwayAddendIdx`, discharged by `runwayAddendIdx_gt_two_w`/`_inj`). -/
theorem runway_lookup_writes_word (w gSep a N k numWin y j : Nat) (g : Nat → Bool)
    (hw : 0 < w) (hgSep : 0 < gSep) (hj : j < numWin)
    (hctrl : g ulookup_ctrl_idx = true)
    (haddr_clean : ∀ i, i < w → g (ulookup_address_idx i) = false)
    (hand_clean : ∀ i, i < w → g (ulookup_and_idx i) = false)
    (haddend_clean : ∀ i, i < k * gSep → g (runwayAddendIdx gSep (1 + 2 * w) i) = false)
    (hy : ∀ i, i < w →
      g (yBaseR w gSep k + j * w + i)
        = encodeReg (yBaseR w gSep k) (numWin * w) y (yBaseR w gSep k + j * w + i)) :
    ∀ i, i < k * gSep →
      Gate.applyNat
          (lookupReadAt w (runwayAddendIdx gSep (1 + 2 * w)) (k * gSep)
            (fun v => (a * (2 ^ w) ^ j * v) % N))
          (Gate.applyNat (copyWindow w (yBaseR w gSep k) j) g)
          (runwayAddendIdx gSep (1 + 2 * w) i)
        = ((a * (2 ^ w) ^ j * WindowedArith.window w y j) % N).testBit i := by
  intro i hi
  set g1 : Nat → Bool := Gate.applyNat (copyWindow w (yBaseR w gSep k) j) g with hg1
  -- copyWindow controls (y-wires) are never address wires (y-base > 2w).
  have hctrl_addr : ∀ i k', i < w → k' < w →
      yBaseR w gSep k + j * w + i ≠ ulookup_address_idx k' := by
    intro i k' hi hk'
    unfold yBaseR ulookup_address_idx; omega
  -- g1 facts (copyWindow loads the window; frames the rest).
  have hg1_addr : ∀ i, i < w →
      g1 (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i :=
    fun i hi => copyWindow_loads_window w (yBaseR w gSep k) numWin y j g
      hctrl_addr haddr_clean hy hj i hi
  have hg1_ctrl : g1 ulookup_ctrl_idx = true := by
    rw [hg1, copyWindow_frame w (yBaseR w gSep k) j g _
      (fun i hi => by unfold ulookup_ctrl_idx ulookup_address_idx; omega)]
    exact hctrl
  have hg1_and : ∀ i, i < w → g1 (ulookup_and_idx i) = false := by
    intro i hi
    rw [hg1, copyWindow_frame w (yBaseR w gSep k) j g _
      (fun k' hk' => by unfold ulookup_and_idx ulookup_address_idx; omega)]
    exact hand_clean i hi
  have hg1_addend : ∀ i, i < k * gSep →
      g1 (runwayAddendIdx gSep (1 + 2 * w) i) = false := by
    intro i hi
    rw [hg1, copyWindow_frame w (yBaseR w gSep k) j g _
      (fun k' hk' => by
        have := runwayAddendIdx_gt_two_w gSep w i
        unfold ulookup_address_idx; omega)]
    exact haddend_clean i hi
  -- the lookup writes the word into the addend (selects T at the window address).
  rw [lookupReadAt_selects_word w (k * gSep) (fun v => (a * (2 ^ w) ^ j * v) % N)
        (runwayAddendIdx gSep (1 + 2 * w)) g1 (WindowedArith.window w y j)
        hw (WindowedArith.window_lt w y j) hg1_ctrl hg1_addr hg1_and
        (fun i _ => runwayAddendIdx_gt_two_w gSep w i)
        (fun a' b' _ _ h => runwayAddendIdx_inj gSep (1 + 2 * w) hgSep a' b' h) i hi,
      hg1_addend i hi, Bool.false_xor]

/-! ## M3 window-step — the addend-reassembly connection.

`contiguousAddend` of a state whose segment-major addend data bits encode `word`
(segment `m`'s data bit `i'` = `word.testBit (m·gSep + i')`) reassembles to
`word % 2^(k·gSep)`.  This is the base-`2^gSep` digit-reconstruction connecting
the lookup-write (which writes `word`'s bits at `runwayAddendIdx = base +
addendIdx(segBase m) i'`, so the DOWN-SHIFT reads them at `addendIdx(segBase m)
i'`) to the down-shifted `contiguousAddend` consumed by the add-at-base.
Mirrors `decodeReg_eq_mod_of_testBit`'s own induction (`Nat.mod_mul` +
`Nat.testBit_div_two_pow`). -/
theorem contiguousAddend_reassembly (gSep word : Nat) :
    ∀ (k : Nat) (h : Nat → Bool),
      (∀ m i', m < k → i' < gSep →
        h (cuccaroAdder.addendIdx (segBase gSep m) i') = word.testBit (m * gSep + i')) →
      contiguousAddend gSep k h = word % 2 ^ (k * gSep) := by
  intro k
  induction k with
  | zero => intro h _; simp [contiguousAddend, Nat.mod_one]
  | succ m ih =>
    intro h hbits
    show contiguousAddend gSep m h
        + decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep h * 2 ^ (m * gSep)
      = word % 2 ^ ((m + 1) * gSep)
    rw [ih h (fun m' i' hm' hi' => hbits m' i' (Nat.lt_succ_of_lt hm') hi'),
        decodeReg_eq_mod_of_testBit (cuccaroAdder.addendIdx (segBase gSep m)) gSep
          (word / 2 ^ (m * gSep)) h
          (fun i' hi' => by
            rw [hbits m i' (Nat.lt_succ_self m) hi', Nat.testBit_div_two_pow,
                Nat.add_comm i' (m * gSep)]),
        show (m + 1) * gSep = m * gSep + gSep from by ring, pow_add, Nat.mod_mul]
    ring

/-! ## M3 window-step — the augend-only congruence.

`contiguousDecode` reads ONLY the segments' augend registers (`segReg =
decodeReg (augendIdx (segBase m)) (gSep+1)`).  So two states agreeing on every
augend position have equal contiguous decode — even if they differ on the
ADDEND (which the lookup-write/unwrite changes, and which sits BELOW `segBase`,
so the all-positions-below `contiguousDecode_congr` cannot bridge it). -/
theorem contiguousDecode_augend_congr (gSep : Nat) :
    ∀ (k : Nat) (f g : Nat → Bool),
      (∀ m i', m < k → i' < gSep + 1 →
        f (cuccaroAdder.augendIdx (segBase gSep m) i')
          = g (cuccaroAdder.augendIdx (segBase gSep m) i')) →
      contiguousDecode gSep k f = contiguousDecode gSep k g := by
  intro k
  induction k with
  | zero => intro f g _; rfl
  | succ m ih =>
      intro f g hagree
      show contiguousDecode gSep m f + segReg gSep m f * 2 ^ (m * gSep)
        = contiguousDecode gSep m g + segReg gSep m g * 2 ^ (m * gSep)
      have h1 : contiguousDecode gSep m f = contiguousDecode gSep m g :=
        ih f g (fun m' i' hm' hi' => hagree m' i' (Nat.lt_succ_of_lt hm') hi')
      have h2 : segReg gSep m f = segReg gSep m g :=
        decodeReg_ext (cuccaroAdder.augendIdx (segBase gSep m)) (gSep + 1) f g
          (fun i' hi' => hagree m i' (Nat.lt_succ_self m) hi')
      rw [h1, h2]

/-! ## M3 window-step — full-state frames (the lookup-I/O touches neither the
accumulator's augend/carry/addend-top nor anything `≥ base` except the addend
data).  These let `contiguousDecode`/`IterReady` (read at augend/carry/addend-top
positions) pass UNCHANGED through `copyWindow` and the lookup-write/unwrite. -/

/-- `copyWindow` (address register in the lookup zone `[1,2w]`) fixes every
    position at or above the accumulator base `1+2w`. -/
theorem copyWindow_fixes_above (w yBase j : Nat) (f : Nat → Bool) (p : Nat)
    (hp : 1 + 2 * w ≤ p) :
    Gate.applyNat (copyWindow w yBase j) f p = f p :=
  copyWindow_frame w yBase j f p (fun i hi => by unfold ulookup_address_idx; omega)

/-- **The runway segment-offset disjointness.**  A position `base + segBase m + o`
    whose within-segment offset `o` is below `segStride` but is NOT an even number
    in `[2, 2gSep]` — i.e. the carry-in (`o=0`), an augend bit (`o` odd), or the
    addend-top (`o = 2gSep+2`) — is NEVER a segment-major addend position
    `runwayAddendIdx`.  (The addend-DATA bits are exactly the even offsets
    `2,4,…,2gSep`.)  Segment-uniqueness by the div/mod bound + parity. -/
theorem segOffset_ne_runwayAddendIdx (gSep base m o pos i : Nat) (hgSep : 0 < gSep)
    (ho_lt : o < 2 * gSep + 3) (ho_not : ∀ t, t < gSep → o ≠ 2 * t + 2)
    (hpos : pos = base + segBase gSep m + o) :
    pos ≠ runwayAddendIdx gSep base i := by
  subst hpos
  intro hEq
  have hr : i % gSep < gSep := Nat.mod_lt _ hgSep
  have hlin : base + segBase gSep m + o
      = base + segBase gSep (i / gSep) + 2 * (i % gSep) + 2 := hEq
  rcases Nat.lt_trichotomy m (i / gSep) with hlt | heq | hgt
  · have hstep : segBase gSep (m + 1) ≤ segBase gSep (i / gSep) := by
      unfold segBase segStride; exact Nat.mul_le_mul_right _ (by omega)
    have hexp : segBase gSep (m + 1) = segBase gSep m + (2 * gSep + 3) := by
      unfold segBase segStride; ring
    omega
  · rw [heq] at hlin
    exact ho_not (i % gSep) hr (by omega)
  · have hstep : segBase gSep (i / gSep + 1) ≤ segBase gSep m := by
      unfold segBase segStride; exact Nat.mul_le_mul_right _ (by omega)
    have hexp : segBase gSep (i / gSep + 1) = segBase gSep (i / gSep) + (2 * gSep + 3) := by
      unfold segBase segStride; ring
    omega

/-- **The lookup-I/O frame.**  Through `lookupReadAt ∘ copyWindow` (the lookup-write
    half of a window step), every position `≥ base` that is NOT a segment-major
    addend position is left UNCHANGED: `copyWindow` only touches the address zone
    (`< base`); `lookupReadAt` only touches its `pos` targets (`runwayAddendIdx`). -/
theorem windowIO_frame (w gSep k yBase j : Nat) (T : Nat → Nat) (g : Nat → Bool)
    (p : Nat) (hp_base : 1 + 2 * w ≤ p)
    (hp_addend : ∀ i, i < k * gSep → p ≠ runwayAddendIdx gSep (1 + 2 * w) i) :
    Gate.applyNat (lookupReadAt w (runwayAddendIdx gSep (1 + 2 * w)) (k * gSep) T)
        (Gate.applyNat (copyWindow w yBase j) g) p
      = g p := by
  rw [lookupReadAt_frame w (k * gSep) T (runwayAddendIdx gSep (1 + 2 * w))
        (Gate.applyNat (copyWindow w yBase j) g)
        (fun i _ => runwayAddendIdx_gt_two_w gSep w i) p hp_addend]
  exact copyWindow_fixes_above w yBase j g p hp_base

/-! ## M3 — THE WINDOW-STEP VALUE THEOREM (the composition).

One full window step (`copyWindow ; lookupReadAt-write ; runwayAddKAt ;
lookupReadAt-unwrite ; copyWindow-uncopy`) ADDS the residue word
`word_j = (a·(2^w)^j·window_j) mod N` (chunked to `2^(k·gSep)`) to the contiguous
accumulator value, threading the five stages on the down-shifted state:

  g  --copy-->  g₁ --write-->  g₂ --runwayAdd-->  g₃ --unwrite-->  g₄ --uncopy-->  g₅

The cleanup stages (`g₄, g₅`) leave the AUGEND untouched, so the value is fixed
once the add lands (`g₃`); the add lands the word via `runwayAddKAt_iter_at_base`
fed by the lookup-write (`runway_lookup_writes_word` + `contiguousAddend_reassembly`).
`IterReady`/the no-overflow bound for the add are imported through the
full-state frames (`windowIO_frame`, `segOffset_ne_runwayAddendIdx`). -/
theorem runwayWindowStep_value (w gSep a N k numWin y j : Nat) (g : Nat → Bool)
    (hw : 0 < w) (hgSep : 0 < gSep) (hj : j < numWin)
    (hctrl : g ulookup_ctrl_idx = true)
    (haddr_clean : ∀ i, i < w → g (ulookup_address_idx i) = false)
    (hand_clean : ∀ i, i < w → g (ulookup_and_idx i) = false)
    (haddend_clean : ∀ i, i < k * gSep → g (runwayAddendIdx gSep (1 + 2 * w) i) = false)
    (hy : ∀ i, i < w → g (yBaseR w gSep k + j * w + i)
        = encodeReg (yBaseR w gSep k) (numWin * w) y (yBaseR w gSep k + j * w + i))
    (hready : IterReady gSep k (fun q => g (q + (1 + 2 * w))))
    (hno : ∀ m, m < k →
      segReg gSep m (fun q => g (q + (1 + 2 * w)))
        + ((a * (2 ^ w) ^ j * WindowedArith.window w y j) % N / 2 ^ (m * gSep)) % 2 ^ gSep
        < 2 ^ (gSep + 1)) :
    contiguousDecode gSep k
        (fun q => Gate.applyNat
          (runwayWindowStep w gSep a N k (1 + 2 * w) (yBaseR w gSep k) j) g (q + (1 + 2 * w)))
      = contiguousDecode gSep k (fun q => g (q + (1 + 2 * w)))
        + (a * (2 ^ w) ^ j * WindowedArith.window w y j) % N % 2 ^ (k * gSep) := by
  simp only [runwayWindowStep, runwayLookupAdd, Gate.applyNat_seq]
  set T : Nat → Nat := fun v => (a * (2 ^ w) ^ j * v) % N with hT
  set word : Nat := (a * (2 ^ w) ^ j * WindowedArith.window w y j) % N with hword
  set g1 := Gate.applyNat (copyWindow w (yBaseR w gSep k) j) g with hg1
  set g2 := Gate.applyNat (lookupReadAt w (runwayAddendIdx gSep (1 + 2 * w)) (k * gSep) T) g1
    with hg2
  set g3 := Gate.applyNat (runwayAddKAt gSep (1 + 2 * w) k) g2 with hg3
  set g4 := Gate.applyNat (lookupReadAt w (runwayAddendIdx gSep (1 + 2 * w)) (k * gSep) T) g3
    with hg4
  set g5 := Gate.applyNat (copyWindow w (yBaseR w gSep k) j) g4 with hg5
  -- (1) the augend register is UNTOUCHED by the lookup-write∘copyWindow (g₂ vs g).
  have haugend_g2 : ∀ m i', m < k → i' < gSep + 1 →
      g2 (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w))
        = g (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w)) := by
    intro m i' hm hi'
    rw [hg2, hg1]
    exact windowIO_frame w gSep k (yBaseR w gSep k) j T g
      (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w)) (by omega)
      (fun i _ => segOffset_ne_runwayAddendIdx gSep (1 + 2 * w) m (2 * i' + 1) _ i hgSep
        (by omega) (fun t ht => by omega)
        (by show segBase gSep m + 2 * i' + 1 + (1 + 2 * w)
              = 1 + 2 * w + segBase gSep m + (2 * i' + 1); omega))
  -- (2) the lookup-write lands the residue word's bits into the segment-major addend.
  have hbits : ∀ m i', m < k → i' < gSep →
      g2 (cuccaroAdder.addendIdx (segBase gSep m) i' + (1 + 2 * w))
        = word.testBit (m * gSep + i') := by
    intro m i' hm hi'
    have hlt : m * gSep + i' < k * gSep := by
      have h1 : (m + 1) * gSep ≤ k * gSep := Nat.mul_le_mul_right _ (by omega)
      have h2 : (m + 1) * gSep = m * gSep + gSep := by ring
      omega
    have hd : (m * gSep + i') / gSep = m := by
      rw [Nat.add_comm (m * gSep) i', Nat.add_mul_div_right i' m hgSep,
          Nat.div_eq_of_lt hi', Nat.zero_add]
    have hmod : (m * gSep + i') % gSep = i' := by
      rw [Nat.add_comm (m * gSep) i', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi']
    have hidx : cuccaroAdder.addendIdx (segBase gSep m) i' + (1 + 2 * w)
        = runwayAddendIdx gSep (1 + 2 * w) (m * gSep + i') := by
      unfold runwayAddendIdx
      rw [hd, hmod]
      show segBase gSep m + 2 * i' + 2 + (1 + 2 * w)
        = 1 + 2 * w + segBase gSep m + 2 * i' + 2
      omega
    rw [hidx, hg2, hg1]
    exact runway_lookup_writes_word w gSep a N k numWin y j g hw hgSep hj hctrl
      haddr_clean hand_clean haddend_clean hy (m * gSep + i') hlt
  -- (3) the runway is still `IterReady` at g₂ (carry-in / addend-top are framed).
  have hready_g2 : IterReady gSep k (fun q => g2 (q + (1 + 2 * w))) := by
    intro m hm
    obtain ⟨hcarry, htop⟩ := hready m hm
    refine ⟨?_, ?_⟩
    · show g2 (segBase gSep m + (1 + 2 * w)) = false
      rw [hg2, hg1, windowIO_frame w gSep k (yBaseR w gSep k) j T g
            (segBase gSep m + (1 + 2 * w)) (by omega)
            (fun i _ => segOffset_ne_runwayAddendIdx gSep (1 + 2 * w) m 0 _ i hgSep
              (by omega) (fun t ht => by omega) (by omega))]
      exact hcarry
    · show g2 (cuccaroAdder.addendIdx (segBase gSep m) gSep + (1 + 2 * w)) = false
      rw [hg2, hg1, windowIO_frame w gSep k (yBaseR w gSep k) j T g
            (cuccaroAdder.addendIdx (segBase gSep m) gSep + (1 + 2 * w)) (by omega)
            (fun i _ => segOffset_ne_runwayAddendIdx gSep (1 + 2 * w) m (2 * gSep + 2) _ i hgSep
              (by omega) (fun t ht => by omega)
              (by show segBase gSep m + 2 * gSep + 2 + (1 + 2 * w)
                    = 1 + 2 * w + segBase gSep m + (2 * gSep + 2); omega))]
      exact htop
  -- (4) segReg is preserved (augend untouched), and the addend chunk = the word chunk.
  have hsegReg_g2 : ∀ m, m < k →
      segReg gSep m (fun q => g2 (q + (1 + 2 * w)))
        = segReg gSep m (fun q => g (q + (1 + 2 * w))) := by
    intro m hm
    exact decodeReg_ext (cuccaroAdder.augendIdx (segBase gSep m)) (gSep + 1) _ _
      (fun i' hi' => haugend_g2 m i' hm hi')
  have haddend_chunk : ∀ m, m < k →
      decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep (fun q => g2 (q + (1 + 2 * w)))
        = (word / 2 ^ (m * gSep)) % 2 ^ gSep := by
    intro m hm
    refine decodeReg_eq_mod_of_testBit (cuccaroAdder.addendIdx (segBase gSep m)) gSep
      (word / 2 ^ (m * gSep)) (fun q => g2 (q + (1 + 2 * w))) (fun i' hi' => ?_)
    show g2 (cuccaroAdder.addendIdx (segBase gSep m) i' + (1 + 2 * w))
      = (word / 2 ^ (m * gSep)).testBit i'
    rw [hbits m i' hm hi', Nat.testBit_div_two_pow, Nat.add_comm i' (m * gSep)]
  -- (5) the add's no-overflow precondition, transported from `hno` via (4).
  have hno_g2 : ∀ m, m < k →
      segReg gSep m (fun q => g2 (q + (1 + 2 * w)))
        + 1 * decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep
            (fun q => g2 (q + (1 + 2 * w)))
        < 2 ^ (gSep + 1) := by
    intro m hm
    rw [hsegReg_g2 m hm, haddend_chunk m hm, Nat.one_mul]
    exact hno m hm
  -- ── the five-stage value chain ──
  -- (A) g₅ vs g₄: copyWindow-uncopy frames the augend (all `≥ base`).
  have hA : contiguousDecode gSep k (fun q => g5 (q + (1 + 2 * w)))
      = contiguousDecode gSep k (fun q => g4 (q + (1 + 2 * w))) := by
    apply contiguousDecode_augend_congr
    intro m i' hm hi'
    show g5 (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w))
      = g4 (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w))
    rw [hg5]
    exact copyWindow_fixes_above w (yBaseR w gSep k) j g4 _ (by omega)
  -- (B) g₄ vs g₃: lookupReadAt-unwrite frames the augend (augend ≠ addend).
  have hB : contiguousDecode gSep k (fun q => g4 (q + (1 + 2 * w)))
      = contiguousDecode gSep k (fun q => g3 (q + (1 + 2 * w))) := by
    apply contiguousDecode_augend_congr
    intro m i' hm hi'
    show g4 (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w))
      = g3 (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w))
    rw [hg4]
    refine lookupReadAt_frame w (k * gSep) T (runwayAddendIdx gSep (1 + 2 * w)) g3
      (fun i _ => runwayAddendIdx_gt_two_w gSep w i)
      (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w)) (fun i _ => ?_)
    exact segOffset_ne_runwayAddendIdx gSep (1 + 2 * w) m (2 * i' + 1) _ i hgSep
      (by omega) (fun t ht => by omega)
      (by show segBase gSep m + 2 * i' + 1 + (1 + 2 * w)
            = 1 + 2 * w + segBase gSep m + (2 * i' + 1); omega)
  -- (C) g₃ vs g₂: the runway add lands `+ contiguousAddend`.
  have hC : contiguousDecode gSep k (fun q => g3 (q + (1 + 2 * w)))
      = contiguousDecode gSep k (fun q => g2 (q + (1 + 2 * w)))
        + contiguousAddend gSep k (fun q => g2 (q + (1 + 2 * w))) := by
    rw [hg3]
    exact runwayAddKAt_iter_at_base gSep (1 + 2 * w) k g2 hready_g2 hno_g2
  -- (D) g₂ vs g: the augend register is unchanged (so the prior accumulator value).
  have hD : contiguousDecode gSep k (fun q => g2 (q + (1 + 2 * w)))
      = contiguousDecode gSep k (fun q => g (q + (1 + 2 * w))) := by
    apply contiguousDecode_augend_congr
    intro m i' hm hi'
    show g2 (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w))
      = g (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w))
    exact haugend_g2 m i' hm hi'
  -- (E) the addend register reassembles the residue word (chunked).
  have hE : contiguousAddend gSep k (fun q => g2 (q + (1 + 2 * w)))
      = word % 2 ^ (k * gSep) := by
    refine contiguousAddend_reassembly gSep word k (fun q => g2 (q + (1 + 2 * w)))
      (fun m i' hm hi' => ?_)
    show g2 (cuccaroAdder.addendIdx (segBase gSep m) i' + (1 + 2 * w))
      = word.testBit (m * gSep + i')
    exact hbits m i' hm hi'
  rw [hA, hB, hC, hD, hE]

end FormalRV.Shor.RunwayWindowed.RunwayMulCorrect
