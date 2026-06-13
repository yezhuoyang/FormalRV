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
open FormalRV.Shor.RunwayWindowed.RunwayLayout (runwayAddKAt runwayAddendIdx)
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

end FormalRV.Shor.RunwayWindowed.RunwayMulCorrect
