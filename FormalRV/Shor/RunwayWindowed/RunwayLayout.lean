/-
  FormalRV.Shor.RunwayWindowed.RunwayLayout — M1 (foundation): the base-shifted
  oblivious-carry-runway adder.
  ════════════════════════════════════════════════════════════════════════════

  The runway-windowed coset multiplier places its accumulator ABOVE the windowed
  lookup zone (control wire `0`, address/AND ancillas `[1, 2w]`), so the runway
  adder must sit at `base = 1 + 2w`, not at `0`.  The verified `runwayAddK` is
  base-0; this module re-bases it to an arbitrary `base` (each segment's Cuccaro
  add shifted by `base`) and proves well-typedness, mirroring
  `RunwayAdderFunctional.runwayAddK_wellTyped` exactly with the base offset.

  REUSE: `segStride`/`segBase` (RunwayAdderFunctional), `cuccaro_n_bit_adder_full`
  + `cuccaro_n_bit_adder_full_wellTyped` + `wellTyped_mono` (FormalRV.BQAlgo).
  NEW: only the `base`-offset (the Cuccaro adder is already `q_start`-parametric,
  so this is a thin re-layout — no new arithmetic).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
import FormalRV.Shor.WindowedModNShor

namespace FormalRV.Shor.RunwayWindowed.RunwayLayout

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
  (segStride segBase wellTyped_mono)
open FormalRV.Shor.WindowedCircuit (copyWindow lookupReadAt)
open FormalRV.BQAlgo.WindowedModNShor
  (wellTyped_foldl_seq_range lookupReadAt_wellTyped copyWindow_wellTyped)

/-- Segment `j`'s width-`(gSep+1)` Cuccaro add, BASED at `base`: the runway is its
    top augend bit.  (= `segAdd gSep j` shifted by `base`; the Cuccaro adder is
    already `q_start`-parametric so this is a pure re-layout.) -/
def segAddAt (gSep base j : Nat) : Gate :=
  cuccaro_n_bit_adder_full (gSep + 1) (base + segBase gSep j)

/-- **The k-segment oblivious-carry-runway adder, BASED at `base`.**  Segments
    added low-to-high (segment `k` outermost), each in its disjoint width-`(gSep+1)`
    Cuccaro block at `[base + segBase j, base + segBase j + segStride)`. -/
def runwayAddKAt (gSep base : Nat) : Nat → Gate
  | 0 => Gate.I
  | k + 1 => Gate.seq (runwayAddKAt gSep base k) (segAddAt gSep base k)

/-- **`runwayAddKAt gSep base k` is well-typed at `base + k·segStride`.**  Each
    segment `j < k` fits in `[base + j·stride, base + (j+1)·stride) ⊆ [0, base +
    k·stride)`.  Mirrors `runwayAddK_wellTyped` with the base offset. -/
theorem runwayAddKAt_wellTyped (gSep base : Nat) :
    ∀ (k : Nat), 0 < k →
      Gate.WellTyped (base + k * segStride gSep) (runwayAddKAt gSep base k) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    refine ⟨?_, ?_⟩
    · -- prefix `runwayAddKAt gSep base m`: well-typed at `base + m·stride ≤ base + (m+1)·stride`.
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        show Gate.WellTyped (base + 1 * segStride gSep) (Gate.I : Gate)
        show 0 < base + 1 * segStride gSep
        unfold segStride; omega
      · refine wellTyped_mono (ih hm) ?_
        have hle : m * segStride gSep ≤ (m + 1) * segStride gSep :=
          Nat.mul_le_mul_right _ (by omega)
        omega
    · -- segment `m`: width-`(gSep+1)` Cuccaro at `base + segBase m`, fits in `base + (m+1)·stride`.
      show Gate.WellTyped (base + (m + 1) * segStride gSep)
        (cuccaro_n_bit_adder_full (gSep + 1) (base + segBase gSep m))
      apply cuccaro_n_bit_adder_full_wellTyped (gSep + 1) (base + segBase gSep m)
      show base + segBase gSep m + 2 * (gSep + 1) + 1 ≤ base + (m + 1) * segStride gSep
      unfold segBase segStride
      have hexp : m * (2 * gSep + 3) + (2 * gSep + 3) = (m + 1) * (2 * gSep + 3) := by ring
      omega

/-! ## M1b — the runway-windowed multiplier layout + fold (defs + well-typedness).

Layout (mirrors the Cuccaro windowed multiplier, accumulator replaced by the
runway register): control wire `0`; lookup address/AND ancillas `[1, 2w]`; runway
accumulator `runwayAddKAt gSep base k` at `base = 1 + 2w` (width `k·segStride`);
multiplicand y-register at `yBase = base + k·segStride`.  The contiguous addend
word (`k·gSep = n` bits) is laid out segment-major into the runway segments'
addend data bits. -/

/-- The segment-major addend index: contiguous word-bit `i` lives in segment
    `i / gSep` at within-segment addend position `i % gSep`. -/
def runwayAddendIdx (gSep base i : Nat) : Nat :=
  cuccaroAdder.addendIdx (base + segBase gSep (i / gSep)) (i % gSep)

/-- Addend positions sit inside the runway register: `runwayAddendIdx … i <
    base + k·segStride` for `i < k·gSep`. -/
theorem runwayAddendIdx_lt (gSep base k i : Nat) (hgSep : 0 < gSep)
    (hi : i < k * gSep) :
    runwayAddendIdx gSep base i < base + k * segStride gSep := by
  unfold runwayAddendIdx segStride segBase
  show base + (i / gSep) * (2 * gSep + 3) + 2 * (i % gSep) + 2
      < base + k * (2 * gSep + 3)
  have hdiv : i / gSep < k := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
  have hmod : i % gSep < gSep := Nat.mod_lt _ hgSep
  have hstep : (i / gSep) * (2 * gSep + 3) + (2 * gSep + 3) ≤ k * (2 * gSep + 3) := by
    have : (i / gSep + 1) * (2 * gSep + 3) ≤ k * (2 * gSep + 3) :=
      Nat.mul_le_mul_right _ hdiv
    calc (i / gSep) * (2 * gSep + 3) + (2 * gSep + 3)
        = (i / gSep + 1) * (2 * gSep + 3) := by ring
      _ ≤ k * (2 * gSep + 3) := this
  omega

/-- **The runway lookup-ADD** (read·add·unread): write the residue word `T[addr]`
    into the segment-major addend register, add it via the runway adder, unread.
    Reuses `lookupReadAt` (adder-agnostic) + `runwayAddKAt`. -/
def runwayLookupAdd (w gSep : Nat) (T : Nat → Nat) (k base : Nat) : Gate :=
  Gate.seq
    (Gate.seq (lookupReadAt w (runwayAddendIdx gSep base) (k * gSep) T)
              (runwayAddKAt gSep base k))
    (lookupReadAt w (runwayAddendIdx gSep base) (k * gSep) T)

/-- **One window step**: copy window `j` of `y` into the address, runway-lookup-add
    the residue word `T_j[v] = (a·(2^w)^j·v) mod N`, then uncopy.  Reuses
    `copyWindow`. -/
def runwayWindowStep (w gSep a N k base yBase j : Nat) : Gate :=
  Gate.seq
    (Gate.seq (copyWindow w yBase j)
              (runwayLookupAdd w gSep (fun v => (a * (2 ^ w) ^ j * v) % N) k base))
    (copyWindow w yBase j)

/-- **The runway-windowed coset multiplier**: fold of window steps (structurally
    identical to `windowedMulOf`, with `runwayAddKAt` as the add and residue
    tables). -/
def runwayWindowedMul (w gSep a N k base yBase numWin : Nat) : Gate :=
  (List.range numWin).foldl
    (fun g j => Gate.seq g (runwayWindowStep w gSep a N k base yBase j)) Gate.I

/-! ### Well-typedness of the fold, at `dim = yBase + numWin·w` with
    `base = 1 + 2w`, `yBase = base + k·segStride`. -/

/-- `runwayLookupAdd` is well-typed: the lookup hits segment-major addend
    positions (inside the runway register, distinct from the AND ancilla), the
    add is `runwayAddKAt_wellTyped`. -/
theorem runwayLookupAdd_wellTyped (w gSep : Nat) (T : Nat → Nat) (k dim : Nat)
    (hw : 0 < w) (hgSep : 0 < gSep) (hk : 0 < k)
    (hbase : 1 + 2 * w + k * segStride gSep ≤ dim) :
    Gate.WellTyped dim (runwayLookupAdd w gSep T k (1 + 2 * w)) := by
  have hlook : Gate.WellTyped dim
      (lookupReadAt w (runwayAddendIdx gSep (1 + 2 * w)) (k * gSep) T) := by
    refine lookupReadAt_wellTyped w (k * gSep) (runwayAddendIdx gSep (1 + 2 * w)) T dim hw
      (by omega) (fun i hi => ?_)
    refine ⟨?_, ?_⟩
    · exact lt_of_lt_of_le (runwayAddendIdx_lt gSep (1 + 2 * w) k i hgSep hi) hbase
    · -- ulookup_and_idx (w-1) = 2w lives in the lookup zone, below base
      have hlow : 1 + 2 * w ≤ runwayAddendIdx gSep (1 + 2 * w) i := by
        unfold runwayAddendIdx
        show 1 + 2 * w ≤ 1 + 2 * w + (i / gSep) * (2 * gSep + 3) + 2 * (i % gSep) + 2
        omega
      unfold ulookup_and_idx; omega
  have hadd : Gate.WellTyped dim (runwayAddKAt gSep (1 + 2 * w) k) :=
    wellTyped_mono (runwayAddKAt_wellTyped gSep (1 + 2 * w) k hk) hbase
  exact ⟨⟨hlook, hadd⟩, hlook⟩

/-- `runwayWindowStep` is well-typed. -/
theorem runwayWindowStep_wellTyped (w gSep a N k numWin j dim : Nat)
    (hw : 0 < w) (hgSep : 0 < gSep) (hk : 0 < k) (hj : j < numWin)
    (hdim : 1 + 2 * w + k * segStride gSep + numWin * w ≤ dim) :
    Gate.WellTyped dim
      (runwayWindowStep w gSep a N k (1 + 2 * w)
        (1 + 2 * w + k * segStride gSep) j) := by
  have hbase : 1 + 2 * w + k * segStride gSep ≤ dim := by omega
  have hjw : ∀ i, i < w → j * w + i < numWin * w := by
    intro i hi
    calc j * w + i < j * w + w := by omega
      _ = (j + 1) * w := by ring
      _ ≤ numWin * w := Nat.mul_le_mul_right w hj
  have hcw : Gate.WellTyped dim
      (copyWindow w (1 + 2 * w + k * segStride gSep) j) := by
    refine copyWindow_wellTyped w (1 + 2 * w + k * segStride gSep) j dim (by omega)
      (fun i hi => ?_) (fun i hi => by omega)
    have := hjw i hi; omega
  exact ⟨⟨hcw, runwayLookupAdd_wellTyped w gSep _ k dim hw hgSep hk hbase⟩, hcw⟩

/-- **`runwayWindowedMul` is well-typed** at `dim ≥ yBase + numWin·w`. -/
theorem runwayWindowedMul_wellTyped (w gSep a N k numWin dim : Nat)
    (hw : 0 < w) (hgSep : 0 < gSep) (hk : 0 < k)
    (hdim : 1 + 2 * w + k * segStride gSep + numWin * w ≤ dim) :
    Gate.WellTyped dim
      (runwayWindowedMul w gSep a N k (1 + 2 * w)
        (1 + 2 * w + k * segStride gSep) numWin) := by
  unfold runwayWindowedMul
  refine wellTyped_foldl_seq_range _ numWin dim (by omega) (fun j hj => ?_)
  exact runwayWindowStep_wellTyped w gSep a N k numWin j dim hw hgSep hk hj hdim

end FormalRV.Shor.RunwayWindowed.RunwayLayout
