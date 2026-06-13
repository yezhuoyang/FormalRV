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

namespace FormalRV.Shor.RunwayWindowed.RunwayLayout

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
  (segStride segBase wellTyped_mono)

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

end FormalRV.Shor.RunwayWindowed.RunwayLayout
