/-
  FormalRV.Shor.CosetEigenstate.ReducedLookupCosetGate — the REDUCED-LOOKUP windowed
  COSET multiplier GATE (the runway-preserving oracle).
  ════════════════════════════════════════════════════════════════════════════

  This mirrors the repo's `windowStepOf`/`windowedMulOf`/`windowedMulCircuitOf`
  (FormalRV/Arithmetic/Windowed/WindowedCircuit.lean, namespace
  `FormalRV.Shor.WindowedCircuit`) but replaces the hard-wired NON-reduced lookup
  table `fun v => a*(2^w)^j*v` with the mod-N-REDUCED table
  `tableValue a N w j` (= `(a*(2^w)^j*v) % N`, from `FormalRV.Shor.WindowedArith`).

  These reduced per-window addends are all `< N`, so the plain Cuccaro add becomes a
  COSET add (the runway absorbs the reduction).  The abstract table-sum + deviation
  are already proven in `CosetTableSum` (`idealAcc_cosetWindowConst = (a·x) mod N`,
  `cosetOutOfPlace_hfwd` the `numWin/2^m` deviation); THIS is the concrete `Gate`.

  WHAT THIS FILE DELIVERS: the three concrete `Gate` defs
  (`reducedWindowStepOf`, `reducedWindowedMulOf`, `cosetModMulCircuitOf`) and the
  WellTyped theorems for them.  The TABLE VALUE does not affect well-typedness (only
  the qubit indices do), so the WellTyped proof mirrors the canonical
  `windowStepOf_cuccaro_wellTyped` verbatim, with the same `bits`/`w`/`span`/`dim`
  side-conditions.

  NOTE (next phase, NOT done here): the VALUE-correctness — that `decodeAcc`
  advances by `tableValue a N w j` / the coset-state shift, discharging
  `CosetTableSum.cosetOutOfPlace_hfwd`'s per-branch `hfac_act` contract for THIS
  concrete gate — is the next phase; this file establishes only that the
  reduced-table gate is well-formed.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
  De-risked via 3 parallel verified attempts (all three produced this file clean).
-/
import FormalRV.Arithmetic.Windowed.WindowedCircuit
import FormalRV.Shor.CosetEigenstate.CosetTableSum

namespace FormalRV.Shor.CosetEigenstate.ReducedLookupCosetGate

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.BQAlgo.WindowedModNShor
  (wellTyped_foldl_seq_range lookupReadAt_wellTyped copyWindow_wellTyped)

/-! ## §1. The reduced-lookup coset gate (mirrors `windowStepOf`, reduced table). -/

/-- **Reduced-lookup window step.**  Identical to `windowStepOf` except the QROM
    table is the mod-N-REDUCED `tableValue a N w j` (= `(a·(2^w)^j·v) % N`) instead
    of the non-reduced `fun v => a·(2^w)^j·v`.  Because the entry value is `< N`, the
    add the lookup feeds into is a coset add (runway-absorbed reduction). -/
def reducedWindowStepOf (A : Adder) (w W N a : Nat) (bits q_start yBase j : Nat) : Gate :=
  Gate.seq (Gate.seq (copyWindow w yBase j)
                     (lookupAddAtOf A w W (tableValue a N w j) bits q_start))
           (copyWindow w yBase j)

/-- **Reduced-lookup windowed multiplier**, a fold of reduced window-steps over
    adder `A` (mirrors `windowedMulOf`). -/
def reducedWindowedMulOf (A : Adder) (w W N a : Nat) (bits q_start yBase numWin : Nat) : Gate :=
  (List.range numWin).foldl
    (fun g j => Gate.seq g (reducedWindowStepOf A w W N a bits q_start yBase j)) Gate.I

/-- **The full reduced-lookup coset modular-multiplier circuit over adder `A`.**
    Same standard layout as `windowedMulCircuitOf`: `ctrl=0`; address bits
    `1,3,…,2w−1`; AND-ancillas `2,4,…,2w`; the adder region at `q_start = 1+2w`
    (spanning `A.span bits`); the `y`-register at `yBase = q_start + A.span bits`.
    Each per-window addend is the mod-N reduced `tableValue a N w j`. -/
def cosetModMulCircuitOf (A : Adder) (w bits N a numWin : Nat) : Gate :=
  reducedWindowedMulOf A w bits N a bits (1 + 2 * w) (1 + 2 * w + A.span bits) numWin

/-! ## §2. Well-typedness (the gate is well-formed).

The table value is invisible to well-typedness — `lookupReadAt_wellTyped` takes the
table `T : Nat → Nat` as a FREE argument and never inspects it; only the qubit
indices (`pos`, the addend register; `w`, the lookup zone) matter.  So the proof of
`reducedWindowStepOf_cuccaro_wellTyped` is a verbatim mirror of the canonical
`FormalRV.Shor.WindowedCosetFamily.windowStepOf_cuccaro_wellTyped`, with the
reduced table `tableValue a N w j` substituted for `fun v => a·(2^w)^j·v`. -/

/-- The QPE-oracle dimension of the coset multiplier (= `WindowedCosetFamily.cosetDim`):
    `2 + 2w + 3·bits`. -/
def cosetDim (w bits : Nat) : Nat := 2 + 2 * w + 3 * bits

/-- **One reduced window step is well-typed at `dim`** (Cuccaro instance, standard
    layout).  Mirrors `windowStepOf_cuccaro_wellTyped`; the reduced table is invisible
    to the proof. -/
theorem reducedWindowStepOf_cuccaro_wellTyped (w bits N a numWin j dim : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin)
    (hdim : 2 + 2 * w + 3 * bits ≤ dim) :
    Gate.WellTyped dim
      (reducedWindowStepOf cuccaroAdder w bits N a bits (1 + 2 * w)
        (1 + 2 * w + cuccaroAdder.span bits) j) := by
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  have hjwi : ∀ i, i < w → j * w + i < bits := by
    intro i hi
    calc j * w + i < j * w + w := by omega
      _ = (j + 1) * w := by ring
      _ ≤ numWin * w := Nat.mul_le_mul_right w hj
      _ = bits := hbits
  have hcw : Gate.WellTyped dim
      (copyWindow w (1 + 2 * w + cuccaroAdder.span bits) j) := by
    rw [hspan]
    refine copyWindow_wellTyped w (1 + 2 * w + (2 * bits + 1)) j dim (by omega)
      (fun i hi => ?_) (fun i hi => by omega)
    have := hjwi i hi; omega
  have haddr_idx : ∀ k, cuccaroAdder.addendIdx (1 + 2 * w) k = 1 + 2 * w + 2 * k + 2 :=
    fun _ => rfl
  have hlook : Gate.WellTyped dim
      (lookupReadAt w (cuccaroAdder.addendIdx (1 + 2 * w)) bits
        (tableValue a N w j)) := by
    refine lookupReadAt_wellTyped w bits (cuccaroAdder.addendIdx (1 + 2 * w)) _ dim hw
      (by omega) (fun k hk => ?_)
    rw [haddr_idx k]
    exact ⟨by omega, by unfold ulookup_and_idx; omega⟩
  unfold reducedWindowStepOf lookupAddAtOf
  exact ⟨⟨hcw, ⟨⟨hlook,
    cuccaro_n_bit_adder_full_wellTyped bits (1 + 2 * w) dim (by omega)⟩, hlook⟩⟩, hcw⟩

/-- **The full reduced-lookup coset modular-multiplier circuit is well-typed at `dim`**
    (Cuccaro instance).  Mirrors `windowedMulCircuitOf_cuccaro_wellTyped`: the fold of
    well-typed steps is well-typed via `wellTyped_foldl_seq_range`. -/
theorem cosetModMulCircuitOf_cuccaro_wellTyped (w bits N a numWin dim : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hdim : 2 + 2 * w + 3 * bits ≤ dim) :
    Gate.WellTyped dim (cosetModMulCircuitOf cuccaroAdder w bits N a numWin) := by
  unfold cosetModMulCircuitOf reducedWindowedMulOf
  refine wellTyped_foldl_seq_range _ numWin dim (by omega) (fun j hj => ?_)
  exact reducedWindowStepOf_cuccaro_wellTyped w bits N a numWin j dim hw hbits hj hdim

/-- **The reduced-lookup coset multiplier circuit is well-typed at its own oracle
    dimension** `cosetDim w bits = 2 + 2w + 3·bits`. -/
theorem cosetModMulCircuitOf_cuccaro_wellTyped_cosetDim (w bits N a numWin : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) :
    Gate.WellTyped (cosetDim w bits)
      (cosetModMulCircuitOf cuccaroAdder w bits N a numWin) :=
  cosetModMulCircuitOf_cuccaro_wellTyped w bits N a numWin (cosetDim w bits) hw hbits
    (by unfold cosetDim; omega)

end FormalRV.Shor.CosetEigenstate.ReducedLookupCosetGate
