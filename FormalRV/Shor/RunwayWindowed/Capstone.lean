/-
  FormalRV.Shor.RunwayWindowed.Capstone
  ════════════════════════════════════════════════════════════════════════════
  THE FAITHFUL, MODULAR runway coset modular-multiplier — what is genuinely verified.

  This capstone reuses ONLY verified, faithful components, built bottom-up the modular way:

      verified oblivious-carry ADDER  →  runway windowed MULTIPLIER  →  its properties

  ┌─ ADDER (own folder, `FormalRV/Arithmetic/ObliviousRunwayAdder/`) ───────────────────────────┐
  │ `runwayAddK` / `runwayAddKAt` — the segmented oblivious-carry-runway adder, VERIFIED:        │
  │   • exactness `RunwayAdderFunctional.runwayAddK_exact`,                                      │
  │   • multi-add `RunwayAdderMultiAdd.runwayAddK_iter_contiguous`,                              │
  │   • CONSTANT parallel DEPTH in the segment count `k` (`ParallelDepth.parallelDepth_runwayAddK_eq`)
  │     — the oblivious-carry depth advantage, the circuit basis of the paper's pipelining claim.│
  └─────────────────────────────────────────────────────────────────────────────────────────────┘
  ┌─ MULTIPLIER (`runwayWindowedMul`, M1–M5 here) ─ built ON the adder (`runwayAddKAt`) ──────────┐
  │ `RunwayFold.runwayWindowedMul_residue` — the windowed fold over the runway adder computes the │
  │   coset modular multiply `y ↦ (a·y) mod N` (reads the accumulator residue), under the         │
  │   per-segment no-overflow condition `hno`.                                                     │
  └─────────────────────────────────────────────────────────────────────────────────────────────┘
  ┌─ DEVIATION (own folder) ─────────────────────────────────────────────────────────────────────┐
  │ `RunwayDeviationFaithful.faithful_total_deviation_le` — the coset/runway deviation ≤ 1/10⁷,    │
  │   the INTRINSIC `2^{-m}` coset-approximation error (Zalka 2006 / Gidney 1905.08488). This is   │
  │   the probabilistic price of the coset technique — NOT a "missing gate" penalty.               │
  └─────────────────────────────────────────────────────────────────────────────────────────────┘

  HONEST SCOPE (no overclaiming, no misleading abstractions):
   • This is a FAITHFUL multiplier: a real arithmetic circuit on a single coset register, built from
     Gidney's own windowed-arithmetic + oblivious-carry-runway constructions (which he ships as
     working Q# code, `Library/1905.07682/.../MulAdd_Window.qs`).  No `permGate` ideal-permutation
     stand-in, no two-coset-register "preserve the b-block" interface, no false "placement
     impossibility" (those were removed — see `E2RunwayReduction` §0 note).
   • What is NOT (yet) here: a FULL Shor success bound riding THIS runway gate.  That needs the
     coset-DEVIATION success-probability framework re-modelled on the single coset register (the
     `hno` no-overflow condition tied to the verified deviation).  It is the genuine open piece —
     flagged, not faked.
   • The EXACT (per-step-reduced) faithful multiplier ALREADY rides the full Shor bound, kernel-clean,
     in `FormalRV/Audit/GidneyEkera2021/ModExpAtSameObjectWeld.lean`
     (`ge2021_oracle_correct_AND_counted_AND_bound` on `measWindowedModNEncodeGate`): oracle
     correctness ∧ Toffoli count ∧ `≥ κ/(log₂N)⁴`, all on ONE gate.  Reuse that for the bound.

  Kernel-clean: axioms ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`.
-/
import FormalRV.Shor.RunwayWindowed.RunwayFold
import FormalRV.Arithmetic.ObliviousRunwayAdder

namespace FormalRV.Shor.RunwayWindowed.Capstone

/-- **Headline (faithful runway coset multiplier — correctness).**  The windowed runway multiplier
    `runwayWindowedMul` — built on the verified oblivious-carry adder — computes the coset modular
    multiply `y ↦ (a·y) mod N`, read off the contiguous accumulator residue, under the per-segment
    no-overflow condition.  (Alias of `RunwayFold.runwayWindowedMul_residue`.) -/
alias runway_modular_multiply_correct := FormalRV.Shor.RunwayWindowed.RunwayFold.runwayWindowedMul_residue

/-! ## The three faithful pillars, simultaneously available (modular: adder → multiplier → deviation). -/

-- MULTIPLIER correctness (built on the runway adder):
#check @FormalRV.Shor.RunwayWindowed.RunwayFold.runwayWindowedMul_residue
-- ADDER constant-depth advantage (independent of segment count k):
#check @FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth.parallelDepth_runwayAddK_eq
-- coset/runway DEVIATION bound (the intrinsic 2^{-m} coset error, ≤ 1/10⁷):
#check @FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayDeviationFaithful.faithful_total_deviation_le

end FormalRV.Shor.RunwayWindowed.Capstone
