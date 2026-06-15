/-
  Audit · webster-2026 "The Pinnacle Architecture" (arXiv:2602.11457) · LAYER 2 —
  ARITHMETIC, FAITHFUL subroutine re-anchor
  ════════════════════════════════════════════════════════════════════════════
  Pinnacle follows Gidney 2025's decomposition into ADDITION / LOOKUP / PHASEUP
  subroutines verbatim (main.tex L866).  This file re-anchors those subroutine
  Toffoli costs on our VERIFIED, value-correct gadgets — the same faithful pass we
  did for Cain-Xu — and records Pinnacle's one genuinely-new arithmetic piece
  (the parallel binary-tree reduction) which is proven in `ParallelReduction.lean`.

  SUBROUTINE  →  VERIFIED GADGET  →  honest relationship to the paper's cost def:
   • ADDITION : measured Gidney adder `gidneyAdderMeasured` (value `(a+b)%2^W`,
       `toffoli = W`).  Paper `g2025_add_toffoli W = W−1`.  We are `+1`: our adder
       does NOT shave the unused top carry.  A conservative over-count of 1, OURS.
   • LOOKUP   : measured unary QROM `unaryQROMAt` (`toffoli = 2^w − 1`).  Paper
       `g2025_lookup_toffoli w = 2^w − w − 1`.  We are `+w`: our merged-AND read
       does NOT do the address-cascade folding.  A conservative over-count, OURS.
   • PHASEUP  : the √-cost SELECT-SWAP; partially realised by `Shor.SplitPhaseFixup`
       (a 2^{w/2} split), not a full faithful gadget yet — SHARED Gidney-2025 item.
   • PARALLEL REDUCTION (Pinnacle-specific): `ParallelReduction.parallelReduction_eq_serial`.

  Per the project rule (a count gap is the PAPER's only if we faithfully implement
  the SAME gadget): the `+1` / `+w` here are OUR less-optimal gadgets, NOT Pinnacle
  errors.  Pinnacle's numeric audit found ZERO arithmetic errors; its only paper
  wrinkle is the minor `ρ≥200` vs re-optimised `w₁=8` (needs `ρ≥160`) threshold
  carryover — a parameter slip, not an arithmetic mistake.
-/
import FormalRV.Arithmetic.MeasuredAdder
import FormalRV.Shor.MeasUncomputeAt
import FormalRV.Audit.Gidney2025.SystemZones
import FormalRV.Audit.Pinnacle.ParallelReduction

namespace FormalRV.Audit.Pinnacle.Faithful

open FormalRV.Arithmetic.MeasuredAdder
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasUncomputeAt

/-- **ADDITION subroutine, faithful**: the measured Gidney adder (a verified circuit
    computing `(a+b)%2^W`, `gidneyAdderMeasured_correct`) has Toffoli count exactly
    the paper's `g2025_add_toffoli W` PLUS ONE — the `+1` being the unused top carry
    our layout does not shave.  A conservative over-count on our side, not a paper
    discrepancy. -/
theorem pinnacle_addition_toffoli (n q_start : Nat) :
    EGate.toffoli (gidneyAdderMeasured (n + 2) q_start)
      = FormalRV.Audit.Gidney2025.g2025_add_toffoli (n + 2) + 1 := by
  rw [toffoli_gidneyAdderMeasured]
  unfold FormalRV.Audit.Gidney2025.g2025_add_toffoli
  omega

/-- **LOOKUP subroutine, faithful**: the measured unary QROM read has Toffoli count
    `2^w − 1`, which is the paper's `g2025_lookup_toffoli w = 2^w − w − 1` PLUS `w`
    — the `+w` being the address-cascade folding our merged-AND read does not do.
    A conservative over-count on our side. -/
theorem pinnacle_lookup_toffoli
    (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) (addrBase ancBase d ctrl base : Nat) :
    EGate.toffoli (unaryQROMAt pos W T addrBase ancBase d ctrl base)
      = FormalRV.Audit.Gidney2025.g2025_lookup_toffoli d + d := by
  rw [toffoli_unaryQROMAt]
  unfold FormalRV.Audit.Gidney2025.g2025_lookup_toffoli
  have hd : d < 2 ^ d := Nat.lt_two_pow_self
  omega

/-! ## Witnesses: the subroutine costs ride value-correct circuits, and Pinnacle's
    own parallel reduction is proven. -/

-- ADDITION value: target = (a+b) % 2^W (the faithful sum).
#check @gidneyAdderMeasured_target_val
-- PARALLEL REDUCTION (Pinnacle-specific, Eq.20): tree accumulation = serial sum.
#check @FormalRV.Audit.Pinnacle.ParallelReduction.parallelReduction_eq_serial

/-
  ════════════════════════════════════════════════════════════════════════════
  FAITHFUL AUDIT VERDICT (Pinnacle logical arithmetic)
  ════════════════════════════════════════════════════════════════════════════
  Pinnacle's logical arithmetic rests ENTIRELY on verified objects:
   • the CFS residue engine (inherited from Gidney 2025, wired in `L2_Arithmetic`);
   • the parallel binary-tree reduction, its one new contribution, proven as a
     sum reordering (`ParallelReduction.parallelReduction_eq_serial`, Eq.20);
   • the addition / lookup subroutines, re-anchored above on the verified measured
     Gidney adder and measured QROM.
  GADGET SIDE — NO PINNACLE GAP.  Where our realised counts differ from the paper
  (adder `+1` top carry, lookup `+w` cascade fold), the difference is OUR gadget
  being slightly less optimal than the paper's — a conservative over-count, not a
  Pinnacle error.  The phaseup √-cost gadget is the one shared Gidney-2025 item we
  realise only partially (`SplitPhaseFixup`).  Pinnacle introduces NO arithmetic
  error; its only paper wrinkle is the `ρ≥200`/`w₁=8` threshold carryover.
-/

end FormalRV.Audit.Pinnacle.Faithful
