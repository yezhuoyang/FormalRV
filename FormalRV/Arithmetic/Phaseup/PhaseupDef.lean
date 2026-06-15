/-
  FormalRV.Arithmetic.Phaseup.PhaseupDef
  ────────────────────────────────────────
  SHARED BASE for the reusable **phaseup** gadget — Gidney 2025's third arithmetic
  subroutine: a phase-gradient table lookup that applies the table-indexed phase
  `(−1)^(ctrl ∧ F(addr))` at SELECT-SWAP √-cost, shared with Pinnacle.

  ## The construction (composition, not from scratch)

  The phase mechanism is ALREADY proven in `FormalRV.Shor.SplitPhaseFixup`
  (`splitPhaseLookup`) and `FormalRV.Shor.PhaseLookupFixup` (`phaseLookup`).  This
  file does NOT re-derive any phase machinery — it merely PACKAGES the verified
  split SELECT-SWAP lookup as the canonical reusable phaseup gadget, exposing the
  table `F`, the address width `w = w1 + w2`, the split `w1, w2`, and the one-hot
  `base` as a clean public interface any paper audit can import.

  * `phaseup dim F w1 w2 base` — the CANONICAL phaseup: the √-cost SELECT-SWAP
    `splitPhaseLookup` (one-hot the hi half, CZ-leaf walk the lo half, un-one-hot),
    a diagonal phase at `4·(2^w1 − 1) + 2·(2^w2 − 1)` Toffolis.
  * `phaseupFull dim w F` — the UNSPLIT `phaseLookup` for cost comparison, the full
    table read at `2·(2^w − 1)` Toffolis.
  * `phaseupSkeleton` / `phaseupFullSkeleton` — the Gate-level T-content twins
    (the BaseUCom phase walk carries no T-counter; cost lives on the literal twin).

  Refs: Gidney 2025 (phaseup subroutine, √(2^w) SELECT-SWAP); Pinnacle (shares it).
-/
import FormalRV.Shor.SplitPhaseFixup
import FormalRV.Shor.PhaseLookupFixup

namespace FormalRV.Arithmetic.Phaseup

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.PhaseLookupFixup
open FormalRV.Shor.SplitPhaseFixup

noncomputable section

/-! ## §1. The canonical phaseup (√-cost SELECT-SWAP). -/

/-- **THE phaseup gadget** — Gidney 2025's phase-gradient table lookup at
    SELECT-SWAP √-cost.  On a basis state with ctrl/address holding the query and
    the AND-ladder + one-hot ancillas clean, it applies the diagonal phase
    `(−1)^(ctrl ∧ F(addr))` (correctness: `PhaseupCorrectness`), where the address
    is split `addr = hi‖lo` into the high `w1` levels and low `w2` levels
    (`w = w1 + w2`) and the `2^w1` one-hot ancillas sit at `base + h`.

    This is exactly the verified `splitPhaseLookup`: one-hot the hi half, run a
    CZ-leaf phase walk over the lo half, un-one-hot the hi half — the √-cost
    construction Gidney–Ekerå charge, vs the full table read `phaseupFull`. -/
def phaseup (dim : Nat) (F : Nat → Bool) (w1 w2 base : Nat) : BaseUCom dim :=
  splitPhaseLookup dim F w1 w2 base

/-- The UNSPLIT phaseup — the full-depth `phaseLookup` over the whole `w`-level
    address, for cost comparison.  Same diagonal phase `(−1)^(ctrl ∧ F(addr))`
    but at the FULL table-read cost `2·(2^w − 1)` Toffolis. -/
def phaseupFull (dim w : Nat) (F : Nat → Bool) : BaseUCom dim :=
  phaseLookup dim w F

/-! ## §2. The Gate-level T-content twins (cost is stated on these). -/

/-- The Gate-level T-content twin of `phaseup`: two one-hot reads + the lo-walk
    classical skeleton (its CZ leaves are Clifford, contributing no T). -/
def phaseupSkeleton (w1 w2 base : Nat) : Gate :=
  splitPhaseLookupSkeleton w1 w2 base

/-- The Gate-level T-content twin of `phaseupFull`: the full phase-walk skeleton. -/
def phaseupFullSkeleton (w : Nat) : Gate :=
  phaseLookupSkeleton w

end -- noncomputable section

end FormalRV.Arithmetic.Phaseup
