/-
  FormalRV.Arithmetic.Phaseup
  ─────────────────────────────
  The reusable **phaseup** gadget — Gidney 2025's third arithmetic subroutine: a
  phase-gradient table lookup that applies the table-indexed diagonal phase
  `(−1)^(ctrl ∧ F(addr))` at SELECT-SWAP √-cost (`O(2^(w/2))`), shared with
  Pinnacle.

  Import this umbrella to get the whole verified phaseup gadget — the canonical
  √-cost SELECT-SWAP `def` (`phaseup`) + the unsplit comparison `phaseupFull`,
  the diagonal phase-action correctness (`phaseup_diagonal`) and end-to-end
  measured-uncompute channel corollary (`measWordUncompute_phaseup`), and the
  Toffoli counts with the √-advantage as a THEOREM (`toffoli_phaseup`,
  `phaseup_toffoli_sqrt`) — as the single public entry point any paper audit can
  import.

  The phase mechanism is REUSED, not re-proved: `phaseup` wraps the verified
  `FormalRV.Shor.SplitPhaseFixup.splitPhaseLookup`, and every correctness / count
  theorem re-exports a `SplitPhaseFixup` / `PhaseLookupFixup` headline under the
  gadget's name.

  See `Phaseup/README.md` for the spine (which file holds which headline), the
  SELECT-SWAP √-cost explanation + ASCII diagram, and the Gidney 2025 / Pinnacle
  paper connection.
-/
import FormalRV.Arithmetic.Phaseup.PhaseupDef
import FormalRV.Arithmetic.Phaseup.PhaseupCorrectness
import FormalRV.Arithmetic.Phaseup.PhaseupResource
