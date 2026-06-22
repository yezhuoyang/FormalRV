/-
  Audit · webster-2026 "The Pinnacle Architecture" (arXiv:2602.11457) · LAYER 2 — ARITHMETIC
  ════════════════════════════════════════════════════════════════════════════
  Pinnacle's LOGICAL factoring arithmetic is NOT new: the paper states (main.tex
  L802-805) it uses "a generalisation of that presented by Gidney [2505.15917] …
  techniques developed by Ekerå–Håstad and by Chevignard et al. … residue number
  system arithmetic to replace modular arithmetic over N with modular arithmetic
  over a set of primes P each of size polylog(N)."  So Pinnacle's arithmetic =
  Gidney-2025's CFS approximate-residue engine, which is ALREADY VERIFIED in
  `FormalRV.Shor.CFS.*` (axiom-clean).  This file WIRES that verified
  engine in as Pinnacle's arithmetic audit (it was previously a bare stub).

  WHAT THE PAPER'S ARITHMETIC NEEDS, and the verified object that supplies it:
   • RNS faithfulness (residue vector ⇒ V mod ∏P)        → `CFS.rns_faithful`
   • exact residue modexp (= g^e mod N, no-wraparound)    → `CFS.residue_modexp_exact_of_lt`,
                                                            `CFS.residue_modexp_via_crt_explicit`
   • per-prime controlled modular-multiply semantics       → `CFS.residueAccumulate_eq`
   • CRT reconstruction with constructed basis             → `CFS.reconstruction_explicit`
   • truncated accumulator, Δ_N/N ≤ |P|·ℓ·2^{-f}           → `CFS.modDev_truncAcc_normalized`
  The lookup/adder/phaseup Toffoli-tally subroutines (tab:subroutines) reuse the
  Gidney2025 per-gadget cost models (`Audit/Gidney2025/SystemZones.lean`:
  `g2025_add_toffoli`/`g2025_lookup_toffoli`/`g2025_modadd_toffoli_halves`) and the
  gate-level `Arithmetic/Windowed/WindowedModN.windowedModNMulCircuit_correct` +
  `Arithmetic/UnaryLookup/UnaryLookupGrayCode`.

  PINNACLE-SPECIFIC ARITHMETIC DELTA (the only new arithmetic obligation) — NOW CLOSED:
  the paper parallelises the outer loop across ρ ≤ |P| working registers and
  combines the ρ truncated accumulators by a BINARY TREE (parallel reduction,
  main.tex L812-813), proving (Eq.20) this is a REORDERING of Gidney's serial
  truncated sum so the final accumulator value is unchanged.  PROVEN in
  `Audit/Pinnacle/ParallelReduction.lean`: `parallelReduction_eq_serial`
  (`parAcc s c ρ = exactAcc s (ρ·c)` — the ρ-way chunked accumulation equals the
  serial `exactAcc`) and `parallelReduction_modDev` (the verified deviation bound
  covers the parallel-reduced value).  A pure reordering of the existing `exactAcc`,
  exactly as predicted — no new primitive.

  ABOVE the arithmetic (OUT OF SCOPE here): the headline <100k-physical-qubit figure
  rests on the generalised-bicycle qLDPC code-layer obligations (separate roadmap).
-/
import FormalRV.Shor.CFS.ResidueNumberSystem
import FormalRV.Shor.CFS.ResidueArith
import FormalRV.Shor.CFS.ResidueCircuit
import FormalRV.Shor.CFS.CRTBasis
import FormalRV.Shor.CFS.TruncatedAccumulation
import FormalRV.Audit.Pinnacle.ParallelReduction

namespace FormalRV.Audit.Pinnacle.L2_Arithmetic

/-! ## Pinnacle's logical arithmetic, supplied by the verified Gidney2025 CFS engine.
    The `#check`s witness that the residue-arithmetic chain Pinnacle's algorithm
    needs is available, axiom-clean, and imported here as Pinnacle's arithmetic audit. -/

-- RNS faithfulness (CRT injectivity): the residue vector determines V mod ∏P.
#check @FormalRV.CFS.rns_faithful
-- Exact residue modexp = g^e mod N when L ≥ N^m (no wraparound) — the modexp value.
#check @FormalRV.CFS.residue_modexp_exact_of_lt
#check @FormalRV.CFS.residue_modexp_via_crt_explicit
-- Per-prime controlled modular-multiply circuit semantics (the loop body).
#check @FormalRV.CFS.residueAccumulate_eq
-- CRT reconstruction with the constructed basis.
#check @FormalRV.CFS.reconstruction_explicit
-- Truncated accumulator with the bounded modular deviation Δ_N/N ≤ |P|·ℓ·2^{-f}.
#check @FormalRV.CFS.modDev_truncAcc_normalized
-- PINNACLE-SPECIFIC: the parallel binary-tree reduction = the serial sum (Eq.20).
#check @FormalRV.Audit.Pinnacle.ParallelReduction.parallelReduction_eq_serial
#check @FormalRV.Audit.Pinnacle.ParallelReduction.parallelReduction_modDev

end FormalRV.Audit.Pinnacle.L2_Arithmetic
