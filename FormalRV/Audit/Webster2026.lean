/-
================================================================================
  AUDIT — Webster et al. 2026, RSA-2048 on a GB-qLDPC stack  (arXiv:2602.11457)
================================================================================
HEADLINE CLAIM:  RSA-2048 in < 100,000 physical qubits.

STATUS (⬜ recorded/assumed):  Phase-C parameter-binding tuple.  The paper's
  algorithm / code / hardware settings are bound through the SHARED L1–L4 interface
  and smoke-checked by reflexivity; semantic verification is deferred.  This is the
  FRAMEWORK SLOT — a reader sees exactly which settings are recorded and what is not
  yet proved.

SETTINGS A READER SHOULD CHECK MATCH THE PAPER:
  • q_A = 3072  (Ekerå–Håstad window count, matching GE2021)
  • GB qLDPC code  [[1620, 16, 24]]  (n = 1620, k = 16, d = 24)
  • hardware  1e-3 error, 1 µs cycle  (paper §III.D primary baseline)

OUR APPROACH:  record (L1 ShorAlgorithm, L4 GB-qLDPC QECCode, hardware) as Lean data
  in the unified four-layer framework; `example … := by rfl` in the corpus file pins
  each field (q_A, (n,k,d), hardware).  This extends the same corpus pattern used for
  the verified papers, so later ticks can add code + resource proofs WITHOUT changing
  the framework.

THE GAP WE DETERMINED:  parameter recording only — the GB parity matrices hx, hz are
  stubbed `[]`.  No verification yet of GB code properties, the Type-B distance-scaling
  conjecture, success rates, resource bounds, or the < 100k-qubit claim.

STILL UNSOLVED:  explicit GB parity-check matrices; GB distance scaling; L3 PPM
  fault-tolerance schedule; end-to-end resource estimation / <100k validation;
  the L1 `rsa_correct` body (shared across papers; awaits the SQIR/Coq port —
  see Audit/Peng2022.lean).

This file REDEFINES NOTHING.  Build:  `lake build FormalRV.Audit.Webster2026`.
-/
import FormalRV.Corpus.Webster2026

/-! ## Recorded settings through the shared interface (⬜) — reader checks these -/
#check @FormalRV.Corpus.Webster2026.webster_shor       -- q_A = 3072
#check @FormalRV.Corpus.Webster2026.webster_code       -- GB [[1620, 16, 24]]
#check @FormalRV.Corpus.Webster2026.webster_hw         -- 1e-3, 1 µs
#check @FormalRV.Corpus.Webster2026.webster_instance   -- ShorAlgorithm × QECCode × QualtranPhysicalParameters
