/-
================================================================================
  AUDIT — Webster et al. 2026, "The Pinnacle Architecture"  (arXiv:2602.11457)
================================================================================
HEADLINE CLAIM:  RSA-2048 in < 100,000 physical qubits, via generalised-bicycle (GB)
  qLDPC codes (Processing Units + Magic Engines + Memory; Pauli-based computation).

STATUS (⬜ tuple + ✅ GB-code framework STARTED):  the parameter tuple is bound
  through the shared L1–L4 interface; AND the semantic formalization has begun
  (`Corpus/Pinnacle.lean`) — a representative GB code of the Pinnacle family is
  CONSTRUCTED and its logical count is DERIVED from the parity matrices (not asserted),
  reusing the cain-xu LDPC machinery.  The RSA-scale instance + the gates/resources
  remain on the roadmap (named below).

SETTINGS A READER SHOULD CHECK MATCH THE PAPER:
  • q_A = 3072  (Ekerå–Håstad window count, matching GE2021)
  • GB qLDPC code  [[1620, 16, 24]]  (n = 1620, k = 16, d = 24)
  • hardware  1e-3 error, 1 µs cycle  (paper §III.D primary baseline)

OUR APPROACH:  record (L1 ShorAlgorithm, L4 GB-qLDPC QECCode, hardware) as Lean data
  in the unified four-layer framework; `example … := by rfl` in the corpus file pins
  each field (q_A, (n,k,d), hardware).  This extends the same corpus pattern used for
  the verified papers, so later ticks can add code + resource proofs WITHOUT changing
  the framework.

THE GAP WE DETERMINED:  the GB-code-PARAMETER framework is now verified on a
  representative `[[72,12,6]]` Pinnacle-family code (k derived from the matrices); the
  RSA-scale GB `[[1620,16,24]]` parity matrices are still recorded/stubbed (deriving k
  at 1620 columns needs the GB homological formula, brute-rank-infeasible), and the
  measurement gadget / magic engine / < 100k resource bound are not yet built.

STILL UNSOLVED (the Pinnacle roadmap, in `Corpus/Pinnacle.lean`):  RSA-scale GB matrices
  + k; the Processing-Unit logical-Pauli-measurement gadget; the Magic Engine resource
  model; PBC compilation + the < 100k-qubit bound; the L1 `rsa_correct` body (shared;
  awaits the SQIR/Coq port — see Audit/Peng2022.lean).

This file REDEFINES NOTHING.  Build:  `lake build FormalRV.Audit.Webster2026`.
-/
import FormalRV.Corpus.Webster2026
import FormalRV.Corpus.Pinnacle

/-! ## Recorded settings through the shared interface (⬜) — reader checks these -/
#check @FormalRV.Corpus.Webster2026.webster_shor       -- q_A = 3072
#check @FormalRV.Corpus.Webster2026.webster_code       -- GB [[1620, 16, 24]]
#check @FormalRV.Corpus.Webster2026.webster_hw         -- 1e-3, 1 µs
#check @FormalRV.Corpus.Webster2026.webster_instance   -- ShorAlgorithm × QECCode × QualtranPhysicalParameters

/-! ## GB-code parameter framework STARTED (✅ verified) — Corpus/Pinnacle.lean -/
#check @FormalRV.Corpus.Pinnacle.pinnacle_gb_72_n          -- [[72,…]] GB code constructed
#check @FormalRV.Corpus.Pinnacle.pinnacle_gb_72_css        -- valid CSS code
#check @FormalRV.Corpus.Pinnacle.pinnacle_gb_72_k_derived  -- k = 12 DERIVED from the matrices
#check @FormalRV.Corpus.Pinnacle.pinnacle_rsa_code_recorded -- RSA instance [[1620,16,24]] recorded
#print axioms FormalRV.Corpus.Pinnacle.pinnacle_gb_72_k_derived
