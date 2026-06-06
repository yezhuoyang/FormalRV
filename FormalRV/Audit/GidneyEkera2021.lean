/-
================================================================================
  AUDIT — Gidney & Ekerå 2021, "How to factor 2048 bit RSA integers in 8 hours
          using 20 million noisy qubits"   (arXiv:1905.09749)
================================================================================
HEADLINE CLAIM:  RSA-2048 in ~20,000,000 physical qubits, in ~8 hours.

STATUS:  resource reproduction with a verified surface-code area/time law and the
  paper's own cited inputs (a feasible-CEILING argument, not end-to-end Hilbert-
  space semantics).

SETTINGS A READER SHOULD CHECK MATCH THE PAPER:
  • distance d = 27 ;  per-logical tile  2·(d+1)² = 1568 qubits
  • logical qubits = 6200  (Ekerå–Håstad windowed) ;  cycle = 1 µs
  • total budget 20,000,000  (Computation 9.72M + Factory 10.28M)
  • Toffoli count = 2.7×10⁹

OUR APPROACH  (two layers):
  (1) FINITE ARCHITECTURE  (GidneyEkera2021Architecture.lean): the tuple is mapped
      to a finite zoned machine; all SysLayer invariants (capacity, exclusivity,
      latency, throughput, decoder backlog) are machine-checked by `decide`, and an
      over-budget schedule (qubit 25M) is REJECTED — the bound is a real constraint.
  (2) RESOURCE REPRODUCTION  (GidneyEkera2021Reproduction.lean): the paper's inputs
      plugged into a verified `surfaceModel` cost law (proven `∀ model`); the qubit
      and time ceilings are computed by rfl and compared to the headline.

THE GAP WE DETERMINED:
  • QUBITS: verified 19.44M = 6200 · (2·1568) ≤ 20M; residual ≤ 600k (~3%) is the
    magic factory — so the reported footprint IS the verified area ceiling, with no
    unverified qubit-side optimization.
  • TIME: the verified naive-sequential ceiling is ~20.25 h; the reported 8 h sits
    2–3× UNDER it.  That ~2.5× is reaction-limited pipelining of the Toffoli critical
    path — the schedule layer permits it, the paper claims it, but full RSA-scale
    pipelining is not verified.  (A fully-serial naive baseline is ~1097× slower,
    quantifying the factory-farm the paper deploys.)

STILL UNSOLVED: full-scale pipelining of all 2.7×10⁹ Toffolis; end-to-end Hilbert-
  space closure (delimited per file header); the factory's detailed wiring.

This file REDEFINES NOTHING.  Build:  `lake build FormalRV.Audit.GidneyEkera2021`.
-/
import FormalRV.Corpus.GidneyEkera2021
import FormalRV.Corpus.GidneyEkera2021Architecture
import FormalRV.Corpus.GidneyEkera2021Reproduction
import FormalRV.Corpus.GE2021DecoderWired
import FormalRV.Corpus.NaiveBaselineCost

/-! ## The recorded parametric tuple (⬜) — reader checks the settings -/
#check @FormalRV.Corpus.GidneyEkera2021.ge2021_instance        -- (Shor q_A=3072, d=27 patch, 1µs/1e-3)

/-! ## Finite architecture: invariants machine-checked, over-budget rejected (➗) -/
#check @FormalRV.Corpus.GidneyEkera2021Architecture.total_is_reported       -- realizes 20,000,000
#check @FormalRV.Corpus.GidneyEkera2021Architecture.zones_partition_budget  -- 9.72M + 10.28M = 20M
#check @FormalRV.Corpus.GidneyEkera2021Architecture.ge2021Ctx_resource_ok   -- schedule fits
#check @FormalRV.Corpus.GidneyEkera2021Architecture.ge2021Ctx_fully_valid   -- resource ∧ causality
#check @FormalRV.Corpus.GidneyEkera2021Architecture.ge2021_overflow_rejected-- 25M is rejected

/-! ## Resource reproduction: verified area/time law vs the headline (➗ / ✅) -/
#check @FormalRV.Corpus.GidneyEkera2021Reproduction.ge2021_qubits_derived          -- 19,443,200
#check @FormalRV.Corpus.GidneyEkera2021Reproduction.ge2021_qubits_reproduce_reported-- ≤ 20M (≤600k gap)
#check @FormalRV.Corpus.GidneyEkera2021Reproduction.ge2021_time_ceiling            -- ~20.25 h ceiling
#check @FormalRV.Corpus.GidneyEkera2021Reproduction.ge2021_time_gap_2_to_3x        -- 8 h is 2-3× under
#check @FormalRV.Corpus.GidneyEkera2021Reproduction.gidney_ekera_2021_reproduced   -- CAPSTONE

/-! ## Decoder is a first-class constraint (➗) -/
#check @FormalRV.Corpus.GE2021DecoderWired.ge2021_fully_valid_with_decoder
#check @FormalRV.Corpus.GE2021DecoderWired.ge2021_underprovisioned_decoder_rejected

/-! ## Naive baseline quantifies the factory-farm gap (➗) -/
#check @FormalRV.Corpus.NaiveBaselineCost.time_gap        -- ~1097× slower without the factory farm
#check @FormalRV.Corpus.NaiveBaselineCost.spacetime_gap   -- ~529× in qubit·hours

/-! ## Axiom audit on the capstone -/
#print axioms FormalRV.Corpus.GidneyEkera2021Reproduction.gidney_ekera_2021_reproduced
