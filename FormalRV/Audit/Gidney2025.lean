/-
================================================================================
  AUDIT — Gidney 2025, "How to factor 2048-bit RSA integers with less than a
          million noisy qubits"   (arXiv:2505.15917)
================================================================================
HEADLINE CLAIM:  RSA-2048 in < 1,000,000 physical qubits, in < 1 week.

STATUS:  the most complete RSA audit in the corpus.  The CFS residue-arithmetic
  engine is verified AXIOM-CLEAN; Assumption 1 (the one conjecture) is STATED as a
  Prop and NEVER asserted.

SETTINGS A READER SHOULD CHECK MATCH THE PAPER  (these are the recorded inputs):
  • Ekerå–Håstad  s = 8 ;  input qubits  n/2 + n/s = 1024 + 256 = 1280   (n = 2048)
  • hot surface code  (n,k,d) = (1352,1,25),  2·(d+1)² = 1352 phys / logical
  • cold storage 430 phys / logical ;  hardware  1e-3 error, 1 µs cycle
  • totals: 1537 logical, 897,864 physical  (< 1,000,000, margin 102,136)

OUR APPROACH  (three layers):
  L1 RESOURCE TALLY  (Corpus/Gidney2025.lean): `decide` re-checks the paper's own
     arithmetic (1280 + 131 + 126 = 1537 ; 897,864 < 1,000,000 ; …).
  L2 SEMANTIC ARITHMETIC CORE  (Shor/CFS/*): proves the residue engine FROM FIRST
     PRINCIPLES — exact modexp via faithful RNS (CRT injectivity), exact CRT
     reconstruction with a CONSTRUCTED basis, bounded truncation error, and linear
     deviation accumulation (the modDev pseudometric).
  L3 CLASSICAL POST-PROCESSING: Ekerå–Håstad exponent identity + factor recovery.

THE GAP WE DETERMINED:  the tallies check internal consistency; the CFS core proves
  the arithmetic engine exact (pre-truncation) and bounded (post-truncation).  NOT
  closed here: (a) the QUANTUM half — QPE recovers the discrete log w.h.p. (anchored
  by SQIRPort.probability_of_success, see Audit/Peng2022.lean); (b) the masked-state
  amplitude identity bridging Δ_N to quantum infidelity (combinatorial core done,
  amplitude step pending); (c) full Gate-IR assembly of all |P| residue registers;
  (d) Assumption 1 itself (a prime set with ∏P ≥ N^m and Δ_N < 2^{-f} exists).

This file REDEFINES NOTHING.  It imports the real theorems and exposes them with
`#check` / `#print axioms` so a reader can confirm they type-check and see the
exact trust base.  Build it:  `lake build FormalRV.Audit.Gidney2025`.
-/
import FormalRV.Corpus.Gidney2025
import FormalRV.Shor.CFS.ResidueArith
import FormalRV.Shor.CFS.ResidueNumberSystem
import FormalRV.Shor.CFS.Reconstruction
import FormalRV.Shor.CFS.CRTBasis
import FormalRV.Shor.CFS.TruncationBound
import FormalRV.Shor.CFS.ModularDeviation
import FormalRV.Shor.CFS.TruncatedAccumulation
import FormalRV.Shor.CFS.ApproxPeriodFinding
import FormalRV.Shor.CFS.ResidueCircuit
import FormalRV.Shor.CFS.EkeraHastad
import FormalRV.Shor.CFS.Assumptions

/-! ## L1 — resource tally  (➗ decide-arithmetic; the paper's own numbers) -/
#check @FormalRV.Corpus.Gidney2025.gidney2025_logical_tally    -- 1280 + 131 + 7·18 = 1537
#check @FormalRV.Corpus.Gidney2025.gidney2025_input_qubits     -- n/2 + n/s = 1280
#check @FormalRV.Corpus.Gidney2025.gidney2025_physical_tally   -- 897,864 < 1,000,000
#check @FormalRV.Corpus.Gidney2025.gidney2025_slack            -- margin 102,136

/-! ## L2 — CFS residue-arithmetic engine  (✅ verified-semantic) -/
#check @FormalRV.CFS.residue_modexp_exact_of_lt        -- exact modexp before truncation
#check @FormalRV.CFS.rns_faithful                       -- RNS faithful = CRT injectivity
#check @FormalRV.CFS.reconstruction_explicit           -- exact CRT reconstruction, constructed basis
#check @FormalRV.CFS.residue_modexp_via_crt_explicit   -- full exact RNS chain -> g^e mod N
#check @FormalRV.CFS.modDev_truncAcc_normalized        -- Δ_N/N ≤ |P|·ℓ·2^{-f} (bounded truncation)
#check @FormalRV.CFS.approx_periodic                    -- approximate periodicity of g^x mod N

/-! ## L3 — Ekerå–Håstad classical recovery  (✅ verified-semantic) -/
#check @FormalRV.CFS.ekera_hastad_exponent             -- g^{N-1} ≡ g^{p+q-2} (mod N)
#check @FormalRV.CFS.ekera_hastad_recovery             -- recover p as a root of X²-(d+2)X+N

/-! ## The ONE conjecture — stated as a Prop, NEVER asserted  (⬜ assumed) -/
#check @FormalRV.CFS.Assumption1

/-! ## Axiom audit — confirm the CFS core is axiom-clean (reader runs this) -/
#print axioms FormalRV.CFS.residue_modexp_via_crt_explicit
#print axioms FormalRV.CFS.ekera_hastad_recovery
