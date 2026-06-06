/-
================================================================================
  AUDIT — Babbush et al. 2026, ECC-256 discrete log on a surface-code stack
          (arXiv:2603.28846)
================================================================================
HEADLINE CLAIM:  ECC-256 in < 500,000 physical qubits, in 18–23 minutes.

STATUS (⬜ recorded/assumed + ➗ a spacetime floor):  the FIRST non-RSA paper — it
  stress-tests that the shared L1 `ShorAlgorithm` interface is modulus-agnostic
  (ECC discrete log, not RSA factoring).  Parameter-binding tuple + a verified
  magic-state spacetime lower bound.

SETTINGS A READER SHOULD CHECK MATCH THE PAPER:
  • q_A = 8 (Ekerå–Håstad window) ;  ECC-256 modulus (N placeholder)
  • surface code  [[425, 1, 14]]  (sized so 1175 logical · 425 ≈ 500,000 physical)
  • hardware  gidney_fowler_realistic  (1e-3 error, 1 µs fast-clock cycle)
  • paper resource constants: ~90M Toffolis, ~1175 logical qubits, 18–23 min

OUR APPROACH:  bind (algorithm, code, hardware) through the shared interface, smoke-
  check fields by reflexivity (q_A = 8, (n,k,d) = (425,1,14)); record the headline
  numbers as `paper_claim_*` constants; and instantiate the PARAMETRIC magic-state
  spacetime floor for Babbush's 90M Toffolis (a genuine lower bound, native_decide).

THE GAP WE DETERMINED:  structural binding + arithmetic cross-check, NOT a semantic
  proof that the algorithm solves ECC-256 or that the physical qubits suffice.  The
  spacetime floor (769,500 qubit·hours) is a proven LOWER bound under a CCZ-factory
  baseline; the naive serial baseline is 301 hours.

STILL UNSOLVED:  L1 `rsa_correct` body (shared, `sorry` pending SQIR/Coq port);
  parity matrices stubbed; subthreshold error ansatz a placeholder; 18–23 min
  wall-clock not circuit-verified; ECC-256 modular arithmetic not re-synthesised
  (the L2 Cuccaro/QROM gadgets are proven for RSA-2048, not re-verified at 256-bit).

This file REDEFINES NOTHING.  Build:  `lake build FormalRV.Audit.Babbush2026`.
-/
import FormalRV.Corpus.Babbush2026
import FormalRV.System.ScheduleAdvance

/-! ## Recorded settings (⬜) — modulus-agnostic interface, first non-RSA paper -/
#check @FormalRV.Corpus.Babbush2026.babbush_shor       -- q_A = 8, ECC-256 (N placeholder)
#check @FormalRV.Corpus.Babbush2026.babbush_code       -- [[425, 1, 14]] surface code
#check @FormalRV.Corpus.Babbush2026.babbush_hw         -- gidney_fowler_realistic
#check @FormalRV.Corpus.Babbush2026.babbush_instance

/-! ## Verified magic-state spacetime FLOOR for 90M Toffolis (➗ native_decide) -/
#check @FormalRV.System.ScheduleAdvance.babbush_ecc256_floor_value   -- 769,500 qubit·hours
#check @FormalRV.System.ScheduleAdvance.babbush_ecc256_naive_hours   -- 301 hours serial baseline
