/-
================================================================================
  AUDIT — Cain, Xu et al. 2026, RSA-2048 on a neutral-atom qLDPC stack
          (lifted-product codes)   (arXiv:2603.28627)        [FOCUS PAPER]
================================================================================
HEADLINE CLAIM:  RSA-2048 in ~10,000 qubits, in ~1 week (with parallelisation).

STATUS:  the deepest LDPC-Shor audit.  We CLOSE the semantic-correctness loop on
  the REAL lifted-product (LP) code family and BRACKET the resource claim between a
  verified naive upper bound and a structural lower bound; the remaining distance is
  the paper's UNCONSTRUCTED optimizations, each named and sized.

SETTINGS A READER SHOULD CHECK MATCH THE PAPER:
  • LP memory  lp_20^{3,7} = [[4350, 1224, 20]]  (k DERIVED from parity matrices)
  • bb18 = [[248, 10, ≤18]] ;  per-Toffoli τ_s: adder 25, ctl-adder 15, lookup 71
  • operation-zone ancilla N_𝒜 = 894 ;  bb18 factory ≈ 2565 ;  cycle 1 µs ; 1e-3
  • Eqs E3 (25n τ_s adder), E4 (30n τ_s ctl-adder), E9 (lookup) at RSA-2048

OUR APPROACH  (four layers):
  • PARAMETRIC SEMANTIC: a naive modexp = sequence of logical-Z PPMs PRESERVES every
    code stabilizer, proved by INDUCTION (holds at the full ~10⁹-PPM scale without
    enumeration) on the real [[18,2,d]] BB code; a lattice-surgery gadget on the LP
    family implements a genuine logical-Pauli measurement.
  • RESOURCE: upper bound by an explicit naive construction; lower bound by structure
    (data block incompressible below rate; critical-path Toffoli depth); soundness
    lemmas prove lower ≤ upper.
  • FINITE INSTANTIATION: bb18/lp_16/lp_20 logical counts k DERIVED from parity
    matrices via GF(2) rank.
  • SYSTEM: the full ~10⁹-cycle modexp schedule is system-correct by induction on the
    tiled block (Lean never materialises the 10⁹-cycle list).

THE GAP WE DETERMINED  (claim ~10⁴ q / ~1 week sits BETWEEN our bounds):
  • verified naive UPPER bound: 7,809 q (full zoned 14,961 q), ~1.3×10¹³ µs (~150 d)
  • the ~4,961-qubit gap = factory-sharing / multi-block packing (NOT constructed)
  • the ~1000× time gap = the parallelisation trick (NOT constructed; only naive
    sequential is proven)

STILL UNSOLVED (this is an LDPC-Shor paper): LP distance d not derived from the
  lifted-product formula (out of scope); full LP parity matrices externally sourced;
  parallelisation + factory-sharing not constructed; distillation correctness assumed;
  decoder algorithm unspecified (only its reaction budget is checked).

This file REDEFINES NOTHING.  Build:  `lake build FormalRV.Audit.CainXu2026`.
-/
import FormalRV.Corpus.CainXu
import FormalRV.Corpus.QianxuVerifiedUpperBound
import FormalRV.Corpus.QianxuModExpLP
import FormalRV.Corpus.QianxuPPMonLP
import FormalRV.Corpus.QianxuLPSurgery
import FormalRV.Corpus.QianxuFullLP
import FormalRV.Corpus.QianxuBounds
import FormalRV.Corpus.QianxuLPComputation
import FormalRV.Corpus.QianxuLPFullSchedule
import FormalRV.Corpus.QianxuGadgetDerivedResource
import FormalRV.Corpus.PaperClaims

/-! ## The recorded tuple (⬜) — reader checks the settings -/
#check @FormalRV.Corpus.CainXu.cainxu_instance

/-! ## Semantic correctness on the REAL LP code (✅ verified-semantic) -/
#check @FormalRV.Corpus.QianxuModExpLP.modexp_preserves_code          -- ∀ PPM seq: code survives (induction)
#check @FormalRV.Corpus.QianxuModExpLP.logical_computation_preserves_code
#check @FormalRV.Corpus.QianxuPPMonLP.ppm_on_LP_is_verified           -- per-PPM is a correct logical meas
#check @FormalRV.Corpus.QianxuLPSurgery.LP_code_has_verified_surgery  -- surgery gadget on LP (not surface)
#check @FormalRV.Corpus.QianxuLPSurgery.bb_LP_surgery_implements_logical_X
#check @FormalRV.Corpus.QianxuLPComputation.computation_order_independent
#check @FormalRV.Corpus.QianxuGadgetDerivedResource.resource_grounded_in_verified_gadget

/-! ## Resource: soundness (lower ≤ upper) + the verified upper bound (✅ / ➗) -/
#check @FormalRV.Corpus.QianxuBounds.qubit_lower_le_upper
#check @FormalRV.Corpus.QianxuBounds.time_floor_all_schedules
#check @FormalRV.Corpus.QianxuVerifiedUpperBound.qianxu_verified_upper_bound  -- 7809 q, 1.3e13 µs ceiling

/-! ## Finite instantiation: k DERIVED from parity matrices (➗ native_decide) -/
#check @FormalRV.Corpus.QianxuFullLP.lp16_k_derived          -- k = 744 = 2610 − rank Hx − rank Hz
#check @FormalRV.Corpus.QianxuFullLP.lp20_k_derived          -- k = 1224

/-! ## The GAP, quantified (➗ decide-arithmetic) -/
#check @FormalRV.Corpus.QianxuFullLP.lp20_qubit_bracketed    -- 4350 ≤ 10000 ≤ 14961
#check @FormalRV.Corpus.QianxuFullLP.lp20_qubit_gap          -- 4961-qubit factory-sharing gap
#check @FormalRV.Corpus.QianxuFullLP.lp20_time_gap           -- ~1000× parallelisation gap
#check @FormalRV.Corpus.QianxuFullLP.full_lp_report

/-! ## Eqs E3 / E4 / E9 recovered (✅ / ➗) -/
#check @FormalRV.PaperClaims.gidney_n_bit_adder_meets_qianxu_E3       -- 25n τ_s
#check @FormalRV.PaperClaims.ctl_adder_n_bit_meets_qianxu_E4          -- 30n τ_s
#check @FormalRV.PaperClaims.qianxu_E9_full_lookup_via_toffoli_count  -- 22,720 τ_s

/-! ## Full ~10⁹-cycle modexp schedule valid by induction (✅) -/
#check @FormalRV.Corpus.QianxuLPFullSchedule.full_modexp_10e9_schedule_valid

/-! ## Axiom audit on the headline semantic result -/
#print axioms FormalRV.Corpus.QianxuVerifiedUpperBound.qianxu_verified_upper_bound
#print axioms FormalRV.Corpus.QianxuModExpLP.modexp_preserves_code
