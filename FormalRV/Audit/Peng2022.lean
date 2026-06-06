/-
================================================================================
  AUDIT — Peng et al. 2022 (SQIR/Coq), "A Formally Certified End-to-End
          Implementation of Shor's Factorization Algorithm"  (arXiv:2204.07112)
================================================================================
HEADLINE CLAIM:  a machine-checked end-to-end Shor (success-probability + gate-count
  bound), originally in Coq/SQIR.

STATUS:  this is where the ONE CROSS-CUTTING verified result lives — the
  N-parametric order-finding success bound  probability_of_success ≥ κ/(log₂ N)⁴,
  ported from SQIR's Coq proof.  It underwrites EVERY other paper's success claim.

SETTINGS:
  • peng_shor: N = 0 (placeholder; the theorem is N-parametric), q_A = 1 (single
    window, no Ekerå–Håstad multi-window optimization)
  • peng_code = (1,1,1) trivial placeholder (Peng has no QEC stack)
  • κ = 4·exp(-2)/π² ≈ 0.0548  (noncomputable real, verified > 0)

OUR APPROACH:
  L1 Shor correctness (`Shor_correct_var`) from verified QPE + a modular-multiplier
     oracle interface (`ModMulImpl`); L2 concrete SQIR-faithful arithmetic gadgets
     (`correct_general_via_interface`).  The headline `master_success_bound` exposes
     the ideal bound κ/(log₂ N)⁴ MINUS a tunable error budget (2π/2^cutoff + num_ops·p_L),
     which every other paper instantiates with its own QEC + hardware parameters.

THE GAP WE DETERMINED:  `master_success_bound` / `Shor_correct_var` are verified
  semantic theorems; BUT the underlying QPE peak bound (`QPE_MMI_correct`) rests on
  a small block of custom quantum axioms (QPE semantics, Euler-totient lower bound,
  continued-fractions recovery, measurement-probability theory).  RUN the
  `#print axioms` below to see the EXACT trust base — the audit's whole point is that
  this is visible, not hidden.  κ is noncomputable (its numeric value ≈ 0.0548 is
  recorded, not arithmetically reduced).

STILL UNSOLVED: discharging the QPE axiom block (finishing the continued-fractions
  bridge + quantum-state semantics); connecting Peng's gate-count bounds to the
  success theorem as a verified resource chain.

This file REDEFINES NOTHING.  Build:  `lake build FormalRV.Audit.Peng2022`.
-/
import FormalRV.Corpus.Peng2022
import FormalRV.Shor.SuccessSensitivity
import FormalRV.Shor.PostQFT.PostQFTCompletion
import FormalRV.Shor.VerifiedShor.ControlledModAddLayer

/-! ## The recorded tuple (⬜) -/
#check @FormalRV.Corpus.Peng2022.peng_instance

/-! ## The success constant κ = 4·exp(-2)/π² (✅) -/
#check @FormalRV.SQIRPort.κ
#check @FormalRV.SQIRPort.κ_pos

/-! ## THE cross-cutting result — order-finding success ≥ κ/(log₂ N)⁴ (✅) -/
#check @FormalRV.SQIRPort.Shor_correct_var                       -- N-parametric, oracle-generic
#check @FormalRV.Shor.SuccessSensitivity.master_success_bound    -- ideal bound − error budget
#check @FormalRV.Shor.SuccessSensitivity.master_success_bound_bundled
#check @VerifiedShor.correct_general_via_interface               -- with SQIR-faithful modmul

/-! ## AXIOM AUDIT — the honest trust base of the headline (reader runs this) -/
#print axioms FormalRV.Shor.SuccessSensitivity.master_success_bound
#print axioms FormalRV.SQIRPort.Shor_correct_var
