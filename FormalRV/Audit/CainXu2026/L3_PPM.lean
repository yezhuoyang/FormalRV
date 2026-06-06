/-
  Audit · cain-xu-2026 · LAYER 3 — PAULI-PRODUCT MEASUREMENT (on the LP code)
  ----------------------------------------------------------------------------
  The computation is a sequence of logical-Z PPMs on the real [[18,2,d]] bivariate-
  bicycle code.  Semantic correctness FIRST: each PPM is a correct logical measurement
  and the whole modexp PRESERVES the code (by induction, scale-free to ~10⁹ PPMs).
  All ✅ verify-clean.
-/
import FormalRV.Audit.CainXu2026.QianxuPPMonLP
import FormalRV.Audit.CainXu2026.QianxuModExpLP
import FormalRV.Audit.CainXu2026.QianxuLPComputation
import FormalRV.Verifier

-- ✅ one PPM measuring logical Z̄₀ on the BB code is a correct, code-preserving logical measurement:
#verify_clean FormalRV.Audit.CainXu2026.QianxuPPMonLP.ppm_on_LP_is_verified
#verify_clean FormalRV.Audit.CainXu2026.QianxuPPMonLP.naive_PPM_preserves_others
-- ✅ ANY sequence of logical-Z PPMs (the whole modexp) preserves every code stabilizer (induction):
#verify_clean FormalRV.Audit.CainXu2026.QianxuModExpLP.modexp_preserves_code
#verify_clean FormalRV.Audit.CainXu2026.QianxuModExpLP.logical_computation_preserves_code
-- ✅ a multi-PPM computation measures both logicals and is order-independent:
#verify_clean FormalRV.Audit.CainXu2026.QianxuLPComputation.computation_measures_both
