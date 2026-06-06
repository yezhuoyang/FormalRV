/-
  Audit · cain-xu-2026 · LAYER 4 — THE qLDPC CODE (lifted-product / bivariate-bicycle)
  ----------------------------------------------------------------------------
  The code parameters are DERIVED from the constructed parity matrices (not asserted),
  and there is a structurally-verified lattice-surgery gadget on the REAL LP code.
  ✅ = verify-clean semantic; ➗ = native_decide numeric (the rank-based k at scale).
-/
import FormalRV.Audit.CainXu2026.QianxuCodeParams
import FormalRV.Audit.CainXu2026.QianxuFullLP
import FormalRV.Audit.CainXu2026.QianxuLPSurgery
import FormalRV.Audit.CainXu2026.QianxuGadgetDerivedResource
import FormalRV.Verifier

-- ✅ the LP-code lattice-surgery gadget implements a genuine logical Pauli measurement (X̄₀):
#verify_clean FormalRV.Audit.CainXu2026.QianxuLPSurgery.LP_code_has_verified_surgery
#verify_clean FormalRV.Audit.CainXu2026.QianxuLPSurgery.bb_LP_surgery_implements_logical_X
-- ✅ the per-PPM resource (τ_s, footprint) is READ OFF the verified gadget, not hand-picked:
#verify_clean FormalRV.Audit.CainXu2026.QianxuGadgetDerivedResource.resource_grounded_in_verified_gadget
-- ➗ k DERIVED from the constructed matrices via GF(2) rank (native_decide at 248 / 4350 columns):
#check @FormalRV.Audit.CainXu2026.QianxuCodeParams.bb18_k_derived       -- bb18 k = 10
#check @FormalRV.Audit.CainXu2026.QianxuFullLP.lp20_k_derived           -- lp_20 k = 1224
