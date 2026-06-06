/-
  Audit · cain-xu-2026 · LAYER 2 — ARITHMETIC (adders / lookups)
  ----------------------------------------------------------------------------
  The paper's per-Toffoli costs (Eqs E3/E4/E9).  E3/E4 are RECOVERED as exact
  structural identities (✅ verify-clean); E9 is an arithmetic (decide) bound (➗).
-/
import FormalRV.Audit.Common.PaperClaims
import FormalRV.Verifier

-- ✅ Eq. E3: the Gidney-variant n-bit adder costs exactly 25·n τ_s:
#verify_clean FormalRV.PaperClaims.gidney_n_bit_adder_meets_qianxu_E3
-- ✅ Eq. E4: the controlled-adder n-bit costs exactly 30·n τ_s:
#verify_clean FormalRV.PaperClaims.ctl_adder_n_bit_meets_qianxu_E4
-- ➗ Eq. E9: full RSA-2048 lookup = 22,720 τ_s (arithmetic recovery, `decide`):
#check @FormalRV.PaperClaims.qianxu_E9_full_lookup_via_toffoli_count
