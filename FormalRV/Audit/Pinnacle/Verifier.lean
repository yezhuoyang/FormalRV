/-
  Audit · Pinnacle · VERIFIER — end-to-end obligation + anti-cheat gate
  ============================================================================
  STATUS: the GB-code-PARAMETER framework is verified on a representative code
  (L4: a real [[72,12,6]] GB code, k DERIVED from the constructed matrices); the
  RSA-scale code, the measurement gadget, the magic engine, and the < 100k
  resource bound are the ROADMAP (README STILL UNSOLVED).  The end-to-end
  < 100k obligation is OPEN — shown openly, not faked.  ✅ verify-clean on what
  is genuinely proven.
-/
import FormalRV.Audit.Pinnacle.L4_Code
import FormalRV.Verifier

-- ✅ the recorded RSA-2048 GB instance [[1620,16,24]] (axiom-free):
#verify_clean FormalRV.Audit.Pinnacle.pinnacle_rsa_code_recorded
-- the GB-code-parameter foundation (➗ native_decide — k DERIVED from matrices):
#check @FormalRV.Audit.Pinnacle.pinnacle_gb_72_k_derived
