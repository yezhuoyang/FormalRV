/-
  Audit · Pinnacle · LAYER 4 — THE GB qLDPC CODE
  The Pinnacle codes are generalised-bicycle codes.  We CONSTRUCT a representative
  [[72,12,6]] GB code and DERIVE its k from the matrices (➗ native_decide); the RSA-scale
  [[1620,16,24]] instance is recorded (k at 1620 cols needs the GB homological formula — GAP).
-/
import FormalRV.Audit.Pinnacle.Pinnacle
import FormalRV.Verifier
#check @FormalRV.Audit.Pinnacle.Pinnacle.pinnacle_gb_72_n          -- ➗ n = 72
#check @FormalRV.Audit.Pinnacle.Pinnacle.pinnacle_gb_72_css        -- ➗ valid CSS
#check @FormalRV.Audit.Pinnacle.Pinnacle.pinnacle_gb_72_k_derived  -- ➗ k = 12 DERIVED (native_decide)
#verify_clean FormalRV.Audit.Pinnacle.Pinnacle.pinnacle_rsa_code_recorded  -- ✅ RSA instance [[1620,16,24]]
