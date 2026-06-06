/-
  Audit · peng-2022 · LAYER 2 — ARITHMETIC
  The success bound is instantiated with a concrete SQIR-faithful modular multiplier
  (built from verified arithmetic).  ✅ verify-clean.
-/
import FormalRV.Shor.VerifiedShor.ControlledModAddLayer
import FormalRV.Verifier
-- ✅ a SQIR-faithful modular multiplier realizes the order-finding oracle:
#verify_clean VerifiedShor.correct_general_via_interface
