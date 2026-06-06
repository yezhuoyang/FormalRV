/-
  Audit · gidney-ekera-2021 · SYSTEM-ZONE SETUP  (GE2021's strength)
  ----------------------------------------------------------------------------
  The reported 20M qubits as a FINITE zoned architecture (Computation 9.72M + Factory
  10.28M); the Shor schedule fits, an over-budget (25M) schedule is REJECTED, and the
  decoder fabric is a first-class constraint.  ✅ = verify-clean.
-/
import FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Architecture
import FormalRV.Audit.GidneyEkera2021.GE2021DecoderWired
import FormalRV.Verifier

-- ✅ the two zones exactly partition the 20,000,000 budget:
#verify_clean FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Architecture.zones_partition_budget
-- ✅ the full Shor schedule fits + resource ∧ causality both hold on the finite architecture:
#verify_clean FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Architecture.ge2021Ctx_fully_valid
-- ✅ decoder fabric is a real constraint (provisioned passes; under-provisioned is rejected):
#verify_clean FormalRV.Audit.GidneyEkera2021.GE2021DecoderWired.ge2021_fully_valid_with_decoder
-- (the over-budget / under-provisioned REJECTIONS — the bound bites, not advisory:)
#check @FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Architecture.ge2021_overflow_rejected
#check @FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Architecture.total_is_reported   -- realizes 20,000,000
