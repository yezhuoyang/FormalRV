/-
  Audit · cain-xu-2026 · SYSTEM-ZONE SETUP
  ----------------------------------------------------------------------------
  The zoned architecture (memory / operation-zone ancilla / factory) and the proof
  that the full ~10⁹-PPM modexp schedule satisfies every system invariant.
  ✅ = verify-clean semantic/decide theorem (axioms ⊆ {propext, Classical.choice, Quot.sound}).
-/
import FormalRV.Audit.CainXu2026.QianxuLPSystemSchedule
import FormalRV.Audit.CainXu2026.QianxuLPFullSchedule
import FormalRV.Verifier

-- ✅ the finite LP architecture satisfies all SysLayer invariants (capacity/exclusivity/decoder/factory):
#verify_clean FormalRV.Audit.CainXu2026.QianxuLPSystemSchedule.lpCtx_all_invariants
-- ✅ the 7809-qubit upper bound is system-realisable (three zones partition it; invariants hold):
#verify_clean FormalRV.Audit.CainXu2026.QianxuLPSystemSchedule.lp_system_realises_upper_bound
-- ✅ the FULL ~10⁹-cycle modexp schedule is system-correct, by induction on the tiled block:
#verify_clean FormalRV.Audit.CainXu2026.QianxuLPFullSchedule.full_modexp_10e9_schedule_valid
