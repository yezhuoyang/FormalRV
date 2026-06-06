/-
  Audit · xu-2024 · VERIFIER — end-to-end obligation + the cross-paper sanity check
  STATUS: parameter-tuple binding + the 24,000× cycle-time OUTLIER cross-check (➗ decide).
  The constant-overhead-FTQC claim is OPEN (README); no number is claimed as a proof.
-/
import FormalRV.Audit.Xu2024.Xu2024
-- ➗ the 24 ms cycle = 24,000 × the 1 µs (10-tenths) baseline (decidable cross-paper outlier):
example : FormalRV.Audit.Xu2024.Xu2024.xu2024_hw.cycle_time_us_tenths = 24000 * 10 := by decide
