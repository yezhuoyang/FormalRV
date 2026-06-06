/-
================================================================================
  AUDIT — cain-xu-2026, RSA-2048 on a lifted-product qLDPC stack (arXiv:2603.28627)
================================================================================
  Per-paper audit folder with the UNIFORM structure:
    Hardware · SystemZones · L1_Algorithm · L2_Arithmetic · L3_PPM · L4_Code · Verifier.
  It REDEFINES NOTHING — it imports the real theorems (now under `FormalRV.Audit.CainXu2026.*`)
  and re-presents them per layer, with `#verify_clean` (the anti-cheat gate) on every theorem
  marked ✅.  See `CainXu2026/README.md` for the headline claim, the settings to check, our
  approach, and the honest per-layer ledger + the named GAPs.

  Verify the whole paper:  `lake build FormalRV.Audit.CainXu2026`
-/
import FormalRV.Audit.CainXu2026.Hardware
import FormalRV.Audit.CainXu2026.SystemZones
import FormalRV.Audit.CainXu2026.L1_Algorithm
import FormalRV.Audit.CainXu2026.L2_Arithmetic
import FormalRV.Audit.CainXu2026.L3_PPM
import FormalRV.Audit.CainXu2026.L4_Code
import FormalRV.Audit.CainXu2026.Verifier
