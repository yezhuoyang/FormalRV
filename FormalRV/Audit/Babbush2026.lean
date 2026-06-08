/-
================================================================================
  AUDIT — Babbush2026, ECC-256 discrete log < 500k qubits / 18–23 min (arXiv:2603.28846)
================================================================================
  Per-paper audit folder, uniform structure (Hardware · SystemZones · L1_Algorithm ·
  L2_Arithmetic · L3_PPM · L4_Code · Verifier · Codegen).  Every file lives in ONE
  flat namespace `FormalRV.Audit.Babbush2026`.  See `Babbush2026/README.md` for
  claim, settings, approach, and the per-layer ledger + GAP.

  Verify:  `lake build FormalRV.Audit.Babbush2026`
-/
import FormalRV.Audit.Babbush2026.Hardware
import FormalRV.Audit.Babbush2026.L1_Algorithm
import FormalRV.Audit.Babbush2026.L2_Arithmetic
import FormalRV.Audit.Babbush2026.L3_PPM
import FormalRV.Audit.Babbush2026.L4_Code
import FormalRV.Audit.Babbush2026.SystemZones
import FormalRV.Audit.Babbush2026.Verifier
import FormalRV.Audit.Babbush2026.Codegen
