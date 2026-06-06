/-
================================================================================
  AUDIT — gidney-ekera-2021, 20M qubits / ~8 h (arXiv:1905.09749)
================================================================================
  Per-paper audit folder, uniform structure (Hardware · SystemZones · L1_Algorithm ·
  L2_Arithmetic · L3_PPM · L4_Code · Verifier).  REDEFINES NOTHING — re-presents the
  GE2021 formalization by layer, with `#verify_clean` on the ✅ theorems.  See
  `GidneyEkera2021/README.md` for claim, settings, approach, and the per-layer ledger + GAP.

  Verify:  `lake build FormalRV.Audit.GidneyEkera2021`
-/
import FormalRV.Audit.GidneyEkera2021.Hardware
import FormalRV.Audit.GidneyEkera2021.SystemZones
import FormalRV.Audit.GidneyEkera2021.L1_Algorithm
import FormalRV.Audit.GidneyEkera2021.L2_Arithmetic
import FormalRV.Audit.GidneyEkera2021.L3_PPM
import FormalRV.Audit.GidneyEkera2021.L4_Code
import FormalRV.Audit.GidneyEkera2021.Verifier
