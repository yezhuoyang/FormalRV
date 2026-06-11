/-
================================================================================
  AUDIT — gidney-ekera-2021, 20M qubits / ~8 h (arXiv:1905.09749)
================================================================================
  Per-paper audit folder, uniform structure (Hardware · SystemZones · L1_Algorithm ·
  L2_Arithmetic · L3_PPM · L4_Code · Verifier · WorkloadAssembly · Codegen).  Every
  file lives in ONE flat namespace `FormalRV.Audit.GidneyEkera2021`.  See
  `GidneyEkera2021/README.md` for claim, settings, approach, and the per-layer
  ledger + GAP.

  Verify:  `lake build FormalRV.Audit.GidneyEkera2021`
-/
import FormalRV.Audit.GidneyEkera2021.Hardware
import FormalRV.Audit.GidneyEkera2021.L1_Algorithm
import FormalRV.Audit.GidneyEkera2021.L2_Arithmetic
import FormalRV.Audit.GidneyEkera2021.L3_PPM
import FormalRV.Audit.GidneyEkera2021.L4_Code
import FormalRV.Audit.GidneyEkera2021.PhysicalSyndrome
import FormalRV.Audit.GidneyEkera2021.SystemZones
import FormalRV.Audit.GidneyEkera2021.Verifier
import FormalRV.Audit.GidneyEkera2021.WorkloadAssembly
import FormalRV.Audit.GidneyEkera2021.Codegen
import FormalRV.Audit.GidneyEkera2021.ShorComposed
