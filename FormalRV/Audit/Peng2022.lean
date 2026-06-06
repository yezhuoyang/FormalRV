/-
================================================================================
  AUDIT — peng-2022 (SQIR/Coq), formally-verified Shor (arXiv:2204.07112)
================================================================================
  Per-paper audit folder, uniform structure (Hardware · SystemZones · L1_Algorithm ·
  L2_Arithmetic · L3_PPM · L4_Code · Verifier · Codegen).  Every file lives in ONE
  flat namespace `FormalRV.Audit.Peng2022`.  THE cross-cutting MACHINE-CHECKED
  order-finding success bound lives in L1; Peng is algorithm-level only, so
  SystemZones / L3 / L4 are honest GAPs.  See `Peng2022/README.md` for claim,
  approach, and the per-layer ledger + GAP.

  Verify:  `lake build FormalRV.Audit.Peng2022`
-/
import FormalRV.Audit.Peng2022.Hardware
import FormalRV.Audit.Peng2022.L1_Algorithm
import FormalRV.Audit.Peng2022.L2_Arithmetic
import FormalRV.Audit.Peng2022.L3_PPM
import FormalRV.Audit.Peng2022.L4_Code
import FormalRV.Audit.Peng2022.SystemZones
import FormalRV.Audit.Peng2022.Verifier
import FormalRV.Audit.Peng2022.Codegen
