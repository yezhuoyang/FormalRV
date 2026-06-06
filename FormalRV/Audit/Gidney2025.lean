/-
================================================================================
  AUDIT — gidney-2025, RSA-2048 <1M qubits <1 week (arXiv:2505.15917)
================================================================================
  Per-paper audit folder, uniform structure (Hardware · SystemZones · L1_Algorithm ·
  L2_Arithmetic · L3_PPM · L4_Code · Verifier · Codegen).  Every file lives in ONE
  flat namespace `FormalRV.Audit.Gidney2025`.  Strength: the CFS residue-arithmetic
  engine (L2) is axiom-clean.  See `Gidney2025/README.md`.

  Verify:  `lake build FormalRV.Audit.Gidney2025`
-/
import FormalRV.Audit.Gidney2025.Hardware
import FormalRV.Audit.Gidney2025.SystemZones
import FormalRV.Audit.Gidney2025.L1_Algorithm
import FormalRV.Audit.Gidney2025.L2_Arithmetic
import FormalRV.Audit.Gidney2025.L3_PPM
import FormalRV.Audit.Gidney2025.L4_Code
import FormalRV.Audit.Gidney2025.Verifier
import FormalRV.Audit.Gidney2025.Codegen
