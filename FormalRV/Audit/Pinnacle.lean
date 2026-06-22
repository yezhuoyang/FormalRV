/-
================================================================================
  AUDIT — webster-2026 "The Pinnacle Architecture", RSA-2048 <100k qubits (arXiv:2602.11457)
================================================================================
  Per-paper audit folder, uniform structure (Hardware · SystemZones · L1_Algorithm ·
  L2_Arithmetic · L3_PPM · L4_Code · Verifier · Codegen).  Every file lives in ONE
  flat namespace `FormalRV.Audit.Pinnacle`.  The GB-code-parameter foundation is
  verified (L4: a real [[72,12,6]] GB code, k DERIVED from the matrices); the rest is
  the roadmap, its end-to-end <100k obligation shown OPEN.  See `Pinnacle/README.md`.

  Verify:  `lake build FormalRV.Audit.Pinnacle`
-/
import FormalRV.Audit.Pinnacle.Hardware
import FormalRV.Audit.Pinnacle.SystemZones
import FormalRV.Audit.Pinnacle.L1_Algorithm
import FormalRV.Audit.Pinnacle.L2_Arithmetic
import FormalRV.Audit.Pinnacle.L2_ArithmeticFaithful
import FormalRV.Audit.Pinnacle.L3_PPM
import FormalRV.Audit.Pinnacle.L4_Code
import FormalRV.Audit.Pinnacle.ParallelReduction
import FormalRV.Audit.Pinnacle.EndToEndQPE
import FormalRV.Audit.Pinnacle.ResourceCheck
import FormalRV.Audit.Pinnacle.FactoringClosure
import FormalRV.Audit.Pinnacle.PPMEndToEnd
import FormalRV.Audit.Pinnacle.Verifier
import FormalRV.Audit.Pinnacle.Codegen
