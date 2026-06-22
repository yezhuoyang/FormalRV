/-
  FormalRV.System.LayeredArtifactInterface — umbrella for the
  shared multi-layer artifact and certificate interface.

  Lean is the trusted verifier: both Lean-generated and external
  (Python / Qiskit / third-party) circuits, schedules, and
  certificates target the SAME checker interfaces; external output
  is always re-derived and re-checked by Lean.

  Content lives in two sibling modules that declare the same
  namespace, so all existing fully-qualified references keep
  working:

    * `LayeredArtifactCore`   — layer tags, artifact wrappers,
      `SystemModels`, `VerifiedSysCallSchedule` + generic checker,
      `LayerCompiler`, external SysCall-schedule certificates.
    * `CompressedSchedule`    — hierarchical compressed schedules:
      expand/resource semantics, compressed + symbolic-repeat
      certificates and the `symbolic_rep_strict_ok` checker.

  This file only re-exports; add new declarations to the pieces.
-/

import FormalRV.System.Artifacts.LayeredArtifactCore
import FormalRV.System.Artifacts.CompressedSchedule
