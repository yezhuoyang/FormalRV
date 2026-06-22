/-
  FormalRV.System.LatticeSurgeryPPMContract — umbrella module kept
  for downstream importers (SurgeryGadgetToSysCalls, SystemChecker,
  SystemInvariantStrengthening, LayeredArtifactInterface,
  CompressedRepeatSoundness, Examples/AdderSystem, Example/Adder2EndToEnd).

  The former 1300-line file was split by topic; this module re-exports
  everything via transitive imports, and every declaration keeps its
  original fully-qualified name in
  `FormalRV.System.LatticeSurgeryPPMContract`:

  * `Core/ScheduleCombinators.lean` — generic SysCall schedule
    combinators (wallclock, shift, seq/par composition).
  * `Compile/PPMScheduleContract.lean` — the durable contract:
    `PPMScheduleCert` / `PPMScheduleCertWithFactoryPorts`,
    `factory_exclusivity_ok`, the strengthened bundle
    `all_invariants_with_factory_ports_ok` + paper aliases, the
    validator, builder, and compose-existence theorems.
  * `Compile/PPMContractInstances.lean` — GE2021 / PPM-pair / 3-PPM
    worked instances, counterexamples, and failure-isolation theorems.
-/

import FormalRV.System.Core.ScheduleCombinators
import FormalRV.System.Compile.PPMScheduleContract
import FormalRV.System.Compile.PPMContractInstances
