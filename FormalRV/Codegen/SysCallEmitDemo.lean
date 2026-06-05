/-
  FormalRV.Codegen.SysCallEmitDemo — STANDALONE demo that PRINTS the emitted `DEVICE-PROGRAM` text
  for the example schedules.  It has `#eval`s (so it is NOT part of the umbrella `lake build`); run
  it on demand with:

      lake env lean FormalRV/Codegen/SysCallEmitDemo.lean

  The schedules themselves, and their invariant pass/fail verdicts, live in build-checked modules
  (`Codegen/SysCallEmit.lean`, `System/SystemInvariantExamples.lean`); this file only renders them.
-/
import FormalRV.Codegen.SysCallEmit
import FormalRV.System.SystemInvariantExamples

open FormalRV.Codegen.SysCallEmit
open FormalRV.System.SystemInvariantExamples

-- §1. One magic-state Toffoli, and two parallel factories (physical ops + system calls).
#eval IO.println (emitSchedule "Toffoli-via-magic-state-teleportation" toffoliViaTeleport)
#eval IO.println s!"-- {physCount toffoliViaTeleport} physical ops, {sysCount toffoliViaTeleport} system calls\n"
#eval IO.println (emitSchedule "two-parallel-factories" parallelTwoMagic)
#eval IO.println s!"-- {physCount parallelTwoMagic} physical ops, {sysCount parallelTwoMagic} system calls\n"

-- §2. The five invariant-checked example programs (2 pass, 3 fail).
#eval IO.println (emitSchedule "PASS-1 sequential PPM pair" passSequential)
#eval IO.println (emitSchedule "PASS-2 parallel distinct ancillas" passParallelDistinct)
#eval IO.println (emitSchedule "FAIL-1 parallel ancilla aliasing (I2)" failAlias)
#eval IO.println (emitSchedule "FAIL-2 two magic reqs in one window (I4)" failThroughput)
#eval IO.println (emitSchedule "FAIL-3 decode slower than reaction budget (I3 decoder)" failDecodeSlow)
