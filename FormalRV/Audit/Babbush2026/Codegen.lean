/-
  Audit · babbush-2026 · CODEGEN — the ACTUAL construction at each level
  ============================================================================
  This file EMITS the detailed construction at every level of the Babbush2026
  stack by instantiating the project's REUSABLE general framework constructors at
  SMALL, representative parameters (so each `#eval` is fast).  The construction
  is REAL — it is the same general emitter the rest of the project verifies, run
  at toy sizes.  Babbush's full parameters are noted in comments at each line.

  How to inspect:  open this file in an editor and read the `#eval` results, or
  run
      lake env lean FormalRV/Audit/Babbush2026/Codegen.lean
  and read what it prints.

  Levels emitted:
    • L1 (algorithm)   — Shor order-finding circuit (Stim)         small instance
    • L2 (arithmetic)  — a representative gate → OpenQASM (Cliff+T) CCX
    • L3 (PPM)         — the CCZ magic-state teleportation gadget   OpenQASM
    • L4 (QEC code)    — the rotated surface code (real d=3 build)  hx / hz / k
    • system          — one surgery gadget → Stim + its footprint  distance-3
-/

import FormalRV.Shor.ShorEmit
import FormalRV.Codegen.GateQasm
import FormalRV.PPM.PPMToQASM
import FormalRV.QEC.FrontendAlgebraic
import FormalRV.QEC.Instances
import FormalRV.QEC.CodeDimension
import FormalRV.LatticeSurgery.ScheduleEmit
import FormalRV.LatticeSurgery.SurgeryDemoSurface

namespace FormalRV.Audit.Babbush2026

/-! ## L1 — the algorithm: Shor order-finding circuit (Stim).
    A readable PREFIX (first 2 modular-mult merges) of the N=15, a=7 instance; the
    FULL circuit is `emitShor 15 7` (large).  Babbush runs Shor on the ECC-256
    elliptic-curve subgroup (first NON-RSA target). -/
#eval FormalRV.Shor.ShorEmit.emitShorPrefix 15 7 2

/-! ## L2 — arithmetic: a representative gate emitted to OpenQASM (Clifford+T).
    A Toffoli (CCX) on qubits 0,1,2 over a 3-qubit register.  Babbush's full
    arithmetic is the 256-bit elliptic-curve modular arithmetic (≈90M Toffolis). -/
#eval FormalRV.Codegen.toQasm (FormalRV.Framework.Gate.CCX 0 1 2) true 3

/-! ## L3 — PPM: the CCZ / T magic-state teleportation gadget (OpenQASM).
    This is the per-Toffoli magic-injection gadget Babbush runs ≈90M times. -/
#eval FormalRV.PPM.PPMToQASM.cczGadgetQASM

/-! ## L4 — QEC code: the rotated surface code.
    Babbush uses a distance d=14 surface code [[425,1,14]] (~425 physical qubits
    per logical tile).  Here is the REAL distance-3 surface-code construction
    (HGP), printed as its X- and Z-check matrices and its derived logical
    dimension k. -/
#eval (FormalRV.QEC.Algebraic.surfaceHGP 3).hx
#eval (FormalRV.QEC.Algebraic.surfaceHGP 3).hz
#eval FormalRV.QEC.derivedK (FormalRV.QEC.Algebraic.surfaceHGP 3)

/-! ## system — one surface-code surgery gadget as a Stim circuit + its footprint.
    Babbush's full schedule tiles ~1175 logical patches into < 500k physical
    qubits; here is a single distance-3 X-surgery gadget and its physical qubit
    count. -/
#eval FormalRV.LatticeSurgery.ScheduleEmit.emitScheduleStim
        [FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery]
#eval FormalRV.LatticeSurgery.ScheduleEmit.gadgetFootprint
        FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery

end FormalRV.Audit.Babbush2026
