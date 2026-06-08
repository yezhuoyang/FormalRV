/-
  Audit · gidney-ekera-2021 · CODEGEN — the ACTUAL construction at each level
  ============================================================================
  This file EMITS the detailed construction at every level of the GE2021 stack
  by instantiating the project's REUSABLE general framework constructors at
  SMALL, representative parameters (so each `#eval` is fast).  The construction
  is REAL — it is the same general emitter the rest of the project verifies, run
  at toy sizes.  GE2021's full parameters are noted in comments at each line.

  How to inspect:  open this file in an editor and read the `#eval` results, or
  run
      lake env lean FormalRV/Audit/GidneyEkera2021/Codegen.lean
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

namespace FormalRV.Audit.GidneyEkera2021

/-! ## L1 — the algorithm: Shor order-finding circuit (Stim).
    A readable PREFIX (first 2 modular-mult merges) of the N=15, a=7 instance; the
    FULL circuit is `emitShor 15 7` (large).  GE2021 uses q_A = 3072 windowed runs. -/
#eval FormalRV.Shor.ShorEmit.emitShorPrefix 15 7 2

/-! ## L2 — arithmetic: a representative gate emitted to OpenQASM (Clifford+T).
    A Toffoli (CCX) on qubits 0,1,2 over a 3-qubit register.  GE2021's full
    arithmetic is the windowed modular exponentiation (≈2.62×10⁹ Toffolis). -/
#eval FormalRV.Codegen.toQasm (FormalRV.Framework.Gate.CCX 0 1 2) true 3

/-! ## L3 — PPM: the CCZ / T magic-state teleportation gadget (OpenQASM).
    This is the per-Toffoli magic-injection gadget GE2021 runs ≈2.62×10⁹ times. -/
#eval FormalRV.PPM.PPMToQASM.cczGadgetQASM

/-! ## L4 — QEC code: the rotated surface code.
    GE2021 uses distance d=27 (2(d+1)² = 1568 physical qubits per logical tile).
    Here is the REAL distance-3 surface-code construction (HGP), printed as its
    X- and Z-check matrices and its derived logical dimension k. -/
#eval (FormalRV.QEC.Algebraic.surfaceHGP 3).hx
#eval (FormalRV.QEC.Algebraic.surfaceHGP 3).hz
#eval FormalRV.QEC.derivedK (FormalRV.QEC.Algebraic.surfaceHGP 3)

/-! ## system — one surface-code surgery gadget as a Stim circuit + its footprint.
    GE2021's full schedule tiles ≈6200 such patches across a 20M-qubit device;
    here is a single distance-3 X-surgery gadget and its physical qubit count. -/
#eval FormalRV.LatticeSurgery.ScheduleEmit.emitScheduleStim
        [FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery]
#eval FormalRV.LatticeSurgery.ScheduleEmit.gadgetFootprint
        FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery

end FormalRV.Audit.GidneyEkera2021
