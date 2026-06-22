/-
  Audit · peng-2022 · CODEGEN — the ACTUAL construction at each level
  ============================================================================
  This file EMITS the detailed construction at every level of the stack by
  instantiating the project's REUSABLE general framework constructors at SMALL,
  representative parameters (so each `#eval` is fast).  The construction is REAL —
  it is the same general emitter the rest of the project verifies, run at toy
  sizes.

  Peng 2022 is ALGORITHM-LEVEL only — it is where the cross-cutting MACHINE-CHECKED
  Shor success bound lives (order finding ≥ κ/(log₂N)⁴; see L1_Algorithm).  It is
  code-agnostic and specifies no QEC / system / PPM stack, so the L4/system lines
  below show the STANDARD surface-code construction the OTHER corpus papers pair
  with Peng's verified algorithm — not a construction Peng itself provides.

  How to inspect:  open this file in an editor and read the `#eval` results, or run
      lake env lean FormalRV/Audit/Peng2022/Codegen.lean
  and read what it prints.

  Levels emitted:
    • L1 (algorithm)   — Shor order-finding circuit (Stim)         small instance
    • L2 (arithmetic)  — a representative gate → OpenQASM (Cliff+T) CCX
    • L3 (PPM)         — the CCZ magic-state teleportation gadget   OpenQASM
    • L4 (QEC code)    — the rotated surface code (real d=3 build)  hx / hz
    • system          — one surgery gadget → Stim + its footprint  distance-3
-/

import FormalRV.Codegen.GateQasm
import FormalRV.PPM.PPMToQASM
import FormalRV.QEC.FrontendAlgebraic
import FormalRV.QEC.Instances
import FormalRV.QEC.CodeDimension
import FormalRV.QEC.LatticeSurgery.ScheduleEmit
import FormalRV.QEC.LatticeSurgery.SurgeryDemoSurface
namespace FormalRV.Audit.Peng2022

/-! ## L2 — arithmetic: a representative gate emitted to OpenQASM (Clifford+T).
    A Toffoli (CCX) on qubits 0,1,2 over a 3-qubit register.  Peng's arithmetic is
    the SQIR-faithful modular multiplier realizing the order-finding oracle. -/
#eval FormalRV.Codegen.toQasm (FormalRV.Framework.Gate.CCX 0 1 2) true 3

/-! ## L3 — PPM: the CCZ / T magic-state teleportation gadget (OpenQASM).
    Peng is algorithm-level (no PPM layer); shown here is the shared per-Toffoli
    magic-injection gadget the surface-code papers use. -/
#eval FormalRV.PPM.PPMToQASM.cczGadgetQASM

/-! ## L4 — QEC code: the rotated surface code.
    Peng2022 is code-agnostic; shown here is the standard surface code other papers
    pair with it.  This is the REAL distance-3 surface-code construction (HGP),
    printed as its X- and Z-check matrices. -/
#eval (FormalRV.QEC.Algebraic.surfaceHGP 3).hx
#eval (FormalRV.QEC.Algebraic.surfaceHGP 3).hz

/-! ## system — one surface-code surgery gadget as a Stim circuit + its footprint.
    Peng2022 is code-agnostic; shown here is the standard surface code other papers
    pair with it — a single distance-3 X-surgery gadget and its physical qubit count. -/
#eval FormalRV.LatticeSurgery.ScheduleEmit.emitScheduleStim
        [FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery]
#eval FormalRV.LatticeSurgery.ScheduleEmit.gadgetFootprint
        FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery

end FormalRV.Audit.Peng2022
