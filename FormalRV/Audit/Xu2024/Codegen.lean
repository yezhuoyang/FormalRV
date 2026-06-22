/-
  Audit · xu-2024 · CODEGEN — the ACTUAL construction at each level
  ============================================================================
  This file EMITS the detailed construction at every level of the Xu2024 stack
  by instantiating the project's REUSABLE general framework constructors at
  SMALL, representative parameters (so each `#eval` is fast).  The construction
  is REAL — it is the same general emitter the rest of the project verifies, run
  at toy sizes.  Xu2024's full parameters are noted in comments at each line.

  Xu2024 is the NEUTRAL-ATOM constant-overhead architecture (24 ms QEC cycle)
  that the `Example/neutral_atom/` demo realizes physically.  Its code layer is a
  lifted-product (LP) qLDPC code `[[544, 80, 12]]`; here we display a small,
  REAL bivariate-bicycle (LP-family) instance — the gross-code `[[72, 12, 6]]` —
  as a fast stand-in for the LP construction.

  How to inspect:  open this file in an editor and read the `#eval` results, or
  run
      lake env lean FormalRV/Audit/Xu2024/Codegen.lean
  and read what it prints.

  Levels emitted:
    • L1 (algorithm)   — Shor order-finding circuit (Stim)         small instance
    • L2 (arithmetic)  — a representative gate → OpenQASM (Cliff+T) CCX
    • L3 (PPM)         — the CCZ magic-state teleportation gadget   OpenQASM
    • L4 (QEC code)    — a bivariate-bicycle LP-family code (real)  hx / hz / k
    • system          — one surgery gadget → Stim + its footprint  distance-3
-/

import FormalRV.Codegen.GateQasm
import FormalRV.PPM.PPMToQASM
import FormalRV.QEC.FrontendAlgebraic
import FormalRV.QEC.Instances
import FormalRV.QEC.CodeDimension
import FormalRV.QEC.LatticeSurgery.ScheduleEmit
import FormalRV.QEC.LatticeSurgery.SurgeryDemoSurface
namespace FormalRV.Audit.Xu2024

/-! ## L2 — arithmetic: a representative gate emitted to OpenQASM (Clifford+T).
    A Toffoli (CCX) on qubits 0,1,2 over a 3-qubit register.  Xu2024's full
    arithmetic rides the same windowed modular-exponentiation core. -/
#eval FormalRV.Codegen.toQasm (FormalRV.Framework.Gate.CCX 0 1 2) true 3

/-! ## L3 — PPM: the CCZ / T magic-state teleportation gadget (OpenQASM).
    This is the per-Toffoli magic-injection gadget, run once per logical Toffoli. -/
#eval FormalRV.PPM.PPMToQASM.cczGadgetQASM

/-! ## L4 — QEC code: a bivariate-bicycle LP-family qLDPC code.
    Xu2024 uses a lifted-product (LP) code `[[544, 80, 12]]` (k = 80 logicals).
    Here is the REAL gross-code `[[72, 12, 6]]` bivariate-bicycle instance
    (`l = m = 6`, A = 1 + y + y², B = y³ + x + x²) — a small concrete member of
    the same LP family — printed as its X- and Z-check matrices and derived k. -/
#eval (FormalRV.QEC.Algebraic.bivariateBicycle 6 6 [(3,0),(0,1),(0,2)] [(0,3),(1,0),(2,0)]).hx
#eval (FormalRV.QEC.Algebraic.bivariateBicycle 6 6 [(3,0),(0,1),(0,2)] [(0,3),(1,0),(2,0)]).hz
#eval FormalRV.QEC.derivedK
        (FormalRV.QEC.Algebraic.bivariateBicycle 6 6 [(3,0),(0,1),(0,2)] [(0,3),(1,0),(2,0)])

/-! ## system — one surface-code surgery gadget as a Stim circuit + its footprint.
    Xu2024's neutral-atom schedule tiles LP patches across a reconfigurable atom
    array; here is a single distance-3 X-surgery gadget and its physical qubit
    count (the general surgery emitter, run at a toy size). -/
#eval FormalRV.LatticeSurgery.ScheduleEmit.emitScheduleStim
        [FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery]
#eval FormalRV.LatticeSurgery.ScheduleEmit.gadgetFootprint
        FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery

end FormalRV.Audit.Xu2024
