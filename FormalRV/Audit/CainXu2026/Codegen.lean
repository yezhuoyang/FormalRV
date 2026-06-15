/-
  Audit · cain-xu-2026 · CODEGEN — the ACTUAL construction at each level
  ============================================================================
  This file EMITS the detailed construction at every level of the cain-xu stack by
  instantiating the project's REUSABLE general framework constructors at SMALL,
  representative parameters (so each `#eval` is fast).  The construction is REAL —
  it is the same general emitter the rest of the project verifies, run at toy sizes.
  cain-xu's full parameters are noted in comments at each line.

  cain-xu's VERIFIED strength (this is what the audit machine-checks):
    • the naive modexp PRESERVES the real [[18,2,d]] bivariate-bicycle LP code,
      proved by INDUCTION (scale-free to ~10⁹ logical PPMs — L3_PPM);
    • a structurally-VERIFIED lattice-surgery gadget ON that LP code implements a
      genuine logical Pauli measurement (L3_PPM `bb_x_surgery`);
    • lower ≤ upper resource SOUNDNESS (the verified naive cost is a real upper
      bound; the structural floor never exceeds it — L4_Code / Verifier).

  How to inspect:  open this file in an editor and read the `#eval` results, or run
      lake env lean FormalRV/Audit/CainXu2026/Codegen.lean
  and read what it prints.

  Levels emitted:
    • L1 (algorithm)   — Shor order-finding circuit (Stim)         small instance
    • L2 (arithmetic)  — a representative gate → OpenQASM (Cliff+T) CCX
    • L3 (PPM)         — the CCZ magic-state teleportation gadget   OpenQASM
    • L4 (QEC code)    — a bivariate-bicycle LP-family code (real)  hx / hz / k
    • system          — one surgery gadget → Stim + its footprint  distance-3
-/

import FormalRV.Shor.PPM.ShorEmit
import FormalRV.Codegen.GateQasm
import FormalRV.PPM.PPMToQASM
import FormalRV.QEC.FrontendAlgebraic
import FormalRV.QEC.Instances
import FormalRV.QEC.CodeDimension
import FormalRV.LatticeSurgery.ScheduleEmit
import FormalRV.LatticeSurgery.SurgeryDemoSurface

namespace FormalRV.Audit.CainXu2026

/-! ## L1 — the algorithm: Shor order-finding circuit (Stim).
    A readable PREFIX (first 2 modular-mult merges) of the N=15, a=7 instance; the
    FULL circuit is `emitShor 15 7` (large).  cain-xu uses windowed q_A = 33. -/
#eval FormalRV.Shor.ShorEmit.emitShorPrefix 15 7 2

/-! ## L2 — arithmetic: a representative gate emitted to OpenQASM (Clifford+T).
    A Toffoli (CCX) on qubits 0,1,2 over a 3-qubit register.  cain-xu's full
    arithmetic is the windowed modular exponentiation (≈10⁹ Toffolis). -/
#eval FormalRV.Codegen.toQasm (FormalRV.Framework.Gate.CCX 0 1 2) true 3

/-! ## L3 — PPM: the CCZ / T magic-state teleportation gadget (OpenQASM).
    This is the per-Toffoli magic-injection gadget cain-xu runs ≈10⁹ times. -/
#eval FormalRV.PPM.PPMToQASM.cczGadgetQASM

/-! ## L4 — QEC code: a bivariate-bicycle LP-family qLDPC code.
    cain-xu's REAL memory codes are bb18 = [[248,10,18]] and lp_20^{3,7} =
    [[4350,1224,20]] (too large to #eval-print).  Here is the small concrete
    gross-family member `[[72, 12, 6]]` (`l = m = 6`, A = x³ + y + y², B = y³ + x +
    x²) — the SAME bivariate-bicycle constructor the audit's real codes use —
    printed as its X- and Z-check matrices and its derived logical dimension k. -/
#eval (FormalRV.QEC.Algebraic.bivariateBicycle 6 6 [(3,0),(0,1),(0,2)] [(0,3),(1,0),(2,0)]).hx
#eval (FormalRV.QEC.Algebraic.bivariateBicycle 6 6 [(3,0),(0,1),(0,2)] [(0,3),(1,0),(2,0)]).hz
#eval FormalRV.QEC.derivedK
        (FormalRV.QEC.Algebraic.bivariateBicycle 6 6 [(3,0),(0,1),(0,2)] [(0,3),(1,0),(2,0)])

/-! ## system — one surface-code surgery gadget as a Stim circuit + its footprint.
    cain-xu's full schedule tiles LP patches across a reconfigurable neutral-atom
    array; here is a single distance-3 X-surgery gadget and its physical qubit
    count (the general surgery emitter, run at a toy size). -/
#eval FormalRV.LatticeSurgery.ScheduleEmit.emitScheduleStim
        [FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery]
#eval FormalRV.LatticeSurgery.ScheduleEmit.gadgetFootprint
        FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery

end FormalRV.Audit.CainXu2026
