/-
  Audit · gidney-2025 · CODEGEN — the ACTUAL construction at each level
  ============================================================================
  This file EMITS the detailed construction at every level of the Gidney-2025
  stack by instantiating the project's REUSABLE general framework constructors
  at SMALL, representative parameters (so each `#eval` is fast).  The
  construction is REAL — it is the same general emitter the rest of the project
  verifies, run at toy sizes.  Gidney-2025's full parameters are noted in
  comments at each line.

  Gidney-2025's real strength is its CFS residue-arithmetic ENGINE — proved
  bottom-up and axiom-clean, and `#verify_clean`'d in `L2_Arithmetic.lean`
  (exact RNS modexp via CRT injectivity, exact CRT reconstruction with a
  constructed basis, bounded truncation error).  This file complements that by
  printing the generic per-level constructions.

  How to inspect:  open this file in an editor and read the `#eval` results, or
  run
      lake env lean FormalRV/Audit/Gidney2025/Codegen.lean
  and read what it prints.

  Levels emitted:
    • L1 (algorithm)   — Shor order-finding circuit (Stim)         small instance
    • L2 (arithmetic)  — a representative gate → OpenQASM (Cliff+T) CCX
    • L3 (PPM)         — the CCZ magic-state teleportation gadget   OpenQASM
    • L4 (QEC code)    — the rotated surface code (real d=3 build)  hx / hz / k
    • system          — one surgery gadget → Stim + its footprint  distance-3
-/

import FormalRV.Codegen.GateQasm
import FormalRV.PPM.PPMToQASM
import FormalRV.QEC.FrontendAlgebraic
import FormalRV.QEC.Instances
import FormalRV.QEC.CodeDimension
import FormalRV.QEC.LatticeSurgery.ScheduleEmit
import FormalRV.QEC.LatticeSurgery.SurgeryDemoSurface
namespace FormalRV.Audit.Gidney2025

/-! ## L2 — arithmetic: a representative gate emitted to OpenQASM (Clifford+T).
    A Toffoli (CCX) on qubits 0,1,2 over a 3-qubit register.  Gidney-2025's full
    arithmetic is the CFS approximate-residue modular exponentiation
    (≈6.5×10⁹ Toffolis), whose engine is verified axiom-clean in L2_Arithmetic. -/
#eval FormalRV.Codegen.toQasm (FormalRV.Framework.Gate.CCX 0 1 2) true 3

/-! ## L3 — PPM: the CCZ / T magic-state teleportation gadget (OpenQASM).
    This is the per-Toffoli magic-injection gadget Gidney-2025 runs ≈6.5×10⁹ times
    (fed by cultivation + 8T→CCZ factories). -/
#eval FormalRV.PPM.PPMToQASM.cczGadgetQASM

/-! ## L4 — QEC code: the rotated surface code.
    Gidney-2025 uses a HOT distance d=25 surface code (2(d+1)² = 1352 physical
    qubits per logical tile), plus yoked cold storage (430 phys/logical).
    Here is the REAL distance-3 surface-code construction (HGP), printed as its
    X- and Z-check matrices and its derived logical dimension k. -/
#eval (FormalRV.QEC.Algebraic.surfaceHGP 3).hx
#eval (FormalRV.QEC.Algebraic.surfaceHGP 3).hz
#eval FormalRV.QEC.derivedK (FormalRV.QEC.Algebraic.surfaceHGP 3)

/-! ## system — one surface-code surgery gadget as a Stim circuit + its footprint.
    Gidney-2025's full schedule tiles ≈1537 logical patches under a 1M-qubit
    device; here is a single distance-3 X-surgery gadget and its physical qubit
    count. -/
#eval FormalRV.LatticeSurgery.ScheduleEmit.emitScheduleStim
        [FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery]
#eval FormalRV.LatticeSurgery.ScheduleEmit.gadgetFootprint
        FormalRV.LatticeSurgery.SurgeryDemoSurface.surface3_x_surgery

end FormalRV.Audit.Gidney2025
