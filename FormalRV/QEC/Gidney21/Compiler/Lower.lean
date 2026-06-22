/-
  FormalRV.QEC.Gidney21.Compiler.Lower
  ────────────────────────────────────
  **THE COMPILER (definitions only, no proofs).**

  A pure pipeline of functions, each `<syntactic object> → <syntactic
  object>`, with NO theorems mixed in — so the compilation can be read and
  re-run independently of the verification (which lives in `../Resource.lean`
  and `../Correctness.lean`):

      Gate  ──gadgetPPM (gateRots ∘ lowerFlat)──▶  PPMProg
            ──compileToPhysical (= compilePPM @ d=27)──▶  PhysCircuit
            ──toStim──▶  Stim program string.

  `compileToPhysical` is the reusable core: it takes a PPM syntactic object
  (over a declared surface-code board) and emits the detailed physical
  circuit with full syndrome extraction.
-/
import FormalRV.QEC.Gidney21.Compiler.Board
import FormalRV.PauliRotation.Compiler.ToPPM.LoweredInstances

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC FormalRV.QEC.Circuit FormalRV.QEC.LogicalLayout
open FormalRV.Resource FormalRV.PauliRotation
open FormalRV.Framework (Gate)

/-- **THE PPM → DETAILED-PHYSICAL COMPILER (d = 27)**: given a board of
surface patches and ANY PPM program (a syntactic object), emit the
monolithic physical circuit — full 27-round syndrome extraction per cycle on
the persistent patches.  This is the reusable entry point John specified:
PPM object in, physical object out. -/
def compileToPhysical (board : List CodeBlock)
    (ppm : FormalRV.PPM.Prog.PPMProg) : PhysCircuit :=
  compilePPM board 27 ppm

/-- The gadget's PPM program — the EXACT object the PauliRotation layer's
`LoweredOK` instance verifies (`lowerFlat (width g) 0 (gateRots g)`); nothing
new is invented. -/
def gadgetPPM (g : Gate) : FormalRV.PPM.Prog.PPMProg :=
  lowerFlat (Resource.width g) 0 (gateRots g)

/-- **Compile a gadget all the way to the monolithic physical circuit.** -/
def gadgetPhysical (g : Gate) : PhysCircuit :=
  compileToPhysical (gadgetBoard g) (gadgetPPM g)

/-- The gadget's full physical circuit as a Stim program string. -/
def gadgetStim (g : Gate) : String := toStim (gadgetPhysical g)

end FormalRV.QEC.Gidney21
