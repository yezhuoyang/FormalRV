/-
  FormalRV.PPM.Gadgets.QFT.AQFTCliffordTBoundary — the QFT leg of the
  per-gadget PPM programme: what is PROVEN about lowering the (approximate
  inverse) QFT toward PPM, and the NAMED contract for the rest.

  ## What is proven (reused, anchored here)

  * `aqft_ladder_isCliffordT`: the compiled cutoff-`c ≤ 2` AQFT phase ladder
    is CLIFFORD+T — its only non-Clifford content is T/T† (depth-1 half
    angles).  Consequence for PPM: realizing the AQFT needs ONLY T-type
    magic (`useT` in the new PPM program syntax) — no CCZ states.
  * `aqft_ladder_error_budget`: the dropped-rotation cost is ≤ 2π/2^c.

  ## The honest gap, as a named contract

  The Clifford+CCX `Gate` IR (this folder's compile source) has no H/S/T,
  so the AQFT ladder CANNOT be fed to `PPMCompilerSpec.compile` — phase
  rotations are outside the arithmetic fragment.  The deferred obligation is
  a compiler from Clifford+T `BaseUCom` circuits to the NEW PPM program
  syntax (`PPM/Syntax/Program.lean`), whose magic is T-only.  We name that
  obligation as `CliffordTToPPMProgContract` below (structural fields now,
  the semantic field arrives with the Phase-D semantics bridge) — exactly
  the named-contract discipline used for `teleportCCXRel`.

  No `sorry`, no `axiom` (the contract is a structure, not an assumption).
-/
import FormalRV.PPM.Gadgets.CompilerContract
import FormalRV.QFT.AQFTCompile
import FormalRV.PPM.Syntax.Program
import FormalRV.Resource.PPMCount

namespace FormalRV.PPM.Gadgets.QFTPPM

open FormalRV.Framework
open FormalRV.Framework.AQFTCompile
open FormalRV.Framework.CliffordTRotations

/-- **The AQFT ladder's non-Clifford content is T-only** (cutoff ≤ 2):
    anchored re-statement of `compileLadder_isCliffordT` — the PPM
    realization of the AQFT needs `useT`-class magic only. -/
theorem aqft_ladder_isCliffordT {dim : Nat} (c : Nat) (hc : c ≤ 2)
    (rs : List PhaseRot) :
    IsCliffordT (compileLadder c rs : BaseUCom dim) :=
  compileLadder_isCliffordT c hc rs

/-- Anchored re-statement of the AQFT approximation budget: ≤ 2π/2^c. -/
theorem aqft_ladder_error_budget (c n : ℕ) (hcn : c ≤ n) :
    ∑ m ∈ Finset.Ico c n, (Real.pi / 2 ^ m) ≤ 2 * Real.pi / 2 ^ c :=
  compileLadder_error_budget c n hcn

/-- **The NAMED deferred contract: Clifford+T circuits → the new PPM
    program syntax.**  Structural obligations stated now (well-formed
    output; T-only magic — no CCZ); the run-semantics correctness field is
    added when the Phase-D `compilePPM` semantics bridge lands.  Discharging
    this contract is what turns `aqft_ladder_isCliffordT` into "the AQFT is
    a concrete `PPMProg`". -/
structure CliffordTToPPMProgContract where
  /-- The compiler from Clifford+T `BaseUCom` circuits to `PPMProg`. -/
  compile : ∀ {dim : Nat}, BaseUCom dim → FormalRV.PPM.Prog.PPMProg
  /-- Output programs are well-formed. -/
  compile_wf : ∀ {dim : Nat} (u : BaseUCom dim),
      IsCliffordT u → (compile u).wf = true
  /-- Clifford+T input consumes NO CCZ magic — T states only. -/
  compile_tOnly : ∀ {dim : Nat} (u : BaseUCom dim),
      IsCliffordT u → FormalRV.Resource.countMagicCCZ (compile u) = 0

end FormalRV.PPM.Gadgets.QFTPPM
