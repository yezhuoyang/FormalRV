/-
  FormalRV.QEC.Gidney21.Correctness
  ─────────────────────────────────
  **SEMANTIC-CORRECTNESS PROOFS — separated from compilation.**

  The two pillars, reused from the existing layers (no new proof of the
  physics): the gadget's PPM program implements its Boolean semantics
  (`LoweredOK`, from PauliRotation) AND each surface patch's syndrome
  extraction measures the [[729,1,27]] stabilizers (parametric, kernel-pure).
-/
import FormalRV.QEC.Gidney21.Compiler.Lower

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC FormalRV.QEC.Circuit FormalRV.QEC.LogicalLayout
open FormalRV.PauliRotation
open FormalRV.Framework (Gate)

/-- **Each patch's syndrome extraction is correct** (parametric, kernel-pure):
the detailed `prep/cx/meas` round of the d=27 patch measures EXACTLY the
`[[729,1,27]]` stabilizers. -/
theorem patch_extraction_correct :
    Round.measuredDataObs
        ((Codes.Surface.rotatedSurface 27).n
          + (Codes.Surface.rotatedSurface 27).hx.length
          + (Codes.Surface.rotatedSurface 27).hz.length)
        (Codes.Surface.rotatedSurface 27).n
        (CSSCode.extractionRound surface27.code)
      = surface27.code.toStabilizers :=
  rotatedExtraction_measures_stabilizers 27

/-- **The packaged per-gadget claim**: PPM-implements-the-gadget AND
patch-extraction-is-correct. -/
def GadgetCompiledOK (g : Gate) : Prop :=
  LoweredOK g
    ∧ Round.measuredDataObs
        ((Codes.Surface.rotatedSurface 27).n
          + (Codes.Surface.rotatedSurface 27).hx.length
          + (Codes.Surface.rotatedSurface 27).hz.length)
        (Codes.Surface.rotatedSurface 27).n
        (CSSCode.extractionRound surface27.code)
      = surface27.code.toStabilizers

/-- Assemble `GadgetCompiledOK` from a gadget's EXISTING `LoweredOK` instance
plus the shared physical-correctness anchor. -/
theorem gadgetCompiledOK_of (g : Gate) (hppm : LoweredOK g) :
    GadgetCompiledOK g :=
  ⟨hppm, patch_extraction_correct⟩

end FormalRV.QEC.Gidney21
