/-
  FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderUncomputeCascade
  Re-export umbrella for the `UncomputeCascade/` sub-folder, split by sub-topic:
    FrameLemmas → Correctness → WellTypedBackbone
  (the backbone holds `gidney_adder_patched_primitive`). Kept at this path so
  external importers resolve unchanged.
-/
import FormalRV.Arithmetic.RippleCarryAdder.UncomputeCascade.FrameLemmas
import FormalRV.Arithmetic.RippleCarryAdder.UncomputeCascade.Correctness
import FormalRV.Arithmetic.RippleCarryAdder.UncomputeCascade.WellTypedBackbone
