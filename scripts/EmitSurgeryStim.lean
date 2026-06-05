/-
  Emit the PHYSICAL syndrome-extraction + merge circuit of the verified distance-3 two-patch
  surface-code XX-merge (`surface3_xx_merge`, joint X̄₁X̄₂ of two [[13,1,3]] patches) as a Stim
  program, for compilation onto a neutral-atom architecture by ZAC.
    `lake env lean --run scripts/EmitSurgeryStim.lean`
  Output: Example/neutral_atom/surface3_xx_merge.stim
-/
import FormalRV.LatticeSurgery.StimEmit
import FormalRV.Corpus.SurgeryDemoMerge

open FormalRV.LatticeSurgery.StimEmit
open FormalRV.Corpus.SurgeryDemoMerge

def main : IO Unit := do
  IO.FS.createDirAll "Example/neutral_atom"
  let stim := surgeryToStim surface3_xx_merge
  let lineCount := (stim.splitOn "\n").length
  IO.FS.writeFile "Example/neutral_atom/surface3_xx_merge.stim" stim
  IO.println s!"emitted surface3_xx_merge.stim ({lineCount} lines)"
