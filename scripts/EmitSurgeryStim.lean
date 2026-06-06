/-
  Emit the PHYSICAL syndrome-extraction + merge circuit of the verified distance-3 two-patch
  surface-code XX-merge (`surface3_xx_merge`, joint X̄₁X̄₂ of two [[13,1,3]] patches) as a Stim
  program, for compilation onto a neutral-atom architecture by ZAC.
    `lake env lean --run scripts/EmitSurgeryStim.lean`
  Output: Example/neutral_atom/surface3_xx_merge.stim
-/
import FormalRV.LatticeSurgery.StimEmit
import FormalRV.Audit.Common.SurgeryDemoMerge
import FormalRV.Audit.Common.SurgeryDemoCNOT

open FormalRV.LatticeSurgery.StimEmit
open FormalRV.Framework.LDPC
open FormalRV.Audit.Common.SurgeryDemoMerge
open FormalRV.Audit.Common.SurgeryDemoCNOT

def emit (name : String) (g : SurgeryGadget) : IO Unit := do
  let stim := surgeryToStim g
  let lc := (stim.splitOn "\n").length
  IO.FS.writeFile s!"Example/neutral_atom/{name}.stim" stim
  IO.println s!"emitted {name}.stim ({lc} lines)"

def main : IO Unit := do
  IO.FS.createDirAll "Example/neutral_atom"
  emit "surface3_xx_merge" surface3_xx_merge        -- joint X̄₁X̄₂ (building block)
  emit "surface3_zz_merge" surface3_zz_merge        -- joint Z̄₁Z̄₂  (2-patch full merge TEMPLATE)
  emit "surface3_zzz_merge" surface3_zzz_merge      -- joint Z̄₁Z̄₂Z̄₃ (3-patch full merge TEMPLATE)
