/-
  FormalRV.QEC.Gidney21.Resource
  ──────────────────────────────
  **RESOURCE PROOFS — counts walked from the compiled physical circuit.**

  Proofs ONLY; the compilation lives in `Compiler/`.  Every number is
  `measCountC` / qubit-counter walking the monolithic `gadgetPhysical g`,
  proven equal to its closed form via the structural recursion of
  `compilePPM` over the WHOLE program (no gadget × formula).
-/
import FormalRV.QEC.Gidney21.Compiler.Lower

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC FormalRV.QEC.Circuit FormalRV.QEC.LogicalLayout
open FormalRV.Resource
open FormalRV.Framework (Gate)

/-- One distance-27 patch is `729 + 728 = 1457` physical qubits. -/
theorem surface27_patchPhysQubits : patchPhysQubits surface27 = 1457 := by
  unfold patchPhysQubits surface27
  obtain ⟨hn, hx, hz⟩ := Codes.Surface.rotatedSurface27_counts
  rw [hn, hx, hz]

/-- **PHYSICAL QUBITS of a gadget**: `width · 1457` (one persistent d=27
patch per logical qubit, reused across all cycles). -/
theorem gadget_qubits (g : Gate) :
    boardPhysQubits (gadgetBoard g) = Resource.width g * 1457 := by
  show boardPhysQubits (uniformBoard surface27 (Resource.width g)) = _
  rw [uniformBoard_physQubits, surface27_patchPhysQubits]

private theorem board_check_sum (g : Gate) :
    ((gadgetBoard g).map (fun b => b.code.hx.length
        + b.code.hz.length)).sum = Resource.width g * 728 := by
  show ((uniformBoard surface27 (Resource.width g)).map _).sum = _
  unfold uniformBoard
  obtain ⟨_, hx, hz⟩ := Codes.Surface.rotatedSurface27_counts
  induction Resource.width g with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.map_cons, List.sum_cons, ih]
      unfold surface27
      rw [hx, hz]
      ring

/-- **SYNDROME MEASUREMENTS of the whole gadget circuit**, by WALKING the
monolithic object: `#physical-PPM-statements · 27 · (width · 728)`. -/
theorem gadget_measCount (g : Gate) :
    measCountC (gadgetPhysical g)
      = physicalStmtCount (gadgetPPM g) * (27 * (Resource.width g * 728)) := by
  show measCountC (compileToPhysical (gadgetBoard g) (gadgetPPM g)) = _
  rw [compileToPhysical, compilePPM_measCount, board_check_sum]

end FormalRV.QEC.Gidney21
