/-
  FormalRV.QEC.Gidney21.Compiler.Board
  ────────────────────────────────────
  **COMPILER — qubit-layout stage (definitions only, no proofs).**

  Allocates one distance-27 rotated surface patch per logical qubit of a
  gadget.  Pure compilation: the proofs about it live in `../Resource.lean`
  and `../Correctness.lean`.
-/
import FormalRV.QEC.LogicalLayout.StimDriver

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC FormalRV.QEC.LogicalLayout FormalRV.Resource
open FormalRV.Framework (Gate)

/-- The GE2021 data patch: the rotated `[[729,1,27]]` surface code, one
logical qubit. -/
def surface27 : CodeBlock :=
  ⟨"sd27", Codes.Surface.rotatedSurface 27, 1, ⟨fun _ => [], fun _ => []⟩⟩

/-- One distance-27 patch per logical qubit of the gadget. -/
def gadgetBoard (g : Gate) : List CodeBlock :=
  uniformBoard surface27 (Resource.width g)

end FormalRV.QEC.Gidney21
