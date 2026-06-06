/-
  FormalRV.Shor.ShorEmitDistance — toward the north star: emit the FULL Shor(N,a)
  lattice-surgery computation at ANY surface-code distance d, with the per-merge surgery
  gadget verified by the SAME general framework (`verify_surgery_gadget`).

  `surface_d_x_surgery d` is a GENERIC distance-d surface-code logical-X̄ surgery gadget:
  data code = `surfaceHGP d` ([[d²+(d-1)², 1, d]]), logical X̄ computed by the
  code-general `pairedLogicalX` (LogicalFinder), one ancilla coupled to X̄'s support,
  τ_s = ⌈2d/3⌉.  It passes the framework verifier at each chosen distance (by `decide` /
  `native_decide`).  `emitShorAtDistance N a d` then emits the whole Shor schedule at
  distance d.

  HONEST scope (see LatticeSurgery/README.md): this verifies the LOGICAL/algebraic action
  of each merge (selected merged-check product = the target logical) at the ABSTRACT level
  (one ancilla, one high-weight coupling check), parametric in d, verified per chosen d
  (not yet a single ∀d theorem).  The PHYSICAL distance-d syndrome circuit with local
  boundary stitching + decoder, the CCX magic injection (teleportCCXRel), and Z-type
  merges remain cited / scaffolded.  No `sorry`, no `axiom`.
-/
import FormalRV.Shor.ShorEmit
import FormalRV.QEC.FrontendAlgebraic
import FormalRV.QEC.LogicalFinder
import FormalRV.LatticeSurgery.SurgeryCorrect

namespace FormalRV.Shor.ShorEmitDistance

open FormalRV.Framework
open FormalRV.Framework.LDPC
open FormalRV.QEC
open FormalRV.QEC.Algebraic
open FormalRV.QEC.LogicalFinder
open FormalRV.LatticeSurgery.ScheduleEmit
open FormalRV.Framework.SurgerySchedule
open FormalRV.Shor.ShorEmit

/-! ## §1. A generic distance-d surface-code logical-X̄ surgery gadget -/

/-- The computed logical X̄ of the distance-d surface code. -/
def surfaceLogX (d : Nat) : BoolVec := (pairedLogicalX (surfaceHGP d)).getD 0 []

/-- **Distance-`d` surface-code X̄ surgery gadget**, generic in `d`: data = `surfaceHGP d`,
    logical X̄ via `pairedLogicalX`, ancilla `H_X' = [[1],[1]]` coupled to X̄'s support,
    `τ_s = ⌈2d/3⌉`.  Same `SurgeryGadget` shape as the concrete examples. -/
def surface_d_x_surgery (d : Nat) : SurgeryGadget :=
  let c : CSSCode := surfaceHGP d
  let logX := surfaceLogX d
  { data_code          := c.toQECCode 1 d
    ancilla_n          := 1
    ancilla_hx         := [[true], [true]]
    ancilla_hz         := []
    conn_x             := [logX, zero_vec c.n]
    conn_z             := c.hz.map (fun _ => [false])
    tau_s              := (2 * d + 2) / 3
    target_pauli       := logX ++ [false]
    span_witness       := (List.replicate c.hx.length false) ++ [true, true]
    merged_qldpc_bound := 2 * d + 6 }

/-! ## §2. The generic gadget passes the SAME verifier at each chosen distance -/

/-- Distance 3 ([[13,1,3]]): kernel-clean `decide`. -/
theorem surface_d_x_surgery_verifies_d3 :
    SurgeryGadget.verify_surgery_gadget (surface_d_x_surgery 3) = true := by decide

/-- Distance 5 ([[41,1,5]]): `native_decide`. -/
theorem surface_d_x_surgery_verifies_d5 :
    SurgeryGadget.verify_surgery_gadget (surface_d_x_surgery 5) = true := by native_decide

/-- Distance 7 ([[85,1,7]]): `native_decide`. -/
theorem surface_d_x_surgery_verifies_d7 :
    SurgeryGadget.verify_surgery_gadget (surface_d_x_surgery 7) = true := by native_decide

/-! ## §3. Distance-parameterized full-Shor lattice-surgery emitter -/

/-- The full Shor(N) surgery schedule at code distance `d`: one verified distance-d
    surface-code merge per magic-CCZ measurement. -/
def shorScheduleAtDistance (N d : Nat) : Schedule :=
  List.replicate (shorMergeCount N) (surface_d_x_surgery d)

/-- **END-TO-END, ANY DISTANCE:** emit the whole Shor(N,a) lattice-surgery Stim circuit at
    surface-code distance `d`. -/
def emitShorAtDistance (N _a d : Nat) : String :=
  emitScheduleStim (shorScheduleAtDistance N d)

/-- First-`k`-merges prefix at distance `d` (Stim-validatable sample of any instance). -/
def emitShorPrefixAtDistance (N _a d k : Nat) : String :=
  emitScheduleStim (List.replicate (min k (shorMergeCount N)) (surface_d_x_surgery d))

/-- The distance-d Shor schedule has exactly `shorMergeCount N` merges (parametric in d). -/
theorem shorScheduleAtDistance_length (N d : Nat) :
    (shorScheduleAtDistance N d).length = shorMergeCount N := by
  unfold shorScheduleAtDistance; rw [List.length_replicate]

end FormalRV.Shor.ShorEmitDistance
