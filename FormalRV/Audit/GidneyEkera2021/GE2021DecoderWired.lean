/-
  FormalRV.Audit.GidneyEkera2021.GE2021DecoderWired — wire the decoder-backlog model into the
  GE2021 system context as a COMPOSED `SpaceTimeInvariant`, so `checkAll` itself
  rejects a decoder-under-provisioned schedule.

  The audit's TOP-1 gap was that the decoder load was named but never bound.  Here
  we make it a first-class system constraint that composes with the resource (A)
  and causal (B) invariants on the SAME `ge2021Ctx`: a machine whose classical
  decode fabric cannot keep up (lanes < patches·decodeLatency) now FAILS the unified
  `checkAll`, exactly as a qubit-capacity or causality violation would.

  No `sorry`, no new `axiom`.
-/

import FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Architecture
import FormalRV.System.DecoderBacklogModel

namespace FormalRV.Audit.GidneyEkera2021.GE2021DecoderWired

open FormalRV.Framework.InvariantFramework
open FormalRV.System.DependencyGraph
open FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Architecture
open FormalRV.LatticeSurgery.SurfaceShorFullSchedule
open FormalRV.System.DecoderBacklogModel

/-- The decoder-backlog invariant: the schedule is decoder-SOUND iff the decode
    fabric is backlog-free (lanes ≥ patches·decodeLatency).  Wraps the parametric
    `DecoderBacklogModel.backlogFree` as a `SpaceTimeInvariant`, so it ANDs into
    `checkAll` like any resource or causal constraint. -/
def decoderBacklogInv (patches decodeLatency lanes : Nat) : SpaceTimeInvariant :=
  { name  := "decoder backlog-free (lanes ≥ patches·decodeLatency)",
    check := fun _ => backlogFree patches decodeLatency lanes }

/-- GE2021 decode load: 6200 patches, 10-cycle (10 µs) decode latency. -/
def ge2021DecoderInv (lanes : Nat) : SpaceTimeInvariant := decoderBacklogInv 6200 10 lanes

/-! ## The unified check now includes the decoder -/

/-- **Provisioned (62 000 lanes): the full check passes** — resource (A) ∧ causality
    (B) ∧ decoder throughput, all on `ge2021Ctx`. -/
theorem ge2021_fully_valid_with_decoder :
    checkAll (baseInvariants ++ [causalityInv shorDeps, ge2021DecoderInv 62_000]) ge2021Ctx = true := by
  decide

/-- **Under-provisioned (6200 lanes, one per patch): the unified check REJECTS** —
    the decoder fabric cannot keep up, so the schedule is invalid even though the
    qubits fit and causality holds. -/
theorem ge2021_underprovisioned_decoder_rejected :
    checkAll (baseInvariants ++ [ge2021DecoderInv 6200]) ge2021Ctx = false := by
  decide

/-- …and it is SPECIFICALLY the decoder that fails: resource (A) still holds on the
    very same context (the classical decode fabric is the binding constraint, not
    the 20 M qubits). -/
theorem ge2021_decoder_is_the_culprit :
    checkAll baseInvariants ge2021Ctx = true
    ∧ (ge2021DecoderInv 6200).check ge2021Ctx = false := by
  exact ⟨ge2021Ctx_resource_ok, by decide⟩

/-- The provisioning threshold composes cleanly (extensibility): adding the decoder
    invariant ANDs in its check without disturbing the others. -/
theorem decoder_inv_composes (lanes : Nat) :
    checkAll (baseInvariants ++ [ge2021DecoderInv lanes]) ge2021Ctx
      = (checkAll baseInvariants ge2021Ctx && (ge2021DecoderInv lanes).check ge2021Ctx) :=
  checkAll_snoc baseInvariants (ge2021DecoderInv lanes) ge2021Ctx

end FormalRV.Audit.GidneyEkera2021.GE2021DecoderWired
