import FormalRV.PPM.QECBridge.LayeredPPMQECInterface
import FormalRV.Core.QuantumGate
import FormalRV.PPM.Semantics.PPMOperational
import FormalRV.PPM.QECBridge.FactoryHierarchy
import FormalRV.PPM.Compiler.SurgeryGadgetLoweringAndQECInstance

namespace FormalRV.Framework.CircuitToPPMInterface
open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.LayeredArtifactInterface
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.Framework.LayeredPPMQECInterface
open FormalRV.Framework.Factory
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.Framework.LDPC
open FormalRV.System.AdderSystem
open FormalRV.System.CompressedRepeatSoundness

theorem toySurgeryQECTraceLoweringEvidence :
    SurgeryQECTraceLoweringEvidence
      toyQECGadgetSpec
      toySchedulableSurgeryGadget
      toySurgeryVerifiedBackendBlock.schedule :=
  { structuralMatch := toy_QECSpecMatchesSurgeryGadget
    scheduleEq      := toySurgeryVerifiedBackendBlock_schedule_eq_composed
    traceMatches    := toySurgeryComposedSchedule_trace_matches }

/-! ### §27.e Status after §27.

    Closed (toy trace lowering):
    * `SurgeryObs` — observation type for the surgery
      protocol shape; derives `DecidableEq`, `Repr`,
      `Inhabited`.
    * `syscallToSurgeryObs?` — per-SysCall projection.
    * `surgeryTraceOfSysCalls`, `surgeryTraceOfCompressedSchedule`
      — list-level + CompressedSchedule-level projections.
    * `expectedSingleRoundTrace` — the canonical six-element
      trace for a `tau_s = 1` surgery gadget.
    * `SurgeryTraceMatchesGadget` — equality predicate with
      a `Decidable` instance.
    * `toySurgeryTraceMatchesGadget` — closed by `decide`.
    * `toySurgeryComposedSchedule_trace_matches` — closed by
      `native_decide`.
    * `SurgeryQECTraceLoweringEvidence` — Prop bundle
      pairing structural match, schedule equation, and
      trace match.
    * `toySurgeryQECTraceLoweringEvidence` — the toy
      concrete instance.

    NOT attempted in this tick:
    * `compileSurgeryGadgetToSysCalls_trace_matches`
      (general theorem for arbitrary `g`): would require
      induction on `tau_s` since the round structure
      repeats.  The `SurgeryTraceMatchesGadget` predicate
      as currently formulated is single-round only; a
      multi-round version would generalise to
      `tau_s`-many fresh-ancilla / entangle / measure /
      decode cycles plus one trailing frame update.
      Left for a future tick.

    Honest open obligations (UNCHANGED):
    * **Full QEC logical correctness** — distance,
      fault-tolerance, syndrome correctness, decoder
      correctness, logical Pauli measurement semantics.
      Trace matching is necessary but FAR from sufficient.
    * `MagicInjectionObligations.CCX_ok` (§17) — Toffoli
      semantic proof remains open.
    * QPE / non-Clifford+T — rejected/deferred via §1.

    QEC semantic-lowering status after §27:
    * **Trace / spec lowering**: CLOSED for the toy
      `tau_s = 1` single-gadget case.
    * **General compiler trace lowering**: open (left as a
      future tick — needs induction on `tau_s`).
    * **Full logical QEC correctness**: STILL OPEN
      (semantic claims at the operator-algebra / state
      level are out of reach for this interface-level
      tick).

    All prior milestones (§11–§26) remain intact. -/

end FormalRV.Framework.CircuitToPPMInterface
