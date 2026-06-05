/-
  FormalRV.System.FTFramework — the SINGLE coherent entry point for the fault-tolerant scheduling
  framework, tying together the two subsystems that grew in parallel:

    * canonical hardware            — `HardwareParams.MachineParams` (incl. the one decoder-reaction
                                       budget, reconciled across all four records);
    * schedule well-formedness      — `DeviceSchedule.scheduleValid` (conflict / wait / capacity /
                                       decoder / reaction) and `ScheduleInv.all_invariants_ok`;
    * resource BRACKET              — `ScheduleBounds.resource_bracket` (lower floor ≤ workload ≤
                                       upper ceiling) + `naive_peak_le_total` (peak ≤ footprint);
    * hardware SENSITIVITY          — `HardwareSensitivity.HW.timeLB` (max-of-four-floors bound,
                                       monotone in every hardware parameter).

  `FTSystem` bundles the hardware + device + schedule, and `ftSystem_naive_guarantee` certifies — for
  ANY size, without enumeration — that a well-formed naive system is valid, reaction-bounded, and
  footprint-bounded.  The GE2021 instance is proven PARAMETRICALLY (never instantiating the
  ~8×10⁹-op schedule concretely).
-/
import FormalRV.System.ScheduleBounds
import FormalRV.System.HardwareSensitivity
import FormalRV.System.FaultTolerantSchedule

namespace FormalRV.System.FTFramework

open FormalRV.System.DeviceSchedule
open FormalRV.System.NaiveSchedule
open FormalRV.System.ScheduleBounds
open FormalRV.System.HardwareParams

/-- A fault-tolerant system under test: canonical hardware + the device view + the schedule, with
    the horizon / floor inputs for the resource bracket. -/
structure FTSystem where
  hw    : MachineParams
  dev   : Device
  sched : DSchedule
  T     : Nat
  fq    : Nat
  prod  : Nat

/-- Well-formedness (for finite schedules): the schedule is valid AND the device mirrors the
    canonical hardware record. -/
def FTSystem.wellFormed (S : FTSystem) : Bool :=
  scheduleValid S.dev S.sched && decide (MachineParams.ofDevice S.dev = S.hw)

/-- Re-export: the hardware-sensitivity runtime lower bound (max of the four resource/causal
    floors), the single front-door for "how the bound responds to each hardware parameter". -/
abbrev timeLowerBound : HardwareSensitivity.HW → Nat → Nat → Nat := HardwareSensitivity.HW.timeLB

/-- **★ The umbrella guarantee ★** — for ANY operation count `M`, a naive system on an adequate
    device whose hardware record mirrors the device is simultaneously:
      (i) a VALID schedule, (ii) decoder-reaction bounded, (iii) footprint (capacity) bounded —
    proven parametrically (no enumeration), composing `naiveSchedule_valid`,
    `reactionRespected_naive`, and `naive_peak_le_total`. -/
theorem ftSystem_naive_guarantee
    (S : FTSystem) (M : Nat)
    (hsched : S.sched = naiveSchedule M)
    (hdev : adequate S.dev)
    (_hcoh : MachineParams.ofDevice S.dev = S.hw) :
    scheduleValid S.dev S.sched = true
    ∧ reactionRespected S.dev S.sched = true
    ∧ schedulePeak S.sched ≤ S.dev.totalResources := by
  rw [hsched]
  exact ⟨naiveSchedule_valid S.dev M hdev,
         reactionRespected_naive S.dev M hdev.2.2,
         naive_peak_le_total S.dev M hdev.1⟩

/-! ## A GE2021 instance, wired end-to-end through the umbrella (parametric — no enumeration). -/

/-- GE2021 system: 20M-qubit / 10 µs-reaction / d=27 device running the full naive RSA-2048
    schedule (`3 · 2 622 824 448` ops), hardware mirrored from the device. -/
def geSystem : FTSystem :=
  { hw    := MachineParams.ofDevice ge2021Device
    dev   := ge2021Device
    sched := naiveSchedule rsa2048_opCount
    T     := rsa2048_opCount
    fq    := 2565
    prod  := 12000 }

/-- The GE2021 system is valid, reaction-bounded and footprint-bounded — via the umbrella, for the
    full ~8×10⁹-op schedule, without ever enumerating it. -/
theorem geSystem_guarantee :
    scheduleValid geSystem.dev geSystem.sched = true
    ∧ reactionRespected geSystem.dev geSystem.sched = true
    ∧ schedulePeak geSystem.sched ≤ geSystem.dev.totalResources :=
  ftSystem_naive_guarantee geSystem rsa2048_opCount rfl ⟨by decide, by decide, by decide⟩ rfl

end FormalRV.System.FTFramework
