/-
  FormalRV.System.HardwareParams — the ONE canonical hardware-parameter record that reconciles the
  four hardware records the two scheduling subsystems grew independently:

    * `DeviceSchedule.Device`            (DeviceOp-schedule view: totalResources, nDecoders,
                                          reactionTime, codeCycleUs, d)
    * `ScheduleInvariantsExplicit.ZonedArch`  (SysCall-checker view: total_sites, t_cycle_us,
                                               v_max_um_per_us, t_react_us)
    * `FaultTolerantSchedule.FTSchedule` (FT bundle: arch + code_distance, tau_s, t_react_us)
    * `HardwareSensitivity.HW`           (sensitivity view: Q, nDec, tReact, d, …)

  Rather than RENAME/move fields (which would ripple into dozens of literals + `native_decide`
  proofs), this file introduces a canonical superset `MachineParams` and PROJECTION adapters.  The
  `reaction_*_eq` lemmas are definitional glue (`rfl`): they NAME which field of each record the
  adapters read as the decoder-reaction budget — they do not certify any pre-existing agreement
  between the records.  This is the single grep-able anchor for "where decoder reaction lives".
-/
import FormalRV.System.DeviceLane.DeviceSchedule
import FormalRV.System.Invariants.ScheduleInvariantsExplicit
import FormalRV.System.Bounds.HardwareSensitivity
import FormalRV.System.Checkers.FaultTolerantSchedule

namespace FormalRV.System.HardwareParams

open FormalRV.System.DeviceSchedule
open FormalRV.System.ScheduleInv
open FormalRV.System.HardwareSensitivity
open FormalRV.System.FTSchedule

/-- The canonical hardware-parameter record: the union of the four views' physical quantities. -/
structure MachineParams where
  totalQubits : Nat   -- = Device.totalResources = ZonedArch.total_sites = HW.Q
  nDecoders   : Nat   -- = Device.nDecoders = HW.nDec
  tReactUs    : Nat   -- ★ CANONICAL decoder reaction budget ★
  cycleUs     : Nat   -- = Device.codeCycleUs = ZonedArch.t_cycle_us
  d           : Nat   -- = Device.d = HW.d (code distance)
  deriving Repr, DecidableEq

/-- Projection from the DeviceOp-schedule `Device` (the most complete view). -/
def MachineParams.ofDevice (dev : Device) : MachineParams :=
  { totalQubits := dev.totalResources, nDecoders := dev.nDecoders, tReactUs := dev.reactionTime,
    cycleUs := dev.codeCycleUs, d := dev.d }

/-- Projection from the SysCall-checker `ZonedArch` (no decoder count or distance → documented 0). -/
def MachineParams.ofZonedArch (a : ZonedArch) : MachineParams :=
  { totalQubits := a.total_sites, nDecoders := 0, tReactUs := a.t_react_us,
    cycleUs := a.t_cycle_us, d := 0 }

/-- Projection from the sensitivity `HW` record (no explicit cycle time → documented 0). -/
def MachineParams.ofHW (h : HW) : MachineParams :=
  { totalQubits := h.Q, nDecoders := h.nDec, tReactUs := h.tReact, cycleUs := 0, d := h.d }

/-! ## Where the decoder-reaction budget lives in each record.

    The three lemmas below are glue BY DEFINITION (`rfl`): each projection adapter copies the
    named field into `tReactUs`, so the equations hold by unfolding.  Their value is documentary
    — a grep-able statement of which field each record uses — not a proof that independently
    defined quantities coincide. -/

theorem reaction_device_eq (dev : Device) :
    (MachineParams.ofDevice dev).tReactUs = dev.reactionTime := rfl
theorem reaction_arch_eq (a : ZonedArch) :
    (MachineParams.ofZonedArch a).tReactUs = a.t_react_us := rfl
theorem reaction_hw_eq (h : HW) :
    (MachineParams.ofHW h).tReactUs = h.tReact := rfl

/-- The FT bundle carries `t_react_us` separately from its `arch.t_react_us`; this predicate
    documents the intended invariant that the two agree (rather than forcing a struct change). -/
def ftReactionConsistent (f : FTSchedule) : Bool := decide (f.t_react_us = f.arch.t_react_us)

/-- The reaction budget the FT bundle uses equals the one in its architecture, via the canonical
    projection — provided the bundle is consistent. -/
theorem reaction_ft_eq (f : FTSchedule) (h : ftReactionConsistent f = true) :
    f.t_react_us = (MachineParams.ofZonedArch f.arch).tReactUs := by
  unfold ftReactionConsistent at h; simpa using h

/-- The GE2021 device (`DeviceSchedule` view) used to anchor the reaction budget at 10 µs. -/
def ge2021Device : Device :=
  { totalResources := 20000000, nDecoders := 1000, reactionTime := 10, codeCycleUs := 1, d := 27 }

/-- Both GE2021 instances (`HardwareSensitivity.ge2021` and `ge2021Device` above) carry a 10 µs
    reaction budget — definitional (`rfl`), since both records store the literal 10. -/
theorem ge2021_reaction_canonical :
    (MachineParams.ofHW ge2021).tReactUs = 10
    ∧ (MachineParams.ofDevice ge2021Device).tReactUs = 10 := ⟨rfl, rfl⟩

end FormalRV.System.HardwareParams
