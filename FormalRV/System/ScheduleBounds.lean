/-
  FormalRV.System.ScheduleBounds — the UNIFICATION of the two bound efforts: bracket ONE resource
  on ONE schedule (`DSchedule`).

  The two subsystems bounded resources on disjoint data models:
    * UPPER bound (main): `NaiveUpperBound.naivePeak_le_footprint` — a sequential schedule's peak
      qubit demand ≤ its static footprint, on `ResourceEstimate`.
    * LOWER bound (this branch): `ScheduleLowerBound.magic_spacetime_floor` / `workload_le` —
      `K·fq·prod ≤ workload ≤ Q·T`, on `DSchedule`.

  Here both are stated on the SAME `DSchedule` (the canonical schedule object: recursively defined
  and proven valid for all sizes), so they genuinely BRACKET the resource the schedule books:

        K · fq · prod   ≤   workload sched   ≤   Q · T            (`resource_bracket`)
        schedulePeak (naiveSchedule M)        ≤   totalResources  (`naive_peak_le_total`, the
                                                                   `DSchedule` analogue of main's
                                                                   `naivePeak_le_footprint`).
-/
import FormalRV.System.NaiveSchedule
import FormalRV.System.ScheduleLowerBound
import FormalRV.System.HardwareParams

namespace FormalRV.System.ScheduleBounds

open FormalRV.System.DeviceSchedule
open FormalRV.System.NaiveSchedule
open FormalRV.System.ScheduleLowerBound

/-! ## §1. Peak active footprint (the shared quantity both efforts bound). -/

/-- Peak active footprint over the schedule's boundary times — the standing qubit demand. -/
def schedulePeak (sched : DSchedule) : Nat :=
  ((boundaries sched).map (activeFootprintSize sched)).foldl max 0

private theorem foldl_max_le : ∀ (L : List Nat) (acc c : Nat),
    acc ≤ c → (∀ x ∈ L, x ≤ c) → L.foldl max acc ≤ c
  | [],      acc, c, ha, _ => ha
  | x :: xs, acc, c, ha, h => by
      apply foldl_max_le xs (max acc x) c
      · exact max_le ha (h x (by simp))
      · intro y hy; exact h y (by simp [hy])

/-- **UPPER bracket (naive ≤ 1)** — the naive serial schedule keeps at most one op live, so its peak
    footprint is `≤ 1`, for ALL sizes (the `DSchedule` analogue of `naivePeak_le_footprint`). -/
theorem naive_peak_le_one (M : Nat) : schedulePeak (naiveSchedule M) ≤ 1 := by
  unfold schedulePeak
  apply foldl_max_le _ 0 1 (by omega)
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨t, _, rfl⟩ := hy
  exact activeFootprintSize_naive_le_one 0 M t

/-- The naive schedule's peak demand never exceeds the device footprint (capacity), for ALL sizes. -/
theorem naive_peak_le_total (dev : Device) (M : Nat) (h : 1 ≤ dev.totalResources) :
    schedulePeak (naiveSchedule M) ≤ dev.totalResources :=
  le_trans (naive_peak_le_one M) h

/-! ## §2. The bracket: lower ≤ actual ≤ upper, on one schedule. -/

/-- **★ THE BOUND UNIFICATION ★** — on any schedule that fits horizon `T`, respects capacity `Q`,
    and whose ops each reserve ≥ `fq` qubits for ≥ `prod` time, the footprint-time the schedule
    books is squeezed between the magic-state floor and the device spacetime:

        (#ops) · fq · prod  ≤  workload sched  ≤  Q · T.

    The left inequality is the impossibility floor (`workload_ge_of_uniform`), the right is the
    packing ceiling (`workload_le`) — one chain on one object. -/
theorem resource_bracket (sched : DSchedule) (T Q fq prod : Nat)
    (hfit : ∀ o ∈ sched, o.end_t ≤ T)
    (hcap : ∀ t ∈ Finset.range T, activeFootprintSize sched t ≤ Q)
    (hf : ∀ o ∈ sched, fq ≤ o.footprint.length)
    (hd : ∀ o ∈ sched, prod ≤ o.dur_t) :
    sched.length * (fq * prod) ≤ workload sched ∧ workload sched ≤ Q * T :=
  ⟨workload_ge_of_uniform sched fq prod hf hd, workload_le sched T Q hfit hcap⟩

/-! ## §3. Connect the two naive efforts numerically. -/

/-- The `DSchedule` op count (`3·K`, prepare→teleport→decode per Toffoli) vs the verified Toffoli
    budget `K`. -/
theorem naive_opcount_eq_three_toff : NaiveSchedule.rsa2048_opCount = 3 * 2622824448 := rfl

/-- The VERIFIED Toffoli budget (`2 622 824 448`, used by `NaiveSchedule`/`ScheduleLowerBound`) is
    below the GE2021 REPORTED Toffoli count (`≈ 2.7×10⁹`, charged by `NaiveUpperBound`); the two
    naive efforts are about the same computation, denominated from different sources. -/
theorem verified_toff_le_reported : (2622824448 : Nat) ≤ 2700000000 := by omega

end FormalRV.System.ScheduleBounds
