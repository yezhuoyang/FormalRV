/-
  FormalRV.System.ScheduleLowerBound — IMPOSSIBILITY (lower-bound) results for device schedules,
  derived from the system invariants + causality.  No schedule, however clever, can beat these.

  1. **Causal-chain bound** (`causal_two`, `causal_chain4`): the user's "a T-state must be distilled
     before injection; syndromes must be measured before decoding" — causally-dependent ops cannot
     overlap, so their durations ADD.  A distill → inject → measure → decode chain cannot be
     compressed below the sum of its four stage times.

  2. **Spacetime packing bound** (`workload_le`, `magic_spacetime_floor`): the BIG one.  In a
     capacity-`Q` schedule over horizon `T`, the total reserved footprint-time (`workload`) is
     `≤ Q · T` — disjoint reservations pack into the spacetime box.  Producing `K` magic states
     costs `≥ K · factory_qubits · production_us` of footprint-time, so `Q · T ≥ K · fq · prod`,
     a floor NO schedule can beat.  At GE2021 numbers (`K = 2 622 824 448`, `fq = 2565`,
     `prod = 12000 µs`) the floor is ≈ `2.24×10⁷` qubit-hours: the paper (`1.6×10⁸`) is ~7× above,
     the naive baseline (`8.46×10¹⁰`) ~3774× above.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import FormalRV.System.DeviceSchedule

namespace FormalRV.System.ScheduleLowerBound

open FormalRV.System.DeviceSchedule
open scoped BigOperators

/-! ## §1. Causal-chain (critical-path) lower bound. -/

/-- **Two causally-dependent ops cannot overlap.**  If `a` must finish before `b` begins, their
    durations ADD — `b` finishes no earlier than `a.begin + a.dur + b.dur`. -/
theorem causal_two (a b : DeviceOp) (h : a.end_t ≤ b.begin_t) :
    a.begin_t + a.dur_t + b.dur_t ≤ b.end_t := by
  unfold DeviceOp.end_t at *; omega

/-- **A distill → inject → measure → decode causal chain cannot be compressed.**  The decode
    finishes no earlier than the start plus ALL four stage durations.  This is exactly the user's
    causality: a T-state must be distilled before injection, and syndromes measured before decoding;
    none of these stages can overlap. -/
theorem causal_chain4 (distill inject meas decode : DeviceOp)
    (h1 : distill.end_t ≤ inject.begin_t) (h2 : inject.end_t ≤ meas.begin_t)
    (h3 : meas.end_t ≤ decode.begin_t) :
    distill.begin_t + distill.dur_t + inject.dur_t + meas.dur_t + decode.dur_t ≤ decode.end_t := by
  unfold DeviceOp.end_t at *; omega

/-! ## §2. Spacetime packing bound: workload ≤ Q · T. -/

/-- The footprint-time "work" of one op (resources × duration). -/
def opWork (o : DeviceOp) : Nat := o.footprint.length * o.dur_t

/-- Total footprint-time reserved by a schedule. -/
def workload (sched : DSchedule) : Nat := (sched.map opWork).sum

/-- Spacetime consumed up to horizon `T`: the per-instant active footprint, summed over time. -/
def spacetimeUsed (sched : DSchedule) (T : Nat) : Nat :=
  ∑ t ∈ Finset.range T, activeFootprintSize sched t

/-- `activeFootprintSize` as an indicator sum over ALL ops (non-active contribute 0). -/
theorem activeFootprintSize_eq_indicator (sched : DSchedule) (t : Nat) :
    activeFootprintSize sched t
      = (sched.map (fun o => if o.activeAt t then o.footprint.length else 0)).sum := by
  unfold activeFootprintSize
  induction sched with
  | nil => simp
  | cons o rest ih =>
      rw [List.filter_cons]
      by_cases h : o.activeAt t = true <;> simp [h, List.map_cons, List.sum_cons, ih]

/-- Swap a `Finset.range` sum with a `List.map` sum. -/
theorem sum_range_listmap (T : Nat) {α : Type _} (L : List α) (g : Nat → α → Nat) :
    ∑ t ∈ Finset.range T, (L.map (fun a => g t a)).sum
      = (L.map (fun a => ∑ t ∈ Finset.range T, g t a)).sum := by
  induction L with
  | nil => simp
  | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

/-- The active time-slots of one op (whose window fits in `[0,T)`) number exactly its duration. -/
theorem card_active_slots (o : DeviceOp) (T : Nat) (h : o.end_t ≤ T) :
    ((Finset.range T).filter (fun t => o.activeAt t = true)).card = o.dur_t := by
  have hset : (Finset.range T).filter (fun t => o.activeAt t = true)
            = Finset.Ico o.begin_t o.end_t := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, DeviceOp.activeAt,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨_, hb, he⟩; exact ⟨hb, he⟩
    · rintro ⟨hb, he⟩; exact ⟨by omega, hb, he⟩
  rw [hset, Nat.card_Ico]
  unfold DeviceOp.end_t; omega

/-- The per-op slice of spacetime equals its workload (footprint × duration), when it fits. -/
theorem op_slice (o : DeviceOp) (T : Nat) (h : o.end_t ≤ T) :
    (∑ t ∈ Finset.range T, if o.activeAt t then o.footprint.length else 0) = opWork o := by
  rw [← Finset.sum_filter, Finset.sum_const, card_active_slots o T h]
  simp [opWork, Nat.mul_comm]

/-- **Fubini**: spacetime consumed = total workload, when every op fits in `[0,T)`. -/
theorem spacetimeUsed_eq_workload (sched : DSchedule) (T : Nat)
    (hfit : ∀ o ∈ sched, o.end_t ≤ T) :
    spacetimeUsed sched T = workload sched := by
  unfold spacetimeUsed workload
  simp only [activeFootprintSize_eq_indicator]
  rw [sum_range_listmap]
  have hmap : sched.map (fun o => ∑ t ∈ Finset.range T, if o.activeAt t then o.footprint.length else 0)
            = sched.map opWork :=
    List.map_congr_left (fun o ho => op_slice o T (hfit o ho))
  rw [hmap]

/-- Spacetime consumed ≤ `Q · T` when capacity `Q` holds at every instant in `[0,T)`. -/
theorem spacetimeUsed_le (sched : DSchedule) (T Q : Nat)
    (hcap : ∀ t ∈ Finset.range T, activeFootprintSize sched t ≤ Q) :
    spacetimeUsed sched T ≤ Q * T := by
  unfold spacetimeUsed
  calc ∑ t ∈ Finset.range T, activeFootprintSize sched t
      ≤ ∑ _t ∈ Finset.range T, Q := Finset.sum_le_sum hcap
    _ = Q * T := by rw [Finset.sum_const, Finset.card_range]; simp [Nat.mul_comm]

/-- **★ Packing bound ★** — total reserved footprint-time ≤ device spacetime `Q · T`. -/
theorem workload_le (sched : DSchedule) (T Q : Nat)
    (hfit : ∀ o ∈ sched, o.end_t ≤ T)
    (hcap : ∀ t ∈ Finset.range T, activeFootprintSize sched t ≤ Q) :
    workload sched ≤ Q * T := by
  rw [← spacetimeUsed_eq_workload sched T hfit]; exact spacetimeUsed_le sched T Q hcap

/-- Workload lower bound: ops each with footprint ≥ `fq` and duration ≥ `prod` reserve
    `≥ (#ops) · fq · prod`. -/
theorem workload_ge_of_uniform (sched : DSchedule) (fq prod : Nat)
    (hf : ∀ o ∈ sched, fq ≤ o.footprint.length) (hd : ∀ o ∈ sched, prod ≤ o.dur_t) :
    sched.length * (fq * prod) ≤ workload sched := by
  unfold workload
  induction sched with
  | nil => simp
  | cons o rest ih =>
      have hfo := hf o (by simp); have hdo := hd o (by simp)
      have ihr := ih (fun x hx => hf x (by simp [hx])) (fun x hx => hd x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have h1 : fq * prod ≤ opWork o := Nat.mul_le_mul hfo hdo
      have hexp : (rest.length + 1) * (fq * prod) = fq * prod + rest.length * (fq * prod) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      omega

/-- **★ MAGIC-STATE SPACETIME FLOOR ★** — for ANY schedule producing magic states (each reserving
    ≥ `fq` factory qubits for ≥ `prod` time), conflict/capacity-bounded by `Q` over horizon `T`, the
    device spacetime obeys `(#magic) · fq · prod ≤ Q · T`.  No scheduling cleverness can beat the
    magic-production spacetime floor. -/
theorem magic_spacetime_floor (sched : DSchedule) (T Q fq prod : Nat)
    (hfit : ∀ o ∈ sched, o.end_t ≤ T)
    (hcap : ∀ t ∈ Finset.range T, activeFootprintSize sched t ≤ Q)
    (hf : ∀ o ∈ sched, fq ≤ o.footprint.length) (hd : ∀ o ∈ sched, prod ≤ o.dur_t) :
    sched.length * (fq * prod) ≤ Q * T :=
  le_trans (workload_ge_of_uniform sched fq prod hf hd) (workload_le sched T Q hfit hcap)

/-! ## §3. The RSA-2048 floor and the gap to paper / naive. -/

/-- The verified windowed RSA-2048 Toffoli (= CCZ magic) budget — the single canonical constant the
    naive schedule, the lower bound, and the hardware-sensitivity floors all denominate against. -/
def rsa2048_toffoli_budget : Nat := 2622824448

/-- The magic-state spacetime floor for windowed RSA-2048, in qubit·µs:
    `K · fq · prod = 2 622 824 448 · 2565 · 12000`. -/
def rsa2048_floor_qubit_us : Nat := 2622824448 * (2565 * 12000)

/-- The floor is denominated against the canonical Toffoli budget. -/
theorem rsa2048_floor_uses_budget :
    rsa2048_floor_qubit_us = rsa2048_toffoli_budget * (2565 * 12000) := rfl

/-- The floor in qubit·HOURS (÷ 3.6×10⁹ µs/h) ≈ `2.24×10⁷`. -/
def rsa2048_floor_qubit_hours : Nat := rsa2048_floor_qubit_us / 3600000000

theorem rsa2048_floor_value : rsa2048_floor_qubit_hours = 22425149 := by native_decide

/-- **The paper sits between 7× and 8× above the floor; the naive baseline between 3773× and 3774×.**
    The paper is near the magic-production limit (good engineering); the naive serial baseline is far
    above it — all the slack is in serial magic production. -/
theorem rsa2048_floor_gaps :
    7 * rsa2048_floor_qubit_hours ≤ 20000000 * 8
    ∧ 20000000 * 8 ≤ 8 * rsa2048_floor_qubit_hours
    ∧ 3773 * rsa2048_floor_qubit_hours ≤ 9636357 * 8782
    ∧ 9636357 * 8782 ≤ 3774 * rsa2048_floor_qubit_hours := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

end FormalRV.System.ScheduleLowerBound
