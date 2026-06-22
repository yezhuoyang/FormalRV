/-
  FormalRV.System.DecoderBacklogModel — a parametric model of the decoder
  throughput / backlog gap.  Where `ResourceAuditGaps.decoderThroughputInv` is a
  one-shot `load ≤ lanes` check, this module models the QUEUE DYNAMICS over time
  and proves the dichotomy:

    • PROVISIONED (lanes ≥ load): the syndrome backlog is ZERO for ALL time —
      reaction-limited execution is sound, the 7.5 h runtime stands.
    • UNDER-PROVISIONED (lanes < load): the backlog grows WITHOUT BOUND (linear in
      time, Fowler/Terhal) — the effective reaction time diverges, so NO fixed
      runtime bound (8 h, 20.25 h, anything) holds.  The classical decoder is then
      the binding constraint, not the qubits.

  Parametric in (patches, decodeLatency, lanes, windows).  GE2021 instantiated.
  Independently reproduced by the FTQ-VM (see `System/VM_AUDIT.md`).

  No Mathlib beyond Nat/omega.  No `sorry`, no `axiom`.
-/

namespace FormalRV.System.DecoderBacklogModel

/-! ## §1. The queue model (per decode-latency window)

    A window is `decodeLatency` cycles.  In one window:
      arrivals = patches · decodeLatency  (each of `patches` patches emits one
                                           syndrome per cycle), and
      services = lanes                    (each of `lanes` decode cores clears one
                                           syndrome per decodeLatency cycles). -/

def arrivalsPerWindow (patches decodeLatency : Nat) : Nat := patches * decodeLatency
def servicesPerWindow (lanes : Nat) : Nat := lanes

/-- Backlog-free iff each window's service ≥ its arrivals. -/
def backlogFree (patches decodeLatency lanes : Nat) : Bool :=
  decide (arrivalsPerWindow patches decodeLatency ≤ servicesPerWindow lanes)

/-- Net backlog added per window (Nat-saturating; 0 when backlog-free). -/
def backlogGrowthPerWindow (patches decodeLatency lanes : Nat) : Nat :=
  arrivalsPerWindow patches decodeLatency - servicesPerWindow lanes

/-- Total syndrome backlog after `k` windows = `k · growth`. -/
def backlogAfter (k patches decodeLatency lanes : Nat) : Nat :=
  k * backlogGrowthPerWindow patches decodeLatency lanes

/-! ## §2. The dichotomy -/

/-- **Provisioned ⇒ ZERO backlog for ALL time.**  If lanes meet the load, the
    syndrome queue never grows — reaction-limited execution is sound. -/
theorem provisioned_no_backlog (k patches decodeLatency lanes : Nat)
    (h : backlogFree patches decodeLatency lanes = true) :
    backlogAfter k patches decodeLatency lanes = 0 := by
  have hle : arrivalsPerWindow patches decodeLatency ≤ servicesPerWindow lanes :=
    of_decide_eq_true h
  unfold backlogAfter backlogGrowthPerWindow
  rw [Nat.sub_eq_zero_of_le hle, Nat.mul_zero]

/-- **Under-provisioned ⇒ backlog grows WITHOUT BOUND.**  If lanes fall short, then
    for ANY bound there is a time `k` whose backlog exceeds it — the queue diverges
    (linear-in-time), so no fixed runtime can hold. -/
theorem underprovisioned_unbounded_backlog (patches decodeLatency lanes : Nat)
    (h : backlogFree patches decodeLatency lanes = false) (bound : Nat) :
    ∃ k, bound < backlogAfter k patches decodeLatency lanes := by
  have hnot : ¬ (arrivalsPerWindow patches decodeLatency ≤ servicesPerWindow lanes) :=
    of_decide_eq_false h
  have hpos : 0 < backlogGrowthPerWindow patches decodeLatency lanes := by
    unfold backlogGrowthPerWindow; omega
  refine ⟨bound + 1, ?_⟩
  unfold backlogAfter
  calc bound < bound + 1 := Nat.lt_succ_self _
    _ = (bound + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ (bound + 1) * backlogGrowthPerWindow patches decodeLatency lanes :=
        Nat.mul_le_mul_left _ hpos

/-! ## §3. Runtime impact — the decoder, not the qubits, is then binding

    The effective reaction time after `k` windows is the time to clear the queue:
    `(backlog + lanes) / lanes · decodeLatency` cycles.  Under-provisioned, the
    backlog term diverges, so the effective reaction time — and the whole
    runtime — exceeds any bound.  (We expose the monotone driver: backlog ≤
    effective reaction work.) -/

/-- Effective decode work outstanding after `k` windows (in syndrome-units): the
    standing service capacity plus the accumulated backlog. -/
def outstandingWork (k patches decodeLatency lanes : Nat) : Nat :=
  servicesPerWindow lanes + backlogAfter k patches decodeLatency lanes

/-- Under-provisioned, the outstanding decode work diverges — the reaction time
    cannot stay at its 10 µs design point, so the reaction-limited 7.5 h (and even
    the 20.25 h d-cycle ceiling) is not a valid runtime bound. -/
theorem underprovisioned_work_diverges (patches decodeLatency lanes : Nat)
    (h : backlogFree patches decodeLatency lanes = false) (bound : Nat) :
    ∃ k, bound < outstandingWork k patches decodeLatency lanes := by
  obtain ⟨k, hk⟩ := underprovisioned_unbounded_backlog patches decodeLatency lanes h bound
  exact ⟨k, by unfold outstandingWork; omega⟩

/-! ## §4. GE2021 instantiated (patches = 6200, decodeLatency = 10 cycles) -/

/-- With 62 000 decode lanes the GE2021 decoder is provisioned: zero backlog ∀ time
    — reaction-limited 7.5 h is sound. -/
theorem ge2021_provisioned_62000 (k : Nat) : backlogAfter k 6200 10 62000 = 0 :=
  provisioned_no_backlog k 6200 10 62000 (by decide)

/-- With only one lane per patch (6200, un-pipelined) the decoder is
    UNDER-provisioned, and the backlog diverges — RSA-2048 does NOT finish in any
    fixed time on that decoder fabric (the decoder is binding, not the 20 M qubits). -/
theorem ge2021_underprovisioned_6200 (bound : Nat) :
    ∃ k, bound < backlogAfter k 6200 10 6200 :=
  underprovisioned_unbounded_backlog 6200 10 6200 (by decide) bound

/-- The provisioning threshold is exactly `patches · decodeLatency` decode lanes:
    62 000 for GE2021.  Below it, divergence; at or above, soundness. -/
theorem ge2021_threshold : arrivalsPerWindow 6200 10 = 62_000 := by decide

end FormalRV.System.DecoderBacklogModel
