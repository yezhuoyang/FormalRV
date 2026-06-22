/-
  FormalRV.System.MagicScheduleComplete — the WHOLE-CIRCUIT magic-aware device schedule:
  latency + qubit cost + routing + waiting, considered together.

  Building on `MagicStateReadiness` (which models one magic state's produce→route→consume
  pipeline and the "wait if not ready" law), this file lifts the law to the WHOLE circuit:

    * **Waiting (whole circuit).**  `respectsReadiness` — NO magic-consuming gate fires before its
      magic is produced and routed.  With `F` pipelined factories the i-th magic state is ready at
      `pipelinedReadyTime i`, and the `waitingSchedule` (every gate fires exactly when its magic is
      ready) provably respects readiness; a premature schedule provably violates it.
    * **Latency.**  Each gate's earliest fire time carries the full `deliveryLatency`
      (`production_us` + routing) plus its position in the factory pipeline.
    * **Qubit cost (whole device).**  `deviceQubits = data + factory + routing` — the surface-code
      data patches, the magic-state-factory footprint (derived from the throughput requirement),
      and the routing/ancilla overhead, summed.
    * **Routing.**  Readiness requires a `TransitQubit` (Factory→Processor) between production and
      consumption; the routing latency is inside `deliveryLatency`.

  Headline: `windowed_rsa2048_device_schedule_ok` bundles, for the windowed RSA-2048 circuit at the
  Gidney–Ekerå hardware parameters with CCZ factories sized for the 8-hour budget: a readiness-
  respecting (waiting) schedule exists, the runtime is magic-pipeline-bounded UNDER an assumed
  magic-limited hypothesis, and the device qubit budget decomposes as data + factory + routing.

  Concrete numbers use the paper-cited `ccz_spec_qianxu` and the canonical workload constants in
  `Params/RSA2048`; the model is parametric in the `MagicStateSpec`.
-/
import FormalRV.System.Magic.MagicStateReadiness
import FormalRV.System.Params.RSA2048

namespace FormalRV.System.MagicScheduleComplete

open FormalRV.System.Architecture
open FormalRV.System.MagicStateReadiness

/-! ## §1. Whole-circuit waiting: no gate fires before its magic is ready. -/

/-- With `F` factories pipelined, the `i`-th magic state (0-indexed) is ready at
    `deliveryLatency + (i / F)·production_us`: factory `i % F` is on its `(i / F)`-th batch. -/
def pipelinedReadyTime (i F : Nat) (spec : MagicStateSpec) (routingLatency : Nat) : Nat :=
  deliveryLatency spec routingLatency + (i / F) * spec.production_us

/-- A consume-time assignment `consumeBegin : gateIndex → time` RESPECTS readiness for `K`
    magic-consuming gates iff every gate `i` fires no earlier than its magic is ready. -/
def respectsReadiness (consumeBegin : Nat → Nat) (K F : Nat)
    (spec : MagicStateSpec) (lat : Nat) : Bool :=
  (List.range K).all (fun i => decide (pipelinedReadyTime i F spec lat ≤ consumeBegin i))

/-- The "always-wait" schedule: gate `i` fires exactly when its magic becomes ready. -/
def waitingSchedule (F : Nat) (spec : MagicStateSpec) (lat : Nat) : Nat → Nat :=
  fun i => pipelinedReadyTime i F spec lat

/-- **The waiting schedule respects readiness — by construction.**  `waitingSchedule` fires gate
    `i` exactly at `pipelinedReadyTime i`, so each check is `ready ≤ ready` and the proof is
    `decide (x ≤ x)`.  The content is existential: a readiness-respecting schedule for all `K`
    consumers EXISTS (contrast `premature_violates_readiness`). -/
theorem waitingSchedule_respectsReadiness (K F : Nat) (spec : MagicStateSpec) (lat : Nat) :
    respectsReadiness (waitingSchedule F spec lat) K F spec lat = true := by
  unfold respectsReadiness waitingSchedule
  rw [List.all_eq_true]
  intro i _
  exact decide_eq_true (Nat.le_refl _)

/-- **A premature schedule violates readiness.**  If any gate `i < K` fires before its magic is
    ready (`consumeBegin i < pipelinedReadyTime i`), the whole-circuit readiness check fails —
    the gate would consume a magic state that is not yet produced/routed. -/
theorem premature_violates_readiness
    (consumeBegin : Nat → Nat) (K F : Nat) (spec : MagicStateSpec) (lat : Nat)
    (i : Nat) (hi : i < K) (hlt : consumeBegin i < pipelinedReadyTime i F spec lat) :
    respectsReadiness consumeBegin K F spec lat = false := by
  unfold respectsReadiness
  rw [List.all_eq_false]
  exact ⟨i, List.mem_range.mpr hi, by simp [Nat.not_le.mpr hlt]⟩

/-! ## §2. SysCall-level demonstration: a full produce→route→consume schedule. -/

/-- A full magic-consuming-gate schedule: the produce→route delivery, then the consumer
    `Gate2q (data, magicQubit)` (the teleportation injection) at `consumeBegin`. -/
def fullMagicGateSchedule (consumeBegin : Nat) : Schedule :=
  magicDelivery 3 1 100 0 ccz_spec_qianxu 15
  ++ [ { kind := SysCallKind.Gate2q 0 100 0,
         begin_us := consumeBegin, end_us := consumeBegin + 1 } ]

/-- The consumer is magic-ready iff some production completed before some routing transit of the
    magic qubit, which completed before the consumer fires (produce → route → consume). -/
def consumerMagicReady (sched : Schedule) (consumeBegin magicQubit : Nat) : Bool :=
  sched.any (fun prod => match prod.kind with
    | SysCallKind.RequestMagicState _ =>
        sched.any (fun tr => match tr.kind with
          | SysCallKind.TransitQubit q _ =>
              q == magicQubit && decide (prod.end_us ≤ tr.begin_us)
                && decide (tr.end_us ≤ consumeBegin)
          | _ => false)
    | _ => false)

/-- **Premature consumption is caught at the SysCall level.**  A gate that fires at 5000 µs — before
    the CCZ is produced (12000 µs) and routed (+15 µs) — is NOT magic-ready: it must WAIT. -/
theorem consume_too_early_not_ready :
    consumerMagicReady (fullMagicGateSchedule 5000) 5000 100 = false := by native_decide

/-- A gate that waits until 12015 µs (production + routing complete) IS magic-ready. -/
theorem consume_after_wait_ready :
    consumerMagicReady (fullMagicGateSchedule 12015) 12015 100 = true := by native_decide

/-! ## §3. Whole-circuit runtime: max(logical depth, magic pipeline) — wait on the slower. -/

/-- Whole-circuit wallclock: the maximum of the logical depth and the magic-supply pipeline
    (`deliveryLatency + ⌈K/F⌉·production_us`).  The circuit waits for whichever is slower. -/
def circuitRuntimeUs (logicalDepthUs K F : Nat) (spec : MagicStateSpec) (lat : Nat) : Nat :=
  Nat.max logicalDepthUs (deliveryLatency spec lat + magicSupplyTimeUs K F spec)

/-- **Magic-limited regime.**  When the magic pipeline exceeds the logical depth (hypothesis `h`),
    the runtime IS the magic pipeline.  The proof is just `max a b = b` given `a ≤ b` —
    `circuitRuntimeUs` is a `Nat.max`; the theorem names the regime, it does not establish that
    any particular circuit is in it. -/
theorem runtime_magic_limited
    (logicalDepthUs K F : Nat) (spec : MagicStateSpec) (lat : Nat)
    (h : logicalDepthUs ≤ deliveryLatency spec lat + magicSupplyTimeUs K F spec) :
    circuitRuntimeUs logicalDepthUs K F spec lat
      = deliveryLatency spec lat + magicSupplyTimeUs K F spec := by
  unfold circuitRuntimeUs
  exact Nat.max_eq_right h

/-! ## §4. Whole-device qubit budget: data + factory + routing. -/

/-- Total device physical qubits = surface-code data patches + magic-factory footprint
    + routing/ancilla overhead. -/
def deviceQubits (dataQubits factoryQubits routingQubits : Nat) : Nat :=
  dataQubits + factoryQubits + routingQubits

/-! ## §5. The windowed RSA-2048 whole-device schedule, at GE2021 parameters.

    Data qubits `9 633 792` (= 3n × 2(d+1)² at d=27, from `WindowedShorPhysicalEstimate`); magic
    budget `K = 2 622 824 448` Toffolis; CCZ factories `F = 1093` sized for the 8-hour budget;
    factory footprint `1093 × 2565 = 2 803 545`; routing/ancilla as a parameter. -/

/-- Windowed RSA-2048 device parameters at GE2021 hardware (magic budget from the canonical
    `Params/RSA2048`; factories/footprint DERIVED from the throughput requirement, not assumed). -/
def rsa2048_data_qubits  : Nat := 9633792
def rsa2048_magic_budget : Nat := FormalRV.System.RSA2048.magicBudget
def rsa2048_factories    : Nat := factoriesNeeded rsa2048_magic_budget 28800000000 ccz_spec_qianxu
def rsa2048_factory_qubits : Nat := factoryFootprint rsa2048_factories ccz_spec_qianxu

theorem rsa2048_factories_value : rsa2048_factories = 1093 := by native_decide
theorem rsa2048_factory_qubits_value : rsa2048_factory_qubits = 2803545 := by native_decide

/-- **★ Whole-device schedule bundle for windowed RSA-2048 at GE2021 hardware ★.**  Simultaneously:

    (1) **Waiting** — the always-wait schedule over all `K` Toffoli magic consumers respects
        readiness.  This conjunct holds BY CONSTRUCTION (`waitingSchedule_respectsReadiness`):
        its content is that such a schedule exists, not that an arbitrary one complies.
    (2) **Magic-limited runtime** — UNDER the assumed hypothesis `h_magic_limited` (the logical
        depth is below the single-factory magic pipeline — plausible, since that pipeline exceeds
        8 hours by `windowed_single_factory_is_magic_limited`, but not proven for the windowed
        circuit here), the single-factory runtime is the magic pipeline; this is why `1093`
        parallel factories are sized for the budget.
    (3) **Qubit budget** — the device decomposes as data (`9 633 792`) + factory (`2 803 545`)
        + routing; the factory share is derived from the throughput requirement, not assumed. -/
theorem windowed_rsa2048_device_schedule_ok (routingQubits logicalDepthUs : Nat)
    (h_magic_limited :
      logicalDepthUs ≤ deliveryLatency ccz_spec_qianxu 15
        + magicSupplyTimeUs rsa2048_magic_budget 1 ccz_spec_qianxu) :
    -- (1) waiting: no premature magic consumption
    respectsReadiness (waitingSchedule rsa2048_factories ccz_spec_qianxu 15)
        rsa2048_magic_budget rsa2048_factories ccz_spec_qianxu 15 = true
    -- (2) magic-limited runtime at one factory: the circuit waits on magic
    ∧ circuitRuntimeUs logicalDepthUs rsa2048_magic_budget 1 ccz_spec_qianxu 15
        = deliveryLatency ccz_spec_qianxu 15
          + magicSupplyTimeUs rsa2048_magic_budget 1 ccz_spec_qianxu
    -- (3) device qubit budget = data + factory + routing
    ∧ deviceQubits rsa2048_data_qubits rsa2048_factory_qubits routingQubits
        = 9633792 + 2803545 + routingQubits := by
  refine ⟨waitingSchedule_respectsReadiness _ _ _ _,
          runtime_magic_limited _ _ _ _ _ h_magic_limited, ?_⟩
  unfold deviceQubits rsa2048_data_qubits
  rw [rsa2048_factory_qubits_value]

end FormalRV.System.MagicScheduleComplete
