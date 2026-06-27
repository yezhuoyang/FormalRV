/-
  FormalRV.System.MagicStateReadiness — the magic-state system call as a RESOURCE with latency,
  qubit footprint, and routing, plus the "wait if not ready" scheduling dependency.

  `Architecture` declares `MagicStateSpec` (`production_us` latency, `factory_qubits` footprint,
  fidelity) and the `RequestMagicState` / `TransitQubit` SysCalls; this file binds them to
  scheduling:

    * A magic state is PRODUCED in a factory (`RequestMagicState`, lasting `production_us`),
      then ROUTED to the processor (`TransitQubit` through a `MagicSupply` channel, lasting the
      channel latency).  Only AFTER both complete is it READY to inject (`magicReadyAt`).
    * The wait law: a consumer that fires before the delivery completes finds the state NOT
      ready — it must WAIT (`consumeBegin ≥ production_us + routing_latency`).
    * `factoryFootprint`: each in-flight production occupies `factory_qubits`; concurrent
      productions must fit the Factory zone capacity.
    * `magicSupplyTimeUs` / `factoriesNeeded` / `factoryQubitShare`: from the circuit's magic
      budget + a per-factory throughput, the supply time, the number of factories, and hence
      the magic share of the device's physical qubits follow.

  Concrete numbers use the paper-cited `ccz_spec_qianxu` (`Architecture.lean`); the model is
  parametric in the `MagicStateSpec`, so any other factory spec plugs in unchanged.
-/
import FormalRV.System.Core.Architecture

set_option maxRecDepth 8000

namespace FormalRV.System.MagicStateReadiness

open FormalRV.System.Architecture

/-! ## §1. Magic-state delivery: produce → route. -/

/-- Total latency before a freshly-started magic state is ready to inject: the factory
    `production_us` (cultivation/distillation) plus the Factory→Processor routing latency. -/
def deliveryLatency (spec : MagicStateSpec) (routingLatency : Nat) : Nat :=
  spec.production_us + routingLatency

/-- A concrete magic-delivery sub-schedule starting at `start`: a `RequestMagicState` in factory
    zone `f` lasting `spec.production_us`, then a `TransitQubit` of the magic qubit through
    MagicSupply channel `cid` lasting `routingLatency`.  Models the physical pipeline. -/
def magicDelivery (f cid magicQubit start : Nat) (spec : MagicStateSpec) (routingLatency : Nat) :
    Schedule :=
  [ { kind := SysCallKind.RequestMagicState f,
      begin_us := start, end_us := start + spec.production_us },
    { kind := SysCallKind.TransitQubit magicQubit cid,
      begin_us := start + spec.production_us,
      end_us := start + spec.production_us + routingLatency } ]

/-- The magic state is READY at time `t` iff every step of its delivery (production + routing)
    has completed by `t`. -/
def magicReadyAt (delivery : Schedule) (t : Nat) : Bool :=
  delivery.all (fun sc => decide (sc.end_us ≤ t))

/-! ## §2. The "wait if not ready" law. -/

/-- **The wait law.**  A magic state whose delivery starts at `start` is ready exactly at
    `start + production_us + routingLatency` — the full `deliveryLatency`.  A consumer that wants
    it earlier finds it NOT ready and must WAIT.  (Proven by reducing the `all` over the two
    delivery steps: the routing end dominates the production end.) -/
theorem magicReadyAt_magicDelivery
    (f cid mq start : Nat) (spec : MagicStateSpec) (lat t : Nat) :
    magicReadyAt (magicDelivery f cid mq start spec lat) t
      = decide (start + deliveryLatency spec lat ≤ t) := by
  unfold magicReadyAt magicDelivery deliveryLatency
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  by_cases hB : start + spec.production_us + lat ≤ t
  · rw [decide_eq_true hB, decide_eq_true (show start + spec.production_us ≤ t by omega),
        Bool.and_true, ← Nat.add_assoc, decide_eq_true (by omega : start + spec.production_us + lat ≤ t)]
  · rw [decide_eq_false hB, Bool.and_false, ← Nat.add_assoc, decide_eq_false hB]

/-- **Earliest legal consume time = the delivery latency.**  Restated: the consumer must wait at
    least `deliveryLatency` after production starts. -/
theorem earliest_consume_is_deliveryLatency
    (f cid mq : Nat) (spec : MagicStateSpec) (lat : Nat) :
    magicReadyAt (magicDelivery f cid mq 0 spec lat) (deliveryLatency spec lat) = true
    ∧ ∀ t, t < deliveryLatency spec lat →
        magicReadyAt (magicDelivery f cid mq 0 spec lat) t = false := by
  refine ⟨?_, ?_⟩
  · rw [magicReadyAt_magicDelivery]; simp
  · intro t ht; rw [magicReadyAt_magicDelivery]; simp; omega

/-! ## §3. Concrete demonstration with the CCZ factory (qianxu cost model).

    `ccz_spec_qianxu`: `factory_qubits = 2565`, `production_us = 12000` (12 ms).  A CCZ delivery
    routed through a 15 µs MagicSupply channel is ready only at `12000 + 15 = 12015 µs`. -/

/-- A CCZ delivery starting at t=0, routed through a 15 µs channel (neutral-atom MagicSupply). -/
def ccz_delivery_demo : Schedule := magicDelivery 3 1 100 0 ccz_spec_qianxu 15

/-- **WAIT, demonstrated.**  A consumer that wants the CCZ at `t = 5000 µs` finds it NOT ready —
    production alone takes 12000 µs.  The circuit must stall. -/
theorem ccz_not_ready_at_5000 : magicReadyAt ccz_delivery_demo 5000 = false := by decide

/-- It is still not ready one tick before the full delivery latency … -/
theorem ccz_not_ready_at_12014 : magicReadyAt ccz_delivery_demo 12014 = false := by decide

/-- … and becomes ready exactly at `12015 µs` (12000 production + 15 routing). -/
theorem ccz_ready_at_12015 : magicReadyAt ccz_delivery_demo 12015 = true := by decide

/-! ## §4. Factory qubit footprint. -/

/-- Factory-zone qubits occupied by `n` concurrently-producing magic states of spec `spec`. -/
def factoryFootprint (n : Nat) (spec : MagicStateSpec) : Nat := n * spec.factory_qubits

/-- A Factory zone of capacity `cap` admits at most `cap / factory_qubits` concurrent productions;
    asking for more OVER-SUBSCRIBES the zone (a capacity violation). -/
def footprintFits (n cap : Nat) (spec : MagicStateSpec) : Bool :=
  decide (factoryFootprint n spec ≤ cap)

/-- One CCZ production occupies 2565 physical qubits. -/
theorem ccz_footprint_one : factoryFootprint 1 ccz_spec_qianxu = 2565 := by decide

/-- **Footprint over-subscription, demonstrated.**  Three concurrent CCZ productions need 7695
    qubits and do NOT fit a 5000-qubit Factory zone; one does. -/
theorem ccz_footprint_oversubscription :
    footprintFits 1 5000 ccz_spec_qianxu = true
    ∧ footprintFits 3 5000 ccz_spec_qianxu = false := by decide

/-! ## §5. Throughput → factory count → factory qubit share (the magic bottleneck).

    A single factory makes one magic state per `production_us`.  Supplying `K` magic states with
    `F` parallel factories takes `⌈K/F⌉ · production_us`.  To meet a runtime budget the circuit may
    need MANY factories — and the circuit WAITS whenever the magic supply lags the logical depth. -/

/-- Magic-supply wallclock for `K` states from `F` parallel factories: `⌈K/F⌉ · production_us`. -/
def magicSupplyTimeUs (K F : Nat) (spec : MagicStateSpec) : Nat :=
  (K + F - 1) / F * spec.production_us

/-- Number of parallel factories needed so the magic supply fits within `budgetUs`:
    enough that `⌈K/F⌉ · production_us ≤ budgetUs`, i.e. `F ≥ K · production_us / budgetUs`. -/
def factoriesNeeded (K budgetUs : Nat) (spec : MagicStateSpec) : Nat :=
  (K * spec.production_us + budgetUs - 1) / budgetUs

/-- Total Factory-zone qubits to sustain that supply: `factoriesNeeded · factory_qubits`. -/
def factoryQubitShare (K budgetUs : Nat) (spec : MagicStateSpec) : Nat :=
  factoryFootprint (factoriesNeeded K budgetUs spec) spec

/-- **The windowed RSA-2048 magic supply is factory-limited.**  With a single CCZ factory, the
    `2 622 824 448` Toffoli magic states (= `Params/RSA2048.magicBudget`, the paper-formula
    windowed CCZ count; the composed-circuit count `2 578 993 152` is bridged in
    `System.Compose.VerifiedWorkloadBridge`) take `2 622 824 448 · 12000 µs ≈ 1.0×10⁹ s` — far beyond the 8-hour budget, so the
    circuit would WAIT on magic.  Hence parallelism is mandatory.  The concrete factory count and
    qubit share for the 8-hour budget (1093 factories, 2 803 545 qubits) are pinned in
    `Magic/MagicScheduleComplete` (`rsa2048_factories_value`, `rsa2048_factory_qubits_value`). -/
theorem windowed_single_factory_is_magic_limited :
    8 * 3600000000 < magicSupplyTimeUs 2622824448 1 ccz_spec_qianxu := by decide

end FormalRV.System.MagicStateReadiness
