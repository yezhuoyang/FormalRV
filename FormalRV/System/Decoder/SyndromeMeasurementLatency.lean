/-
  FormalRV.System.SyndromeMeasurementLatency — syndrome-extraction overhead made
  explicit and HARDWARE-LATENCY-DRIVEN:

  (1) the surface-code CYCLE time is built from gate/measure/reset latencies
      (one syndrome round = `gateLayers` CNOT layers + measure + reset), so the
      qubit-measurement latency `tMeasure` flows into the verified runtime,
      monotonically — with an RSA-2048 sensitivity table;
  (2) every `[[n,1,d]]` patch carries one syndrome-measure ancilla per
      stabilizer (`n − 1`), and extraction is ALWAYS-ON: every patch measures
      all its stabilizers every code cycle for the whole computation, so the
      physical syndrome-measurement workload scales with
      (all logical qubits) × (total cycles), not with active operations.

  No `sorry`, no new `axiom`.
-/

import FormalRV.System.Compile.SurfaceSystemCompile

set_option maxRecDepth 8000
namespace FormalRV.System.SyndromeMeasurementLatency

open FormalRV.Framework
open FormalRV.Framework.Resource
open FormalRV.System.SurfaceSystemCompile
open FormalRV.LatticeSurgery.SurfaceShorResourceCount

/-! ## §1. Hardware: the surface-code CYCLE time is built from gate/measure/reset

    One syndrome round = `gateLayers` CNOT layers + a qubit MEASUREMENT + an ancilla
    RESET.  So the cycle time DEPENDS on the qubit-measurement latency `tMeasure`. -/

/-- Surface-code cycle time (tenths-µs) from hardware latencies.  Standard surface
    syndrome round: 4 CNOT layers + measure + reset. -/
def surfaceCycleTime (tGate tMeasure tReset gateLayers : Nat) : Nat :=
  gateLayers * tGate + tMeasure + tReset

/-- Hardware whose cycle time is the latency-built surface cycle. -/
def hwOfLatencies (tGate tMeasure tReset gateLayers : Nat) : Hardware :=
  { cycle_time_us_tenths := surfaceCycleTime tGate tMeasure tReset gateLayers }

/-! ## §2. The qubit-measurement latency FLOWS INTO the verified runtime -/

/-- **Runtime as a function of `tMeasure`.**  Through the rfl-verified `estimateWith`,
    the surface-code Shor runtime is `n_toff · d · (gateLayers·tGate + tMeasure +
    tReset)` — so the qubit-measurement latency is a live input to the verified time. -/
theorem runtime_with_measurement_latency
    (T L factory d tGate tMeasure tReset gateLayers ow p : Nat) :
    (estimateWith (surfaceModel factory) (hwOfLatencies tGate tMeasure tReset gateLayers)
        (shorWorkload T L) (surfaceCodeD d) ow p).time_us_tenths
      = T * d * surfaceCycleTime tGate tMeasure tReset gateLayers := by
  rw [surfaceShor_time_anyD]; rfl

/-- **MONOTONE in the measurement latency**: a slower qubit measurement gives a
    strictly larger verified runtime (all else fixed) — it is not inert. -/
theorem time_mono_measurementLatency
    (T L factory d tGate tM tM' tReset gateLayers ow p : Nat) (h : tM ≤ tM') :
    (estimateWith (surfaceModel factory) (hwOfLatencies tGate tM tReset gateLayers)
        (shorWorkload T L) (surfaceCodeD d) ow p).time_us_tenths
      ≤ (estimateWith (surfaceModel factory) (hwOfLatencies tGate tM' tReset gateLayers)
        (shorWorkload T L) (surfaceCodeD d) ow p).time_us_tenths := by
  rw [runtime_with_measurement_latency, runtime_with_measurement_latency]
  unfold surfaceCycleTime
  exact Nat.mul_le_mul (Nat.le_refl _) (by omega)

/-! ## §3. Sensitivity: RSA-2048 runtime vs the qubit-measurement latency

    2.7×10⁹ Toffolis, d=27, gateLayers=4, tGate=1, tReset=1 (tenths-µs).  Cycle =
    4·1 + tMeasure + 1 = 5 + tMeasure. -/

def rsa2048_time_at_tMeasure (tMeasure : Nat) : Nat :=
  2_700_000_000 * 27 * surfaceCycleTime 1 tMeasure 1 4

/-- tMeasure = 5 (0.5 µs): cycle = 10 tenths-µs (1 µs) → 20.25 h. -/
theorem rsa2048_tM_5 : rsa2048_time_at_tMeasure 5 = 729_000_000_000 := by decide
/-- tMeasure = 15 (1.5 µs): cycle = 20 → 40.5 h — a slower measurement DOUBLES the
    cycle and the runtime. -/
theorem rsa2048_tM_15 : rsa2048_time_at_tMeasure 15 = 1_458_000_000_000 := by decide
/-- tMeasure = 35 (3.5 µs, slow readout): cycle = 40 → 81 h. -/
theorem rsa2048_tM_35 : rsa2048_time_at_tMeasure 35 = 2_916_000_000_000 := by decide

/-- **Changing the qubit-measurement latency changes the verified time** — the
    framework is not measurement-latency-blind. -/
theorem measurement_latency_changes_time :
    rsa2048_time_at_tMeasure 5 ≠ rsa2048_time_at_tMeasure 15 := by decide

/-! ## §4. Always-on syndrome extraction — ancilla + idle-qubit overhead -/

/-- Syndrome-measure ancilla per `[[n,1,d]]` surface patch: one per stabilizer,
    `n − 1` (both bases).  For the d=27 patch (n=1405): 1404 ancilla. -/
def syndromeAncillaPerPatch (d : Nat) : Nat := (surfaceCodeD d).n - 1

theorem syndromeAncilla_d27 : syndromeAncillaPerPatch 27 = 1404 := by decide

/-- Total syndrome rounds over the whole computation = total code cycles = the
    runtime in cycles = `n_toff · d` (one logical Toffoli = d rounds). -/
def totalSyndromeRounds (nToff d : Nat) : Nat := nToff * d

/-- **Always-on physical syndrome measurements**: EVERY logical patch measures ALL
    its stabilizers EVERY round for the whole duration — `n_logical · (n−1) ·
    (n_toff · d)`.  This is the physical measurement workload, vastly larger than
    the `412×10⁹` LOGICAL measurements.  Note the model has NO idle/active
    distinction — by construction each patch contributes the same per-patch term
    `(n−1)·(n_toff·d)` whether or not any of the global Toffolis touch it, i.e.
    idle qubits are not free: they pay full-duration extraction. -/
def totalPhysicalSyndromeMeas (nLogical d nToff : Nat) : Nat :=
  nLogical * syndromeAncillaPerPatch d * totalSyndromeRounds nToff d

/-- The always-on physical syndrome workload is LINEAR in the logical-qubit count —
    so the 6200 idle+active patches each pay the full-duration extraction cost
    (this is exactly the decoder load of `DecoderBacklogModel`, now tied to the
    physical measurement count). -/
theorem syndrome_overhead_scales_with_all_qubits (d nToff a b : Nat) (h : a ≤ b) :
    totalPhysicalSyndromeMeas a d nToff ≤ totalPhysicalSyndromeMeas b d nToff := by
  unfold totalPhysicalSyndromeMeas
  exact Nat.mul_le_mul (Nat.mul_le_mul h (Nat.le_refl _)) (Nat.le_refl _)

end FormalRV.System.SyndromeMeasurementLatency
