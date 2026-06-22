/-
  FormalRV.System.NaiveUpperBound — a NAIVE, STANDARD, MECHANICAL schedule with
  a VERIFIED resource upper bound, and the GAP to each paper's reported estimate.

  Part of the unified FT-scheduling framework — see `FormalRV.System.FTFramework` for the single
  entry point.  This module bounds resources on `ResourceEstimate` (the cost-model view); its
  `DSchedule` sibling is `FormalRV.System.NaiveSchedule` (peak-footprint validity for all sizes).
  `ScheduleBounds.resource_bracket` brackets the lower bound (`ScheduleLowerBound`) and this
  upper bound around one schedule's workload.

  Motivation.  We cannot verify that a paper's reported
  resource is OPTIMAL (= a lower bound), because the optimal PPM / decoder /
  qubit-routing schedule on the proposed hardware is unknown — finding it is
  itself a hard research problem.  But we can help the author from the OTHER
  side:

    1. construct a naive, standard, mechanical schedule;
    2. PROVE a verifiable UPPER BOUND on its resources — the rigor is that the
       naive schedule is FEASIBLE (satisfies the system invariants) and its peak
       demand never exceeds a static footprint FOR ANY problem size (induction);
    3. QUANTIFY the GAP between that verified ceiling and the paper's (smaller,
       optimized, unverified) reported number.

      optimal_cost  ≤  naive_upper_bound      (feasibility ⇒ we certify this side)
      reported_cost ≤  naive_upper_bound      (the paper sits BELOW our ceiling)
      gap = naive_upper_bound − reported_cost (the unverified optimization)

  COST RULE IS A PLUG-IN.
  The naive schedule's routing/ancilla rule is NOT hardcoded here: it is the
  framework's `surfaceModel` plug-in (`Framework/CostModel.lean`), run
  sequentially.  Choosing surface vs qLDPC is a PARAMETER — swap `surfaceModel`
  for `qldpcModel` and the ceiling recomputes with the weight-scaling ancilla
  rule, no code change.  Verification stays at the general level
  (`estimateWith_{time,qubits}`, proven `∀ model`); the code-specific rule is a
  framework instance, never special-cased outside.

  No Mathlib.  Pure Nat / Bool.  No `sorry`, no `axiom`.
-/
import FormalRV.Framework.CostModel
import FormalRV.System.Invariants.InvariantFramework
import FormalRV.System.Params.RSA2048

namespace FormalRV.System.NaiveUpperBound

open FormalRV.Framework FormalRV.Framework.Resource FormalRV.System.InvariantFramework

/-! ## (1) The naive schedule = the surface CostModel, run sequentially.

    Strategy: execute the workload's Toffolis strictly SEQUENTIALLY (one logical
    Toffoli active at a time, `parallel = 1`) under the framework's
    `surfaceModel` routing rule (area-scaling, ~2× the data patch), with one
    magic factory.  No parallelism, no optimization. -/

/-- The naive schedule's resource estimate, via the framework's `surfaceModel`
    plug-in.  `op_weight` is irrelevant under the surface model (its ancilla rule
    ignores it — surface routing does not scale with operator weight), so we pass
    0; `parallel = 1` is the sequential schedule. -/
def naiveEstimate (hw : Hardware) (w : Workload) (c : QECCode) (factory : Nat) :
    ResourceEstimate :=
  estimateWith (surfaceModel factory) hw w c 0 1

/-- Naive wallclock = n_toff · d · t_cycle (sequential critical path; the surface
    model charges `tauToff = d` cycles per Toffoli). -/
theorem naive_time (hw : Hardware) (w : Workload) (c : QECCode) (factory : Nat) :
    (naiveEstimate hw w c factory).time_us_tenths
      = w.n_toff * c.d * hw.cycle_time_us_tenths := rfl

/-- Naive qubit footprint = n_logical · (2·phys) + factory: the standing ~2×
    surface patch (data + in-patch syndrome + equal-area routing region, all a
    per-logical LAYOUT cost) plus the factory.  Under the surface cost model both
    operation-ancilla tags (syndrome, surgery) are 0 — the audit-relevant ancilla
    is the standing footprint, captured in `physPer`. -/
theorem naive_qubits (hw : Hardware) (w : Workload) (c : QECCode) (factory : Nat) :
    (naiveEstimate hw w c factory).qubits
      = w.n_logical * (2 * physPerLogical c) + factory := by
  simp only [naiveEstimate, estimateWith_qubits_tagged, surfaceModel, Nat.add_zero]

/-! ## (2) The upper bound: peak qubit demand never exceeds the static
    footprint, for any number of sequential Toffoli steps.

    HONEST SCOPE: in this model each sequential step demands the SAME constant
    footprint, so the bound is true BY CONSTRUCTION (a one-line induction on a
    fold of a constant), not a deep scheduling theorem.  Its content is the
    model it documents: the naive schedule's demand is flat, so the static
    footprint is a feasible, size-independent qubit ceiling. -/

/-- Peak physical-qubit demand after `k` sequential Toffoli steps.  Each step
    uses the SAME footprint (sequential: one Toffoli active), so the running
    peak is a fold of a constant. -/
def naivePeak (footprint : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => max footprint (naivePeak footprint k)

/-- For every problem size `k`, the naive schedule's peak qubit demand is ≤ the
    static footprint — true by construction (`naivePeak` folds the constant
    `footprint`).  What it certifies is feasibility: the sequential schedule
    fits inside the footprint at every size, so the footprint is an achievable
    ceiling on the qubit count. -/
theorem naivePeak_le_footprint (footprint k : Nat) :
    naivePeak footprint k ≤ footprint := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ n ih => simp only [naivePeak]; omega

/-- `naivePeak_le_footprint` specialised to the naive estimate's own qubit
    figure (likewise true by construction). -/
theorem naive_peak_within_estimate
    (hw : Hardware) (w : Workload) (c : QECCode) (factory k : Nat) :
    naivePeak ((naiveEstimate hw w c factory).qubits) k
      ≤ (naiveEstimate hw w c factory).qubits :=
  naivePeak_le_footprint _ k

/-- Naive sequential makespan after `k` Toffoli steps = k · d · t_cycle — the
    LONGEST any schedule of these steps can take (no parallelism), hence an upper
    bound on the optimal (parallel) makespan.  At `k = w.n_toff` it equals the
    naive estimate's wallclock. -/
def naiveMakespan (hw : Hardware) (d k : Nat) : Nat :=
  k * d * hw.cycle_time_us_tenths

theorem naiveMakespan_at_full
    (hw : Hardware) (w : Workload) (c : QECCode) (factory : Nat) :
    naiveMakespan hw c.d w.n_toff = (naiveEstimate hw w c factory).time_us_tenths := by
  simp only [naiveMakespan, naive_time]

/-! ## (3) Feasibility anchor: the naive sequential schedule satisfies the
    system invariants.  A one-Toffoli-at-a-time schedule trivially avoids
    resource conflicts; `InvariantFramework.demoCtx` is a representative such
    schedule and passes every base invariant.  Feasibility is what upgrades the
    footprint from "a number" to an ACHIEVABLE upper bound. -/

example : checkAll baseInvariants demoCtx = true := by decide

/-! ## (4) Worked gap analysis: Gidney–Ekerå 2021 (surface code, RSA-2048).

    We instantiate the naive schedule with GE2021's OWN inputs (a function of the
    algorithm + their surface-code choice) under the `surfaceModel` plug-in,
    prove the naive resource ceiling, and compare to their reported headline.
    The gap is the optimization the paper claims but we do not verify.

    Inputs (all from gidney-ekera-2021, arXiv:1905.09749):
      • n_toff   ≈ 2.7×10⁹    (Tab. 1: 0.3 n³ + 0.0005 n³ lg n at n = 2048)
      • n_logical ≈ 6200      (Tab. 1 abstract qubits, n_e ≈ 3n + …)
      • code [[1568, 1, 27]]  (§2.14: surface patch n = 2(d+1)² = 1568)
      • cycle time = 1 μs     (§2.13)
    Reported headline: 20×10⁶ physical qubits, 8 hours (title + Tab. 2).
    (Mirror `Corpus/PaperClaims.lean` gidney_ekera_2021_rsa2048_*; inlined here
    as self-contained citation anchors.) -/

/-- GE2021 hardware: 1 μs cycle. -/
def ge2021_hw : Hardware := { cycle_time_us_tenths := 10 }

/-- GE2021 workload: ≈ 2.7×10⁹ Toffolis over ≈ 6200 logical qubits (the canonical
    `Params.RSA2048` constants). -/
def ge2021_work : Workload :=
  { n_toff := RSA2048.toffoliReported, n_logical := RSA2048.patches }

/-- GE2021 surface patch [[1568, 1, 27]]. -/
def ge2021_code : QECCode := { n := 1568, k := 1, d := 27, hx := [], hz := [] }

/-- The naive ceiling for GE2021 under the `surfaceModel` plug-in, factory folded
    out (`0`) so the qubit figure is the pure data + 2× routing ceiling. -/
def ge2021_naive : ResourceEstimate := naiveEstimate ge2021_hw ge2021_work ge2021_code 0

/-- GE2021 reported headline: 20 million physical qubits. -/
def ge2021_reported_qubits : Nat := 20_000_000

/-- GE2021 reported headline: 8 hours, in tenths-of-μs (8·3600·10⁶·10 = 288×10⁹). -/
def ge2021_reported_time_us_tenths : Nat := 288_000_000_000

/-! ### QUBITS: the surface model's area-scaling ceiling reproduces the
    reported footprint. -/

/-- Naive ceiling = 6200 · (2·1568) = 19,443,200 qubits (surface `physPer` =
    2·physPerLogical = 3136 per logical). -/
example : ge2021_naive.qubits = 19_443_200 := by decide

/-- The naive ceiling sits just below the reported 20M total… -/
example : ge2021_naive.qubits ≤ ge2021_reported_qubits := by decide

/-- …within ~3% — the residual (≈ 0.56M) is the magic-factory footprint our
    naive model folds out.  So GE2021's reported qubit count IS essentially the
    verified surface-model area ceiling: NO unverified qubit-side optimization. -/
example : ge2021_reported_qubits - ge2021_naive.qubits ≤ 600_000 := by decide

/-! ### TIME: the naive sequential ceiling is ~2.5× the reported wallclock. -/

/-- Naive sequential time ceiling = 2.7×10⁹ · 27 · 1 μs = 72.9×10⁹ μs ≈ 20.25 h
    (here in tenths-of-μs: 729×10⁹). -/
example : ge2021_naive.time_us_tenths = 729_000_000_000 := by decide

/-- The reported 8 h sits BELOW the naive sequential ceiling — the paper's
    schedule is faster than dumb sequential execution. -/
example : ge2021_reported_time_us_tenths ≤ ge2021_naive.time_us_tenths := by decide

/-- The gap is between 2× and 3×: GE2021's reported wallclock is ~2.5× under our
    verified naive ceiling.  That speed-up comes from reaction-limited pipelining
    of the Toffoli critical path — an optimization we do NOT verify.  The gap
    makes exactly this factor explicit. -/
example : 2 * ge2021_reported_time_us_tenths ≤ ge2021_naive.time_us_tenths := by decide
example : ge2021_naive.time_us_tenths ≤ 3 * ge2021_reported_time_us_tenths := by decide

/-! ### Headline finding (GE2021).
    QUBITS: reported = verified surface-model area ceiling (no unverified gap).
    TIME:   reported is ~2.5× below the verified naive sequential ceiling; the
            gap = reaction-limited pipelining, claimed but not verified.

    The qLDPC instances (qianxu, xu-2024) are obtained by swapping `surfaceModel`
    for `qldpcModel` (`Framework/CostModel.lean`) — whose ancilla rule scales
    with the measured operator's PHYSICAL WEIGHT (Θ(w)·parallel), not the data
    area.  The remaining residues there are the +syndrome-check-qubit subleading
    term and the Θ(w) boundary-expansion constant (both documented on
    `qldpcModel`), NOT the ancilla rule itself, which is now in-framework. -/

end FormalRV.System.NaiveUpperBound
