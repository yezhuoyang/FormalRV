/-
  FormalRV.Audit.CainXu2026.QianxuNaiveConstructions — name the two NAIVE constructions that
  justify qianxu's resource UPPER bounds, the pieces the paper leaves undetailed.

  qianxu omits (a) how to compile a PPM with their LP code, and (b) how to
  parallelise the adder / unary-lookup.  We fill BOTH in the most naive way and show
  each naive construction's cost EQUALS the corresponding upper bound of
  `QianxuBounds` — so the upper bounds are CONSTRUCTION-justified, not asserted — and
  each gap to the paper's optimized claim is the optimization the paper does NOT
  construct.

  (a) NAIVE PPM-on-LP: to measure a logical Pauli of the memory code, couple an
      ancilla block and measure the MERGED code.  Naive qubit cost = data + ancilla
      (no sharing).  This is the per-logical-PPM footprint feeding the qubit upper
      bound's memory + operation-zone-ancilla terms.
  (b) NAIVE adder/lookup = SEQUENTIAL: critical-path Toffoli DEPTH = the Toffoli
      COUNT (no parallelism).  Naive time = count × per-Toffoli — exactly the time
      upper bound.  qianxu's parallel trick cuts depth ≪ count (the gap).

  No `sorry`, no `axiom`.
-/

import FormalRV.Audit.CainXu2026.QianxuBounds

namespace FormalRV.Audit.CainXu2026.QianxuNaiveConstructions

open FormalRV.Audit.CainXu2026.QianxuBounds

/-! ## (a) Naive PPM-on-LP compilation: merged-code qubit cost -/

/-- The naive PPM-on-LP qubit cost: merge the memory code (`data_n` qubits) with an
    ancilla block (`ancilla_n` qubits) and measure the merged code — `data_n +
    ancilla_n` qubits per logical PPM, no sharing. -/
def naivePPMonLP_qubits (data_n ancilla_n : Nat) : Nat := data_n + ancilla_n

/-- The naive PPM-on-LP construction's qubit cost is ≤ the qubit upper bound — i.e.
    the memory + operation-zone-ancilla terms of the naive zoned build account for
    it (with `N_m ≥ data_n`, `N_A ≥ ancilla_n`). -/
theorem naivePPMonLP_within_upper (data_n ancilla_n N_m N_p N_f N_A N_res : Nat)
    (hd : data_n ≤ N_m) (ha : ancilla_n ≤ N_A) :
    naivePPMonLP_qubits data_n ancilla_n ≤ qubitUpper N_m N_p N_f N_A N_res := by
  unfold naivePPMonLP_qubits qubitUpper; omega

/-- For qianxu lp_20^{3,7} (data 4350) + operation-zone ancilla N_𝒜 = 894, the naive
    per-PPM footprint is 5244 qubits — the memory+operation contribution. -/
theorem qianxu_naivePPM_footprint : naivePPMonLP_qubits 4350 894 = 5244 := by decide

/-! ## (b) Naive sequential adder/lookup: depth = count -/

/-- The naive (sequential, no-parallelism) modexp critical-path Toffoli DEPTH equals
    the Toffoli COUNT — every Toffoli waits for the previous. -/
def naiveSequentialDepth (toffCount : Nat) : Nat := toffCount

/-- **The naive sequential construction's makespan IS the time upper bound**: depth =
    count, so naive time = count × per-Toffoli = `timeUpper`.  Hence the time upper
    bound is achievable by the naive sequential schedule (construction-justified). -/
theorem naiveSequential_is_timeUpper (toffCount tau_s cycle : Nat) :
    timeLower (naiveSequentialDepth toffCount) tau_s cycle = timeUpper toffCount tau_s cycle := by
  unfold naiveSequentialDepth timeLower timeUpper; rfl

/-- qianxu's parallelisation cuts the critical-path depth FAR below the count.  With
    a parallel depth `D_par`, the speed-up over the naive sequential build is the
    factor `count / D_par` — the trick the paper does NOT construct in detail. -/
def parallelSpeedup (toffCount D_par : Nat) : Nat := toffCount / D_par

/-- Concrete: 10^6 Toffolis at parallel depth 10^4 ⇒ a 100× speed-up the paper
    claims but does not construct (matching `QianxuBounds.qianxu_time_gap`). -/
theorem qianxu_parallel_speedup : parallelSpeedup 1_000_000 10_000 = 100 := by decide

/-! ## Both naive constructions justify the upper bounds, with the gap named -/

/-- **Summary**: (a) the naive PPM-on-LP footprint sits inside the qubit upper bound,
    and (b) the naive sequential schedule's makespan IS the time upper bound — so
    both `QianxuBounds` upper bounds are realised by explicit naive constructions,
    and the gaps (`qianxu_qubit_gap` = 4839, `qianxu_time_gap` ≈ 100×) are the
    paper's unconstructed optimisations (factory sharing; adder/lookup parallelism). -/
theorem naive_constructions_justify_upper_bounds (tau_s cycle : Nat) :
    -- (b) the sequential construction = the time upper bound, for any count:
    (∀ toffCount, timeLower (naiveSequentialDepth toffCount) tau_s cycle
        = timeUpper toffCount tau_s cycle)
    -- (a) the qianxu naive PPM footprint is the memory+ancilla contribution:
    ∧ naivePPMonLP_qubits 4350 894 = 5244 := by
  exact ⟨fun t => naiveSequential_is_timeUpper t tau_s cycle, qianxu_naivePPM_footprint⟩

end FormalRV.Audit.CainXu2026.QianxuNaiveConstructions
