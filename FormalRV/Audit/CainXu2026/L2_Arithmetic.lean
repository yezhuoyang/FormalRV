/-
  Audit · cain-xu-2026 · LAYER 2 — ARITHMETIC (adders / lookups)
  ----------------------------------------------------------------------------
  The paper's per-Toffoli costs (Eqs E3/E4/E9): E3/E4 are RECOVERED as exact
  structural identities (✅ verify-clean); E9 is an arithmetic (decide) bound (➗).

  Also holds the two NAIVE constructions that JUSTIFY the resource upper bounds
  (was `QianxuNaiveConstructions`): the merged-code PPM footprint and the
  sequential adder/lookup depth, each shown to realise the corresponding
  `ResourceBounds` upper bound (those `def`s live in L4_Code).

  ONE flat namespace `FormalRV.Audit.CainXu2026`.
-/
import FormalRV.Framework.PaperClaims
import FormalRV.Audit.CainXu2026.L4_Code
import FormalRV.Verifier

namespace FormalRV.Audit.CainXu2026

/-============================================================================
  PART A — Naive constructions that justify the upper bounds
           (was QianxuNaiveConstructions)
============================================================================-/

/-! ## (a) Naive PPM-on-LP compilation: merged-code qubit cost -/

/-- The naive PPM-on-LP qubit cost: merge the memory code (`data_n` qubits) with an
    ancilla block (`ancilla_n` qubits) and measure the merged code — `data_n +
    ancilla_n` qubits per logical PPM, no sharing. -/
def naivePPMonLP_qubits (data_n ancilla_n : Nat) : Nat := data_n + ancilla_n

/-- The naive PPM-on-LP construction's qubit cost is ≤ the qubit upper bound. -/
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
    count, so naive time = count × per-Toffoli = `timeUpper`. -/
theorem naiveSequential_is_timeUpper (toffCount tau_s cycle : Nat) :
    timeLower (naiveSequentialDepth toffCount) tau_s cycle = timeUpper toffCount tau_s cycle := by
  unfold naiveSequentialDepth timeLower timeUpper; rfl

/-- qianxu's parallelisation cuts the critical-path depth FAR below the count. -/
def parallelSpeedup (toffCount D_par : Nat) : Nat := toffCount / D_par

/-- Concrete: 10^6 Toffolis at parallel depth 10^4 ⇒ a 100× speed-up. -/
theorem qianxu_parallel_speedup : parallelSpeedup 1_000_000 10_000 = 100 := by decide

/-- **Summary**: (a) the naive PPM-on-LP footprint sits inside the qubit upper bound,
    and (b) the naive sequential schedule's makespan IS the time upper bound. -/
theorem naive_constructions_justify_upper_bounds (tau_s cycle : Nat) :
    (∀ toffCount, timeLower (naiveSequentialDepth toffCount) tau_s cycle
        = timeUpper toffCount tau_s cycle)
    ∧ naivePPMonLP_qubits 4350 894 = 5244 := by
  exact ⟨fun t => naiveSequential_is_timeUpper t tau_s cycle, qianxu_naivePPM_footprint⟩

end FormalRV.Audit.CainXu2026

-- ✅ Eq. E3: the Gidney-variant n-bit adder costs exactly 25·n τ_s:
#verify_clean FormalRV.PaperClaims.gidney_n_bit_adder_meets_qianxu_E3
-- ✅ Eq. E4: the controlled-adder n-bit costs exactly 30·n τ_s:
#verify_clean FormalRV.PaperClaims.ctl_adder_n_bit_meets_qianxu_E4
-- ➗ Eq. E9: full RSA-2048 lookup = 22,720 τ_s (arithmetic recovery, `decide`):
#check @FormalRV.PaperClaims.qianxu_E9_full_lookup_via_toffoli_count
