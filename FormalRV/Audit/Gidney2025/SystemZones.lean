/-
  Audit · gidney-2025 · SYSTEM-ZONE SETUP / RESOURCE TALLY
  ============================================================================
  The reported < 1,000,000-qubit footprint realised as a machine-checked
  internal-consistency TALLY: the paper's component qubit / Toffoli / window
  counts add up to its stated totals (the `decide` theorems below).  This is
  arithmetic-tally verification (like the GE2021 corpus tuple), NOT yet a
  zoned syscall schedule with space-time invariants.

  Merged here (one flat namespace `FormalRV.Audit.Gidney2025`):
    • the headline workload + yoked cold-storage placeholder;
    • the logical / input / physical / window / lookup / period TALLIES;
    • the gap-vs-GE2021 (≈22× fewer qubits, ≈2.4× more Toffolis) + vs-CFS24;
    • the L2 per-gadget Toffoli cost models (add / lookup / modular adder).

  ⬜ GAP — the footprint is a tally, not a zoned schedule with invariants; the
  yoked surface codes / cultivation / 8T→CCZ factories have no Lean
  construction (coarse Nat placeholders).  No `sorry`, no new `axiom`.
-/
import FormalRV.Framework.ResourceEstimate

namespace FormalRV.Audit.Gidney2025

open FormalRV.Framework FormalRV.Framework.Resource

/-============================================================================
  PART A — Headline workload + cold storage
============================================================================-/

/-- Gidney-2025 workload: `6.5×10⁹` Toffolis (main.tex:1191), `1537` logical qubits
    (main.tex:1173). -/
def gidney2025_work : Workload :=
  { n_toff := 6_500_000_000, n_logical := 1537 }

/-- Cold (idle) storage uses a YOKED 2D-parity-check surface code: `430` physical qubits per
    idle logical qubit (main.tex:1163), vs `1352` for a hot distance-25 patch.  No `QECCode`
    slot — it is a concatenated/yoked construction the framework does not yet model. -/
def gidney2025_cold_physical_per_logical : Nat := 430

/-============================================================================
  PART B — Cross-checks of the paper's stated TALLIES (machine-checked arithmetic)

  The verification value-add: the paper's own component arithmetic, confirmed
  by `decide`.
============================================================================-/

/-- **Logical-qubit tally**: `1280` (cold input `m`) `+ 131` (active-hot logical, a paper-stated
    LITERAL — see caveat: it does NOT equal `3f+2ℓ+⌈log m⌉ = 152`) `+ 7·18 = 126` (idle hot
    patches) `= 1537 < 1600` (main.tex:1173). -/
theorem gidney2025_logical_tally : 1280 + 131 + 7 * 18 = 1537 := by decide

/-- Input/exponent qubits: `m = ⌊n/2⌋ + ⌊n/s⌋ = 1024 + 256 = 1280` at `n=2048, s=8`
    (Ekerå–Håstad; main.tex:1030,1166). -/
theorem gidney2025_input_qubits : 2048 / 2 + 2048 / 8 = 1280 := by decide

/-- Window counts (ceil division): `W₁ = ⌈m/w₁⌉ = 214`, `W₃ = ⌈ℓ/w₃⌉ = 7`, `W₄ = ⌈ℓ/w₄⌉ = 5`
    at `m=1280, ℓ=21, w₁=6, w₃=3, w₄=5` (main.tex:1035–1037). -/
theorem gidney2025_window_counts :
    (1280 + 6 - 1) / 6 = 214 ∧ (21 + 3 - 1) / 3 = 7 ∧ (21 + 5 - 1) / 5 = 5 := by decide

/-- **Physical-qubit tally**: cold `1280·430` + active-hot `131·1352` + idle-hot `7·18·1352`
    `= 897 864`, reported as `< 1 000 000` for slack (main.tex:1168–1176). -/
theorem gidney2025_physical_tally :
    1280 * 430 + 131 * 1352 + 7 * 18 * 1352 = 897864 := by decide

/-- The encoded workload's logical count matches the reconciled tally. -/
theorem gidney2025_work_consistent :
    gidney2025_work.n_logical = 1280 + 131 + 7 * 18 := by decide

/-- Largest lookup (`w₁ = 6` address qubits) needs `2⁶ − 6 − 1 = 57` CCZ states
    (Babbush QROM cost `2ⁿ − n − 1`; main.tex:1204). -/
theorem gidney2025_lookup_ccz : 2 ^ 6 - 6 - 1 = 57 := by decide

/-- CCZ-state period `= 150 / 6 = 25 µs` equals the `d = 25` lattice-surgery period
    (6 factories, 150 rounds/CCZ; main.tex:1192). -/
theorem gidney2025_ccz_period : 150 / 6 = 25 := by decide

/-- The `< 1 000 000` headline holds with ≈100k slack: `897 864 < 1 000 000` and
    `1 000 000 − 897 864 = 102 136` (main.tex:1176). -/
theorem gidney2025_slack : 897864 < 1000000 ∧ 1000000 - 897864 = 102136 := by decide

-- Headline resource vector: (Toffolis, logical qubits, physical qubits).
#eval (gidney2025_work.n_toff, gidney2025_work.n_logical,
       1280 * 430 + 131 * 1352 + 7 * 18 * 1352)   -- (6500000000, 1537, 897864)

/-============================================================================
  PART C — Gap-vs-reported: Gidney 2025 against GE2021 in the framework

  The trade made explicit: ≈22× fewer physical qubits, paid for by ≈2.4× more
  Toffolis.
============================================================================-/

/-- Physical-qubit reduction GE2021 → Gidney2025 is ≈ 22×: `897864·22 = 19 753 008 < 20 000 000`
    (GE2021's 20M; main.tex:88,1245). -/
theorem gidney2025_vs_ge2021_qubit_cut : 897864 * 22 < 20000000 := by decide

/-- Toffoli INCREASE GE2021 → Gidney2025: `2.7×10⁹ → 6.5×10⁹` (> 2× more — the space saving is
    paid for in gates/time; main.tex:94,157). -/
theorem gidney2025_vs_ge2021_toffoli : 2_700_000_000 * 2 < 6_500_000_000 := by decide

/-- Toffoli REDUCTION vs CFS24: `2×10¹² / 6.5×10⁹ ≈ 308×`, far beyond the paper's loose ">100×"
    claim (`300·6.5×10⁹ < 2×10¹²`; main.tex:95,158). -/
theorem gidney2025_vs_cfs24_toffoli : 300 * 6_500_000_000 < 2_000_000_000_000 := by decide

/-============================================================================
  PART D — L2 gadget Toffoli costs

  Essentially all work is addition, lookup, and "phaseup" (main.tex:989).  Their
  per-gadget Toffoli costs (cited), plus Gidney's modular-adder improvement to
  `2.5n`.
============================================================================-/

/-- `n`-qubit Gidney-2018 addition: `n − 1` Toffolis (main.tex:993). -/
def g2025_add_toffoli (n : Nat) : Nat := n - 1
/-- `n`-address Babbush QROM lookup: `2ⁿ − n − 1` Toffolis (main.tex:996). -/
def g2025_lookup_toffoli (n : Nat) : Nat := 2 ^ n - n - 1
/-- Modular adder cost `2.5n` (`= 5n/2`) — vs Berry et al. `3.5n` (main.tex:977). -/
def g2025_modadd_toffoli_halves (n : Nat) : Nat := 5 * n   -- in half-Toffoli units (2.5n = 5n/2)

/-- The `f = 33` accumulator addition in loop4 needs `f − 1 = 32` CCZ states (main.tex:1195–1196). -/
theorem g2025_loop4_add_ccz : g2025_add_toffoli 33 = 32 := by decide
/-- The `w₁ = 6` lookup needs `2⁶ − 6 − 1 = 57` CCZ states (main.tex:1203–1204). -/
theorem g2025_loop1_lookup_ccz : g2025_lookup_toffoli 6 = 57 := by decide
/-- Gidney's modular adder beats Berry's: `2.5n < 3.5n` (`5n < 7n` in half units, for `n>0`). -/
theorem g2025_modadd_beats_berry (n : Nat) (hn : 0 < n) :
    g2025_modadd_toffoli_halves n < 7 * n := by
  unfold g2025_modadd_toffoli_halves; omega

end FormalRV.Audit.Gidney2025
