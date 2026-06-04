/-
  FormalRV.Corpus.Gidney2025 — Phase-C corpus paper #3.

  Gidney 2025, "How to factor 2048-bit RSA integers with less than a
  million noisy qubits" (arXiv:2505.15917). Surface-code + yoked-
  surface-code cold storage + cultivation on superconducting qubits.

  Parametric tuple bound here:
    L1 ShorAlgorithm     : q_A = 8  (Ekerå–Håstad-style parameter `s`,
                           paper §3.1 / notes line 72-73; m=1280 input
                           qubits for n=2048)
    L4 QECCode           : (n, k, d) = (1352, 1, 25) — hot-region
                           rotated surface code at distance 25,
                           n_physical = 2(d+1)² = 2·26² = 1352
                           (paper §3.2, notes line 128).  Yoked cold-
                           storage region (d=8-10, 430 phys/logical) is
                           a separate region this tick does not model.
    HW QualtranPhysical  : `gidney_fowler_realistic` (1e-3 gate err,
                           1 μs cycle) — paper §3.2 explicit, notes
                           line 22-23.
-/

import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Framework.ResourceEstimate
import FormalRV.Qualtran.Bridge

namespace FormalRV.Corpus.Gidney2025

open FormalRV.Framework FormalRV.Framework.Resource FormalRV.Qualtran

/-- Gidney 2025 Shor instance: RSA-2048 with Ekerå–Håstad `s = 8`
parameter (input qubits m = n/2 + ⌈n/(2s)⌉ = 1024 + 128 = 1152;
paper reports 1280 due to extra ancillas). -/
def gidney2025_shor : ShorAlgorithm :=
  { N := 0, q_A := 8 }

/-- Gidney 2025 hot-region surface-code patch: distance-25 rotated
surface code, 1352 physical qubits per logical (paper §3.2 / notes
line 128: `2(d+1)² = 2·26² = 1352`). -/
def gidney2025_code : QECCode :=
  { n := 1352, k := 1, d := 25, hx := [], hz := [] }

/-- Gidney 2025 hardware: same canonical `gidney_fowler_realistic`
profile as GE2021 — 1e-3 physical error, 1 μs cycle time, square
grid NN connectivity (paper §3.2). -/
def gidney2025_hw : QualtranPhysicalParameters :=
  gidney_fowler_realistic

/-- The full parametric tuple. -/
def gidney2025_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (gidney2025_shor, gidney2025_code, gidney2025_hw)

/-- Smoke: paper-stated parameters read back. -/
example : gidney2025_instance.1.q_A = 8 := by rfl
example : gidney2025_instance.2.1.n = 1352 ∧
          gidney2025_instance.2.1.k = 1 ∧
          gidney2025_instance.2.1.d = 25 := ⟨rfl, rfl, rfl⟩
example : gidney2025_instance.2.2 = gidney_fowler_realistic := rfl

/-! ## §2. Headline resource workload + cold storage.

    Beyond the (algorithm, code, hardware) tuple, the paper's headline RSA-2048 cost. -/

/-- Gidney-2025 workload: `6.5×10⁹` Toffolis (main.tex:1191), `1537` logical qubits
    (main.tex:1173). -/
def gidney2025_work : Workload :=
  { n_toff := 6_500_000_000, n_logical := 1537 }

/-- Cold (idle) storage uses a YOKED 2D-parity-check surface code: `430` physical qubits per
    idle logical qubit (main.tex:1163), vs `1352` for a hot distance-25 patch.  No `QECCode`
    slot — it is a concatenated/yoked construction the framework does not yet model. -/
def gidney2025_cold_physical_per_logical : Nat := 430

/-! ## §3. Cross-checks of the paper's stated TALLIES (machine-checked arithmetic).

    The verification value-add: the paper's own component arithmetic, confirmed by `decide`. -/

/-- **Logical-qubit tally**: `1280` (cold input) `+ 131` (active hot `3f+2ℓ+⌈log m⌉`)
    `+ 7·18` (idle hot patches) `= 1537 < 1600` (main.tex:1173). -/
theorem gidney2025_logical_tally : 1280 + 131 + 7 * 18 = 1537 := by decide

/-- **Physical-qubit tally**: cold `1280·430` + active-hot `131·1352` + idle-hot `7·18·1352`
    `= 897 864`, reported as `< 1 000 000` for slack (main.tex:1168–1176). -/
theorem gidney2025_physical_tally :
    1280 * 430 + 131 * 1352 + 7 * 18 * 1352 = 897864 := by decide

/-- Hot patch size: `2·(d+1)² = 2·26² = 1352` at `d = 25` (main.tex:1162). -/
theorem gidney2025_hot_patch_size : 2 * (25 + 1) ^ 2 = 1352 := by decide

/-- The encoded workload's logical count matches the reconciled tally. -/
theorem gidney2025_work_consistent :
    gidney2025_work.n_logical = 1280 + 131 + 7 * 18 := by decide

/-- Largest lookup (`w₁ = 6` address qubits) needs `2⁶ − 6 − 1 = 57` CCZ states
    (Babbush QROM cost `2ⁿ − n − 1`; main.tex:1204). -/
theorem gidney2025_lookup_ccz : 2 ^ 6 - 6 - 1 = 57 := by decide

/-- CCZ-state period `= 150 / 6 = 25 µs` equals the `d = 25` lattice-surgery period
    (6 factories, 150 rounds/CCZ; main.tex:1192). -/
theorem gidney2025_ccz_period : 150 / 6 = 25 := by decide

/-! ## §4. Gap-vs-reported: Gidney 2025 against GE2021 in the framework.

    The trade made explicit: ≈22× fewer physical qubits, paid for by ≈2.4× more Toffolis. -/

/-- Physical-qubit reduction GE2021 → Gidney2025 is ≈ 22×: `897864·22 = 19 753 008 < 20 000 000`
    (GE2021's 20M; main.tex:88,1245). -/
theorem gidney2025_vs_ge2021_qubit_cut : 897864 * 22 < 20000000 := by decide

/-- Toffoli INCREASE GE2021 → Gidney2025: `2.7×10⁹ → 6.5×10⁹` (> 2× more — the space saving is
    paid for in gates/time; main.tex:94,157). -/
theorem gidney2025_vs_ge2021_toffoli : 2_700_000_000 * 2 < 6_500_000_000 := by decide

-- Headline resource vector: (Toffolis, logical qubits, physical qubits).
#eval (gidney2025_work.n_toff, gidney2025_work.n_logical,
       1280 * 430 + 131 * 1352 + 7 * 18 * 1352)   -- (6500000000, 1537, 897864)

/-! ## §5. L2 gadget Toffoli costs.

    Essentially all work is addition, lookup, and "phaseup" (main.tex:989).  Their per-gadget
    Toffoli costs (cited), plus Gidney's modular-adder improvement to `2.5n`. -/

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

/-! ## §6. Chosen parameters + an honest note on the paper's numbers.

    Grid-scan-selected parameters minimizing `q³·t` (main.tex:1006–1017):
      `s = 8` (Ekerå–Håstad), `ℓ ∈ [18,25]` (prime bit length), `w₁ = 6` (loop1 window),
      `w₃ ∈ [2,6]`, `w₄ ∈ [2,8]`, `f = 33` (truncated accumulator).

    All numbers above are the paper's CLAIMED values, verified for internal arithmetic
    consistency — NOT derived from a Lean circuit.  One minor textual slip noted for honesty:
    the runtime states "expected number of shots is 9.2" then computes with `9.1`
    (`12.07·9.1/24 = 4.63` days; main.tex:1216).  Negligible (rounding), reported not hidden. -/

end FormalRV.Corpus.Gidney2025
