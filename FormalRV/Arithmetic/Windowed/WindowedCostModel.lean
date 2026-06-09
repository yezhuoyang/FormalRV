/-
  FormalRV.Shor.WindowedCostModel — verifying Gidney–Ekerå's reported resource numbers
  (1905.09749, "Abstract circuit model cost estimate", main.tex:685–731).

  ⚠ AUDIT / SCOPE (read this).  Everything in THIS file is the PAPER'S cost-accounting
  FORMULA arithmetic — `ℚ`-valued functions reproducing the paper's §"cost estimate"
  equations and proving they reduce to `0.3 n³ + …`.  These are NOT derived from a circuit;
  they verify that the paper's accounting is internally consistent.

  The resource counts that ARE derived from the formally-verified `Gate` circuit (by
  `tcount`/`maxIdx` recursion on the actual term) live in `FormalRV.Shor.WindowedCircuit`:
    * Toffoli count — `windowedMulCircuit_toffoli` (one multiply-add) and
      `composedModExp_toffoli` (the full `numMults`-multiplication exponentiation skeleton);
      `windowedMulCircuit_toffoli_padded` shows the `lg n` term IS the adder over the
      `g_pad ≈ 3 lg n` coset-padding qubits.
    * Qubit count — `width` (= `maxIdx + 1`, computed from the `Gate`); `width_…_padding`
      proves (kernel `decide`) that padding the register by `pad` widens the circuit by
      `2·pad` qubits — the `lg n` qubit term is the padding qubits the circuit acts on.
    * Magic-state demand — `WindowedPPM.windowedMulCircuit_magicDemand` (= the structural
      Toffoli count, via the proven `shorMagicDemand_eq_ccxCount`).
  HONEST GAP: that structural circuit is the *unoptimized* construction (`≈ 6 n³` at
  `w = lg n`); the paper's `0.3 n³` additionally needs Gray-code + measurement-uncompute
  (the `4·w·2^w → 2^w` lookup optimization) and oblivious runways, which are not yet built
  as `Gate`s.  This file checks the paper's *optimized* formula reduces correctly; it does
  NOT claim that formula is the `tcount` of a verified circuit.

  We formalize the paper's EXACT cost formulas (the products, parameters plugged in) over
  ℚ and verify, exactly and honestly, that the abstract's reported leading-order figures
  `0.3 n³ + 0.0005 n³ lg n` Toffolis and `500 n² + n² lg n` measurement depth are valid
  (rounded-up) upper bounds on those formulas.

  Honesty note: the paper itself calls these "approximate upper bounds" (l.731).  The
  EXACT leading Toffoli coefficient is `123/512 ≈ 0.2402` (not `0.3`); the paper reports
  `0.3` because it rounds the intermediate `LookupAdditionCount ≈ 0.08·n·n_e` up to
  `0.1·n·n_e` (l.704–705).  We prove BOTH the exact coefficients and that they sit below
  the paper's reported numbers.

  Paper parameters (main.tex:690): `g_exp = g_mul = 5`, `g_sep = 1024`,
  `g_pad = 2 lg n + lg n_e + 10 ≈ 3 lg n + 10`, and (Ekerå–Håstad) `n_e = 1.5 n`.

  Typo flag (main.tex:712): the printed per-lookup Toffoli term `2^{g_exp+g_pad}` must be
  `2^{g_exp+g_mul}` (= 2^10): the lookup table is addressed by the `g_exp+g_mul` window
  bits (l.594, "Toffoli count … 2^{g_mul+g_exp}"), and only `g_mul` reproduces the
  reported `0.2 n_e n²`.  We use the correct `2^{g_exp+g_mul}`.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace FormalRV.Shor.WindowedCostModel

/-! ## The paper's cost formulas (parameters plugged in; `L := lg n`). -/

/-- `LookupAdditionCount(n, n_e)` (main.tex eq. l.700–707):
    `(2 n n_e)/(g_exp g_mul) · (g_sep+1)/g_sep`, with `g_exp=g_mul=5`, `g_sep=1024`. -/
def lookupAdditionCount (n n_e : ℚ) : ℚ := (2 * n * n_e) / (5 * 5) * ((1024 + 1) / 1024)

/-- Per-lookup-addition Toffoli cost (main.tex l.712, corrected `g_mul`):
    `2n + n·g_pad/g_sep + 2^{g_exp+g_mul}`, with `g_sep=1024`, `g_pad = 3L+10`,
    `2^{g_exp+g_mul} = 2^10`. -/
def perLookupToffoli (n L : ℚ) : ℚ := 2 * n + n * (3 * L + 10) / 1024 + 2 ^ 10

/-- `ToffoliCount(n, n_e)` (main.tex eq. l.715–721) = LookupAdditionCount · perLookupToffoli. -/
def toffoliCount (n n_e L : ℚ) : ℚ := lookupAdditionCount n n_e * perLookupToffoli n L

/-- `LookupAdditionCount` simplifies exactly to `41/512 · n · n_e`
    (`41/512 ≈ 0.0801`; the paper rounds this up to `0.1`, l.705). -/
theorem lookupAdditionCount_eq (n n_e : ℚ) :
    lookupAdditionCount n n_e = 41 / 512 * n * n_e := by
  unfold lookupAdditionCount; ring

/-! ## Exact closed forms (with `n_e = 1.5 n`). -/

/-- The EXACT Toffoli count of the paper's model at `n_e = 1.5 n`:
    `123/512 · n³ + 369/1048576 · n³ lg n + 1230/1048576 · n³ + 123 · n²`. -/
theorem toffoliCount_closed (n L : ℚ) :
    toffoliCount n (3 * n / 2) L
      = 123 / 512 * n ^ 3 + 369 / 1048576 * n ^ 3 * L
        + 1230 / 1048576 * n ^ 3 + 123 * n ^ 2 := by
  unfold toffoliCount lookupAdditionCount perLookupToffoli; ring

/-- **The exact leading coefficients are below the paper's reported `0.3` and `0.0005`.**
    So the abstract's `0.3 n³ + 0.0005 n³ lg n` (1905.09749, main.tex:78/214) is a valid
    rounded-up upper bound on the paper's exact cost model; the exact values are
    `n³`-coeff `= 123/512 ≈ 0.2402` and `n³·lg n`-coeff `= 369/1048576 ≈ 0.000352`. -/
theorem toffoli_coeffs_le_paper :
    (123 : ℚ) / 512 ≤ 3 / 10 ∧ (369 : ℚ) / 1048576 ≤ 5 / 10000 := by
  refine ⟨by norm_num, by norm_num⟩

/-- **The reported Toffoli count is a genuine upper bound on the cost model for all
    `n ≥ 2100`, `lg n ≥ 0`.**  (The exact leading `0.2402 n³` plus the lower-order
    `123 n²` / `0.00117 n³` terms stay under `0.3 n³`; `2100` covers RSA-2048 and up
    once the `lg n` slack is counted, and the bound is clean to state for `n ≥ 2100`.) -/
theorem toffoliCount_le_paper (n L : ℚ) (hn : 2100 ≤ n) (hL : 0 ≤ L) :
    toffoliCount n (3 * n / 2) L ≤ 3 / 10 * n ^ 3 + 5 / 10000 * n ^ 3 * L := by
  rw [toffoliCount_closed]
  have hn0 : (0 : ℚ) ≤ n := by linarith
  -- 123 n² ≤ (3/10 − 123/512 − 1230/1048576) n³  for n ≥ 2100  (coefficient ≈ 0.0586)
  have hquad : (123 : ℚ) * n ^ 2 ≤ (3 / 10 - 123 / 512 - 1230 / 1048576) * n ^ 3 := by
    have hstep : (123 : ℚ) ≤ (3 / 10 - 123 / 512 - 1230 / 1048576) * n := by
      have : (3 / 10 - 123 / 512 - 1230 / 1048576) * n
              ≥ (3 / 10 - 123 / 512 - 1230 / 1048576) * 2100 := by
        apply mul_le_mul_of_nonneg_left hn (by norm_num)
      linarith [this]
    nlinarith [sq_nonneg n, hstep, hn0]
  -- the lg n coefficient: 369/1048576 ≤ 5/10000
  have hlg : (369 : ℚ) / 1048576 * n ^ 3 * L ≤ 5 / 10000 * n ^ 3 * L := by
    have hn3 : (0 : ℚ) ≤ n ^ 3 := by positivity
    nlinarith [mul_nonneg hn3 hL]
  nlinarith [hquad, hlg]

/-- **The headline RSA-2048 instance, verified exactly.**  At `n = 2048`, `n_e = 3072`,
    `lg n = 11`, the paper's cost model gives exactly `503808 · 5206 = 2 622 824 448`
    Toffolis, which is `≤` the abstract's reported `0.3 n³ + 0.0005 n³ lg n ≈ 2.6242·10⁹`
    (they agree to within 0.05%). -/
theorem toffoliCount_rsa2048 :
    toffoliCount 2048 3072 11 = 2622824448
    ∧ toffoliCount 2048 3072 11 ≤ 3 / 10 * 2048 ^ 3 + 5 / 10000 * 2048 ^ 3 * 11 := by
  refine ⟨?_, ?_⟩ <;>
    · unfold toffoliCount lookupAdditionCount perLookupToffoli; norm_num

/-! ## Measurement depth (main.tex eq. l.723–729). -/

/-- Per-lookup measurement depth (l.712): `2 g_sep + 2 g_pad + 2^{g_exp+g_mul}`. -/
def perLookupDepth (L : ℚ) : ℚ := 2 * 1024 + 2 * (3 * L + 10) + 2 ^ 10

/-- `MeasurementDepth(n, n_e)` = LookupAdditionCount · perLookupDepth. -/
def measurementDepth (n n_e L : ℚ) : ℚ := lookupAdditionCount n n_e * perLookupDepth L

/-- Exact measurement depth at `n_e = 1.5 n`: `≈ 371.4 n² + 0.72 n² lg n`, comfortably
    under the abstract's reported `500 n² + n² lg n`. -/
theorem measurementDepth_le_paper (n L : ℚ) (hn : 0 ≤ n) (hL : 0 ≤ L) :
    measurementDepth n (3 * n / 2) L ≤ 500 * n ^ 2 + 1 * n ^ 2 * L := by
  have hclosed : measurementDepth n (3 * n / 2) L
      = 380316 / 1024 * n ^ 2 + 738 / 1024 * n ^ 2 * L := by
    unfold measurementDepth lookupAdditionCount perLookupDepth; ring
  rw [hclosed]
  have hn2 : (0 : ℚ) ≤ n ^ 2 := by positivity
  nlinarith [mul_nonneg hn2 hL, hn2]

/-! ## Logical-qubit count (main.tex:78/212: `3n + 0.002 n lg n`).

The paper gives no closed-form *equation* for the qubit count (unlike Toffoli/depth); the
`3n` is the three `n`-qubit work registers, the `0.002 n lg n` is the coset-padding +
oblivious-runway overhead.  We verify the leading register count `3n`; the `lg n` padding
coefficient is the paper's reported figure (cited, not re-derived — methodology: do not
invent what the paper does not state as a formula). -/

/-- The three `n`-qubit work registers of the windowed modular exponentiation: the running
    product (`productreg`, l.508), the multiplier/input factor, and the target/scratch.
    The exponent register is recycled via the semiclassical QFT (l.486) and so does NOT
    contribute to the steady-state space — which is why the leading qubit count is `3n`,
    not `3n + n_e`. -/
def workRegisterQubits (n : ℕ) : ℕ := n + n + n

/-- The leading logical-qubit count is exactly `3n` (the paper's `3n + 0.002 n lg n`
    has leading term `3n`; the `0.002 n lg n` is the cited coset/runway padding). -/
theorem workRegisterQubits_eq (n : ℕ) : workRegisterQubits n = 3 * n := by
  unfold workRegisterQubits; ring

/-! ## Approximation deviation (main.tex:741–755) — the EXACT `≈ 10⁻⁷`. -/

/-- Per-addition deviation (main.tex:741): `n / (g_sep · 2^{g_pad})`, with `g_sep = 1024`
    and `2^{g_pad} = 2^{2 lg n + lg n_e + 10} = n² · n_e · 1024` (the paper's substitution,
    l.751).  The `g_pad ∝ lg n` scaling is what makes the total deviation `n`-independent. -/
def perAddDeviation (n n_e : ℚ) : ℚ := n / (1024 * (n ^ 2 * n_e * 1024))

/-- Total deviation (main.tex eq. l.746–755) = `LookupAdditionCount · perAddDeviation`
    (subadditivity, Gidney Thm 2.10). -/
def totalDeviation (n n_e : ℚ) : ℚ := lookupAdditionCount n n_e * perAddDeviation n n_e

/-- **The total approximation deviation is a CONSTANT `41/536870912 ≈ 7.64·10⁻⁸`,
    independent of `n` and `n_e`** — the `n²·n_e` factors cancel.  This verifies the paper's
    `TotalDeviation ≈ 10⁻⁷` (main.tex:753): the padding `g_pad ∝ lg n` is engineered exactly
    so the approximation error does NOT grow with the problem size.  (Honest note: this is
    the precise reason the resource counts carry the `+lg n` terms — the per-shot `lg n`
    overhead is the price of keeping the fidelity, hence the shot count, constant in `n`.) -/
theorem totalDeviation_eq_const (n n_e : ℚ) (hn : n ≠ 0) (hne : n_e ≠ 0) :
    totalDeviation n n_e = 41 / 536870912 := by
  unfold totalDeviation lookupAdditionCount perAddDeviation
  field_simp
  ring

/-- The total deviation is `≤ 10⁻⁷`, matching the paper's reported figure. -/
theorem totalDeviation_le (n n_e : ℚ) (hn : n ≠ 0) (hne : n_e ≠ 0) :
    totalDeviation n n_e ≤ 1 / 10000000 := by
  rw [totalDeviation_eq_const n n_e hn hne]; norm_num

end FormalRV.Shor.WindowedCostModel
