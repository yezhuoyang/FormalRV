/-
  Audit · Pinnacle · LAYER 4 — THE GB qLDPC CODE
  ============================================================================
  Pinnacle's processing units, magic engines, and memory are all built from
  generalised-bicycle (GB) qLDPC codes (Webster et al. 2026, "The Pinnacle
  Architecture", arXiv:2602.11457).  This is Pinnacle's REAL verified strength:
  the GB-code-PARAMETER framework — a representative GB code CONSTRUCTED, with
  its logical count `k` DERIVED from the constructed parity matrices (not
  asserted), reusing the project's shared `bivariateBicycle` / `CSSCode` /
  GF(2)-`rank` / `derivedK` machinery (it REDEFINES NOTHING).

  THE ARCHITECTURE (paper §II):
    • PROCESSING UNIT — a bridged GB qLDPC code block + an ancillary
      measurement-gadget system; performs an arbitrary logical Pauli-product
      measurement on its logical qubits each logical cycle (Pauli-based comp.).
    • MAGIC ENGINE — a GB code block + magic-injection ancillas; delivers one
      high-fidelity |C̄CZ̄⟩ per processing unit per cycle.
    • MEMORY (optional) — low-overhead GB code-block storage, accessed via ports.
  Headline: RSA-2048 in < 100 000 physical qubits (p=1e-3, 1 µs cycle, 10 µs
  reaction), using a factoring algorithm based on Gidney's.

  What this layer VERIFIES:
    • the Pinnacle codes are GB codes — the SAME family as the [[72,12,6]]
      gross-code instance below; we CONSTRUCT it and DERIVE k = 12 from the
      parity matrices (k = n − rank H_X − rank H_Z), not hardcoded.
    • the paper's RSA-2048 instance is recorded as the GB code ⟦510,16,24⟧
      (paper main.tex line 502: ⟦510,16,24⟧, n_cb = 2n = 1020, n_g = 99, n_b = 51;
      the processing-block footprint is n_pb = n_cb + 4n_g + 4n_b = 1620, recorded
      separately as `pinnacle_n_pb` — it is NOT the code's n).

  ⬜ RECORDED / GAP: the RSA-scale ⟦510,16,24⟧ parity matrices are stubbed
  `[]` — deriving k at 510 columns needs the GB homological formula (brute
  rank infeasible, exactly as for lp_20 in cain-xu).  See README STILL UNSOLVED.

  This file also holds the full Pinnacle parametric tuple `pinnacle_instance`
  (Shor × QECCode × hardware), since it bundles the L1 algorithm, this L4 code,
  and the hardware parameters.
-/
import FormalRV.Framework.L4_QECCode
import FormalRV.QEC.FrontendAlgebraic
import FormalRV.QEC.CodeDimension   -- general helper `derivedK`
import FormalRV.Audit.Pinnacle.Hardware
import FormalRV.Audit.Pinnacle.L1_Algorithm
import FormalRV.Verifier

namespace FormalRV.Audit.Pinnacle

open FormalRV.Framework FormalRV.Qualtran
open FormalRV.QEC.Algebraic
open FormalRV.QEC   -- brings the general `derivedK`

/-! ## The Pinnacle GB-code family — k DERIVED from constructed matrices (➗)

    A representative generalised-bicycle code of the Pinnacle family: the
    `[[72,12,6]]` "gross-code"-family bivariate-bicycle code
    (`a = x³ + y + y²`, `b = y³ + x + x²`, over `ℓ = m = 6`).  The same
    construction (`bivariateBicycle`) scales to the paper's RSA instance. -/
def pinnacle_gb_72 : FormalRV.QEC.CSSCode :=
  bivariateBicycle 6 6 [(3, 0), (0, 1), (0, 2)] [(0, 3), (1, 0), (2, 0)]

/-- `n = 72` physical qubits (= 2·ℓ·m = 2·6·6). -/
theorem pinnacle_gb_72_n : pinnacle_gb_72.n = 72 := by native_decide

/-- It is a valid CSS code (the two circulant blocks commute). -/
theorem pinnacle_gb_72_css : pinnacle_gb_72.css_condition = true := by native_decide

/-- **k = 12 DERIVED from the constructed parity matrices** (`k = n − rank H_X − rank H_Z`
    over GF(2)), not hardcoded — the GB-code-parameter framework the Pinnacle codes need.
    Certificate `native_decide` (kernel `decide` for the rank times out at 72 columns). -/
theorem pinnacle_gb_72_k_derived : derivedK pinnacle_gb_72 = 12 := by native_decide

/-! ## The paper's RSA-2048 instance — recorded (full GB matrices brute-rank-infeasible) -/

/-- Pinnacle's RSA-2048 generalised-bicycle CODE is `⟦510, 16, 24⟧` (paper main.tex Table at
line 502: `⟦510,16,24⟧`, ℓ=255, with `n_cb = 2n = 1020` code-block qubits, `n_g = 99`, `n_b = 51`).
The code's `n` is **510** — NOT 1620; 1620 is the PROCESSING-BLOCK footprint `n_pb = n_cb + 4n_g +
4n_b = 1020 + 396 + 204 = 1620` (an architecture constant, recorded as `pinnacle_n_pb` below), which
the resource formula `n = n_pb·⌈N/k⌉ + n_me` (paper line 751) uses — not the QECCode `n` field.
Parity matrices stubbed `[]` — deriving `k` at 510 columns needs the GB homological formula
(brute-rank-infeasible, exactly as lp_20 in cain-xu). -/
def pinnacle_code : QECCode :=
  { n := 510, k := 16, d := 24, hx := [], hz := [] }

/-- The PROCESSING-BLOCK footprint `n_pb = n_cb + 4·n_g + 4·n_b = 1020 + 4·99 + 4·51 = 1620`
    (paper line 502/476/521) — the per-block physical-qubit count that drives the resource formula.
    This is an ARCHITECTURE constant, NOT the GB code's `n` (= 510). -/
def pinnacle_n_pb : Nat := 1620

/-- The full parametric tuple for the Pinnacle instance. -/
def pinnacle_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (pinnacle_shor, pinnacle_code, pinnacle_hw)

/-- Pinnacle's RSA-2048 generalised-bicycle code is recorded as `⟦510,16,24⟧` (paper line 502);
    its `k`/`d` are paper-recorded (parity matrices stubbed — deriving `k` needs the GB homological
    formula, out of brute rank reach, exactly as for lp_20 in cain-xu).  The processing-block
    footprint `n_pb = 1620` is recorded separately (`pinnacle_n_pb`), NOT as the code's `n`. -/
theorem pinnacle_rsa_code_recorded :
    pinnacle_code.n = 510 ∧
    pinnacle_code.k = 16 ∧
    pinnacle_code.d = 24 ∧
    pinnacle_n_pb = 1620 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Smoke: paper-stated parameters read back. q_A = 3072; GB code `⟦510,16,24⟧`; n_pb = 1620;
hardware matches the 1e-3 / 1 µs baseline. -/
example : pinnacle_instance.1.q_A = 3072 := by rfl
example : pinnacle_instance.2.1.n = 510 ∧
          pinnacle_instance.2.1.k = 16 ∧
          pinnacle_instance.2.1.d = 24 := ⟨rfl, rfl, rfl⟩
example : pinnacle_instance.2.2.physical_error_thousandths = 1 := by rfl

end FormalRV.Audit.Pinnacle

#check @FormalRV.Audit.Pinnacle.pinnacle_gb_72_n          -- ➗ n = 72
#check @FormalRV.Audit.Pinnacle.pinnacle_gb_72_css        -- ➗ valid CSS
#check @FormalRV.Audit.Pinnacle.pinnacle_gb_72_k_derived  -- ➗ k = 12 DERIVED (native_decide)
#verify_clean FormalRV.Audit.Pinnacle.pinnacle_rsa_code_recorded  -- ✅ RSA instance ⟦510,16,24⟧, n_pb=1620
