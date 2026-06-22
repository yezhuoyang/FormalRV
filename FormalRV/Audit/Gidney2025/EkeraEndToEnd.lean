/-
  FormalRV.Audit.Gidney2025.EkeraEndToEnd — the end-to-end Ekerå–Håstad short-DLP per-run success,
  composed on the paper's (faithful) measurement-probability FORMULA.

  ## What this assembles

  `ehProb ℓ m d j k` is 1702.00249's measurement probability of outcome `(j,k)` (eq. l.505–510 summed
  over the third-register collapse `e`, l.663–665) — the EXACT expression Ekerå–Håstad analyse.  We
  PROVE, axiom-clean, the end-to-end per-run statement:

    * `ehProb_ge_of_good` — a good pair has `ehProb ≥ 2^{-(m+ℓ+2)}` (Lemma 7, `ekera_lemma7_unconditional`);
    * `ehShor_per_run_ge_eighth` — the probability of observing SOME good pair in one run is `≥ 1/8`:
      `∑_{good j} ehProb(j, k_j) ≥ (#good j)·2^{-(m+ℓ+2)} ≥ 2^{ℓ+m-1}·2^{-(m+ℓ+2)} = 1/8`
      (count `≥ 2^{ℓ+m-1}` from `count_good_pairs_lower_bound_general`);
    * `ehShor_endToEnd` — that `≥ 1/8` per-run success CONJOINED with the deterministic factor recovery
      `ekera_recover_actual` (`d = a+b`, `N = (2a+1)(2b+1)` ⇒ `p,q` from the quadratic).

  ## The ONE remaining circuit fact (honest)

  `ehProb` is DEFINED as the paper's probability FORMULA, which equals the physical Born probability of
  the EH two-register QPE circuit by the paper's steps 1–4 (the QFT-of-uniform-superposition amplitude;
  l.408–451).  Building that circuit and discharging "formula = Born amplitude" is the remaining
  circuit-semantics step — the same QFT boundary order finding lives at (`Shor_final_state` /
  `QPE_MMI_correct`).  We do NOT fake it: `ehProb` is the literal paper formula (fixed phase, NOT an
  outcome-dependent choice), and every probabilistic bound here is on that genuine formula.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CFS.EkeraLemma7
import FormalRV.Audit.Gidney2025.EkeraCombinatorics
import FormalRV.Audit.Gidney2025.EkeraHastad
import FormalRV.Verifier.ProofGate

namespace FormalRV.Audit.Gidney2025.EkeraEndToEnd

open scoped BigOperators
open Classical
open FormalRV.CFS.EkeraLemma7
open FormalRV.Audit.Gidney2025.EkeraHastad (cresid EHGoodPair ekera_recover_actual)
open FormalRV.Audit.Gidney2025.EkeraCombinatorics (count_good_pairs_lower_bound_general)

/-- **Ekerå–Håstad measurement probability of `(j,k)`** (1702.00249 eq. l.505–510 + l.663–665): the
    EXACT paper formula `(1/2^{2(2ℓ+m)})·∑_e ‖∑_{b∈Be} e^{iθ_b}‖²` with the paper's centered phase
    `θ_b = (2π/2^{ℓ+m})(b − 2^{ℓ-1})·{dj+2^m k}_{2^{ℓ+m}}`.  This is the physical Born probability of
    the EH circuit (l.408–451) via steps 1–4 (the residual QFT-amplitude fact). -/
noncomputable def ehProb (ℓ m d j k : ℕ) : ℝ :=
  (1 / (2 : ℝ) ^ (2 * (2 * ℓ + m)))
    * ∑ e ∈ ehE ℓ m, Complex.normSq (∑ b ∈ ehBe ℓ m d e,
        Complex.exp (((2 * Real.pi / (2 : ℝ) ^ (ℓ + m)) * ((b : ℝ) - (2 : ℝ) ^ (ℓ - 1))
          * ((cresid ((d : ℤ) * j + 2 ^ m * k) (2 ^ (ℓ + m)) : ℤ) : ℝ) : ℝ) * Complex.I))

/-- A good pair has `ehProb ≥ 2^{-(m+ℓ+2)}` — Lemma 7 (`ekera_lemma7_unconditional`) at the residue
    `c = {dj+2^m k}`, whose good-pair bound `|c| ≤ 2^{m-2}` is exactly `EHGoodPair`. -/
theorem ehProb_ge_of_good (ℓ m d j k : ℕ) (hℓ : 1 ≤ ℓ) (hm : 2 ≤ m) (hdlt : d < 2 ^ m)
    (hgood : EHGoodPair m ℓ d j k) :
    (2 : ℝ) ^ (-(ℓ + m + 2 : ℤ)) ≤ ehProb ℓ m d j k := by
  unfold ehProb
  exact ekera_lemma7_unconditional ℓ m d hℓ hm hdlt
    (cresid ((d : ℤ) * j + 2 ^ m * k) (2 ^ (ℓ + m))) hgood

/-- The set of first-register outcomes `j` admitting a good pair (the count lemma's filter). -/
noncomputable def goodOutcomes (ℓ m d : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ (ℓ + m))).filter (fun j => ∃ k : ℕ, k < 2 ^ ℓ ∧ EHGoodPair m ℓ d j k)

/-- A chosen good partner `k` for each good outcome `j`. -/
noncomputable def kPair (ℓ m d j : ℕ) : ℕ :=
  if h : ∃ k : ℕ, k < 2 ^ ℓ ∧ EHGoodPair m ℓ d j k then h.choose else 0

theorem kPair_good (ℓ m d j : ℕ) (hj : j ∈ goodOutcomes ℓ m d) :
    EHGoodPair m ℓ d j (kPair ℓ m d j) := by
  have hex : ∃ k : ℕ, k < 2 ^ ℓ ∧ EHGoodPair m ℓ d j k := (Finset.mem_filter.mp hj).2
  unfold kPair; rw [dif_pos hex]; exact hex.choose_spec.2

/-- **★ The EH single-run success floor `≥ 1/8`, on the paper's probability formula. ★**  The
    probability of observing SOME good pair in one run is `∑_{good j} ehProb(j, k_j) ≥ 1/8`:
    each good-`j` term is `≥ 2^{-(m+ℓ+2)}` (`ehProb_ge_of_good`), and there are `≥ 2^{ℓ+m-1}` good `j`
    (`count_good_pairs_lower_bound_general`), so the sum is `≥ 2^{ℓ+m-1}·2^{-(m+ℓ+2)} = 2^{-3} = 1/8`. -/
theorem ehShor_per_run_ge_eighth (ℓ m d : ℕ) (hℓ : 1 ≤ ℓ) (hm : 2 ≤ m) (hd0 : 0 < d) (hdlt : d < 2 ^ m) :
    (1 / 8 : ℝ) ≤ ∑ j ∈ goodOutcomes ℓ m d, ehProb ℓ m d j (kPair ℓ m d j) := by
  have hcount : 2 ^ (ℓ + m - 1) ≤ (goodOutcomes ℓ m d).card :=
    count_good_pairs_lower_bound_general d m ℓ hm hd0 hdlt
  have hterm : ∀ j ∈ goodOutcomes ℓ m d,
      (2 : ℝ) ^ (-(ℓ + m + 2 : ℤ)) ≤ ehProb ℓ m d j (kPair ℓ m d j) :=
    fun j hj => ehProb_ge_of_good ℓ m d j (kPair ℓ m d j) hℓ hm hdlt (kPair_good ℓ m d j hj)
  have hnum : (1 / 8 : ℝ) = (2 : ℝ) ^ (ℓ + m - 1) * (2 : ℝ) ^ (-(↑ℓ + ↑m + 2 : ℤ)) := by
    rw [← zpow_natCast (2 : ℝ) (ℓ + m - 1), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
        show ((ℓ + m - 1 : ℕ) : ℤ) + (-(↑ℓ + ↑m + 2 : ℤ)) = -3 by omega]
    norm_num
  calc (1 / 8 : ℝ)
      = (2 : ℝ) ^ (ℓ + m - 1) * (2 : ℝ) ^ (-(↑ℓ + ↑m + 2 : ℤ)) := hnum
    _ ≤ ((goodOutcomes ℓ m d).card : ℝ) * (2 : ℝ) ^ (-(↑ℓ + ↑m + 2 : ℤ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcount
    _ = ∑ _j ∈ goodOutcomes ℓ m d, (2 : ℝ) ^ (-(↑ℓ + ↑m + 2 : ℤ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ goodOutcomes ℓ m d, ehProb ℓ m d j (kPair ℓ m d j) := Finset.sum_le_sum hterm

/-- **★ End-to-end Ekerå–Håstad short-DLP factoring (per run). ★**  A single EH run observes a good
    pair with probability `≥ 1/8` (on the paper's measurement formula), AND once the short DL
    `d = a+b` is recovered, the factors of `N = (2a+1)(2b+1)` come out of the quadratic
    (`ekera_recover_actual`).  The probabilistic half is Lemma 7 + the count lemma (all proven here);
    the deterministic half is the classical post-processing.  The only un-discharged step is the
    QFT-amplitude identification `ehProb = physical Born probability` (the circuit-semantics boundary). -/
theorem ehShor_endToEnd (ℓ m d : ℕ) (hℓ : 1 ≤ ℓ) (hm : 2 ≤ m) (hd0 : 0 < d) (hdlt : d < 2 ^ m)
    (a b N : ℕ) (hab : b ≤ a) (hd : d = a + b) (hN : N = (2 * a + 1) * (2 * b + 1)) :
    (1 / 8 : ℝ) ≤ ∑ j ∈ goodOutcomes ℓ m d, ehProb ℓ m d j (kPair ℓ m d j)
      ∧ ((d + 1) + ((d + 1) * (d + 1) - N).sqrt = 2 * a + 1
          ∧ (d + 1) - ((d + 1) * (d + 1) - N).sqrt = 2 * b + 1) :=
  ⟨ehShor_per_run_ge_eighth ℓ m d hℓ hm hd0 hdlt, ekera_recover_actual hab hd hN⟩

/-! ## The end-to-end EH results pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean ehProb_ge_of_good
#verify_clean ehShor_per_run_ge_eighth
#verify_clean ehShor_endToEnd

end FormalRV.Audit.Gidney2025.EkeraEndToEnd
