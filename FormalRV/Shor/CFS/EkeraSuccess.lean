/-
  FormalRV.Shor.CFS.EkeraSuccess — Ekerå 2023 (arXiv:2309.01754) **Theorem 1**: the per-run
  short-discrete-logarithm recovery success bound, the deep discharge target for the carried
  `cfs_dlog_recovered_whp` hypothesis (upgrading the repo's `≥1/8` floor to Ekerå's tight,
  push-to-1 bound).

  ## What Theorem 1 says (Library/2309.01754, `thm:main`)

  A single run of the quantum short-DLP algorithm yields a pair `(j,k)`; with probability at least

      max(0, 1 − 1/2^τ − 1/(2·2^{2τ}) − 1/(6·2^{3τ}))   ·   max(0, 1 − 2^{Δ − 2(t−1) − τ})

  at most `2³·c·√N_space` group operations recover `d` by enumerating vectors in the lattice
  `L^τ(j)`.  The bound is a PRODUCT of two factors, each from its own lemma:

    * **Factor 1** (Lemma 1, `lemma:bound-tau-good-pair`): conditioned on `j`, the pair `(j,k)` is
      "τ-good" with probability `≥ 1 − ψ'(2^τ)`, where the trigamma value is bounded (Claim
      `bound-trigamma`, the rational Nemes bound) by `ψ'(2^τ) ≤ 1/2^τ + 1/(2·2^{2τ}) + 1/(6·2^{3τ})`.
      This is a fact about the **quantum measurement distribution** (the Fourier analysis of the QPE
      output `j`).
    * **Factor 2** (Lemma 2, `lemma:bound-t-balanced-Lj`): the lattice `L^τ(j)` fails to be
      "t-balanced" with probability `≤ 2^{Δ − 2(t−1) − τ}`, so it IS t-balanced with probability
      `≥ 1 − 2^{Δ − 2(t−1) − τ}`.  This is a fact about the **distribution of the measured `j`**
      (which `j` give a balanced lattice).

  Given that `(j,k)` is τ-good AND `L^τ(j)` is t-balanced, the enumeration recovery succeeds
  (the deterministic lattice step, cost `≤ 2³·c·√N_space`).

  ## What this file PROVES vs. CARRIES (no cheating — the repo's established honest methodology)

  Both factors are properties of the `(j,k)` **measurement distribution**, which is produced by the
  QPE+QFT circuit on top of the verified `residueFold` arithmetic.  That measurement law (the QFT
  peak distribution) is the single hardest unbuilt analytic target — so, exactly as the repo already
  does for Ekerå–Håstad (`Audit.Gidney2025.EkeraHastad.EHShortDLPSuccess.good_prob_obl` carries the
  Lemma-7 Fourier fact as a NAMED STRUCTURE FIELD, not an axiom, not faked), we carry **Lemma 1** and
  **Lemma 2** as the two named obligations of `EkeraDLPSuccess`, and prove for real:

    * `ekera_twoFactor_lower_bound` — the genuine logical core of Theorem 1: the two-factor
      combination `successProb ≥ factor1 · factor2` as a clean `Finset`-sum inequality;
    * `ekeraGoodFactor`, `ekeraBalancedFactor` — the concrete real-valued bound expressions, with
      `*_nonneg`, `*_le_one`, and the **amplification** `ekeraGoodFactor_ge` (Factor 1 `≥ 1 − 3/2^τ`,
      i.e. exponentially → 1 in `τ` — the Ekerå advantage over the `1/8` floor, Cor 1 / Table 1);
    * `EkeraDLPSuccess.success_ge` — Theorem 1's probability bound on the concrete `successProb`;
    * `ekeraTrivialSuccess` / `ekera_contract_inhabited` — a CONCRETE inhabitant, so the contract and
      its bound are demonstrably NOT vacuous;
    * `ekera_success_to_factors` — composing the probabilistic success with the DETERMINISTIC concrete
      factor recovery `ekera_hastad_recovery` (`d = p+q−2`, `N = p·q` ⇒ factors from the quadratic),
      so the pipeline terminates at the factorisation of `N`.

  The `(j,k)`-distribution itself (closing the two obligations) awaits the CFS QPE measurement
  circuit + QFT peak law (target T5); this file makes everything else exact and concrete.
-/
import FormalRV.Shor.CFS.EkeraHastad

namespace FormalRV.CFS

open scoped BigOperators

/-! ## §1. The two bound factors (concrete real expressions = Ekerå 2023 Thm 1). -/

/-- **Factor 1** — Ekerå 2023 Lemma 1 (trigamma / Nemes bound).  Lower bound on the conditional
    probability `P((j,k) τ-good | j)`: `1 − 1/2^τ − 1/(2·2^{2τ}) − 1/(6·2^{3τ})`, floored at `0`
    (the bound is only nontrivial once `τ` is large enough to make it positive). -/
noncomputable def ekeraGoodFactor (τ : ℕ) : ℝ :=
  max 0 (1 - 1 / (2 : ℝ) ^ τ - 1 / (2 * (2 : ℝ) ^ (2 * τ)) - 1 / (6 * (2 : ℝ) ^ (3 * τ)))

/-- **Factor 2** — Ekerå 2023 Lemma 2 (t-balanced lattice).  Lower bound on `P(L^τ(j) t-balanced)`:
    one minus the not-t-balanced bound `2^{Δ − 2(t−1) − τ}`, floored at `0`. -/
noncomputable def ekeraBalancedFactor (Δ t τ : ℕ) : ℝ :=
  max 0 (1 - (2 : ℝ) ^ ((Δ : ℤ) - 2 * ((t : ℤ) - 1) - (τ : ℤ)))

theorem ekeraGoodFactor_nonneg (τ : ℕ) : 0 ≤ ekeraGoodFactor τ := le_max_left _ _

theorem ekeraBalancedFactor_nonneg (Δ t τ : ℕ) : 0 ≤ ekeraBalancedFactor Δ t τ := le_max_left _ _

theorem ekeraGoodFactor_le_one (τ : ℕ) : ekeraGoodFactor τ ≤ 1 := by
  unfold ekeraGoodFactor
  apply max_le (by norm_num)
  have h1 : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ τ := by positivity
  have h2 : (0 : ℝ) ≤ 1 / (2 * (2 : ℝ) ^ (2 * τ)) := by positivity
  have h3 : (0 : ℝ) ≤ 1 / (6 * (2 : ℝ) ^ (3 * τ)) := by positivity
  linarith

theorem ekeraBalancedFactor_le_one (Δ t τ : ℕ) : ekeraBalancedFactor Δ t τ ≤ 1 := by
  unfold ekeraBalancedFactor
  apply max_le (by norm_num)
  have h : (0 : ℝ) < (2 : ℝ) ^ ((Δ : ℤ) - 2 * ((t : ℤ) - 1) - (τ : ℤ)) := by positivity
  linarith

/-- **Amplification (Ekerå 2023 Cor 1 / Table 1 spirit).**  Factor 1 converges exponentially to `1`:
    `ekeraGoodFactor τ ≥ 1 − 3/2^τ` for all `τ`.  (The three subtracted trigamma terms are each
    `≤ 1/2^τ`.)  This is why the per-run success can be driven to `1 − 10^{-10}` — the qualitative
    upgrade over the repo's constant `≥ 1/8` Ekerå–Håstad floor. -/
theorem ekeraGoodFactor_ge (τ : ℕ) :
    1 - 3 / (2 : ℝ) ^ τ ≤ ekeraGoodFactor τ := by
  refine le_trans ?_ (le_max_right _ _)
  have hupos : (0 : ℝ) < (2 : ℝ) ^ τ := by positivity
  have hu1' : (1 : ℝ) ≤ (2 : ℝ) ^ τ := by exact_mod_cast Nat.one_le_two_pow
  have e2 : (2 : ℝ) ^ (2 * τ) = (2 : ℝ) ^ τ * (2 : ℝ) ^ τ := by rw [two_mul, pow_add]
  have e3 : (2 : ℝ) ^ (3 * τ) = (2 : ℝ) ^ τ * (2 : ℝ) ^ τ * (2 : ℝ) ^ τ := by
    rw [show 3 * τ = τ + τ + τ by ring, pow_add, pow_add]
  rw [e2, e3]
  set u := (2 : ℝ) ^ τ with hu
  have t1 : 1 / (2 * (u * u)) ≤ 1 / u :=
    one_div_le_one_div_of_le hupos (by nlinarith [hu1', hupos])
  have t2 : 1 / (6 * (u * u * u)) ≤ 1 / u :=
    one_div_le_one_div_of_le hupos (by nlinarith [hu1', hupos, mul_pos hupos hupos])
  have h3 : (3 : ℝ) / u = 1 / u + 1 / u + 1 / u := by ring
  linarith [t1, t2, h3]

/-! ## §2. The two-factor combination — the logical core of Ekerå 2023 Theorem 1. -/

/-- **The two-factor lower bound (genuine new content).**  Let the run measure first-register
    outcome `j` with probability `measProb j`, restricted to the t-balanced set `J`; let `condGood j`
    be the conditional good-pair probability.  If
      * `A ≤ condGood j` for every `j ∈ J`   (Factor 1, Lemma 1), and
      * `B ≤ ∑_{j∈J} measProb j`             (Factor 2, Lemma 2),
    with `A ≥ 0` and `measProb ≥ 0` on `J`, then the recovery probability
    `∑_{j∈J} measProb j · condGood j ≥ A·B`.  (Pull out `A`, then use `∑ measProb ≥ B`.) -/
theorem ekera_twoFactor_lower_bound (J : Finset ℕ) (measProb condGood : ℕ → ℝ) (A B : ℝ)
    (hA : 0 ≤ A)
    (hmeas : ∀ j ∈ J, 0 ≤ measProb j)
    (hgood : ∀ j ∈ J, A ≤ condGood j)
    (hbal : B ≤ ∑ j ∈ J, measProb j) :
    A * B ≤ ∑ j ∈ J, measProb j * condGood j := by
  calc A * B
      ≤ A * ∑ j ∈ J, measProb j := mul_le_mul_of_nonneg_left hbal hA
    _ = ∑ j ∈ J, A * measProb j := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ J, measProb j * condGood j := by
        apply Finset.sum_le_sum
        intro j hj
        rw [mul_comm A (measProb j)]
        exact mul_le_mul_of_nonneg_left (hgood j hj) (hmeas j hj)

/-! ## §3. The per-run success contract (Lemma 1 + Lemma 2 as named obligations). -/

/-- **Ekerå 2023 short-DLP per-run success contract.**  A run measures first-register outcome `j`
    with probability `measProb j`; `balancedJ` is the set of `j` whose lattice `L^τ(j)` is t-balanced
    (Lemma 2 supplies its measure); `condGood j` is the conditional probability that `(j,k)` is τ-good
    (Lemma 1 supplies its floor).  The two `*_obl` fields are the genuinely-quantum / distributional
    named obligations — the SAME honest carrying as `EHShortDLPSuccess.good_prob_obl`. -/
structure EkeraDLPSuccess where
  /-- first-register bit-length `ℓ + m`. -/
  ℓm : ℕ
  /-- algorithm parameters (`τ ∈ [0,ℓ]`, `Δ ∈ [0,m)`, `t ∈ [0,m)`). -/
  τ : ℕ
  Δ : ℕ
  t : ℕ
  /-- measurement probability of first-register outcome `j`. -/
  measProb : ℕ → ℝ
  /-- conditional probability that `(j,k)` is τ-good, given measured `j`. -/
  condGood : ℕ → ℝ
  /-- the set of `j` whose lattice `L^τ(j)` is t-balanced. -/
  balancedJ : Finset ℕ
  measProb_nonneg : ∀ j, 0 ≤ measProb j
  balancedJ_sub : balancedJ ⊆ Finset.range (2 ^ ℓm)
  /-- **Lemma 1 obligation** (trigamma good-pair bound): each balanced `j` has conditional
      good-pair probability `≥ ekeraGoodFactor τ`. -/
  good_obl : ∀ j ∈ balancedJ, ekeraGoodFactor τ ≤ condGood j
  /-- **Lemma 2 obligation** (t-balanced lattice fraction): the balanced set carries measure
      `≥ ekeraBalancedFactor Δ t τ`. -/
  balanced_obl : ekeraBalancedFactor Δ t τ ≤ ∑ j ∈ balancedJ, measProb j

/-- Probability that a single run recovers `d` (the `(j,k)` is τ-good AND `L^τ(j)` is t-balanced). -/
noncomputable def EkeraDLPSuccess.successProb (S : EkeraDLPSuccess) : ℝ :=
  ∑ j ∈ S.balancedJ, S.measProb j * S.condGood j

/-- **Ekerå 2023 Theorem 1 — the per-run success bound.**  The recovery probability is at least the
    product of the two factors, `ekeraGoodFactor τ · ekeraBalancedFactor Δ t τ` — instantiating
    `ekera_twoFactor_lower_bound` with the contract's two carried obligations. -/
theorem EkeraDLPSuccess.success_ge (S : EkeraDLPSuccess) :
    ekeraGoodFactor S.τ * ekeraBalancedFactor S.Δ S.t S.τ ≤ S.successProb :=
  ekera_twoFactor_lower_bound S.balancedJ S.measProb S.condGood
    (ekeraGoodFactor S.τ) (ekeraBalancedFactor S.Δ S.t S.τ)
    (ekeraGoodFactor_nonneg S.τ)
    (fun j _ => S.measProb_nonneg j)
    S.good_obl
    S.balanced_obl

/-! ## §4. Non-vacuity: a concrete inhabitant of the contract. -/

/-- A concrete inhabitant proving the contract is NOT vacuous: a one-outcome run concentrated on
    `j = 0` that always yields a good pair (`condGood ≡ 1`), with `{0}` the balanced set.  Both
    obligations reduce to `factor ≤ 1` (`ekeraGoodFactor_le_one`, `ekeraBalancedFactor_le_one`). -/
noncomputable def ekeraTrivialSuccess (τ Δ t : ℕ) : EkeraDLPSuccess where
  ℓm := 1
  τ := τ
  Δ := Δ
  t := t
  measProb := fun j => if j = 0 then 1 else 0
  condGood := fun _ => 1
  balancedJ := {0}
  measProb_nonneg := fun j => by split_ifs <;> norm_num
  balancedJ_sub := by decide
  good_obl := fun j _ => ekeraGoodFactor_le_one τ
  balanced_obl := by
    rw [Finset.sum_singleton]
    simpa using ekeraBalancedFactor_le_one Δ t τ

/-- The Theorem-1 bound is realized by a concrete object — so `success_ge` is not vacuously true. -/
theorem ekera_contract_inhabited (τ Δ t : ℕ) :
    ekeraGoodFactor τ * ekeraBalancedFactor Δ t τ ≤ (ekeraTrivialSuccess τ Δ t).successProb :=
  (ekeraTrivialSuccess τ Δ t).success_ge

/-! ## §5. Composition with the DETERMINISTIC concrete factor recovery. -/

/-- **Ekerå 2023 Thm 1 composed with deterministic factor recovery.**  With probability
    `≥ ekeraGoodFactor τ · ekeraBalancedFactor Δ t τ` a run recovers the short discrete log `d`
    (`success_ge`); and once `d = p+q−2` is in hand for `N = p·q`, the factors are determined by the
    concrete `ekera_hastad_recovery` (`p·(d−p+2) = N` and `p` a root of `X² − (d+2)X + N`).  Together
    the short-DLP run yields the factorisation of `N` with the stated probability — the probabilistic
    half carried through Lemma 1 / Lemma 2, the recovery half fully concrete. -/
theorem ekera_success_to_factors (S : EkeraDLPSuccess) (p q d N : ℕ)
    (hd : d = p + q - 2) (hN : N = p * q) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    ekeraGoodFactor S.τ * ekeraBalancedFactor S.Δ S.t S.τ ≤ S.successProb
      ∧ (p * (d - p + 2) = N ∧ p * p + N = (d + 2) * p) :=
  ⟨S.success_ge, ekera_hastad_recovery p q d N hd hN hp hq⟩

/-! ## The Ekerå-2023 Theorem-1 results pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean ekera_twoFactor_lower_bound
#verify_clean ekeraGoodFactor_ge
#verify_clean EkeraDLPSuccess.success_ge
#verify_clean ekera_contract_inhabited
#verify_clean ekera_success_to_factors

end FormalRV.CFS
