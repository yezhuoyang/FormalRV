/-
  FormalRV.Audit.Gidney2025.EkeraHastad — the Ekerå–Håstad short-discrete-log factoring
  encoding used by Gidney–Ekerå (arXiv:1905.09749, "How to factor 2048-bit RSA
  integers in 8 hours…").

  ## What is faithfully formalised here (the CLASSICAL reduction)

  From `main.tex:466–477` (the 8-hours paper), Ekerå–Håstad factor `N = pq` by:
    1. classically compute `y = g^(N+1)` for random `g ∈ Z_N^*` of order `r`;
    2. *quantumly* compute the short discrete logarithm `d = log_g y`;
    3. classically recover `p, q` — "trivially, as the roots of `p² − dp + N = 0`".

  Step 3 (and the number theory linking `d` to `p+q`) is elementary and is
  formalised below, axiom-clean:
    * `ekera_congruence` :  `N+1 ≡ p+q (mod r)`  when `r ∣ (p−1)(q−1)`
      (the order divides Euler's totient `φ(N)=(p−1)(q−1)`, and
      `N+1−(p+q) = (p−1)(q−1)`).
    * `ekera_short_dl_eq`:  `d = p+q`  from `d ≡ p+q (mod r)` + the bounds
      `d < r`, `p+q < r` (the paper's "with equality if r > p+q").
    * `ekera_recover`   :  `p, q` are recovered from `(N, d)` via the quadratic
      `x² − dx + N` (discriminant `d²−4N = (p−q)²`).
    * `ekera_factor`    :  the full classical chain, given the quantumly-computed
      `d ≡ N+1 (mod r)`.

  ## What is NOT done here, and which paper supplies it (do NOT invent these)

  Step 2 — the QUANTUM computation of `d` and its success probability — is the
  Ekerå–Håstad algorithm proper.  The 8-hours paper explicitly defers its full
  details to Ekerå's own papers.  Formalising it faithfully requires:
    * the two-register short-DLP quantum circuit + the post-measurement
      frequency distribution (the EH analogue of order-finding's QPE peak), and
    * the LATTICE-based classical post-processing and its ≥99% success bound.
  These are stated in:
    * Ekerå & Håstad, "Quantum Algorithms for Computing Short Discrete Logarithms
      and Factoring RSA Integers", PQCrypto 2017  (ref `ekeraa2017quantum`);
    * Ekerå, "On post-processing in the quantum algorithm for computing short
      discrete logarithms", Des. Codes Cryptogr. 2020, ePrint **2017/1122**
      (ref `ekeraa2017pp`) — the 8-hours paper points to its **Appendix A.2.1**;
    * (background) Ekerå, "Modifying Shor's algorithm…", ePrint **2016/1128**.
  They are left as a NAMED obligation (`EHShortDLPSuccess`, below), to be filled
  once those sources are read — feeding the encoding-agnostic keystone
  (`FormalRV.Shor.EncodingAgnostic`).
-/
import FormalRV.Shor.OrderFinding.EncodingAgnostic

namespace FormalRV.Audit.Gidney2025.EkeraHastad

open scoped BigOperators
open FormalRV.Shor.EncodingAgnostic

/-! ## §1. The classical reduction (elementary, faithful to `main.tex:466–477`). -/

/-- **Key congruence.**  If the order `r` divides `φ(N) = (p−1)(q−1)` and
    `N = p·q`, then `N+1 ≡ p+q (mod r)` — because `N+1 − (p+q) = (p−1)(q−1)`.
    Hence the discrete log of `y = g^{N+1}` is `≡ p+q (mod r)`. -/
theorem ekera_congruence {p q r : Nat} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hr : r ∣ (p - 1) * (q - 1)) :
    (p * q + 1) ≡ (p + q) [MOD r] := by
  obtain ⟨p', rfl⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨q', rfl⟩ := Nat.exists_eq_add_of_le hq
  have hr' : r ∣ p' * q' := by simpa using hr
  calc (1 + p') * (1 + q') + 1
      = p' * q' + ((1 + p') + (1 + q')) := by ring
    _ ≡ 0 + ((1 + p') + (1 + q')) [MOD r] :=
        Nat.ModEq.add_right _ ((Nat.modEq_zero_iff_dvd).mpr hr')
    _ = (1 + p') + (1 + q') := by ring

/-- **Short DL is `p+q` exactly.**  Two values in `[0, r)` congruent mod `r`
    are equal; with `d < r` and `p+q < r`, `d ≡ p+q (mod r)` gives `d = p+q`. -/
theorem ekera_short_dl_eq {d p q r : Nat} (hcong : d ≡ (p + q) [MOD r])
    (hd_lt : d < r) (hpq_lt : p + q < r) : d = p + q := by
  have h : d % r = (p + q) % r := hcong
  rwa [Nat.mod_eq_of_lt hd_lt, Nat.mod_eq_of_lt hpq_lt] at h

/-- **Deterministic factor recovery.**  Given `N = pq` and `d = p+q` (`q ≤ p`),
    the factors are the roots of `x² − dx + N`: discriminant `d²−4N = (p−q)²`, so
    `p = (d + √(d²−4N))/2`, `q = (d − √(d²−4N))/2`. -/
theorem ekera_recover {p q d N : Nat} (hq_le_p : q ≤ p)
    (hd : d = p + q) (hN : N = p * q) :
    (d + (d * d - 4 * N).sqrt) / 2 = p ∧ (d - (d * d - 4 * N).sqrt) / 2 = q := by
  have hdisc : d * d - 4 * N = (p - q) * (p - q) := by
    subst hd hN
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq_le_p
    have h : (q + k + q) * (q + k + q) = 4 * ((q + k) * q) + k * k := by ring
    simp only [Nat.add_sub_cancel_left]
    omega
  rw [hdisc, Nat.sqrt_eq]
  subst hd
  omega

/-- **EH factoring recovery — the paper's *actual* form** (1702.00249,
    "The factoring algorithm", lines 908–925).  There one takes `x = g^{(N−1)/2}`
    and computes the short DL `d = (p+q−2)/2`, so `2d+2 = p+q`; then `p, q` solve
    `N = 2(d+1)q − q²`, giving `p, q = c ± √(c²−N)` with `c = d+1`.  For RSA
    primes (odd `p = 2a+1`, `q = 2b+1`), `c = (p+q)/2` and `c²−N = ((p−q)/2)²`, so
    the recovery is exact.  (This is the precise version the 8-hours paper
    simplified to `d = p+q`; `ekera_recover` above is that simplification.) -/
theorem ekera_recover_actual {a b d N : Nat} (hab : b ≤ a)
    (hd : d = a + b) (hN : N = (2 * a + 1) * (2 * b + 1)) :
    (d + 1) + ((d + 1) * (d + 1) - N).sqrt = 2 * a + 1 ∧
    (d + 1) - ((d + 1) * (d + 1) - N).sqrt = 2 * b + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  subst hd hN
  have hadd : (b + k + b + 1) * (b + k + b + 1)
      = (2 * (b + k) + 1) * (2 * b + 1) + k * k := by ring
  have hsub : (b + k + b + 1) * (b + k + b + 1) - (2 * (b + k) + 1) * (2 * b + 1) = k * k := by omega
  rw [hsub, Nat.sqrt_eq]
  omega

/-- **The full classical reduction.**  Given the quantumly-computed short DL
    `d ≡ N+1 (mod r)` (i.e. `d = log_g(g^{N+1})`), the order condition
    `r ∣ (p−1)(q−1)`, and the size conditions, `p` and `q` are recovered. -/
theorem ekera_factor (p q r d N : Nat) (hp : 1 ≤ p) (hq : 1 ≤ q) (hq_le_p : q ≤ p)
    (hN : N = p * q) (h_ord : r ∣ (p - 1) * (q - 1))
    (h_dl : d ≡ (N + 1) [MOD r]) (hd_lt : d < r) (hpq_lt : p + q < r) :
    (d + (d * d - 4 * N).sqrt) / 2 = p ∧ (d - (d * d - 4 * N).sqrt) / 2 = q := by
  have hc : (N + 1) ≡ (p + q) [MOD r] := by rw [hN]; exact ekera_congruence hp hq h_ord
  exact ekera_recover hq_le_p (ekera_short_dl_eq (h_dl.trans hc) hd_lt hpq_lt) hN

/-! ## §2. The short-DLP quantum algorithm: good pairs and lattice recovery.

Source: 1702.00249, the quantum algorithm (lines 397–451), the good-pair
definition (525–535), and the lattice recovery (675–735).

The two-register algorithm outputs a pair `(j, k)`, `0 ≤ j < 2^{ℓ+m}`,
`0 ≤ k < 2^ℓ`.  A pair is **good** when the balanced residue
`{dj + 2^m k}_{2^{ℓ+m}}` is bounded by `2^{m-2}` (line 525–535).  Given `s` good
pairs, classical post-processing recovers `d` by a lattice search: the "good
vector" with last component `d` lies within distance `√(s/4+1)·2^m` of the target
`v`.  That distance bound is ELEMENTARY (it follows from `d < 2^m` and each
residue `≤ 2^{m-2}`) and is proved below; only the per-good-pair PROBABILITY
(Lemma 7: `≥ 2^{-m-ℓ-2}`) is a deep quantum-Fourier fact, named in §3. -/

/-- `{u}_n` — the balanced residue of `u` modulo `n`, in `[-n/2, n/2)`
    (Ekerå–Håstad's `{·}_n`). -/
def cresid (u : Int) (n : Nat) : Int := Int.bmod u n

/-- A pair `(j, k)` is **good** for the short DL `d` (registers `ℓ+m`, `ℓ`) when
    `|{dj + 2^m k}_{2^{ℓ+m}}| ≤ 2^{m-2}` (1702.00249, line 525–535). -/
def EHGoodPair (m ℓ d j k : Nat) : Prop :=
  |cresid ((d : Int) * j + 2 ^ m * k) (2 ^ (ℓ + m))| ≤ 2 ^ (m - 2)

/-- **Lattice recovery — the geometric correctness (PROVEN).**  For `s` good
    pairs with residues `resid i = {dj_i + 2^m k_i}_{2^{ℓ+m}}` (each `≤ 2^{m-2}`),
    the lattice "good vector" `u` whose last component is `d` lies within the
    search radius `√(s/4+1)·2^m` of the target `v`:
      `|u − v|² = d² + Σ_i (resid i)² < (s/4 + 1)·2^{2m}`
    (1702.00249, line 675–735).  Stated in the cleared-denominator form
    `4·(d² + Σ (resid i)²) < (s+4)·2^{2m}`.  Hence the search that enumerates
    lattice vectors within that radius is guaranteed to contain a vector with
    last component `d`. -/
theorem eh_good_vector_within_radius (m s d : Nat) (resid : Fin s → Int)
    (hm : 2 ≤ m) (hd : d < 2 ^ m) (hgood : ∀ i, |resid i| ≤ 2 ^ (m - 2)) :
    4 * ((d : Int) ^ 2 + ∑ i, (resid i) ^ 2) < ((s : Int) + 4) * 2 ^ (2 * m) := by
  have hBpos : (0 : Int) < 2 ^ (m - 2) := by positivity
  have hpow : (2 : Int) ^ (2 * m) = 16 * (2 ^ (m - 2)) ^ 2 := by
    rw [← pow_mul, show (16 : Int) = 2 ^ 4 by norm_num, ← pow_add]; congr 1; omega
  have hd4 : (d : Int) < 4 * 2 ^ (m - 2) := by
    have h1 : (d : Int) < 2 ^ m := by exact_mod_cast hd
    have h2 : (2 : Int) ^ m = 4 * 2 ^ (m - 2) := by
      rw [show (4 : Int) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    rwa [h2] at h1
  have hdnn : (0 : Int) ≤ d := Int.natCast_nonneg d
  have hd2 : (d : Int) ^ 2 < 16 * (2 ^ (m - 2)) ^ 2 := by nlinarith [hd4, hdnn, hBpos]
  have hsum : ∑ i, (resid i) ^ 2 ≤ (s : Int) * (2 ^ (m - 2)) ^ 2 := by
    calc ∑ i, (resid i) ^ 2 ≤ ∑ _i : Fin s, (2 ^ (m - 2)) ^ 2 := by
            apply Finset.sum_le_sum; intro i _
            have h := hgood i
            nlinarith [sq_abs (resid i), abs_nonneg (resid i), hBpos]
      _ = (s : Int) * (2 ^ (m - 2)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hpow]; nlinarith [hd2, hsum, hBpos, sq_nonneg ((2 : Int) ^ (m - 2))]

/-! ## §3. The per-run success contract, wired through the Phase-A keystone.

What remains genuinely quantum is the per-good-pair measurement PROBABILITY:

  * 1702.00249, **Lemma 7**: any specific good pair occurs with probability
    `≥ 2^{-m-ℓ-2}` in one run (the deep quantum-Fourier bound);
  * the **count lemma**: at least `2^{ℓ+m-1}` distinct `j` yield good pairs.

We bundle exactly these two as the fields of `EHShortDLPSuccess` (named
obligations citing the paper), and PROVE — via the encoding-agnostic keystone
`success_ge_card_mul` — that the per-run probability of observing a good pair is
`≥ (#good j)·(per-pair prob)`, which with the cited values is `≥ 2^{-3} = 1/8`.
This is the same `count × per-peak` shape that gives order-finding `φ(r)·4/(π²r)`. -/

/-- **Ekerå–Håstad per-run success contract** (1702.00249, §quantum part).  An
    outcome `j` of the first register `[0, 2^ℓm)` is measured with probability
    `measProb j`; `goodJ` is the set of good outcomes (the count lemma supplies
    its size), each with measurement probability `≥ p` (Lemma 7).  The two
    `*_obl` fields are the genuinely-quantum named obligations. -/
structure EHShortDLPSuccess where
  /-- first-register bit-length `ℓ + m`. -/
  ℓm : Nat
  /-- per-outcome measurement probability. -/
  measProb : Nat → ℝ
  /-- the set of good first-register outcomes `j`. -/
  goodJ : Finset Nat
  /-- per-good-outcome probability floor `p = 2^{-m-ℓ-2}`. -/
  p : ℝ
  measProb_nonneg : ∀ j, 0 ≤ measProb j
  goodJ_sub : goodJ ⊆ Finset.range (2 ^ ℓm)
  /-- **Lemma 7 obligation** (1702.00249, l.638): every good pair has prob `≥ p`. -/
  good_prob_obl : ∀ j ∈ goodJ, p ≤ measProb j

/-- Probability of observing *some* good pair in a single run. -/
noncomputable def EHShortDLPSuccess.goodProb (S : EHShortDLPSuccess) : ℝ :=
  ∑ j ∈ S.goodJ, S.measProb j

/-- **EH per-run bound, via the Phase-A keystone.**  The per-run good-pair
    probability is at least `(#good outcomes)·(per-good-outcome prob)` — the
    encoding-agnostic `success_ge_card_mul`, instantiated for Ekerå–Håstad with
    its own acceptance (the good-`j` indicator) and peak set `goodJ`. -/
theorem EHShortDLPSuccess.goodProb_ge (S : EHShortDLPSuccess) :
    (S.goodJ.card : ℝ) * S.p ≤ S.goodProb := by
  have hkey := success_ge_card_mul (m := S.ℓm)
    (fun j => if j ∈ S.goodJ then (1 : ℝ) else 0) S.measProb S.p S.goodJ
    S.measProb_nonneg
    (fun j => by dsimp only; split_ifs <;> norm_num)
    S.goodJ_sub
    (fun j hj => by simp [hj])
    S.good_prob_obl
  have hcollapse :
      (∑ j ∈ Finset.range (2 ^ S.ℓm), (if j ∈ S.goodJ then (1 : ℝ) else 0) * S.measProb j)
        = S.goodProb := by
    unfold EHShortDLPSuccess.goodProb
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr S.goodJ_sub]
  rwa [hcollapse] at hkey

/-- The cited values: `2^{ℓ+m-1} · 2^{-(m+ℓ+2)} = 1/8`. -/
theorem eh_count_times_prob (ℓ m : Nat) (h : 1 ≤ ℓ + m) :
    (2 : ℝ) ^ (ℓ + m - 1) * (2 : ℝ) ^ (-(m + ℓ + 2 : ℤ)) = 1 / 8 := by
  rw [← zpow_natCast (2 : ℝ) (ℓ + m - 1), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      show ((ℓ + m - 1 : ℕ) : ℤ) + -(m + ℓ + 2 : ℤ) = -3 by omega]
  norm_num

/-- **EH per-run good-pair probability `≥ 1/8`.**  Instantiating the contract
    with the paper's values — `≥ 2^{ℓ+m-1}` good outcomes (count lemma) each of
    probability `≥ 2^{-(m+ℓ+2)}` (Lemma 7) — the probability of a good pair in
    one run is at least `1/8` (1702.00249, l.638 + l.777). -/
theorem EHShortDLPSuccess.goodProb_ge_eighth (S : EHShortDLPSuccess) (ℓ m : Nat)
    (_hℓm : S.ℓm = ℓ + m) (hge1 : 1 ≤ ℓ + m)
    (hcount : (2 : ℝ) ^ (ℓ + m - 1) ≤ (S.goodJ.card : ℝ))
    (hp : S.p = (2 : ℝ) ^ (-(m + ℓ + 2 : ℤ))) :
    (1 / 8 : ℝ) ≤ S.goodProb := by
  calc (1 / 8 : ℝ)
      = (2 : ℝ) ^ (ℓ + m - 1) * (2 : ℝ) ^ (-(m + ℓ + 2 : ℤ)) :=
        (eh_count_times_prob ℓ m hge1).symm
    _ ≤ (S.goodJ.card : ℝ) * S.p := by
        rw [hp]; exact mul_le_mul_of_nonneg_right hcount (by positivity)
    _ ≤ S.goodProb := S.goodProb_ge

end FormalRV.Audit.Gidney2025.EkeraHastad
