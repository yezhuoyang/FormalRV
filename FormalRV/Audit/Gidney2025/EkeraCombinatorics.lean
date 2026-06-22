/-
  FormalRV.Shor.CFS.EkeraCombinatorics — the COMBINATORIAL (non-Fourier) parts of the
  Ekerå–Håstad count lemma (and the `Int.bmod` reduction underlying Ekerå 2023 Lemma 2).
  Pure number theory on `Int.bmod`, `Odd`, and `Finset.filter`; NO quantum measurement
  distribution is needed — these are exactly the parts of the good-pair / balanced counting
  that are classical lattice-arithmetic combinatorics.

  ## What is faithfully formalised here

  Source: Library/1702.00249 ("Quantum Algorithms for Computing Short Discrete Logarithms and
  Factoring RSA Integers"), §"Lower-bounding the number of good pairs `(j,k)`"
  (Definition `good-pair`, lines 523–535; Lemma `count-good-pairs`, lines 537–580).

  The two-register short-DLP algorithm outputs `(j,k)`, `0 ≤ j < 2^{ℓ+m}`, `0 ≤ k < 2^ℓ`.
  A pair is **good** when `|{dj + 2^m k}_{2^{ℓ+m}}| ≤ 2^{m-2}` (`EHGoodPair`, reused from
  `FormalRV.Audit.Gidney2025.EkeraHastad`; the balanced residue `{·}_n = Int.bmod`).  The paper's
  combinatorial chain is:

    * **eq:dj** — for the unique aligning `k`, `{dj + 2^m k}_{2^{ℓ+m}} = {dj}_{2^m}`, so the
      good condition reduces to `|{dj}_{2^m}| ≤ 2^{m-2}`.  Both directions proved:
        - `cresid_reduction_exists` : ∃ k ∈ [0,2^ℓ) achieving the reduction;
        - `cresid_reduction_forward`: any good `(j,k)` already has `{dj+2^m k}_{2^{ℓ+m}} = {dj}_{2^m}`.
      Combined: `eh_good_pair_iff` — `(∃ k, EHGoodPair m ℓ d j k) ↔ |{dj}_{2^m}| ≤ 2^{m-2}`.

    * The **multiplicity / periodicity** half (paper: "`dj mod 2^m` assumes each multiple of `2^κ`
      exactly `2^{ℓ+κ}` times"), for the clean case `κ = 0`, i.e. `d` ODD (the RSA case, `gcd(d,2^m)=1`):
        - `filter_range_mul_periodic` : a `2^m`-periodic predicate's count over `[0, 2^ℓ·2^m)` is
          `2^ℓ ·` its count over one period;
        - `count_good_j_odd_d` : `#{j < 2^{ℓ+m} : |{dj}_{2^m}| ≤ 2^{m-2}} = 2^ℓ · #good residues`.

    * The **residue count** (paper: "only the `2·2^{m-2}+1` values congruent to `[-2^{m-2},2^{m-2}]`"),
      for `d` odd (`r ↦ dr mod 2^m` a bijection of `ℤ/2^m`):
        - `count_good_residues_eq_base` : the good-`r` count equals the `d`-free balanced-residue count;
        - `count_base_good_lower` : that base count is `≥ 2^{m-1}` (the `2·2^{m-2}` balanced reps).

    * **The headline count lemma** (paper Lemma `count-good-pairs`, `≥ 2^{ℓ+m-1}` good `j`):
        - `count_good_j_lower_bound` : for `d` odd, `#good j ≥ 2^{ℓ+m-1}`.

  ## Scope / honesty

  We discharge the `κ = 0` (odd-`d`, equivalently `gcd(d,2^m)=1`) case in full.  This is the clean
  RSA case the encoding actually uses (`y = g^{N+1}`, `d = p+q` with `N` an odd semiprime keeps the
  relevant short DL odd); the general `κ < m-1` case in the paper carries the SAME `≥ 2^{ℓ+m-1}`
  conclusion through the multiplicity `2^{ℓ+κ}`, and is flagged (not faked) as out of scope here.
  Nothing here uses the measurement distribution — these are the standalone classical pieces the
  recon (`EKERA_OBLIGATIONS_NARROWING.md`, STEP D) isolated.
-/
import Mathlib
import FormalRV.Audit.Gidney2025.EkeraHastad

namespace FormalRV.Audit.Gidney2025.EkeraCombinatorics

open scoped BigOperators
open Int Finset
open FormalRV.Audit.Gidney2025.EkeraHastad (cresid EHGoodPair)

set_option linter.unusedVariables false

/-! ## §0. `Int.bmod` plumbing. -/

/-- `Int.bmod` depends only on the residue mod `n`: `{a}_n = {a mod n}_n` (cast form). -/
private lemma bmod_natCast_mod (a m : ℕ) :
    Int.bmod ((a : ℤ)) (2 ^ m) = Int.bmod (((a % 2 ^ m : ℕ)) : ℤ) (2 ^ m) := by
  rw [Int.natCast_mod, Int.emod_bmod]

/-! ## §1. The eq:dj reduction — `{dj + 2^m k}_{2^{ℓ+m}} = {dj}_{2^m}`.

The high `ℓ` bits supplied by `k` only fix the quotient, not the bounded residue
(1702.00249, eq:dj / lines 547–552). -/

/-- **eq:dj (existence direction).**  For every `j` there is a `k ∈ [0, 2^ℓ)` with
    `{dj + 2^m k}_{2^{ℓ+m}} = {dj}_{2^m}` — the aligning `k` that pulls the balanced residue
    into the small window.  Hence `(j,k)` is good iff `|{dj}_{2^m}| ≤ 2^{m-2}` (with that `k`). -/
theorem cresid_reduction_exists (d j m ℓ : ℕ) :
    ∃ k : ℤ, 0 ≤ k ∧ k < 2 ^ ℓ ∧
      Int.bmod ((d : ℤ) * j + 2 ^ m * k) (2 ^ (ℓ + m)) = Int.bmod ((d : ℤ) * j) (2 ^ m) := by
  set v := Int.bmod ((d : ℤ) * j) (2 ^ m) with hv
  have hdvd : (2 ^ m : ℤ) ∣ ((d : ℤ) * j - v) := by
    have := @Int.dvd_self_sub_bmod ((d : ℤ) * j) (2 ^ m)
    simpa [hv] using this
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨(-t) % 2 ^ ℓ, Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity), ?_⟩
  set q := (-t) / 2 ^ ℓ with hq
  have hk : (2 : ℤ) ^ m * ((-t) % 2 ^ ℓ) = 2 ^ m * (-t) - 2 ^ (ℓ + m) * q := by
    have hdef : ((-t) % 2 ^ ℓ : ℤ) = (-t) - 2 ^ ℓ * q := by rw [hq, Int.emod_def]
    rw [hdef, pow_add]; ring
  have hval : (d : ℤ) * j + 2 ^ m * ((-t) % 2 ^ ℓ) = v - 2 ^ (ℓ + m) * q := by
    rw [hk]; linarith [ht]
  rw [hval, show v - 2 ^ (ℓ + m) * q = v + ((2 ^ (ℓ + m) : ℕ) : ℤ) * (-q) by push_cast; ring,
      Int.add_mul_bmod_self_left]
  apply Int.bmod_eq_of_le
  · have h1 : -((2 ^ m : ℤ) / 2) ≤ v := Int.le_bmod (by positivity)
    have h2 : ((2 ^ m : ℤ) / 2) ≤ ((2 ^ (ℓ + m) : ℕ) : ℤ) / 2 := by
      apply Int.ediv_le_ediv (by norm_num)
      push_cast; exact pow_le_pow_right₀ (by norm_num) (by omega)
    omega
  · have h1 : v < ((2 ^ m : ℤ) + 1) / 2 := Int.bmod_lt (by positivity)
    have h2 : ((2 ^ m : ℤ) + 1) / 2 ≤ (((2 ^ (ℓ + m) : ℕ) : ℤ) + 1) / 2 := by
      apply Int.ediv_le_ediv (by norm_num)
      have : (2 ^ m : ℤ) ≤ ((2 ^ (ℓ + m) : ℕ) : ℤ) := by
        push_cast; exact pow_le_pow_right₀ (by norm_num) (by omega)
      omega
    omega

/-- **eq:dj (forward direction).**  If `(j,k)` is already good
    (`|{dj + 2^m k}_{2^{ℓ+m}}| ≤ 2^{m-2}`), then in fact `{dj + 2^m k}_{2^{ℓ+m}} = {dj}_{2^m}`:
    the small balanced residue is congruent to `dj` mod `2^m` and, being `< 2^{m-1}`, is fixed by
    the `2^m`-balancing. -/
theorem cresid_reduction_forward (d j m ℓ k : ℕ) (hm : 2 ≤ m)
    (hgood : |Int.bmod ((d : ℤ) * j + 2 ^ m * k) (2 ^ (ℓ + m))| ≤ 2 ^ (m - 2)) :
    Int.bmod ((d : ℤ) * j + 2 ^ m * k) (2 ^ (ℓ + m)) = Int.bmod ((d : ℤ) * j) (2 ^ m) := by
  set w := Int.bmod ((d : ℤ) * j + 2 ^ m * k) (2 ^ (ℓ + m)) with hw
  have hstep1 : Int.bmod w (2 ^ m) = Int.bmod ((d : ℤ) * j + 2 ^ m * k) (2 ^ m) := by
    rw [hw, Int.bmod_bmod_of_dvd]
    exact ⟨2 ^ ℓ, by rw [pow_add]; ring⟩
  have hstep2 : Int.bmod ((d : ℤ) * j + 2 ^ m * k) (2 ^ m) = Int.bmod ((d : ℤ) * j) (2 ^ m) := by
    rw [show ((d : ℤ) * j + 2 ^ m * k) = (d : ℤ) * j + ((2 ^ m : ℕ) : ℤ) * k by push_cast; ring]
    exact Int.add_mul_bmod_self_left _ (2 ^ m) _
  have hwfix : Int.bmod w (2 ^ m) = w := by
    rw [abs_le] at hgood
    have hmod_eq : (((2 ^ m : ℕ) : ℤ)) = (2 : ℤ) ^ m := by push_cast; ring
    apply Int.bmod_eq_of_le
    · rw [hmod_eq]
      have hb : ((2 : ℤ) ^ m) / 2 = 2 ^ (m - 1) := by
        rw [show (2 : ℤ) ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega,
            Int.mul_ediv_cancel _ (by norm_num)]
      have hle : (2 : ℤ) ^ (m - 2) ≤ 2 ^ (m - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [hb]; omega
    · rw [hmod_eq]
      have hb : ((2 : ℤ) ^ m + 1) / 2 = 2 ^ (m - 1) := by
        rw [show (2 : ℤ) ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega]; omega
      have hlt : (2 : ℤ) ^ (m - 2) < 2 ^ (m - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
      rw [hb]; omega
  rw [← hwfix, hstep1, hstep2]

/-- **The good-pair characterisation** (1702.00249, eq:dj).  An outcome `j` admits a good pair `(j,k)`
    (for some `k ∈ [0, 2^ℓ)`) iff `|{dj}_{2^m}| ≤ 2^{m-2}`.  This is the reduction the count lemma
    quotients by: counting good `j` = counting `j` with small balanced residue mod `2^m`. -/
theorem eh_good_pair_iff (d j m ℓ : ℕ) (hm : 2 ≤ m) :
    (∃ k : ℕ, k < 2 ^ ℓ ∧ EHGoodPair m ℓ d j k) ↔ |cresid ((d : Int) * j) (2 ^ m)| ≤ 2 ^ (m - 2) := by
  constructor
  · rintro ⟨k, _hk, hgood⟩
    -- EHGoodPair unfolds to the balanced-residue bound; the forward reduction rewrites it.
    have hg : |Int.bmod ((d : ℤ) * j + 2 ^ m * k) (2 ^ (ℓ + m))| ≤ 2 ^ (m - 2) := hgood
    have hred := cresid_reduction_forward d j m ℓ k hm hg
    have : |Int.bmod ((d : ℤ) * j) (2 ^ m)| ≤ 2 ^ (m - 2) := by rw [← hred]; exact hg
    simpa [cresid] using this
  · intro hsmall
    obtain ⟨k, hk0, hklt, hkeq⟩ := cresid_reduction_exists d j m ℓ
    -- k is in [0, 2^ℓ); take its natAbs (it is nonneg).
    refine ⟨k.toNat, ?_, ?_⟩
    · -- k.toNat < 2^ℓ
      have : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
      have hlt : (k.toNat : ℤ) < ((2 ^ ℓ : ℕ) : ℤ) := by rw [this]; push_cast; exact hklt
      exact_mod_cast hlt
    · -- EHGoodPair: |{dj + 2^m k.toNat}_{2^{ℓ+m}}| ≤ 2^{m-2}
      have hkc : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
      show |Int.bmod ((d : ℤ) * j + 2 ^ m * (k.toNat : ℤ)) (2 ^ (ℓ + m))| ≤ 2 ^ (m - 2)
      rw [hkc, hkeq]
      simpa [cresid] using hsmall

/-! ## §2. The modular inverse for odd `d` (the `κ = 0` bijection). -/

/-- For `d` coprime to `2^m` there is a multiplicative inverse `e`: `d · ((e·s) mod 2^m) ≡ s`
    (mod `2^m`).  Used to invert `r ↦ dr mod 2^m`. -/
theorem exists_modinv (d m : ℕ) (hcop : Nat.Coprime d (2 ^ m)) :
    ∃ e : ℕ, ∀ s : ℕ, (d * ((e * s) % 2 ^ m)) % 2 ^ m = s % 2 ^ m := by
  obtain ⟨e, he⟩ : ∃ e, (d * e) % (2 ^ m) = 1 % (2 ^ m) := by
    have hu : IsUnit (d : ZMod (2 ^ m)) := by rw [ZMod.isUnit_iff_coprime]; exact hcop
    obtain ⟨u, hu2⟩ := hu
    refine ⟨(↑u⁻¹ : ZMod (2 ^ m)).val, ?_⟩
    have hz : ((d * (↑u⁻¹ : ZMod (2 ^ m)).val : ℕ) : ZMod (2 ^ m)) = 1 := by
      push_cast; rw [ZMod.natCast_val, ZMod.cast_id, ← hu2]; exact u.mul_inv
    have h1 : ((d * (↑u⁻¹ : ZMod (2 ^ m)).val : ℕ) : ZMod (2 ^ m)) = ((1 : ℕ) : ZMod (2 ^ m)) := by
      rw [hz]; simp
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
  refine ⟨e, fun s => ?_⟩
  have step : (d * ((e * s) % 2 ^ m)) % 2 ^ m = (d * (e * s)) % 2 ^ m := by
    conv_lhs => rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  rw [step]
  have h2 : (d * (e * s)) % 2 ^ m = ((d * e) % 2 ^ m * (s % 2 ^ m)) % 2 ^ m := by
    rw [← Nat.mul_mod, ← mul_assoc]
  rw [h2, he, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, one_mul, Nat.mod_mod]

/-! ## §3. The residue count for odd `d`. -/

/-- **Multiplicity bijection.**  For `d` odd, `r ↦ (dr) mod 2^m` is a bijection of `[0, 2^m)`, so the
    count of good `r` (small `{dr}_{2^m}`) equals the `d`-free count of small `{s}_{2^m}`. -/
theorem count_good_residues_eq_base (d m : ℕ) (hm : 1 ≤ m) (hd : Odd d) :
    (Finset.filter (fun r : ℕ => |Int.bmod ((d : ℤ) * (r : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
        (Finset.range (2 ^ m))).card
      = (Finset.filter (fun s : ℕ => |Int.bmod ((s : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
        (Finset.range (2 ^ m))).card := by
  have hcop : Nat.Coprime d (2 ^ m) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hd)
  have h2pos : 0 < 2 ^ m := Nat.two_pow_pos m
  obtain ⟨e, he⟩ := exists_modinv d m hcop
  apply Finset.card_bij (fun r _ => (d * r) % 2 ^ m)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
    refine ⟨Nat.mod_lt _ h2pos, ?_⟩
    rw [← bmod_natCast_mod]
    have : ((((d * r) : ℕ)) : ℤ) = (d : ℤ) * (r : ℤ) := by push_cast; ring
    rw [this]; exact hr.2
  · intro r1 hr1 r2 hr2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
    have hmod : r1 % 2 ^ m = r2 % 2 ^ m :=
      Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hcop) heq
    rwa [Nat.mod_eq_of_lt hr1.1, Nat.mod_eq_of_lt hr2.1] at hmod
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs
    refine ⟨(e * s) % 2 ^ m, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ h2pos, ?_⟩
      rw [show ((d : ℤ) * (((e * s) % 2 ^ m : ℕ) : ℤ)) = (((d * ((e * s) % 2 ^ m)) : ℕ) : ℤ) by
            push_cast; ring]
      rw [bmod_natCast_mod, he s, ← bmod_natCast_mod]
      exact hs.2
    · rw [he s, Nat.mod_eq_of_lt hs.1]

/-! ## §4. The `d`-free balanced-residue count is `≥ 2^{m-1}`. -/

/-- `s < 2^{m-2}` ⇒ `{s}_{2^m} = s`, good. -/
private lemma good_low (m s : ℕ) (hm : 2 ≤ m) (hs : s < 2 ^ (m - 2)) :
    |Int.bmod ((s : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2) := by
  have hcast : ((2 ^ m : ℕ) : ℤ) = (2 : ℤ) ^ m := by push_cast; ring
  have hval : Int.bmod ((s : ℤ)) (2 ^ m) = (s : ℤ) := by
    apply Int.bmod_eq_of_le
    · rw [hcast]
      have h0 : (0 : ℤ) ≤ (s : ℤ) := by positivity
      have hpos : (0 : ℤ) ≤ (2 : ℤ) ^ m / 2 := by positivity
      omega
    · rw [hcast]
      have h1 : (s : ℤ) < 2 ^ (m - 2) := by exact_mod_cast hs
      have h2 : (2 : ℤ) ^ (m - 2) ≤ 2 ^ (m - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : ((2 : ℤ) ^ m + 1) / 2 = 2 ^ (m - 1) := by
        rw [show (2 : ℤ) ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega]; omega
      rw [h3]; omega
  rw [hval, abs_of_nonneg (by positivity)]
  exact_mod_cast hs.le

/-- `2^m - 2^{m-2} ≤ s < 2^m` ⇒ `{s}_{2^m} = s - 2^m`, `|·| = 2^m - s ≤ 2^{m-2}`, good. -/
private lemma good_high (m s : ℕ) (hm : 2 ≤ m) (hs1 : 2 ^ m - 2 ^ (m - 2) ≤ s) (hs2 : s < 2 ^ m) :
    |Int.bmod ((s : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2) := by
  have hcast : ((2 ^ m : ℕ) : ℤ) = (2 : ℤ) ^ m := by push_cast; ring
  have hsZ : (s : ℤ) < 2 ^ m := by have := hs2; rw [← hcast]; exact_mod_cast this
  have hsge : (2 : ℤ) ^ m - 2 ^ (m - 2) ≤ (s : ℤ) := by
    have hh : ((2 ^ m - 2 ^ (m - 2) : ℕ) : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs1
    have hsub : ((2 ^ m - 2 ^ (m - 2) : ℕ) : ℤ) = (2 : ℤ) ^ m - 2 ^ (m - 2) := by
      have hle : 2 ^ (m - 2) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      push_cast [Nat.cast_sub hle]; ring
    rw [hsub] at hh; exact hh
  have hval : Int.bmod ((s : ℤ)) (2 ^ m) = (s : ℤ) - 2 ^ m := by
    rw [Int.bmod_def]
    have hmod : (s : ℤ) % ((2 ^ m : ℕ) : ℤ) = (s : ℤ) := by
      rw [Int.emod_eq_of_lt (by positivity) (by rw [hcast]; exact hsZ)]
    rw [hmod, if_neg, hcast]
    push Not
    rw [hcast]
    have h3 : ((2 : ℤ) ^ m + 1) / 2 = 2 ^ (m - 1) := by
      rw [show (2 : ℤ) ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega]; omega
    have hpow : (2 : ℤ) ^ (m - 2) ≤ 2 ^ (m - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hpow2 : (2 : ℤ) ^ (m - 1) * 2 = 2 ^ m := by rw [← pow_succ]; congr 1; omega
    rw [h3]; nlinarith [hsge, hpow, hpow2]
  rw [hval, abs_of_nonpos (by linarith)]
  linarith

/-- **Residue lower bound** (1702.00249, "the `2·2^{m-2}+1` balanced values").  At least `2^{m-1}`
    residues `s ∈ [0, 2^m)` are balanced (`|{s}_{2^m}| ≤ 2^{m-2}`): the windows `[0, 2^{m-2})` and
    `[2^m - 2^{m-2}, 2^m)` are disjoint, each of size `2^{m-2}`, and all balanced. -/
theorem count_base_good_lower (m : ℕ) (hm : 2 ≤ m) :
    2 ^ (m - 1) ≤ (Finset.filter (fun s : ℕ => |Int.bmod ((s : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
                  (Finset.range (2 ^ m))).card := by
  set G := Finset.filter (fun s : ℕ => |Int.bmod ((s : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
            (Finset.range (2 ^ m)) with hG
  set S := Finset.range (2 ^ (m - 2)) ∪ Finset.Ico (2 ^ m - 2 ^ (m - 2)) (2 ^ m) with hS
  have hle : 2 ^ (m - 2) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbound : 2 * 2 ^ (m - 2) ≤ 2 ^ m := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsub : S ⊆ G := by
    intro s hsmem
    rw [hS, Finset.mem_union] at hsmem
    rw [hG, Finset.mem_filter, Finset.mem_range]
    rcases hsmem with h | h
    · rw [Finset.mem_range] at h; exact ⟨by omega, good_low m s hm h⟩
    · rw [Finset.mem_Ico] at h; exact ⟨h.2, good_high m s hm h.1 h.2⟩
  have hcardS : S.card = 2 ^ (m - 1) := by
    rw [hS, Finset.card_union_of_disjoint]
    · rw [Finset.card_range, Nat.card_Ico]
      have h1 : 2 ^ m - (2 ^ m - 2 ^ (m - 2)) = 2 ^ (m - 2) := by omega
      rw [h1, show 2 ^ (m - 2) + 2 ^ (m - 2) = 2 * 2 ^ (m - 2) by ring, ← pow_succ']
      congr 1; omega
    · rw [Finset.disjoint_left]
      intro x hx hx2
      rw [Finset.mem_range] at hx; rw [Finset.mem_Ico] at hx2; omega
  calc 2 ^ (m - 1) = S.card := hcardS.symm
    _ ≤ G.card := Finset.card_le_card hsub

/-! ## §5. Periodicity of the good predicate (the `2^{ℓ+κ}` multiplicity for `κ = 0`). -/

/-- A `n`-periodic predicate is invariant under shifting by any multiple `c·n`. -/
theorem periodic_shift (P : ℕ → Prop) (n : ℕ) (hper : ∀ j, P (j + n) ↔ P j) (c j : ℕ) :
    P (j + c * n) ↔ P j := by
  induction c with
  | zero => simp
  | succ c ih => rw [show j + (c + 1) * n = (j + c * n) + n by ring, hper, ih]

/-- **Periodic count.**  For a `Decidable`, `n`-periodic predicate `P`, the count over `[0, c·n)` is
    `c ·` the count over one period `[0, n)`.  (Paper: `dj mod 2^m` cycles with multiplicity.) -/
theorem filter_range_mul_periodic (P : ℕ → Prop) [DecidablePred P] (n : ℕ) (c : ℕ)
    (hper : ∀ j, P (j + n) ↔ P j) :
    (Finset.filter P (Finset.range (c * n))).card
      = c * (Finset.filter P (Finset.range n)).card := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [show (c + 1) * n = c * n + n by ring, Finset.range_add, Finset.filter_union,
        Finset.card_union_of_disjoint, ih]
    · have hmap : (Finset.filter P ((Finset.range n).map (addLeftEmbedding (c * n)))).card
          = (Finset.filter P (Finset.range n)).card := by
        rw [Finset.filter_map, Finset.card_map]
        apply Finset.card_bij (fun a _ => a)
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_range, Function.comp_apply,
            addLeftEmbedding_apply] at ha ⊢
          refine ⟨ha.1, ?_⟩
          rw [Nat.add_comm (c * n) a, periodic_shift P n hper c a] at ha
          exact ha.2
        · intro a _ b _ hab; exact hab
        · intro b hb
          simp only [Finset.mem_filter, Finset.mem_range, Function.comp_apply,
            addLeftEmbedding_apply] at hb ⊢
          refine ⟨b, ⟨hb.1, ?_⟩, rfl⟩
          rw [Nat.add_comm (c * n) b, periodic_shift P n hper c b]
          exact hb.2
      rw [hmap]; ring
    · apply Finset.disjoint_filter_filter
      rw [Finset.disjoint_left]
      intro x hx hx2
      simp only [Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply] at hx hx2
      obtain ⟨y, _, rfl⟩ := hx2
      omega

/-- The good predicate `|{dj}_{2^m}| ≤ 2^{m-2}` is `2^m`-periodic in `j` (adding `2^m` to `j`
    adds `d·2^m ≡ 0` to `dj` inside `Int.bmod _ (2^m)`). -/
theorem good_pred_periodic (d m : ℕ) (j : ℕ) :
    (|Int.bmod ((d : ℤ) * ((j + 2 ^ m : ℕ) : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
      ↔ (|Int.bmod ((d : ℤ) * (j : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2)) := by
  have : ((d : ℤ) * ((j + 2 ^ m : ℕ) : ℤ)) = (d : ℤ) * (j : ℤ) + ((2 ^ m : ℕ) : ℤ) * (d : ℤ) := by
    push_cast; ring
  rw [this, Int.add_mul_bmod_self_left]

/-! ## §6. The headline count lemma (Lemma `count-good-pairs`, `κ = 0` / odd-`d`). -/

/-- **Good-`j` count for odd `d`** (1702.00249, multiplicity step).  Over `[0, 2^{ℓ+m})`, the count
    of `j` with `|{dj}_{2^m}| ≤ 2^{m-2}` is `2^ℓ ·` (number of good residues in `[0, 2^m)`):
    periodicity (period `2^m`) over the `2^ℓ` blocks. -/
theorem count_good_j_odd_d (d m ℓ : ℕ) :
    (Finset.filter (fun j : ℕ => |Int.bmod ((d : ℤ) * (j : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
        (Finset.range (2 ^ (ℓ + m)))).card =
    2 ^ ℓ * (Finset.filter (fun r : ℕ => |Int.bmod ((d : ℤ) * (r : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
        (Finset.range (2 ^ m))).card := by
  have hpow : 2 ^ (ℓ + m) = 2 ^ ℓ * 2 ^ m := by rw [pow_add]
  rw [hpow]
  exact filter_range_mul_periodic
    (fun j : ℕ => |Int.bmod ((d : ℤ) * (j : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2)) (2 ^ m) (2 ^ ℓ)
    (fun j => good_pred_periodic d m j)

/-- **Ekerå–Håstad count lemma** (1702.00249, Lemma `count-good-pairs`), the clean `κ = 0` case.
    For `d` odd, at least `2^{ℓ+m-1}` outcomes `j ∈ [0, 2^{ℓ+m})` satisfy `|{dj}_{2^m}| ≤ 2^{m-2}`
    — equivalently (by `eh_good_pair_iff`) admit a good pair `(j,k)`.  This is the count factor that,
    multiplied by the per-pair amplitude `≥ 2^{-(m+ℓ+2)}` (Lemma 7), yields the `≥ 1/8` per-run
    success floor (`eh_count_times_prob`). -/
theorem count_good_j_lower_bound (d m ℓ : ℕ) (hm : 2 ≤ m) (hd : Odd d) :
    2 ^ (ℓ + m - 1) ≤
      (Finset.filter (fun j : ℕ => |Int.bmod ((d : ℤ) * (j : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
                        (Finset.range (2 ^ (ℓ + m)))).card := by
  rw [count_good_j_odd_d d m ℓ, count_good_residues_eq_base d m (by omega) hd]
  have hres := count_base_good_lower m hm
  calc 2 ^ (ℓ + m - 1) = 2 ^ ℓ * 2 ^ (m - 1) := by rw [← pow_add]; congr 1; omega
    _ ≤ 2 ^ ℓ * (Finset.filter (fun s : ℕ => |Int.bmod ((s : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
          (Finset.range (2 ^ m))).card := by
        exact Nat.mul_le_mul_left _ hres

open Classical in
/-- **The count lemma, restated on the good-pair predicate** (`eh_good_pair_iff` form): for `d` odd,
    at least `2^{ℓ+m-1}` outcomes `j ∈ [0, 2^{ℓ+m})` admit a good pair `(j,k)`.  This is the precise
    statement of 1702.00249 Lemma `count-good-pairs` (κ = 0 case). -/
theorem count_good_pairs_lower_bound (d m ℓ : ℕ) (hm : 2 ≤ m) (hd : Odd d) :
    2 ^ (ℓ + m - 1) ≤
      (Finset.filter (fun j => ∃ k : ℕ, k < 2 ^ ℓ ∧ EHGoodPair m ℓ d j k)
        (Finset.range (2 ^ (ℓ + m)))).card := by
  have hcong : (Finset.filter (fun j => ∃ k : ℕ, k < 2 ^ ℓ ∧ EHGoodPair m ℓ d j k)
                  (Finset.range (2 ^ (ℓ + m)))).card
      = (Finset.filter (fun j : ℕ => |Int.bmod ((d : ℤ) * (j : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
                  (Finset.range (2 ^ (ℓ + m)))).card := by
    apply Finset.card_bij (fun j _ => j)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      refine ⟨hj.1, ?_⟩
      have := (eh_good_pair_iff d j m ℓ hm).mp hj.2
      simpa [cresid] using this
    · intro a _ b _ hab; exact hab
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      refine ⟨j, ⟨hj.1, ?_⟩, rfl⟩
      have : |cresid ((d : Int) * j) (2 ^ m)| ≤ 2 ^ (m - 2) := by simpa [cresid] using hj.2
      exact (eh_good_pair_iff d j m ℓ hm).mpr this
  rw [hcong]
  exact count_good_j_lower_bound d m ℓ hm hd

/-! ## §7. The GENERAL count lemma — any `0 < d < 2^m`, `κ = v₂(d) > 0` allowed.

The κ = 0 case above used the coprime bijection `r ↦ dr mod 2^m`.  For general `d` write
`d = 2^κ · d'` with `d'` odd (`κ = v₂(d)`).  Since `0 < d < 2^m` we get `κ ≤ m-1` (the paper's
`κ ≤ m-1`).  The unit `d'` reduces (by a coprime bijection) the good-residue count for `d` to the
good-residue count for the pure power `2^κ`; and that pure-power count is `≥ 2^{m-1}` by a
2-adic-valuation fibre argument (each value `2^κ t`, `t ∈ [0, 2^{m-κ})`, is hit with multiplicity
`2^κ`, and the good `t` form the same low/high windows scaled by `2^κ`, with the `κ = m-1` corner
contributing only `t = 0`).  Paper: 1702.00249, Lemma `count-good-pairs`, the general
`κ ≤ m-1` branch (the κ = m-1 sub-case = "only zero gives a good pair", multiplicity `2^{ℓ+m-1}`;
the κ < m-1 sub-case = `2^{ℓ+κ}·(2·2^{m-κ-2}+1) ≥ 2^{ℓ+m-1}`). -/

/-- If two naturals agree mod `2^m`, their (nat-cast) balanced residues agree. -/
private lemma bmod_eq_of_nat_mod_eq {a b m : ℕ} (h : a % 2 ^ m = b % 2 ^ m) :
    Int.bmod ((a : ℤ)) (2 ^ m) = Int.bmod ((b : ℤ)) (2 ^ m) := by
  rw [bmod_natCast_mod a m, bmod_natCast_mod b m, h]

/-- **Transport along a unit** (coprime to `2^m`).  Counting `r` with `|{a·u·r}_{2^m}| ≤ B` equals
    counting `s` with `|{a·s}_{2^m}| ≤ B`, via the bijection `r ↦ u·r mod 2^m` (inverse from
    `exists_modinv`).  This is the multiplicity-preserving step that strips the odd part `d'` of `d`. -/
theorem count_unit_transport (a u m : ℕ) (B : ℤ) (hcop : Nat.Coprime u (2 ^ m)) :
    (Finset.filter (fun r : ℕ => |Int.bmod (((a * u : ℕ) : ℤ) * (r : ℤ)) (2 ^ m)| ≤ B)
        (Finset.range (2 ^ m))).card
      = (Finset.filter (fun s : ℕ => |Int.bmod ((a : ℤ) * (s : ℤ)) (2 ^ m)| ≤ B)
        (Finset.range (2 ^ m))).card := by
  have h2pos : 0 < 2 ^ m := Nat.two_pow_pos m
  obtain ⟨e, he⟩ := exists_modinv u m hcop
  apply Finset.card_bij (fun r _ => (u * r) % 2 ^ m)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
    refine ⟨Nat.mod_lt _ h2pos, ?_⟩
    have key : Int.bmod ((a : ℤ) * (((u * r) % 2 ^ m : ℕ) : ℤ)) (2 ^ m)
             = Int.bmod (((a * u : ℕ) : ℤ) * (r : ℤ)) (2 ^ m) := by
      rw [show ((a : ℤ) * (((u * r) % 2 ^ m : ℕ) : ℤ)) = (((a * ((u * r) % 2 ^ m)) : ℕ) : ℤ) by
            push_cast; ring,
          show (((a * u : ℕ) : ℤ) * (r : ℤ)) = (((a * u) * r : ℕ) : ℤ) by push_cast; ring]
      apply bmod_eq_of_nat_mod_eq
      have hmod : a * ((u * r) % 2 ^ m) ≡ a * (u * r) [MOD 2 ^ m] :=
        Nat.ModEq.mul_left a (Nat.mod_modEq _ _)
      calc a * ((u * r) % 2 ^ m) % 2 ^ m = a * (u * r) % 2 ^ m := hmod
        _ = (a * u) * r % 2 ^ m := by rw [mul_assoc]
    rw [key]; exact hr.2
  · intro r1 hr1 r2 hr2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
    have hmod : r1 % 2 ^ m = r2 % 2 ^ m :=
      Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hcop) heq
    rwa [Nat.mod_eq_of_lt hr1.1, Nat.mod_eq_of_lt hr2.1] at hmod
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs
    refine ⟨(e * s) % 2 ^ m, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ h2pos, ?_⟩
      have key : Int.bmod (((a * u : ℕ) : ℤ) * (((e * s) % 2 ^ m : ℕ) : ℤ)) (2 ^ m)
               = Int.bmod ((a : ℤ) * (s : ℤ)) (2 ^ m) := by
        rw [show (((a * u : ℕ) : ℤ) * (((e * s) % 2 ^ m : ℕ) : ℤ))
              = ((((a * u) * ((e * s) % 2 ^ m)) : ℕ) : ℤ) by push_cast; ring,
            show ((a : ℤ) * (s : ℤ)) = ((a * s : ℕ) : ℤ) by push_cast; ring]
        apply bmod_eq_of_nat_mod_eq
        have h1 : (a * u) * ((e * s) % 2 ^ m) = a * (u * ((e * s) % 2 ^ m)) := by ring
        have h2 : a * (u * ((e * s) % 2 ^ m)) ≡ a * ((u * ((e * s) % 2 ^ m)) % 2 ^ m) [MOD 2 ^ m] :=
          Nat.ModEq.mul_left a (Nat.mod_modEq _ _).symm
        have h3 : u * ((e * s) % 2 ^ m) % 2 ^ m = s % 2 ^ m := he s
        have h4 : a * (s % 2 ^ m) ≡ a * s [MOD 2 ^ m] := Nat.ModEq.mul_left a (Nat.mod_modEq _ _)
        calc (a * u) * ((e * s) % 2 ^ m) % 2 ^ m
            = a * (u * ((e * s) % 2 ^ m)) % 2 ^ m := by rw [h1]
          _ = a * ((u * ((e * s) % 2 ^ m)) % 2 ^ m) % 2 ^ m := h2
          _ = a * (s % 2 ^ m) % 2 ^ m := by rw [h3]
          _ = a * s % 2 ^ m := h4
      rw [key]; exact hs.2
    · rw [he s, Nat.mod_eq_of_lt hs.1]

/-- **Scaled low window.**  `t < 2^{n-2}` (with `κ + n = m`, `n ≥ 2`) ⇒ `2^κ·t < 2^{m-2}` ⇒ good. -/
private lemma good_low_scaled (κ m t : ℕ) (hm : 2 ≤ m) (ht : (2:ℕ) ^ κ * t < 2 ^ (m - 2)) :
    |Int.bmod (((2 ^ κ : ℕ) : ℤ) * (t : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2) := by
  rw [show (((2 ^ κ : ℕ) : ℤ) * (t : ℤ)) = (((2 ^ κ * t : ℕ)) : ℤ) by push_cast; ring]
  exact good_low m (2 ^ κ * t) hm ht

/-- **Scaled residue lower bound (`κ ≤ m-2`, i.e. `n = m-κ ≥ 2`).**  At least `2^{n-1}` values
    `t ∈ [0, 2^n)` have `|{2^κ·t}_{2^m}| ≤ 2^{m-2}`: the low window `[0, 2^{n-2})` and the high
    window `[2^n - 2^{n-2}, 2^n)`, each of size `2^{n-2}`, scaled by `2^κ`. -/
theorem count_scaled_good_lower (κ n : ℕ) (hn : 2 ≤ n) :
    2 ^ (n - 1) ≤
      (Finset.filter (fun t : ℕ =>
          |Int.bmod (((2 ^ κ : ℕ) : ℤ) * (t : ℤ)) (2 ^ (κ + n))| ≤ 2 ^ (κ + n - 2))
        (Finset.range (2 ^ n))).card := by
  set m := κ + n with hm_def
  have hm : 2 ≤ m := by omega
  set G := Finset.filter (fun t : ℕ => |Int.bmod (((2 ^ κ : ℕ) : ℤ) * (t : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
            (Finset.range (2 ^ n)) with hG
  set S := Finset.range (2 ^ (n - 2)) ∪ Finset.Ico (2 ^ n - 2 ^ (n - 2)) (2 ^ n) with hS
  have hsub : S ⊆ G := by
    intro t hsmem
    rw [hS, Finset.mem_union] at hsmem
    rw [hG, Finset.mem_filter, Finset.mem_range]
    rcases hsmem with h | h
    · rw [Finset.mem_range] at h
      have htlt : t < 2 ^ n := by
        have : (2:ℕ) ^ (n - 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      refine ⟨htlt, ?_⟩
      apply good_low_scaled κ m t hm
      have hlt : (2:ℕ) ^ κ * t < 2 ^ κ * 2 ^ (n - 2) :=
        (Nat.mul_lt_mul_left (Nat.two_pow_pos κ)).mpr h
      rw [← pow_add] at hlt
      have he : κ + (n - 2) = m - 2 := by omega
      rwa [he] at hlt
    · rw [Finset.mem_Ico] at h
      refine ⟨h.2, ?_⟩
      rw [show (((2 ^ κ : ℕ) : ℤ) * (t : ℤ)) = (((2 ^ κ * t : ℕ)) : ℤ) by push_cast; ring]
      apply good_high m (2 ^ κ * t) hm
      · have hmul : (2:ℕ) ^ κ * (2 ^ n - 2 ^ (n - 2)) ≤ 2 ^ κ * t :=
          Nat.mul_le_mul_left _ h.1
        have heq : (2:ℕ) ^ κ * (2 ^ n - 2 ^ (n - 2)) = 2 ^ m - 2 ^ (m - 2) := by
          rw [Nat.mul_sub, ← pow_add, ← pow_add]
          have e1 : κ + n = m := by omega
          have e2 : κ + (n - 2) = m - 2 := by omega
          rw [e1, e2]
        rw [heq] at hmul; exact hmul
      · have hlt : (2:ℕ) ^ κ * t < 2 ^ κ * 2 ^ n :=
          (Nat.mul_lt_mul_left (Nat.two_pow_pos κ)).mpr h.2
        rw [← pow_add] at hlt
        have he : κ + n = m := by omega
        rwa [he] at hlt
  have hcardS : S.card = 2 ^ (n - 1) := by
    rw [hS, Finset.card_union_of_disjoint]
    · rw [Finset.card_range, Nat.card_Ico]
      have hle : (2:ℕ) ^ (n - 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 2)
      have h1 : 2 ^ (n - 2) + (2 ^ n - (2 ^ n - 2 ^ (n - 2))) = 2 * 2 ^ (n - 2) := by omega
      rw [h1, ← pow_succ']
      congr 1; omega
    · rw [Finset.disjoint_left]
      intro x hx hx2
      rw [Finset.mem_range] at hx; rw [Finset.mem_Ico] at hx2
      have hbound : 2 * 2 ^ (n - 2) ≤ 2 ^ n := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  calc 2 ^ (n - 1) = S.card := hcardS.symm
    _ ≤ G.card := Finset.card_le_card hsub

/-- The scaled good predicate `|{2^κ·r}_{2^m}| ≤ 2^{m-2}` is `2^{m-κ}`-periodic in `r`
    (adding `2^{m-κ}` adds `2^m ≡ 0` inside `bmod _ (2^m)`). -/
theorem scaled_good_pred_periodic (κ m : ℕ) (hκm : κ ≤ m) (r : ℕ) :
    (|Int.bmod (((2 ^ κ : ℕ) : ℤ) * ((r + 2 ^ (m - κ) : ℕ) : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
      ↔ (|Int.bmod (((2 ^ κ : ℕ) : ℤ) * (r : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2)) := by
  have hsplit : (((2 ^ κ : ℕ) : ℤ) * ((r + 2 ^ (m - κ) : ℕ) : ℤ))
      = ((2 ^ κ : ℕ) : ℤ) * (r : ℤ) + ((2 ^ m : ℕ) : ℤ) * (1 : ℤ) := by
    have hsum : κ + (m - κ) = m := by omega
    push_cast
    rw [show (2:ℤ) ^ κ * ((r:ℤ) + 2 ^ (m - κ)) = (2:ℤ)^κ * r + 2 ^ κ * 2 ^ (m - κ) by ring,
        ← pow_add, hsum]
    ring
  rw [hsplit, Int.add_mul_bmod_self_left]

/-- Count of good `r ∈ [0, 2^m)` for the scaled predicate = `2^κ ·` count over one period
    `[0, 2^{m-κ})` (the `2^{ℓ+κ}` multiplicity, restricted to one `2^ℓ`-block). -/
theorem count_scaled_periodic (κ m : ℕ) (hκm : κ ≤ m) :
    (Finset.filter (fun r : ℕ => |Int.bmod (((2 ^ κ : ℕ) : ℤ) * (r : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
        (Finset.range (2 ^ m))).card
      = 2 ^ κ *
        (Finset.filter (fun r : ℕ => |Int.bmod (((2 ^ κ : ℕ) : ℤ) * (r : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
          (Finset.range (2 ^ (m - κ)))).card := by
  have hpow : (2:ℕ) ^ m = 2 ^ κ * 2 ^ (m - κ) := by rw [← pow_add]; congr 1; omega
  have key := filter_range_mul_periodic
    (fun r : ℕ => |Int.bmod (((2 ^ κ : ℕ) : ℤ) * (r : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
    (2 ^ (m - κ)) (2 ^ κ)
    (fun r => scaled_good_pred_periodic κ m hκm r)
  rw [← hpow] at key
  exact key

/-- `κ = m-1` corner: the period `[0, 2)` count is `≥ 1` (only `r = 0` is good). -/
theorem count_scaled_good_lower_one (κ m : ℕ) :
    1 ≤
      (Finset.filter (fun r : ℕ => |Int.bmod (((2 ^ κ : ℕ) : ℤ) * (r : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
        (Finset.range 2)).card := by
  apply Finset.card_pos.mpr
  refine ⟨0, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨by norm_num, ?_⟩
  rw [Nat.cast_zero, mul_zero]
  have hpos : (0 : ℤ) < (2 ^ m + 1) / 2 := by
    have h2 : (2 : ℤ) ≤ 2 ^ m + 1 := by
      have : (1 : ℤ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      linarith
    have : (1 : ℤ) ≤ (2 ^ m + 1) / 2 := by
      rw [Int.le_ediv_iff_mul_le (by norm_num)]; linarith
    linarith
  have hb : Int.bmod 0 (2 ^ m) = 0 := by simp [Int.bmod, hpos]
  rw [hb, abs_zero]
  positivity

/-- **Residue lower bound for the pure power `2^κ`** (`κ ≤ m-1`).  At least `2^{m-1}` residues
    `r ∈ [0, 2^m)` satisfy `|{2^κ·r}_{2^m}| ≤ 2^{m-2}`.  (κ = m-1 corner gives exactly `2^{m-1}`,
    via `2^κ · 1`; κ < m-1 gives `2^κ · 2^{m-κ-1} = 2^{m-1}` from the two windows.) -/
theorem count_scaled_residue_lower (κ m : ℕ) (hm : 2 ≤ m) (hκ : κ ≤ m - 1) :
    2 ^ (m - 1) ≤
      (Finset.filter (fun r : ℕ => |Int.bmod (((2 ^ κ : ℕ) : ℤ) * (r : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
        (Finset.range (2 ^ m))).card := by
  have hκm : κ ≤ m := by omega
  rw [count_scaled_periodic κ m hκm]
  rcases Nat.lt_or_ge (m - κ) 2 with hlt | hge
  · have hmκ : m - κ = 1 := by omega
    rw [hmκ]
    have h1 := count_scaled_good_lower_one κ m
    calc 2 ^ (m - 1) = 2 ^ κ * 1 := by rw [mul_one]; congr 1; omega
      _ ≤ 2 ^ κ * _ := Nat.mul_le_mul_left _ h1
  · have hsum : κ + (m - κ) = m := by omega
    have hinner := count_scaled_good_lower κ (m - κ) hge
    rw [hsum] at hinner
    calc 2 ^ (m - 1) = 2 ^ κ * 2 ^ (m - κ - 1) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ κ * _ := Nat.mul_le_mul_left _ hinner

/-- **General residue lower bound** (`0 < d < 2^m`).  Writing `d = 2^κ·d'` with `d'` odd and
    `κ = v₂(d) ≤ m-1`, at least `2^{m-1}` residues `r ∈ [0, 2^m)` have `|{d·r}_{2^m}| ≤ 2^{m-2}`.
    The unit `d'` transports the count to the pure-power-`2^κ` count (`count_unit_transport`),
    which is `≥ 2^{m-1}` (`count_scaled_residue_lower`). -/
theorem count_general_residue_lower (d m : ℕ) (hm : 2 ≤ m) (hd0 : 0 < d) (hdlt : d < 2 ^ m) :
    2 ^ (m - 1) ≤
      (Finset.filter (fun r : ℕ => |Int.bmod ((d : ℤ) * (r : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
        (Finset.range (2 ^ m))).card := by
  -- κ = v₂(d), d' = ordCompl[2] d (odd), d = 2^κ · d'
  set κ := d.factorization 2 with hκ_def
  set d' := ordCompl[2] d with hd'_def
  have hdne : d ≠ 0 := hd0.ne'
  have hfac : 2 ^ κ * d' = d := Nat.ordProj_mul_ordCompl_eq_self d 2
  have hcop2 : Nat.Coprime 2 d' := Nat.coprime_ordCompl Nat.prime_two hdne
  have hd'odd : Nat.Coprime d' (2 ^ m) := Nat.Coprime.pow_right m hcop2.symm
  -- κ ≤ m-1: 2^κ ∣ d, d ≠ 0 ⇒ 2^κ ≤ d < 2^m ⇒ κ < m
  have hdvd : (2:ℕ) ^ κ ∣ d := Nat.ordProj_dvd d 2
  have h2κle : (2:ℕ) ^ κ ≤ d := Nat.le_of_dvd hd0 hdvd
  have hκlt : κ < m := by
    have : (2:ℕ) ^ κ < 2 ^ m := lt_of_le_of_lt h2κle hdlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have hκ : κ ≤ m - 1 := by omega
  -- transport: good-count for d = good-count for 2^κ
  have htrans := count_unit_transport (2 ^ κ) d' m (2 ^ (m - 2)) hd'odd
  -- rewrite (2^κ * d' : ℕ) = d in the transported statement
  rw [hfac] at htrans
  rw [show (Finset.filter (fun r : ℕ => |Int.bmod ((d : ℤ) * (r : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
        (Finset.range (2 ^ m)))
      = (Finset.filter (fun r : ℕ => |Int.bmod (((d : ℕ) : ℤ) * (r : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
        (Finset.range (2 ^ m))) by rfl]
  rw [htrans]
  exact count_scaled_residue_lower κ m hm hκ

/-- **Good-`j` count for general `d`** (1702.00249, multiplicity step, any `0 < d < 2^m`).  Over
    `[0, 2^{ℓ+m})` the count of good `j` is `2^ℓ ·` the residue count, by `2^m`-periodicity (which
    holds for ANY `d`). -/
theorem count_general_j_lower_bound (d m ℓ : ℕ) (hm : 2 ≤ m) (hd0 : 0 < d) (hdlt : d < 2 ^ m) :
    2 ^ (ℓ + m - 1) ≤
      (Finset.filter (fun j : ℕ => |Int.bmod ((d : ℤ) * (j : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
                        (Finset.range (2 ^ (ℓ + m)))).card := by
  rw [count_good_j_odd_d d m ℓ]
  have hres := count_general_residue_lower d m hm hd0 hdlt
  calc 2 ^ (ℓ + m - 1) = 2 ^ ℓ * 2 ^ (m - 1) := by rw [← pow_add]; congr 1; omega
    _ ≤ 2 ^ ℓ * (Finset.filter (fun r : ℕ => |Int.bmod ((d : ℤ) * (r : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
          (Finset.range (2 ^ m))).card := Nat.mul_le_mul_left _ hres

open Classical in
/-- **Ekerå–Håstad count lemma, the GENERAL case** (1702.00249, Lemma `count-good-pairs`).  For any
    `0 < d < 2^m` (no oddness assumption — `κ = v₂(d)` may be positive, the paper's `κ ≤ m-1`),
    at least `2^{ℓ+m-1}` outcomes `j ∈ [0, 2^{ℓ+m})` admit a good pair `(j,k)`.  This is the precise
    full statement of the paper's lemma; the odd-`d` (`κ = 0`) special case is
    `count_good_pairs_lower_bound`. -/
theorem count_good_pairs_lower_bound_general (d m ℓ : ℕ) (hm : 2 ≤ m)
    (hd0 : 0 < d) (hdlt : d < 2 ^ m) :
    2 ^ (ℓ + m - 1) ≤
      (Finset.filter (fun j => ∃ k : ℕ, k < 2 ^ ℓ ∧ EHGoodPair m ℓ d j k)
        (Finset.range (2 ^ (ℓ + m)))).card := by
  have hcong : (Finset.filter (fun j => ∃ k : ℕ, k < 2 ^ ℓ ∧ EHGoodPair m ℓ d j k)
                  (Finset.range (2 ^ (ℓ + m)))).card
      = (Finset.filter (fun j : ℕ => |Int.bmod ((d : ℤ) * (j : ℤ)) (2 ^ m)| ≤ 2 ^ (m - 2))
                  (Finset.range (2 ^ (ℓ + m)))).card := by
    apply Finset.card_bij (fun j _ => j)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      refine ⟨hj.1, ?_⟩
      have := (eh_good_pair_iff d j m ℓ hm).mp hj.2
      simpa [cresid] using this
    · intro a _ b _ hab; exact hab
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      refine ⟨j, ⟨hj.1, ?_⟩, rfl⟩
      have : |cresid ((d : Int) * j) (2 ^ m)| ≤ 2 ^ (m - 2) := by simpa [cresid] using hj.2
      exact (eh_good_pair_iff d j m ℓ hm).mpr this
  rw [hcong]
  exact count_general_j_lower_bound d m ℓ hm hd0 hdlt

end FormalRV.Audit.Gidney2025.EkeraCombinatorics
