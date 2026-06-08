/-
  FormalRV.Audit.Gidney2025.CFS.TruncationBound — SEMANTIC layer 3 of the Gidney-2025 / Chevignard–Fouque–
  Schrottenloher factoring algorithm: the APPROXIMATE-reconstruction deviation bound.

  Per "semantic proof BEFORE resource proof".  Layers 1–2 (`ResidueArith`, `ResidueNumberSystem`)
  established the EXACT residue arithmetic: carry the modexp product over the prime set `P`
  (`∏P = L ≥ N^m`), reconstruct `V mod L`, reduce mod `N`, get `g^e mod N`.  But the whole point of
  CFS — what makes it cheap enough for Gidney's 2025 estimate — is that the reconstruction is NOT
  done exactly.  The (fractional) CRT reconstruction is a sum of `|P|` rational terms; CFS TRUNCATES
  each term to `f` fractional bits.  This file bounds the resulting deviation.

  The quantitative heart (paper eq:modevbound, structure `Δ ≤ |P|·…·2^{-f}`):

    * `truncBits`            — truncate `x` to `f` fractional bits: `⌊x·2^f⌋ / 2^f`.
    * `truncBits_le`         — truncation never overshoots: `truncBits x f ≤ x`.
    * `truncBits_err_lt`     — single-term error is `< 2^{-f}`: `x − truncBits x f < 1/2^f`.
    * `sum_truncBits_error`  — the approximate reconstruction (sum of `t` truncated terms) deviates
                               from the exact sum by `< t · 2^{-f}`.  With `t = |P|`, this is the
                               modular-deviation bound's `2^{-f}` scaling, rigorously.

  HONEST remaining gap (NOT asserted here): tying `t · 2^{-f}` to the paper's exact `|P|·ℓ·2^{-f}`
  with the bit-width factor `ℓ`, and proving the exact fractional-CRT identity `V/L = ∑ a_j y_j/p_j
  (mod 1)` that these terms truncate.  Assumption 1 (a prime set with small deviation exists) stays
  a genuine conjecture (see `ResidueArith.lean` header).
-/
import Mathlib
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS

open scoped BigOperators

/-- Truncate `x` to `f` fractional bits: `⌊x·2^f⌋ / 2^f`. -/
noncomputable def truncBits (x : ℝ) (f : ℕ) : ℝ := (⌊x * 2 ^ f⌋ : ℝ) / 2 ^ f

/-- Truncation never overshoots. -/
theorem truncBits_le (x : ℝ) (f : ℕ) : truncBits x f ≤ x := by
  unfold truncBits
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le (x * 2 ^ f)

/-- The single-term truncation error is strictly below one unit in the last place, `2^{-f}`. -/
theorem truncBits_err_lt (x : ℝ) (f : ℕ) : x - truncBits x f < 1 / 2 ^ f := by
  have hpos : (0 : ℝ) < 2 ^ f := by positivity
  have h : x * 2 ^ f - 1 < (⌊x * 2 ^ f⌋ : ℝ) := Int.sub_one_lt_floor _
  have e1 : x - truncBits x f = (x * 2 ^ f - (⌊x * 2 ^ f⌋ : ℝ)) / 2 ^ f := by
    unfold truncBits; field_simp
  rw [e1, div_lt_div_iff₀ hpos hpos]
  nlinarith [mul_lt_mul_of_pos_right (show x * 2 ^ f - (⌊x * 2 ^ f⌋ : ℝ) < 1 by linarith) hpos]

/-- **General deviation bound over any nonempty index set.**  Replacing each term `g j` (`j` ranging
    over a nonempty finset `s`) by its `f`-bit truncation deviates from the exact sum by
    `< |s| · 2^{-f}`.  The reusable core; the `Fin`/double-sum forms below are instances. -/
theorem sum_truncBits_error' {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (g : ι → ℝ) (f : ℕ) :
    |(∑ j ∈ s, g j) - ∑ j ∈ s, truncBits (g j) f| < s.card / 2 ^ f := by
  have hsum : (∑ j ∈ s, g j) - ∑ j ∈ s, truncBits (g j) f
      = ∑ j ∈ s, (g j - truncBits (g j) f) := by rw [← Finset.sum_sub_distrib]
  rw [hsum]
  have hnonneg : 0 ≤ ∑ j ∈ s, (g j - truncBits (g j) f) :=
    Finset.sum_nonneg (fun j _ => by linarith [truncBits_le (g j) f])
  rw [abs_of_nonneg hnonneg]
  calc ∑ j ∈ s, (g j - truncBits (g j) f)
      < ∑ _j ∈ s, (1 / 2 ^ f : ℝ) :=
        Finset.sum_lt_sum_of_nonempty hs (fun j _ => truncBits_err_lt (g j) f)
    _ = s.card / 2 ^ f := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem sum_truncBits_error {t : ℕ} (ht : 0 < t) (g : Fin t → ℝ) (f : ℕ) :
    |(∑ j, g j) - ∑ j, truncBits (g j) f| < t / 2 ^ f := by
  haveI : NeZero t := ⟨by omega⟩
  have := sum_truncBits_error' (Finset.univ : Finset (Fin t)) Finset.univ_nonempty g f
  simpa [Finset.card_univ, Fintype.card_fin] using this

/-- **The CFS reconstruction's deviation bound (paper eq:modevbound).**  The approximate
    reconstruction `eq:comp_v` is a DOUBLE sum over `|P|` residues `j` and `ℓ` bits `k` — exactly
    `|P|·ℓ` truncated additions.  Truncating each to `f` bits deviates from the exact reconstruction
    by `< |P|·ℓ · 2^{-f}`, which is `Δ_N(V − (Ṽ ≪ t)) ≤ O(|P|·ℓ·2^{-f})` (the `ℓ` factor is the
    residue bit-width, the `|P|` factor is the number of primes). -/
theorem sum_truncBits_error_double {P ell : ℕ} (hP : 0 < P) (hl : 0 < ell)
    (g : Fin P → Fin ell → ℝ) (f : ℕ) :
    |(∑ j, ∑ k, g j k) - ∑ j, ∑ k, truncBits (g j k) f| < (P * ell : ℕ) / 2 ^ f := by
  haveI : NeZero P := ⟨by omega⟩
  haveI : NeZero ell := ⟨by omega⟩
  have e : ∀ h : Fin P → Fin ell → ℝ, (∑ j, ∑ k, h j k) = ∑ x : Fin P × Fin ell, h x.1 x.2 :=
    fun h => by rw [Fintype.sum_prod_type]
  rw [e g, e (fun j k => truncBits (g j k) f)]
  have := sum_truncBits_error' (Finset.univ : Finset (Fin P × Fin ell)) Finset.univ_nonempty
    (fun x => g x.1 x.2) f
  simpa [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using this

/-! ## The deviation-bound theorems pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean truncBits_le
#verify_clean truncBits_err_lt
#verify_clean sum_truncBits_error
#verify_clean sum_truncBits_error_double

end FormalRV.CFS
