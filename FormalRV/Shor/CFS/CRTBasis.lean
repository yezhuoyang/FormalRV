/-
  FormalRV.Shor.CFS.CRTBasis — CONSTRUCTION of the CRT contribution factors `u_j` from modular
  inverses, discharging the `u_j mod p_i = δ_{i,j}` hypothesis of `CFS.Reconstruction`.

  The reconstruction theorem (`CFS.Reconstruction.reconstruction`) took the existence of a CRT basis
  `u_j` with `u_j mod p_i = δ_{i,j}` as a hypothesis.  Gidney 2025 (main.tex, eq for `u_j`) gives the
  explicit formula

      u_j = (L / p_j) · MultiplicativeInverse_{p_j}(L / p_j)

  This file builds exactly that and PROVES the δ-property, so the reconstruction holds with no
  basis hypothesis at all (`reconstruction_explicit`).  Only classical (precomputable) data is used;
  `crtBasis` is `noncomputable` solely because it goes through `ZMod`'s inverse.
-/
import FormalRV.Shor.CFS.Reconstruction

namespace FormalRV.CFS

open scoped BigOperators

/-- `L / p_j = ∏_{i ≠ j} p_i`, the product of the OTHER primes. -/
noncomputable def Lhat {t : ℕ} (p : Fin t → ℕ) (j : Fin t) : ℕ := ∏ i ∈ Finset.univ.erase j, p i

/-- **The explicit CRT contribution factor** `u_j = (L/p_j) · (L/p_j)⁻¹ mod p_j` (Gidney 2025). -/
noncomputable def crtBasis {t : ℕ} (p : Fin t → ℕ) (j : Fin t) : ℕ :=
  Lhat p j * ((Lhat p j : ZMod (p j))⁻¹).val

/-- `L/p_j` is coprime to `p_j` (it is a product of primes each coprime to `p_j`). -/
theorem Lhat_coprime {t : ℕ} (p : Fin t → ℕ)
    (hco : ∀ i j, i ≠ j → Nat.Coprime (p i) (p j)) (j : Fin t) :
    Nat.Coprime (Lhat p j) (p j) := by
  unfold Lhat
  exact Nat.Coprime.prod_left (fun i hi => hco i j (Finset.ne_of_mem_erase hi))

/-- **The defining δ-property of the CRT basis**: `crtBasis p j mod p i = δ_{i,j}`.
    For `i = j` the inverse makes it `≡ 1`; for `i ≠ j`, `p i` divides `L/p_j` so it is `≡ 0`. -/
theorem crtBasis_delta {t : ℕ} (p : Fin t → ℕ) (hp : ∀ i, 1 < p i)
    (hco : ∀ i j, i ≠ j → Nat.Coprime (p i) (p j)) (i j : Fin t) :
    crtBasis p j % p i = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    haveI : NeZero (p i) := ⟨by have := hp i; omega⟩
    have hcop : Nat.Coprime (Lhat p i) (p i) := Lhat_coprime p hco i
    have hone : (crtBasis p i : ZMod (p i)) = 1 := by
      unfold crtBasis; rw [Nat.cast_mul]; exact ZMod.mul_val_inv hcop
    rw [if_pos rfl]
    have hmod : crtBasis p i ≡ 1 [MOD p i] := by
      rw [← ZMod.natCast_eq_natCast_iff]; exact_mod_cast hone
    rw [Nat.ModEq, Nat.mod_eq_of_lt (hp i)] at hmod
    exact hmod
  · rw [if_neg h]
    have hdvd : p i ∣ Lhat p j := by
      unfold Lhat
      exact Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩)
    unfold crtBasis
    exact Nat.dvd_iff_mod_eq_zero.mp (hdvd.mul_right _)

/-- **Reconstruction with the CONSTRUCTED basis** (no basis hypothesis).  Using `crtBasis`, the CRT
    dot product reconstructs `V` exactly modulo `L = ∏ p_i`.  Requires only that the `p_i` are
    primes (`1 < p_i`) and pairwise coprime. -/
theorem reconstruction_explicit {t : ℕ} (p : Fin t → ℕ) (hp : ∀ i, 1 < p i)
    (hco : ∀ i j, i ≠ j → Nat.Coprime (p i) (p j)) (V : ℕ) :
    (∑ j, (V % p j) * crtBasis p j) % (∏ i, p i) = V % (∏ i, p i) :=
  reconstruction p hco V (crtBasis p) (crtBasis_delta p hp hco)

/-- **The full exact RNS chain with the constructed basis**: run the modexp as an integer product,
    represent it over the prime set `p`, reconstruct via the explicit CRT basis, reduce mod `N` —
    the result is `g^e mod N` exactly, with NO basis hypothesis (cf. `residue_modexp_via_crt`). -/
theorem residue_modexp_via_crt_explicit (g e N : ℕ) (hN : 2 ≤ N) {m : ℕ} (hm : 1 ≤ m)
    (he : e < 2 ^ m) {tP : ℕ} (p : Fin tP → ℕ) (hp : ∀ i, 1 < p i)
    (hco : ∀ i j, i ≠ j → Nat.Coprime (p i) (p j)) (hL : N ^ m ≤ ∏ i, p i) :
    (∑ j, (modexpProd g N m e % p j) * crtBasis p j) % (∏ i, p i) % N = g ^ e % N :=
  residue_modexp_via_crt g e N (∏ i, p i) hN hm hL he p hco rfl (crtBasis p)
    (crtBasis_delta p hp hco)

/-! ## The basis-construction theorems pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean crtBasis_delta
#verify_clean reconstruction_explicit
#verify_clean residue_modexp_via_crt_explicit

end FormalRV.CFS
