/-
  FormalRV.Shor.CFS.Reconstruction — the EXACT CRT reconstruction of the CFS modular
  exponentiation (Gidney 2025 §"Approximate Residue Arithmetic", eq:comp_v / the `∑ r_j u_j` form).

  Per "semantic proof BEFORE resource proof".  Layer 1 (`ResidueArith`) proved the residue modexp
  is exact mod `L`; layer 2 (`ResidueNumberSystem`) proved the residue representation is faithful.
  This file connects them by formalising the paper's ACTUAL reconstruction step (main.tex eq:comp_v):

      r_j = (∏_k M_k^{e_k}) mod p_j           -- the residue of the product modulo prime p_j
      u_j = (L/p_j) · MultInv_{p_j}(L/p_j)     -- the CRT contribution factor, u_j mod p_i = δ_{i,j}
      V   = (∑_j r_j u_j) mod L mod N           -- reconstruct the product, then reduce mod N

  NOTE — this corrects an earlier mischaracterisation in the CFS umbrella: the reconstruction is the
  EXACT INTEGER Chinese-remainder dot product (it equals `V mod L` on the nose), *not* a fractional
  approximation.  The approximation enters only later, when each term is truncated to `f` bits
  (`CFS.TruncationBound`).  So the "exact fractional-CRT identity" listed as an open gap is in fact
  this exact integer identity, proved here.

  The reconstruction's defining property of `u_j` (`u_j mod p_i = δ_{i,j}`) is taken as the
  hypothesis `hu`; constructing such `u_j` from modular inverses is classical precomputation, not a
  quantum cost, and any concrete CRT basis satisfies it.
-/
import FormalRV.Shor.CFS.ResidueArith
import FormalRV.Shor.CFS.ResidueNumberSystem
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS

open scoped BigOperators

/-- **Exact CRT reconstruction (paper eq:comp_v core).**  Let `p` be the pairwise-coprime prime set
    with product `L = ∏ p_i`, let `r_j = V mod p_j` be the residue vector of `V`, and let `u_j` be
    the CRT contribution factors (`u_j mod p_i = δ_{i,j}`).  Then the dot product reconstructs `V`
    exactly modulo `L`:  `(∑_j r_j u_j) mod L = V mod L`.  Proof: each `p_i` sees `∑_j r_j u_j ≡ r_i
    ≡ V`, so by CRT (`modEq_prod_of_forall`) the congruence holds mod the product. -/
theorem reconstruction {t : ℕ} (p : Fin t → ℕ)
    (hco : ∀ i j, i ≠ j → Nat.Coprime (p i) (p j))
    (V : ℕ) (u : Fin t → ℕ) (hu : ∀ i j, u j % p i = if i = j then 1 else 0) :
    (∑ j, (V % p j) * u j) % (∏ i, p i) = V % (∏ i, p i) := by
  apply modEq_prod_of_forall p hco
  intro i
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
  simp_rw [Nat.cast_mul]
  rw [Finset.sum_eq_single i]
  · -- the surviving (j = i) term equals `↑V`
    have hui : (↑(u i) : ZMod (p i)) = 1 := by
      have h1 : u i % p i = 1 := by simpa using hu i i
      rw [← ZMod.natCast_mod (u i) (p i), h1, Nat.cast_one]
    have hVi : (↑(V % p i) : ZMod (p i)) = ↑V := ZMod.natCast_mod V (p i)
    rw [hui, hVi, mul_one]
  · -- every `j ≠ i` term vanishes because `u_j ≡ 0 (mod p_i)`
    intro j _ hji
    have huj : (↑(u j) : ZMod (p i)) = 0 := by
      have h0 : u j % p i = 0 := by rw [hu i j, if_neg (fun e => hji e.symm)]
      rw [← ZMod.natCast_mod (u j) (p i), h0, Nat.cast_zero]
    rw [huj, mul_zero]
  · intro hnot; exact absurd (Finset.mem_univ i) hnot

/-- **The full exact RNS chain.**  Run the modexp as the integer product `modexpProd g N m e`,
    represent it by its residues over the prime set `p` (with `∏p = L ≥ N^m`), reconstruct via the
    CRT dot product, reduce mod `N`: the result is `g^e mod N` exactly, for an `m`-bit exponent.

    This is the EXACT (pre-truncation) semantic specification of the CFS arithmetic engine:
    `(∑_j r_j u_j) mod L mod N = g^e mod N`, combining layers 1+2 with the reconstruction. -/
theorem residue_modexp_via_crt (g e N L : ℕ) (hN : 2 ≤ N) {m : ℕ} (hm : 1 ≤ m)
    (hL : N ^ m ≤ L) (he : e < 2 ^ m)
    {tP : ℕ} (p : Fin tP → ℕ) (hco : ∀ i j, i ≠ j → Nat.Coprime (p i) (p j))
    (hLp : (∏ i, p i) = L) (u : Fin tP → ℕ) (hu : ∀ i j, u j % p i = if i = j then 1 else 0) :
    (∑ j, (modexpProd g N m e % p j) * u j) % L % N = g ^ e % N := by
  have hrec : (∑ j, (modexpProd g N m e % p j) * u j) % L = modexpProd g N m e % L := by
    have := reconstruction p hco (modexpProd g N m e) u hu
    rwa [hLp] at this
  rw [hrec]
  exact residue_modexp_exact_of_lt g e N L hN hm hL he

/-! ## The reconstruction theorems pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean reconstruction
#verify_clean residue_modexp_via_crt

end FormalRV.CFS
