/-
  FormalRV.Audit.Gidney2025.CFS.ResidueNumberSystem — SEMANTIC layer 2 of the Gidney-2025 / Chevignard–
  Fouque–Schrottenloher factoring algorithm: the RESIDUE NUMBER SYSTEM is faithful.

  Per "semantic proof BEFORE resource proof".  `ResidueArith.lean` proved that computing the
  modular-exponentiation product modulo the friendly modulus `L` (then mod `N`) is exact when
  `L ≥ N^m` (no wraparound).  But CFS never represents that product as one big integer: it carries
  it in a RESIDUE NUMBER SYSTEM — a vector of residues `(V mod p₁, …, V mod p_t)` over a set of
  small pairwise-coprime primes `P = {p_j}` with `∏ p_j = L`.  All the arithmetic (the controlled
  multiplications) happens componentwise on those residues.

  For that to recover the answer, the residue representation must be FAITHFUL: the residue vector
  must determine `V mod L` uniquely.  That is exactly the Chinese Remainder Theorem's injectivity,
  proved here from `Nat.modEq_and_modEq_iff_modEq_mul` by induction over the prime list:

    * `coprime_list_prod`        — a number coprime to every modulus is coprime to their product.
    * `modEq_list_prod_of_forall`— agreeing mod each pairwise-coprime modulus ⟹ agreeing mod ∏.
    * `rns_faithful`             — the residue vector `(V mod p_j)_j` determines `V mod ∏ p_j`.

  Combined with `ResidueArith.residue_modexp_exact`, this is the semantic justification of the CFS
  *exact* residue arithmetic: do the whole modexp in the residue domain over `P`, reconstruct
  `V mod L`, reduce mod `N`, get `g^e mod N`.  The remaining honest gap (the *approximate* /
  truncated fractional reconstruction and its modular-deviation bound `Δ_N ≤ |P|·ℓ·2^{-f}`) is
  itemised in `ResidueArith.lean` and is NOT asserted here.
-/
import Mathlib
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS

/-- A number coprime to every element of a list is coprime to the list's product.  (Each prime in
    `P` is coprime to the product of the others — the well-formedness of the RNS modulus `L = ∏P`.) -/
theorem coprime_list_prod (m : ℕ) :
    ∀ l : List ℕ, (∀ x ∈ l, m.Coprime x) → m.Coprime l.prod
  | [], _ => by simpa using (Nat.coprime_one_right m)
  | a :: l, h => by
      have ha : m.Coprime a := h a (by simp)
      have hl : m.Coprime l.prod := coprime_list_prod m l (fun x hx => h x (by simp [hx]))
      simpa [List.prod_cons] using ha.mul_right hl

/-- **CRT, product form.**  If `a ≡ b` modulo every modulus in a list of PAIRWISE-COPRIME moduli,
    then `a ≡ b` modulo their product.  (Inductive CRT via `Nat.modEq_and_modEq_iff_modEq_mul`.) -/
theorem modEq_list_prod_of_forall (a b : ℕ) :
    ∀ l : List ℕ, l.Pairwise Nat.Coprime → (∀ m ∈ l, a ≡ b [MOD m]) → a ≡ b [MOD l.prod]
  | [], _, _ => by simp only [List.prod_nil]; exact Nat.modEq_one
  | m :: l, hpw, h => by
      have hpw' := List.pairwise_cons.mp hpw
      have hm : a ≡ b [MOD m] := h m (by simp)
      have hl : a ≡ b [MOD l.prod] :=
        modEq_list_prod_of_forall a b l hpw'.2 (fun x hx => h x (by simp [hx]))
      have hcop : m.Coprime l.prod := coprime_list_prod m l hpw'.1
      rw [List.prod_cons]
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hm, hl⟩

/-- **CRT, `Fin`-indexed product form.**  If `a ≡ b` modulo every modulus `p i` (pairwise coprime),
    then `a ≡ b` modulo `∏ i, p i`.  This is the `Fin`-indexed bridge used by the reconstruction
    identity (`CFS.Reconstruction`); proved from the `List` form via `List.ofFn`. -/
theorem modEq_prod_of_forall {t : ℕ} (p : Fin t → ℕ)
    (hco : ∀ i j, i ≠ j → Nat.Coprime (p i) (p j))
    (a b : ℕ) (h : ∀ i, a ≡ b [MOD p i]) : a ≡ b [MOD ∏ i, p i] := by
  rw [← List.prod_ofFn]
  refine modEq_list_prod_of_forall a b _ ?_ ?_
  · rw [List.pairwise_ofFn]
    exact fun i j hij => hco i j (ne_of_lt hij)
  · intro mm hm
    rw [List.mem_ofFn] at hm
    obtain ⟨i, rfl⟩ := hm
    exact h i

/-- **RNS faithfulness (CRT injectivity).**  Over a set of pairwise-coprime moduli `P` (the CFS
    prime set, with `∏P = L`), two naturals with IDENTICAL residue vectors agree modulo `L`.
    Hence the residue representation loses no information about `V mod L`: the entire modexp may be
    carried componentwise in the residue domain and `V mod L` recovered exactly. -/
theorem rns_faithful (l : List ℕ) (hpw : l.Pairwise Nat.Coprime) (V W : ℕ)
    (h : ∀ m ∈ l, V % m = W % m) : V % l.prod = W % l.prod :=
  modEq_list_prod_of_forall V W l hpw h

/-- Consequence for a value already reduced: if `V < L = ∏P` and `W` shares its residue vector,
    then `W % L = V` exactly — the residue vector pins down the unique representative in `[0, L)`. -/
theorem rns_recover (l : List ℕ) (hpw : l.Pairwise Nat.Coprime) (V W : ℕ)
    (hV : V < l.prod) (h : ∀ m ∈ l, V % m = W % m) : W % l.prod = V := by
  have := (rns_faithful l hpw V W h).symm
  rwa [Nat.mod_eq_of_lt hV] at this

/-! ## The faithfulness theorems pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean rns_faithful
#verify_clean rns_recover
#verify_clean modEq_list_prod_of_forall
#verify_clean modEq_prod_of_forall

end FormalRV.CFS
