/-
  FormalRV.Audit.Gidney2025.CFS.ResidueArith — SEMANTIC foundation of the Gidney-2025 / Chevignard–Fouque–
  Schrottenloher approximate-residue-arithmetic factoring algorithm.

  Per the discipline "semantic proof BEFORE resource proof": before the Gidney-2025 resource
  tallies (Corpus/Gidney2025.lean) mean anything, the algorithm's arithmetic must be proved to
  compute the right thing.  This file proves the EXACT residue-modular-exponentiation core:

    * `residue_no_wraparound`  — the reason residue arithmetic works: a value `< L` is unchanged
      by `% L`, so computing `% L` then `% N` equals `% N` directly (no wraparound).
    * `modexpProd_modEq`       — the product of the `m` controlled multiplications is
      `≡ g^(e mod 2^m) (mod N)` (so `= g^e mod N` for `e < 2^m`).
    * `modexpProd_lt`          — that product is `< N^m`, hence `< L` whenever `L ≥ N^m`
      (paper eq:bound-L).
    * `residue_modexp_exact`   — combining them: computing the modexp via residue arithmetic
      mod `L` then mod `N` yields exactly `g^e mod N`  (paper §"Approximate Residue Arithmetic",
      eq:comp_v, before truncation).

  Still TODO for the FULL semantic proof (honest): the CRT reconstruction `∑ r_j u_j ≡ V (mod L)`,
  the truncation modular-deviation bound `Δ_N ≤ |P|·ℓ·2^{-f}` (eq:modevbound), the Ekerå–Håstad
  post-processing, and the quantum-circuit semantics.  Assumption 1 (a prime set `P` with
  `∏P ≥ N^m` and small modular deviation exists) is a genuine CONJECTURE — an honest axiom, not
  asserted here.
-/
import Mathlib
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS

/-! ## §1. The no-wraparound principle (why residue arithmetic is exact). -/

/-- **Residue arithmetic is exact when there is no wraparound.**  If `V < L` then `V % L = V`,
    so computing modulo `L` then modulo `N` equals `V % N` directly.  This is precisely why the
    algorithm may use a friendly modulus `L ≥ N^m` instead of the unknown-factor modulus `N`. -/
theorem residue_no_wraparound (V N L : Nat) (h : V < L) : V % L % N = V % N := by
  rw [Nat.mod_eq_of_lt h]

/-! ## §2. The modular-exponentiation product. -/

/-- The `m`-th bit value of `e` (`0` or `1`). -/
def bit (e m : Nat) : Nat := e / 2 ^ m % 2

/-- Precomputed constant `M_m = g^(2^m) mod N`. -/
def Mconst (g N m : Nat) : Nat := g ^ (2 ^ m) % N

/-- The residue-arithmetic modular-exponentiation PRODUCT `∏_{k<m} M_k^{e_k}`, kept as an
    UNREDUCED integer (the series of controlled multiplications). -/
def modexpProd (g N : Nat) : Nat → Nat → Nat
  | 0,     _ => 1
  | m + 1, e => modexpProd g N m e * Mconst g N m ^ bit e m

/-- Binary step: `e % 2^(m+1) = e % 2^m + 2^m · bit e m` (this is exactly `Nat.mod_mul`). -/
theorem mod_two_pow_succ (e m : Nat) :
    e % 2 ^ (m + 1) = e % 2 ^ m + 2 ^ m * bit e m := by
  unfold bit; rw [pow_succ, Nat.mod_mul]

/-- **Congruence**: the product of the controlled multiplications is `≡ g^(e mod 2^m) (mod N)`. -/
theorem modexpProd_modEq (g N e : Nat) : ∀ m,
    modexpProd g N m e ≡ g ^ (e % 2 ^ m) [MOD N]
  | 0 => by simp only [modexpProd, pow_zero, Nat.mod_one]; exact Nat.ModEq.refl 1
  | m + 1 => by
      have ih := modexpProd_modEq g N e m
      have hfac : Mconst g N m ^ bit e m ≡ g ^ (2 ^ m * bit e m) [MOD N] := by
        unfold Mconst
        calc (g ^ (2 ^ m) % N) ^ bit e m
            ≡ (g ^ (2 ^ m)) ^ bit e m [MOD N] := (Nat.mod_modEq _ _).pow _
          _ = g ^ (2 ^ m * bit e m) := by rw [← pow_mul]
      calc modexpProd g N (m + 1) e
          = modexpProd g N m e * Mconst g N m ^ bit e m := rfl
        _ ≡ g ^ (e % 2 ^ m) * g ^ (2 ^ m * bit e m) [MOD N] := ih.mul hfac
        _ = g ^ (e % 2 ^ m + 2 ^ m * bit e m) := by rw [← pow_add]
        _ = g ^ (e % 2 ^ (m + 1)) := by rw [← mod_two_pow_succ]

/-! ## §3. The product is `≤ (N-1)^m`, hence `< N^m ≤ L` for `m ≥ 1`. -/

/-- The product of the controlled multiplications is `≤ (N-1)^m` (each factor is `≤ N-1`). -/
theorem modexpProd_le (g e : Nat) {N : Nat} (hN : 2 ≤ N) : ∀ m, modexpProd g N m e ≤ (N - 1) ^ m
  | 0 => by simp [modexpProd]
  | m + 1 => by
      have ih := modexpProd_le g e hN m
      have hf : Mconst g N m ^ bit e m ≤ N - 1 := by
        rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ m) with h | h
        · simp only [bit, h, pow_zero]; omega
        · simp only [bit, h, pow_one, Mconst]
          have := Nat.mod_lt (g ^ (2 ^ m)) (show 0 < N by omega); omega
      calc modexpProd g N (m + 1) e
          = modexpProd g N m e * Mconst g N m ^ bit e m := rfl
        _ ≤ (N - 1) ^ m * (N - 1) := Nat.mul_le_mul ih hf
        _ = (N - 1) ^ (m + 1) := (pow_succ (N - 1) m).symm

/-- For `m ≥ 1` and `N ≥ 2`, the product is STRICTLY `< N^m` (so it fits below any `L ≥ N^m`). -/
theorem modexpProd_lt_pow (g e : Nat) {N : Nat} (hN : 2 ≤ N) {m : Nat} (hm : 1 ≤ m) :
    modexpProd g N m e < N ^ m :=
  lt_of_le_of_lt (modexpProd_le g e hN m) (Nat.pow_lt_pow_left (by omega) (by omega))

/-! ## §4. EXACT residue modular exponentiation (no truncation yet). -/

/-- **The residue-arithmetic modular exponentiation is EXACT (no-wraparound form).**  Whenever the
    product `< L`, computing it modulo `L` then modulo `N` yields exactly `g^(e mod 2^m) mod N`.
    This is the semantic heart of the algorithm before approximation (paper eq:comp_v). -/
theorem residue_modexp_exact (g e N L m : Nat) (hlt : modexpProd g N m e < L) :
    modexpProd g N m e % L % N = g ^ (e % 2 ^ m) % N := by
  rw [residue_no_wraparound _ _ _ hlt]
  exact modexpProd_modEq g N e m

/-- **The residue modexp is exact for any valid Shor instance**: `N ≥ 2`, `m ≥ 1`, `L ≥ N^m`
    (the bound `eq:bound-L`).  Then `(∏ M_k^{e_k}) % L % N = g^(e mod 2^m) % N`. -/
theorem residue_modexp_exact_shor (g e N L : Nat) (hN : 2 ≤ N) {m : Nat} (hm : 1 ≤ m)
    (hL : N ^ m ≤ L) :
    modexpProd g N m e % L % N = g ^ (e % 2 ^ m) % N :=
  residue_modexp_exact g e N L m (lt_of_lt_of_le (modexpProd_lt_pow g e hN hm) hL)

/-- For an `m`-bit exponent (`e < 2^m`), the exact statement reads `… = g^e mod N`. -/
theorem residue_modexp_exact_of_lt (g e N L : Nat) (hN : 2 ≤ N) {m : Nat} (hm : 1 ≤ m)
    (hL : N ^ m ≤ L) (he : e < 2 ^ m) :
    modexpProd g N m e % L % N = g ^ e % N := by
  rw [residue_modexp_exact_shor g e N L hN hm hL, Nat.mod_eq_of_lt he]

/-! ## §5. The semantic foundation passes the VERIFIER gate (sorry-free, axiom-clean).

    Per "semantic proof before resource proof": these are REAL semantic theorems (the residue
    modexp computes `g^e mod N`), and `#verify_clean` confirms they use no `sorry`/extra axiom. -/

#verify_clean residue_modexp_exact_of_lt
#verify_clean residue_modexp_exact_shor
#verify_clean modexpProd_modEq

end FormalRV.CFS
