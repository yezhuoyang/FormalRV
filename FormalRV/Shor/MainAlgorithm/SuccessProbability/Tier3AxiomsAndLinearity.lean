import FormalRV.Shor.MainAlgorithm.SuccessProbability.SpecializedShorVersion

namespace FormalRV.SQIRPort

/-! ### Tier-3 number-theoretic supporting axioms (Coq: `NumTheory.v`) -/

/-- `ord a N` satisfies the `Order` predicate when `gcd(a, N) = 1` and
`1 ≤ a < N` (Coq: `NumTheory.v` `ord_Order`).

**Closed 2026-05-23 from the constructive `ord` def**:
Existence of a witness `k > 0` with `a^k % N = 1` follows from
Euler's theorem `Nat.pow_totient_mod_eq_one` (using `1 < N`, which
follows from `0 < a ∧ a < N`). The minimality clause of `Order`
follows from `Nat.find_min'`. -/
theorem ord_Order (a N : Nat) (h_pos : 0 < a) (h_lt : a < N)
    (h_coprime : Nat.gcd a N = 1) : Order a (ord a N) N := by
  have h_N_ge_2 : 1 < N := by omega
  have h_exists : ∃ k, 0 < k ∧ a^k % N = 1 := by
    refine ⟨Nat.totient N, ?_, ?_⟩
    · exact Nat.totient_pos.mpr (by omega : 0 < N)
    · exact Nat.pow_totient_mod_eq_one h_N_ge_2 h_coprime
  unfold ord
  rw [dif_pos h_exists]
  refine ⟨(Nat.find_spec h_exists).1, (Nat.find_spec h_exists).2, ?_⟩
  intros s h_s_pos h_s_lt h_eq
  have h_find_le : Nat.find h_exists ≤ s := Nat.find_min' h_exists ⟨h_s_pos, h_eq⟩
  omega

/-- The modular inverse is bounded above by the modulus (Coq:
`NumTheory.v` `modinv_upper_bound`).  Required to specialise
`MultiplyCircuitProperty`'s input range.

**Closed 2026-05-23 from the constructive `modinv` def**:
`Int.emod` of any Int by a positive Int lands in `[0, N)`;
`Int.toNat` preserves this bound. -/
theorem modinv_upper_bound (a N : Nat) (h_pos : 1 < N) : modinv a N < N := by
  unfold modinv
  have h_N_pos : (0 : Int) < (N : Int) := by exact_mod_cast (by omega : 0 < N)
  have h_lt : (Nat.gcdA a N) % (N : Int) < (N : Int) := Int.emod_lt_of_pos _ h_N_pos
  have h_ge : (0 : Int) ≤ (Nat.gcdA a N) % (N : Int) :=
    Int.emod_nonneg _ (by exact_mod_cast (by omega : N ≠ 0))
  exact (Int.toNat_lt h_ge).mpr h_lt

/-- When `Order a r N` holds, `a · modinv a N ≡ 1 (mod N)` (Coq:
`NumTheory.v` `Order_modinv_correct`).  This is the spec that ties
the modular inverse to the order and allows the RCIR multiplier to
have a "reverse" half.

**Closed 2026-05-23 via Bezout extraction** (Phase 2 axiom #6):
1. From `Order a r N`: derive `Nat.gcd a N = 1` (via `Nat.dvd_mod_iff`)
   and `1 < N` (else `a^r % 1 = 0 ≠ 1`).
2. Bezout: `Int.gcd_a_modEq` gives `a * Nat.gcdA a N ≡ gcd a N [ZMOD N]`;
   coprime ⟹ `a * Nat.gcdA a N ≡ 1 [ZMOD N]`.
3. `modinv = ((Nat.gcdA a N) % N).toNat`, so `(modinv : Int) = (gcdA a N) % N`.
4. `(gcdA a N) % N ≡ gcdA a N [ZMOD N]` (`Int.mod_modEq`).
5. Multiplying: `(a * modinv : Int) ≡ a * gcdA a N ≡ 1 [ZMOD N]`.
6. Cast back to `Nat.ModEq` via `Int.natCast_modEq_iff`; finalize with `1 % N = 1`. -/
theorem Order_modinv_correct (a N r : Nat) (h_ord : Order a r N) (h_lt : a < N) :
    a * modinv a N % N = 1 := by
  obtain ⟨h_r_pos, h_arN, h_min⟩ := h_ord
  have h_N_pos : 0 < N := by omega
  have h_coprime : Nat.gcd a N = 1 := by
    have h1 : Nat.gcd a N ∣ a := Nat.gcd_dvd_left a N
    have h2 : Nat.gcd a N ∣ N := Nat.gcd_dvd_right a N
    have h3 : Nat.gcd a N ∣ a^r := dvd_pow h1 (Nat.pos_iff_ne_zero.mp h_r_pos)
    have h4 : Nat.gcd a N ∣ a^r % N := (Nat.dvd_mod_iff h2).mpr h3
    rw [h_arN] at h4
    exact Nat.eq_one_of_dvd_one h4
  have h_N_ge_2 : 1 < N := by
    rcases Nat.lt_or_eq_of_le h_N_pos with h | h
    · exact h
    · exfalso
      have : N = 1 := h.symm
      rw [this] at h_arN
      simp [Nat.mod_one] at h_arN
  have h_bezout_int : (a : Int) * Nat.gcdA a N ≡ 1 [ZMOD (N : Int)] := by
    have := Int.gcd_a_modEq a N
    rw [show ((Nat.gcd a N : Int) = 1) from by exact_mod_cast h_coprime] at this
    exact this
  have h_minv_int : (modinv a N : Int) = (Nat.gcdA a N) % (N : Int) := by
    unfold modinv
    have h_ge : (0 : Int) ≤ (Nat.gcdA a N) % (N : Int) :=
      Int.emod_nonneg _ (by exact_mod_cast (by omega : N ≠ 0))
    exact Int.toNat_of_nonneg h_ge
  have h_mod_eq : (Nat.gcdA a N) % (N : Int) ≡ Nat.gcdA a N [ZMOD (N : Int)] :=
    Int.mod_modEq _ _
  have h_target_int : ((a * modinv a N : Nat) : Int) ≡ 1 [ZMOD (N : Int)] := by
    push_cast
    rw [h_minv_int]
    calc (a : Int) * (Nat.gcdA a N % N)
        ≡ (a : Int) * Nat.gcdA a N [ZMOD (N : Int)] := Int.ModEq.mul_left _ h_mod_eq
      _ ≡ 1 [ZMOD (N : Int)] := h_bezout_int
  have h_target_nat : a * modinv a N ≡ 1 [MOD N] := by
    have h1 : ((a * modinv a N : Nat) : Int) ≡ ((1 : Nat) : Int) [ZMOD ((N : Nat) : Int)] := by
      simpa using h_target_int
    exact (Int.natCast_modEq_iff).mp h1
  have h_1_mod : 1 % N = 1 := Nat.mod_eq_of_lt h_N_ge_2
  rw [Nat.ModEq] at h_target_nat
  rw [h_target_nat, h_1_mod]

-- (removed 2026-06-09) Deprecated placeholder axioms `f_modmult_circuit_MMI`
-- and `f_modmult_circuit_uc_well_typed` deleted, along with the placeholder
-- `f_modmult_circuit` they referenced.  Use the constructive, proven
-- `FormalRV.BQAlgo.f_modmult_circuit_verified_bits_MMI` /
-- `..._uc_well_typed`; cite
-- `FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms` for end-to-end
-- Shor correctness.

/-! ## §10.5. `uc_eval` linearity over state-vector superpositions (Phase 4.D)

Three reusable lemmas that lift the standard matrix-algebra identities
`Matrix.mul_sum` / `Matrix.mul_smul` to the `uc_eval` notation. Used
downstream by the QPE orbit-decomposition step of
`h_orbit_exists` in `QPE_MMI_correct_assuming_orbit_factorization` —
applying a unitary to `(1/√r) · ∑_k |ψ_k⟩` becomes `(1/√r) · ∑_k uc_eval
U · |ψ_k⟩` via these. No new axioms; each is a one-line wrapper around
mathlib's existing matrix-distributivity. -/

/-- **`uc_eval` distributes over finite sums** (Phase 4.D). Direct lift
of `Matrix.mul_sum`. -/
theorem uc_eval_mul_sum {dim r : Nat} (U : FormalRV.Framework.BaseUCom dim)
    (v : Fin r → Matrix (Fin (2^dim)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval U * (∑ i : Fin r, v i)
      = ∑ i : Fin r, FormalRV.Framework.uc_eval U * v i :=
  Matrix.mul_sum _ _ _

/-- **`uc_eval` commutes with scalar multiplication** (Phase 4.D).
Direct lift of `Matrix.mul_smul`. -/
theorem uc_eval_mul_smul {dim : Nat} (U : FormalRV.Framework.BaseUCom dim)
    (c : ℂ) (v : Matrix (Fin (2^dim)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval U * (c • v)
      = c • (FormalRV.Framework.uc_eval U * v) :=
  Matrix.mul_smul _ _ _

/-- **`uc_eval` distributes over scalar-multiplied sums** (Phase 4.D).
Combined form of `uc_eval_mul_sum` + `uc_eval_mul_smul`. This is the
exact pattern needed for the QPE orbit step: `U * (∑ c_i · |v_i⟩) =
∑ c_i · (U · |v_i⟩)`. -/
theorem uc_eval_mul_sum_smul {dim r : Nat} (U : FormalRV.Framework.BaseUCom dim)
    (c : Fin r → ℂ) (v : Fin r → Matrix (Fin (2^dim)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval U * (∑ i : Fin r, c i • v i)
      = ∑ i : Fin r, c i • (FormalRV.Framework.uc_eval U * v i) := by
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Matrix.mul_smul _ _ _

end FormalRV.SQIRPort
