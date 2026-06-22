/-
  FormalRV.Shor.CFS.RNSModulusExistence — the SIZE-UNBOUNDED RNS-modulus existence is provable, and
  WHY that does NOT settle the paper's (small-prime) conjecture `SmallPrimeRNSModulusExists`.

  ## The finding

  `SmallPrimeRNSModulusExists N m f ℓ` (in `CFS.Assumptions`) — Gidney 2025 Assumption 1 — asks for
  `ℓ`-BIT primes whose product is `≥ N^m` and within `N/2^f` of a multiple of `N`.  The `ℓ`-bit
  (small-prime) clause is the whole point: it keeps the residue-number-system registers small.

  DROP that clause and you get `UnboundedPrimeRNSModulusExists` (below).  This weaker statement is
  EASY: by **Dirichlet's theorem** there are infinitely many primes `≡ 1 (mod N)`; the product of any
  number of them is `≡ 1 (mod N)`, so its modular deviation is exactly `min(1, N-1) = 1`, which is
  `< N/2^f` as soon as `2^f < N` (true for RSA: `N ≈ 2^2048`, `f = 32`).  Taking `m` such primes
  (each `> N`) also gives product `≥ N^m`.  This is `unboundedRNSModulus_of_lt_two_pow` — a genuine,
  axiom-clean proof.

  ## Why this is NOT the conjecture (honesty)

  The construction uses primes `≥ N + 1 ≈ 2^2048` — astronomically larger than the `ℓ`-bit
  (`ℓ ≈ 20`–`50`) primes the algorithm actually needs.  With the bit bound restored, the problem
  becomes the real one: can a product of SMALL primes be driven to within `N/2^f` of a multiple of
  `N`?  That is an equidistribution / subset-product question with only numerical evidence in the
  paper — it stays the named assumption `SmallPrimeRNSModulusExists`.

  `smallPrimeRNSModulus_imp_unbounded` records that the genuine (small-prime) assumption implies this
  weak one — confirming the weak one is strictly weaker.  We do NOT wire
  `unboundedRNSModulus_of_lt_two_pow` into any downstream result, so the pipeline is not silently made
  unconditional on this technicality; downstream carries `SmallPrimeRNSModulusExists`.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CFS.Assumptions

namespace FormalRV.CFS

open scoped BigOperators

/-- The `ℓ`-bit-free weakening of `SmallPrimeRNSModulusExists`: distinct primes (ANY size) whose
    product is `≥ N^m` and within `N/2^f` of a multiple of `N`.  Provable (below), hence too weak to
    be the paper's conjecture. -/
def UnboundedPrimeRNSModulusExists (N m f : ℕ) : Prop :=
  ∃ (t : ℕ) (p : Fin t → ℕ),
    (∀ i j, i ≠ j → Nat.Coprime (p i) (p j)) ∧
    (∀ i, (p i).Prime) ∧
    N ^ m ≤ ∏ i, p i ∧
    modDev N (∏ i, p i) 0 * 2 ^ f < N

/-- The genuine (small-prime) assumption implies the size-unbounded one (just forget the `ℓ`-bit
    clause) — so `UnboundedPrimeRNSModulusExists` is the WEAKER statement. -/
theorem smallPrimeRNSModulus_imp_unbounded {N m f ℓ : ℕ}
    (h : SmallPrimeRNSModulusExists N m f ℓ) : UnboundedPrimeRNSModulusExists N m f := by
  obtain ⟨t, p, hcop, hpr, _hbit, hge, hdev⟩ := h
  exact ⟨t, p, hcop, hpr, hge, hdev⟩

/-! ### A strictly increasing sequence of primes `≡ 1 (mod N)` (Dirichlet). -/

/-- The next prime `> k` with `p ≡ 1 (mod N)` (Dirichlet's theorem on primes in `1 + Nℤ`). -/
noncomputable def nextPrime1 (N k : ℕ) (hN : N ≠ 0) : ℕ :=
  (Nat.forall_exists_prime_gt_and_modEq k (q := N) (a := 1) hN (Nat.coprime_one_left N)).choose

theorem nextPrime1_spec (N k : ℕ) (hN : N ≠ 0) :
    k < nextPrime1 N k hN ∧ (nextPrime1 N k hN).Prime ∧ nextPrime1 N k hN ≡ 1 [MOD N] :=
  (Nat.forall_exists_prime_gt_and_modEq k (q := N) (a := 1) hN (Nat.coprime_one_left N)).choose_spec

/-- The sequence: `seqPrime1 0 > N`, and each `seqPrime1 (i+1) > seqPrime1 i`. -/
noncomputable def seqPrime1 (N : ℕ) (hN : N ≠ 0) : ℕ → ℕ
  | 0 => nextPrime1 N N hN
  | (i + 1) => nextPrime1 N (seqPrime1 N hN i) hN

theorem seqPrime1_prime (N : ℕ) (hN : N ≠ 0) (i : ℕ) : (seqPrime1 N hN i).Prime := by
  cases i with
  | zero => exact (nextPrime1_spec N N hN).2.1
  | succ k => exact (nextPrime1_spec N (seqPrime1 N hN k) hN).2.1

theorem seqPrime1_modEq (N : ℕ) (hN : N ≠ 0) (i : ℕ) : seqPrime1 N hN i ≡ 1 [MOD N] := by
  cases i with
  | zero => exact (nextPrime1_spec N N hN).2.2
  | succ k => exact (nextPrime1_spec N (seqPrime1 N hN k) hN).2.2

theorem seqPrime1_lt_succ (N : ℕ) (hN : N ≠ 0) (i : ℕ) :
    seqPrime1 N hN i < seqPrime1 N hN (i + 1) :=
  (nextPrime1_spec N (seqPrime1 N hN i) hN).1

theorem seqPrime1_strictMono (N : ℕ) (hN : N ≠ 0) : StrictMono (seqPrime1 N hN) :=
  strictMono_nat_of_lt_succ (seqPrime1_lt_succ N hN)

theorem seqPrime1_gt (N : ℕ) (hN : N ≠ 0) (i : ℕ) : N < seqPrime1 N hN i := by
  induction i with
  | zero => exact (nextPrime1_spec N N hN).1
  | succ k ih => exact lt_trans ih (seqPrime1_lt_succ N hN k)

/-! ### Discharging the size-unbounded statement. -/

/-- **★ `UnboundedPrimeRNSModulusExists` holds whenever `2^f < N` (and `1 < N`). ★**  Construction:
    `m` distinct primes `≡ 1 (mod N)` (Dirichlet), each `> N`.  Their product is `≡ 1 (mod N)` (so the
    modular deviation is `1 < N/2^f`) and `≥ N^m`.  **CAVEAT:** the primes are `≥ N+1`, so this does
    NOT satisfy the paper's `ℓ`-bit constraint (`SmallPrimeRNSModulusExists`); it shows only that the
    size-unbounded statement, lacking that bound, is too weak to be the real conjecture. -/
theorem unboundedRNSModulus_of_lt_two_pow (N m f : ℕ) (h1N : 1 < N) (hf : 2 ^ f < N) :
    UnboundedPrimeRNSModulusExists N m f := by
  have hN : N ≠ 0 := by omega
  refine ⟨m, fun i : Fin m => seqPrime1 N hN i, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hvalne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    have hne : seqPrime1 N hN i ≠ seqPrime1 N hN j := (seqPrime1_strictMono N hN).injective.ne hvalne
    exact (Nat.coprime_primes (seqPrime1_prime N hN i) (seqPrime1_prime N hN j)).mpr hne
  · exact fun i => seqPrime1_prime N hN i
  · calc N ^ m = ∏ _i : Fin m, N := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i : Fin m, seqPrime1 N hN i :=
            Finset.prod_le_prod' (fun i _ => le_of_lt (seqPrime1_gt N hN i))
  · set P := ∏ i : Fin m, seqPrime1 N hN i with hP
    have hcast : (P : ZMod N) = 1 := by
      rw [hP, Nat.cast_prod]
      refine Finset.prod_eq_one (fun i _ => ?_)
      rw [← Nat.cast_one]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (seqPrime1_modEq N hN i)
    have hPmod : P ≡ 1 [MOD N] := by
      have : (P : ZMod N) = ((1 : ℕ) : ZMod N) := by rw [hcast, Nat.cast_one]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
    have hLmod : P % N = 1 := by
      have h : P % N = 1 % N := hPmod
      rwa [Nat.mod_eq_of_lt h1N] at h
    have hf1 : fwdDist N P 0 = 1 := by
      unfold fwdDist
      rw [hLmod, Nat.zero_mod, Nat.sub_zero, Nat.add_comm 1 N, Nat.add_mod_left,
          Nat.mod_eq_of_lt h1N]
    have hf2 : fwdDist N 0 P = N - 1 := by
      unfold fwdDist
      rw [hLmod, Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt (by omega : N - 1 < N)]
    have hdev : modDev N P 0 = 1 := by unfold modDev; rw [hf1, hf2]; omega
    rw [hdev, one_mul]; exact hf

/-! ## The discharge results pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean unboundedRNSModulus_of_lt_two_pow
#verify_clean smallPrimeRNSModulus_imp_unbounded

end FormalRV.CFS
