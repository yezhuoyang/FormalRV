import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.Determinant
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Data.Int.GCD
import FormalRV.Core.QuantumGate
import FormalRV.Core.QuantumLib
import FormalRV.Shor.QPE
import FormalRV.Shor.QPEAmplitude
import FormalRV.Shor.Eigenstate
import FormalRV.Shor.TotientLowerBound
import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement

namespace FormalRV.SQIRPort

/-- **`Shor_correct_var_conditional`** (added 2026-05-24; expanded
2026-05-24 18:55 with structural-blocker note): the fully-conditional
form of `Shor_correct_var`. Takes the two remaining deep obligations
(`QPE_MMI_correct` and `phi_n_over_n_lowerbound`) as explicit
universally-quantified hypotheses, so the theorem's own axiom
dependence is exactly the standard kernel (`propext`,
`Classical.choice`, `Quot.sound`).

This is the right shape for callers who can supply weaker, problem-
specific versions of the two hypotheses (e.g., a smaller `r` range
where the totient bound is decidable, or an alternative QPE
correctness theorem). It is also the cleanest separation of the
quantum + post-processing chain (Lean-proved here) from the two
external deep results (QPE 4/π² distribution and Mertens-style
totient density).

`Shor_correct_var` (below) recovers the original axiom-using
statement by instantiating these hypotheses with the corresponding
axioms.

## Why the two hypotheses are NOT mere "missing-tactic" gaps

**`h_QPE_MMI_correct`** is not a closeable Lean lemma in the current
framework. It depends on the correctness of *controlled single-qubit
gates*, but `Framework/UnitaryOps.lean:972` defines

  `control q (UCom.app1 _ _) = SKIP`

as a deliberate `TODO(BQAlgo)` placeholder. This stub erases every
single-qubit gate inside a controlled circuit. Because QPE's phase
kickback works precisely by inserting controlled-U at each
precision-bit position, the stub makes
`uc_eval (controlled_powers (lifted f) m)` independent of `f`'s
eigenphase — exactly the dependence QPE_var_on_eigenstate's
conclusion needs. Closing this hypothesis requires:

  1. defining `controlled_R q n θ φ λ` as the standard 2-CNOT +
     3-rotation decomposition;
  2. replacing the `app1` SKIP case with `controlled_R`;
  3. proving `uc_eval_controlled_R_correct` (the 4×4 block-matrix
     equality, ~200–500 LOC);
  4. reviewing ~110 existing references to `control` for theorems
     that silently relied on the SKIP behavior.

See `notes/control-stub-fix-scope.md` for the full enumeration.

**`h_phi_n_over_n_lowerbound`** is not arithmetic automation. It is
the Mertens-third-theorem-style lower bound

  `φ(r)/r ≥ exp(-2) / (log₂ N)^4` for `r ≤ N`.

Mathlib currently provides only upper bounds on `Nat.totient`
(`Nat.totient_le`, `Nat.totient_lt`, plus algebraic identities like
`Nat.totient_mul`); no Mertens-style lower bound is available in
usable form. The trivial weakening `φ(r)/r ≥ 1/r` is arithmetically
insufficient (requires `r ≤ e²·(log₂ N)^4`, fails for `r` near `N`).
SQIR's own proof routes through an external Coq `euler` library
(see `notes/shor-remaining-axioms.md` for the full roadmap). -/
theorem Shor_correct_var_conditional
    (a r N m n anc : Nat) (u : Nat → BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_modmul : ModMulImpl a N n anc u)
    (h_wt : ∀ i, i < m → uc_well_typed (u i))
    (h_QPE_MMI_correct :
      ∀ (a' r' N' m' n' anc' k' : Nat) (f' : Nat → BaseUCom (n' + anc')),
        BasicSetting a' r' N' m' n' →
        ModMulImpl a' N' n' anc' f' →
        (∀ i, i < m' → uc_well_typed (f' i)) →
        k' < r' →
        prob_partial_meas (basis_vector (2^m') (s_closest m' k' r'))
            (Shor_final_state m' n' anc' f')
          ≥ 4 / (Real.pi^2 * (r' : ℝ)))
    (h_phi_n_over_n_lowerbound :
      ∀ (r' N' : Nat), 0 < r' → r' ≤ N' →
        ((Nat.totient r' : ℝ) / (r' : ℝ))
          ≥ Real.exp (-2) / (Nat.log2 N' : ℝ)^4) :
    probability_of_success a r N m n anc u ≥ κ / (Nat.log2 N : ℝ)^4 := by
  -- Unpack BasicSetting
  obtain ⟨⟨h_a_pos, h_a_lt⟩, h_ord, ⟨h_Nsq_lt, h_2m⟩, ⟨h_N_lt, h_2n⟩⟩ := h_basic
  have h_r_pos : 0 < r := h_ord.1
  have h_N_pos : 0 < N := by omega
  have h_r_lt_N : r < N := Order_r_lt_N a r N h_N_pos h_ord
  have h_r_le_N : r ≤ N := Nat.le_of_lt h_r_lt_N
  have h_r_pos_R : (0 : ℝ) < r := by exact_mod_cast h_r_pos
  have h_r_ne_R : (r : ℝ) ≠ 0 := ne_of_gt h_r_pos_R
  -- The integrand
  set f : Nat → ℝ := fun x =>
      r_found x m r a N *
        prob_partial_meas (basis_vector (2^m) x) (Shor_final_state m n anc u)
    with hf_def
  -- Non-negativity of f
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    refine mul_nonneg ?_ (prob_partial_meas_nonneg _ _)
    unfold r_found
    split_ifs <;> norm_num
  -- Step 1: Σ_{x<2^m} f(x) ≥ Σ_{i<r} f(s_closest m i r), via subset+injectivity.
  have h_step1 :
      ∑ i ∈ Finset.range r, f (s_closest m i r)
        ≤ ∑ x ∈ Finset.range (2^m), f x := by
    rw [show (∑ i ∈ Finset.range r, f (s_closest m i r))
          = ∑ x ∈ (Finset.range r).image (fun i => s_closest m i r), f x from ?_]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        rw [Finset.mem_range] at hi ⊢
        exact s_closest_ub a r N m n i ⟨⟨h_a_pos, h_a_lt⟩, h_ord, ⟨h_Nsq_lt, h_2m⟩, ⟨h_N_lt, h_2n⟩⟩ hi
      · intro x _ _; exact hf_nonneg x
    · rw [Finset.sum_image]
      intros i hi j hj heq
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      exact s_closest_injective a r N m n
        ⟨⟨h_a_pos, h_a_lt⟩, h_ord, ⟨h_Nsq_lt, h_2m⟩, ⟨h_N_lt, h_2n⟩⟩ i j hi hj heq
  -- Step 2: per-term lower bound for i coprime to r.
  -- Define g(i) := (Nat.gcd i r == 1) * 4/(π²·r)
  set g : Nat → ℝ := fun i =>
    (if Nat.gcd i r = 1 then (1 : ℝ) else 0) * (4 / (Real.pi^2 * (r : ℝ)))
    with hg_def
  have h_step2 :
      ∀ i ∈ Finset.range r, g i ≤ f (s_closest m i r) := by
    intro i hi
    rw [Finset.mem_range] at hi
    show g i ≤ f (s_closest m i r)
    by_cases hcop : Nat.gcd i r = 1
    · -- coprime case
      show (if Nat.gcd i r = 1 then (1:ℝ) else 0) * (4 / (Real.pi^2 * (r:ℝ)))
            ≤ r_found (s_closest m i r) m r a N *
                prob_partial_meas (basis_vector (2^m) (s_closest m i r))
                  (Shor_final_state m n anc u)
      rw [if_pos hcop, one_mul]
      have h_rf : r_found (s_closest m i r) m r a N = 1 :=
        r_found_1 a r N m n i
          ⟨⟨h_a_pos, h_a_lt⟩, h_ord, ⟨h_Nsq_lt, h_2m⟩, ⟨h_N_lt, h_2n⟩⟩ hi hcop
      rw [h_rf, one_mul]
      exact h_QPE_MMI_correct a r N m n anc i u
        ⟨⟨h_a_pos, h_a_lt⟩, h_ord, ⟨h_Nsq_lt, h_2m⟩, ⟨h_N_lt, h_2n⟩⟩ h_modmul h_wt hi
    · -- non-coprime case: g(i) = 0 ≤ f(s_closest)
      show (if Nat.gcd i r = 1 then (1:ℝ) else 0) * (4 / (Real.pi^2 * (r:ℝ)))
            ≤ f (s_closest m i r)
      rw [if_neg hcop, zero_mul]
      exact hf_nonneg _
  -- Step 3: Σ g over [0, r) = (4/(π²·r)) · ϕ(r)
  have h_step3 :
      ∑ i ∈ Finset.range r, g i
        = (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ) := by
    show (∑ i ∈ Finset.range r,
           (if Nat.gcd i r = 1 then (1:ℝ) else 0) * (4 / (Real.pi^2 * (r:ℝ))))
          = (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ)
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    -- Σ_{i<r} (if Nat.gcd i r = 1 then 1 else 0) = ϕ(r)
    rw [Nat.totient]
    push_cast
    rw [show ((Finset.range r).filter (Nat.Coprime r)).card
          = ((Finset.range r).filter (fun i => Nat.gcd i r = 1)).card from ?_]
    · rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
          Nat.smul_one_eq_cast, Finset.filter_congr_decidable]
    · congr 1; ext i; simp [Nat.Coprime, Nat.coprime_comm]
  -- Step 4: bound by Euler totient
  have h_step4 :
      (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ)
        ≥ κ / (Nat.log2 N : ℝ)^4 := by
    have h_phi : ((Nat.totient r : ℝ) / (r : ℝ))
                  ≥ Real.exp (-2) / (Nat.log2 N : ℝ)^4 :=
      h_phi_n_over_n_lowerbound r N h_r_pos h_r_le_N
    have h_pi_sq : (0 : ℝ) < Real.pi^2 := pow_pos Real.pi_pos 2
    -- (4/(π²·r)) · ϕ(r) = (4/π²) · (ϕ(r)/r)
    have h_rewrite :
        (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ)
          = (4 / Real.pi^2) * ((Nat.totient r : ℝ) / (r : ℝ)) := by
      field_simp
    rw [h_rewrite]
    -- κ/(log₂ N)^4 = (4/π²) · exp(-2)/(log₂ N)^4
    have h_κ : κ / (Nat.log2 N : ℝ)^4
              = (4 / Real.pi^2) * (Real.exp (-2) / (Nat.log2 N : ℝ)^4) := by
      unfold κ; field_simp
    rw [h_κ]
    -- Both factors positive; reduce to ϕ/r ≥ exp(-2)/log^4
    apply mul_le_mul_of_nonneg_left h_phi
    positivity
  -- Combine: probability_of_success = Σ_x f(x) ≥ Σ_i f(s_closest) ≥ Σ_i g(i) = κ/log^4.
  unfold probability_of_success
  have h_chain :
      κ / (Nat.log2 N : ℝ)^4
        ≤ ∑ x ∈ Finset.range (2^m),
            r_found x m r a N *
              prob_partial_meas (basis_vector (2^m) x) (Shor_final_state m n anc u) := by
    calc κ / (Nat.log2 N : ℝ)^4
        ≤ (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ) := h_step4
      _ = ∑ i ∈ Finset.range r, g i := h_step3.symm
      _ ≤ ∑ i ∈ Finset.range r, f (s_closest m i r) :=
            Finset.sum_le_sum h_step2
      _ ≤ ∑ x ∈ Finset.range (2^m), f x := h_step1
  exact h_chain

/-- **`Shor_correct_var_from_QPE_and_totient`** — discoverable alias
for `Shor_correct_var_conditional`. Same statement, more descriptive
name making the two external assumptions explicit. Kernel-clean
(no new axioms; identical proof obligations).

See `Shor_correct_var_conditional` above for the full docstring
including the structural-blocker analysis. -/
theorem Shor_correct_var_from_QPE_and_totient
    (a r N m n anc : Nat) (u : Nat → BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_modmul : ModMulImpl a N n anc u)
    (h_wt : ∀ i, i < m → uc_well_typed (u i))
    (h_QPE_MMI_correct :
      ∀ (a' r' N' m' n' anc' k' : Nat) (f' : Nat → BaseUCom (n' + anc')),
        BasicSetting a' r' N' m' n' →
        ModMulImpl a' N' n' anc' f' →
        (∀ i, i < m' → uc_well_typed (f' i)) →
        k' < r' →
        prob_partial_meas (basis_vector (2^m') (s_closest m' k' r'))
            (Shor_final_state m' n' anc' f')
          ≥ 4 / (Real.pi^2 * (r' : ℝ)))
    (h_phi_n_over_n_lowerbound :
      ∀ (r' N' : Nat), 0 < r' → r' ≤ N' →
        ((Nat.totient r' : ℝ) / (r' : ℝ))
          ≥ Real.exp (-2) / (Nat.log2 N' : ℝ)^4) :
    probability_of_success a r N m n anc u ≥ κ / (Nat.log2 N : ℝ)^4 :=
  Shor_correct_var_conditional a r N m n anc u h_basic h_modmul h_wt
    h_QPE_MMI_correct h_phi_n_over_n_lowerbound

-- `Shor_correct_var` moved to `PostQFT.lean` (2026-05-27) so it can use
-- the new `theorem QPE_MMI_correct` (proved via the LSB pipeline) in
-- place of the deleted axiom of the same name.

/-! ## §5. The specialised version (Coq: `Shor.v:1295`).

`Shor_correct` is `Shor_correct_var` instantiated at the concrete
modular-multiplication circuit family that SQIR builds from RCIR.
TIER1 records the statement; the specific `f_modmult_circuit` is
axiomatised pending the RCIR port.
-/

/-- Ancilla qubit count used by the reversible modular-multiplication
circuit (Coq: `ModMult.v` `modmult_rev_anc`).
**Closed 2026-05-23**: realized as `2*n + 1` — a generic upper bound
sufficient for downstream typing. The specific RCIR implementation
in Coq uses a similar linear-in-n count. -/
def modmult_rev_anc (n : Nat) : Nat := 2 * n + 1

/-- The RCIR-derived modular-multiplication oracle family
(Coq: `Shor.v:118` `f_modmult_circuit`).

**DEPRECATED (2026-05-29, Tick 84):** This is a placeholder axiom.
The verified replacement is `FormalRV.BQAlgo.f_modmult_circuit_verified_bits`,
which is constructively defined (not axiomatic) and built on the
SQIR-faithful modular multiplier `sqir_modmult_MCP_gate`.  For
end-to-end Shor correctness without this axiom, cite
`FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms`. -/
@[deprecated "Use FormalRV.BQAlgo.f_modmult_circuit_verified_bits and cite FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms" (since := "2026-05-29")]
axiom f_modmult_circuit :
  (a ainv N n : Nat) → Nat → BaseUCom (n + modmult_rev_anc n)

/-- The modular inverse of `a` mod `N`
(Coq: `NumTheory.v` `modinv`).

**Closed 2026-05-23 as a constructive def** (Phase 2 axiom #4):
Defined via mathlib's `Nat.gcdA` (extended Euclidean algorithm):
Bezout gives `a * Nat.gcdA a N + N * Nat.gcdB a N = gcd(a, N)`.
When `a` is coprime to `N`, the first coefficient is the inverse
modulo `N`. We reduce it mod `N` and convert back to `Nat`. -/
def modinv (a N : Nat) : Nat :=
  ((Nat.gcdA a N) % (N : Int)).toNat

/-- The multiplicative order of `a` mod `N` as a function
(Coq: `NumTheory.v` `ord`).

**Closed 2026-05-23 as a constructive def** (Phase 2 axioms #2+#3):
Defined as `Nat.find` over the predicate `0 < k ∧ a^k % N = 1` when
that set is non-empty (which it is for `a` coprime to `N` via Euler);
returns 0 otherwise. `noncomputable` because the existence check
uses Classical decidability of `∃ k : Nat, ...`. -/
noncomputable def ord (a N : Nat) : Nat :=
  open Classical in
  if h : ∃ k, 0 < k ∧ a^k % N = 1 then Nat.find h else 0

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

/-! ### Tier-3 RCIR circuit-level supporting axioms (Coq: `ExtrShor.v`) -/

/-- The RCIR-derived `f_modmult_circuit` family satisfies `ModMulImpl`.

**DEPRECATED (2026-05-29, Tick 84):** The verified replacement is
`FormalRV.BQAlgo.f_modmult_circuit_verified_bits_MMI` (proven, not
axiomatic).  Cite `FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms`
for end-to-end Shor correctness. -/
@[deprecated "Use FormalRV.BQAlgo.f_modmult_circuit_verified_bits_MMI and cite FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms" (since := "2026-05-29")]
axiom f_modmult_circuit_MMI
    (a ainv N n : Nat)
    (_h_a_lt : a < N) (_h_ainv_lt : ainv < N)
    (_h_inv : a * ainv % N = 1) :
    ModMulImpl a N n (modmult_rev_anc n) (f_modmult_circuit a ainv N n)

/-- Every iterate of the RCIR `f_modmult_circuit` family is well-typed.

**DEPRECATED (2026-05-29, Tick 84):** The verified replacement is
`FormalRV.BQAlgo.f_modmult_circuit_verified_bits_uc_well_typed`
(proven, not axiomatic).  Cite
`FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms` for
end-to-end Shor correctness. -/
@[deprecated "Use FormalRV.BQAlgo.f_modmult_circuit_verified_bits_uc_well_typed and cite FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms" (since := "2026-05-29")]
axiom f_modmult_circuit_uc_well_typed
    (a ainv N n : Nat)
    (_h_N : 1 < N) (_h_a_lt : a < N) (_h_ainv_lt : ainv < N) :
    ∀ i, uc_well_typed (f_modmult_circuit a ainv N n i)

-- `Shor_correct` (the specialised version at `f_modmult_circuit`) moved
-- to `PostQFT.lean` (2026-05-27) so it can use the new `Shor_correct_var`
-- (proved via the LSB pipeline).

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

/-! ## §11. `QPE_var_on_eigenstate` — semantic foundation for QPE correctness

The hook directive (2026-05-24) asked for the central QPE semantic
theorem: for an eigenstate `ψ` of the family `f` with phase `θ` (i.e.,
`uc_eval (f i) * ψ = exp(2πi · 2^i · θ) • ψ`), evaluating `QPE_var m anc f`
on `|0^m⟩ ⊗ ψ` yields `kron_vec (qpe_phase_state m θ) ψ`.

This is the inner semantic step of SQIR's `QPE_semantics_full`
(`QPEGeneral.v` line 105, ~180 LOC of Coq + multi-file `QuantumLib`
support). Implementing it in Lean requires:

  1. **CRITICAL (primary blocker)**: replacing the current `control` STUB
     at `Framework/UnitaryOps.lean:972`. The stub definition is

         control q (UCom.app1 _ _) = SKIP

     which means `control q U` does NOT represent controlled-U when `U`
     contains single-qubit gates — instead it deletes them. Since QPE's
     `controlled_powers (lifted f)` is built from `control i (lifted (f i))`
     and the `f i` family contains the modular-multiplier circuit (which
     necessarily has single-qubit gates), this stub makes the entire
     QPE phase-estimation mechanism semantically vacuous for any `f` that
     isn't a pure-CNOT circuit. A correct implementation requires the
     full controlled-`R(θ,φ,λ)` Toffoli-style decomposition flagged
     `TODO(BQAlgo)` at line 962.
  2. Replacing the `QFTinv n = npar_H n` stub at `Framework/QPE.lean:36`
     with the real inverse QFT circuit.
  3. Proving inverse-QFT-on-superposition correctness (the
     `(1/√2^k) · ∑_x exp(2πi · x · θ) |x⟩ ↦ qpe_phase_state k θ` step).
  4. Proving the `controlled_powers` cascade: on input
     `(npar_H k ⊗ I) (|0^k⟩ ⊗ ψ)`, output is
     `(1/√2^k) · ∑_x exp(2πi · x · θ) |x⟩ ⊗ ψ`. Needs (1).
  5. Tensor / `pad_u` linearity over `kron_vec` summands. The framework
     currently has ZERO `pad_u`-on-`kron_vec` interaction lemmas (grep
     `Framework/` for `pad_u.*kron_vec`).
  6. The `map_qubits (·+m) ∘ f` shift's preservation of eigenstate action
     on the `ψ` register (via `pad_u` block-disjoint commutativity).

Per the hook's fallback clause ("If the full theorem is too hard, prove
the smallest kernel-clean semantic helper and report the exact blocker"),
this tick delivers the **m = 0 base case** — the ONLY case where the
theorem can be settled with the current framework, because:

- At `m = 0`, the `controlled_powers (lifted f) 0 = SKIP` by
  `controlled_powers_zero` — the stubbed `control` is never invoked.
- The `QFTinv 0 = SKIP` and `npar_H 0 = SKIP`, so the QFTinv stub is
  also bypassed.
- The eigenstate hypothesis is vacuously satisfied: the circuit never
  touches `ψ`.

For any `m ≥ 1`, the stubbed `control` (item 1) is invoked at the
`(lifted f) 0` step of `controlled_powers`, and the proof becomes
unsound (it would conclude that `QPE_var 1 anc f * (|0⟩ ⊗ ψ) =
(H ⊗ I) * (kron_zeros 1 ⊗ ψ)` regardless of `f`'s eigenphase, which
contradicts the conclusion `kron_vec (qpe_phase_state 1 θ) ψ` for
nonzero θ). This is not an "infrastructure missing" gap — it's an
"infrastructure deliberately wrong" gap. **Item 1 must close before
any m ≥ 1 case is even well-posed.**

**Strict-honesty summary**: The general-m `QPE_var_on_eigenstate`
theorem **cannot be proven** in this framework as it currently stands —
not because the proof is hard, but because the `control` primitive
does not implement what its docstring claims. Any attempt would either
add `axiom`s (forbidden by the directive) or use `sorry` (forbidden by
the directive). The only honest, sorry-free, axiom-free deliverable
is the m = 0 case below, plus this explicit infrastructure-bug report.

Estimated scope to close items 1–6 per `Framework/QPE.lean:357`:
~1500 LOC (items 1–2 being pure circuit constructions, items 3–6 being
the multi-file proof body). -/

/-- **QPE_var at m = 0 evaluates to the identity matrix** (when the
data register is non-empty). Direct unfolding: `QPE_var 0 anc f` is
`seq (npar_H 0) (seq (controlled_powers c 0) (QFTinv 0))`, and all
three components are `SKIP`, evaluating to the `dim = anc` identity. -/
theorem QPE_var_zero_eq_one (anc : Nat) (h : 0 < anc)
    (f : Nat → BaseUCom anc) :
    FormalRV.Framework.uc_eval (QPE_var 0 anc f) =
      (1 : FormalRV.Framework.Square (0 + anc)) := by
  unfold QPE_var
  rw [FormalRV.Framework.BaseUCom.uc_eval_QPE]
  have hd : 0 < 0 + anc := by omega
  rw [FormalRV.Framework.BaseUCom.uc_eval_QFTinv_zero_eq_one hd,
      FormalRV.Framework.BaseUCom.uc_eval_controlled_powers_zero_eq_one _ hd,
      FormalRV.Framework.BaseUCom.uc_eval_npar_H_zero_eq_one hd,
      Matrix.one_mul, Matrix.one_mul]

/-- **QPE_var_on_eigenstate — m = 0 base case** (the smallest kernel-clean
semantic helper per the hook directive).

For any data-register state `ψ` and phase `θ`, evaluating `QPE_var 0 anc f`
on `kron_vec (kron_zeros 0) ψ` yields `kron_vec (qpe_phase_state 0 θ) ψ`.
The eigenstate hypothesis on `f` is not required at `m = 0` because the
zero-precision QPE circuit is the identity and never invokes `f`.

Proof: `QPE_var 0 anc f` evaluates to the identity (via
`QPE_var_zero_eq_one`), so the LHS simplifies to
`kron_vec (kron_zeros 0) ψ`. Pointwise, both `kron_zeros 0` and
`qpe_phase_state 0 θ` are the single-entry matrix with value `1` at
index `0 : Fin 1` — the former by `basis_vector` definition, the latter
because `qpe_amp 0 0 θ = 1` (the empty `Fin 1`-sum collapses to
`exp(0) = 1`). The two kron_vecs are therefore pointwise equal. -/
theorem QPE_var_on_eigenstate_zero (anc : Nat) (h : 0 < anc)
    (f : Nat → BaseUCom anc) (θ : ℝ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval (QPE_var 0 anc f) *
        (FormalRV.Framework.kron_vec
          (FormalRV.Framework.kron_zeros 0) ψ :
         Matrix (Fin (2^(0 + anc))) (Fin 1) ℂ)
      = FormalRV.Framework.kron_vec
          (FormalRV.Framework.qpe_phase_state 0 θ) ψ := by
  rw [QPE_var_zero_eq_one anc h f, Matrix.one_mul]
  ext i j
  rw [FormalRV.Framework.kron_vec_apply,
      FormalRV.Framework.kron_vec_apply]
  have h_idx :
      (FormalRV.Framework.kron_vec_high i :
        Fin (2^0)).val = 0 := by
    have hlt := (FormalRV.Framework.kron_vec_high i :
                 Fin (2^0)).isLt
    have h2 : (2^0 : Nat) = 1 := pow_zero 2
    omega
  have h_zeros :
      FormalRV.Framework.kron_zeros 0
        (FormalRV.Framework.kron_vec_high i) 0 = 1 := by
    unfold FormalRV.Framework.kron_zeros
    exact FormalRV.Framework.basis_vector_apply_eq _ _ _ _ h_idx
  have h_phase :
      FormalRV.Framework.qpe_phase_state 0 θ
        (FormalRV.Framework.kron_vec_high i) 0 = 1 := by
    rw [FormalRV.Framework.qpe_phase_state_apply, h_idx]
    unfold FormalRV.Framework.qpe_amp
    simp [pow_zero]
  rw [h_zeros, h_phase]

/-! ## §12. Dim-cast bridge (Phase 4.E)

Two helpers for the dim-equality `2^(m + (n + anc)) = 2^m * 2^n * 2^anc`
that bridges between `QPE_var`'s natural output dimension and
`Shor_final_state`'s product-form `QState` type. The first is the bare
Nat equality; the second shows that `prob_partial_meas` is invariant
under `QState.cast` over any dim equality.

Together they let the user of `QPE_MMI_correct_assuming_orbit_factorization`
discharge the third conjunct of `h_orbit_exists` (the probability
equality between `Shor_final_state` and the orbit-superposition
`actual_state`) by exhibiting `actual_state` as a cast of a vector
on `Fin (2^(m + (n + anc)))`. -/

/-- **Dim-equality bridge** for the Shor combined-register product
form: `2^(m + (n + anc)) = 2^m * 2^n * 2^anc`. Pure Nat fact: two
applications of `pow_add` + `mul_assoc`. -/
theorem dim_assoc_eq (m n anc : Nat) :
    2^(m + (n + anc)) = 2^m * 2^n * 2^anc := by
  rw [pow_add, pow_add, mul_assoc]

/-- **`prob_partial_meas` is invariant under `QState.cast`**: for any
dim equality `h_eq : a = b`, the partial-measurement probability of
the cast vector equals that of the original. The proof uses `subst`
to reduce the cast to the identity (modulo `Subsingleton.elim` on
the `Fin 1` row index).

Used in the review chain to swap between `QState (2^(m + (n + anc)))`
(the natural output dimension of `uc_eval (QPE_var ...)`) and
`QState (2^m * 2^n * 2^anc)` (the product form used by
`Shor_final_state`'s signature). -/
theorem prob_partial_meas_cast {m_dim a b : Nat} (h_eq : a = b)
    (ψ : QState m_dim) (φ : QState a) :
    prob_partial_meas ψ (QState.cast h_eq φ : QState b)
      = prob_partial_meas ψ φ := by
  subst h_eq
  have h_eq_state : (QState.cast rfl φ : QState a) = φ := by
    unfold QState.cast
    funext i j
    have hj : j = 0 := Subsingleton.elim j 0
    rw [hj]; simp
  rw [h_eq_state]

/-! ## §13. Tightened conditional: `QPE_MMI_correct_modulo_qpe_semantics`

`QPE_MMI_correct_assuming_orbit_factorization` (§10.x) takes the entire
`h_orbit_exists` existential as a single hypothesis, packaging both
the (now-proven) orbit-side requirements and the (still-blocked) QPE
circuit-semantics step.

With Phase 4.A/4.C/4.D/4.E complete (the orbit-side infrastructure in
`SQIRPort/Eigenstate.lean`), we can substitute the proven β family
(`modmult_eigenstate_combined`) and the orbit-superposition state
(`shor_orbit_state` below) into the existential, leaving only the
single state-equality hypothesis `h_qpe_semantics` — which IS the
4.B circuit-semantics step. This narrows the "what's left to prove"
surface to one named identity. -/

/-- **Shor orbit-superposition state**: the closed-form
`(1/√r) · ∑_{k<r} qpe_phase_state_m(k/r) ⊗ ψ_k^{combined}` that the
QPE_var circuit IDEALLY outputs on input `|0^m⟩ ⊗ |1⟩_n ⊗ |0⟩_anc`.

Used as the `actual_state` witness in the tighter
`QPE_MMI_correct_modulo_qpe_semantics` conditional. -/
noncomputable def shor_orbit_state (a r N m n anc : Nat) :
    Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ :=
  fun i j => (1 / (Real.sqrt r : ℂ)) *
    ((∑ j_idx : Fin r,
       FormalRV.Framework.kron_vec
         (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
         (modmult_eigenstate_combined a r N n anc j_idx))
      i j)

/-- **`QPE_MMI_correct_modulo_qpe_semantics`** (Phase 4 tightened
conditional): strictly stronger than
`QPE_MMI_correct_assuming_orbit_factorization` because it discharges
the orbit-side conjuncts (orthonormality + state factorization) using
the now-proven `modmult_eigenstate_combined` + its orthonormality
theorem.

The only remaining hypothesis is the genuine 4.B QPE circuit-semantics
step: the equality
`prob_partial_meas Shor_final_state = prob_partial_meas shor_orbit_state`,
i.e., that QPE_var applied to the Shor input state actually produces
the orbit-superposition closed form (modulo measurement-probability
equivalence).

This is the maximal closure achievable WITHOUT fixing the `control`
stub at `Framework/UnitaryOps.lean:972`. Closing the `h_qpe_semantics`
hypothesis ⟹ closing `QPE_MMI_correct`. -/
theorem QPE_MMI_correct_modulo_qpe_semantics
    (a r N m n anc k : Nat) (f : Nat → BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_mmi : ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_qpe_semantics :
      prob_partial_meas (basis_vector (2^m) (s_closest m k r))
          (Shor_final_state m n anc f)
        = prob_partial_meas (basis_vector (2^m) (s_closest m k r))
              (shor_orbit_state a r N m n anc)) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  apply QPE_MMI_correct_assuming_orbit_factorization a r N m n anc k f
    h_basic h_mmi h_wt h_k_lt
  obtain ⟨⟨h_a_pos, h_a_lt⟩, h_ord, _, h_n_bounds⟩ := h_basic
  obtain ⟨h_r_pos, h_arN, h_min⟩ := h_ord
  have h_N_gt_one : 1 < N := by omega
  have h_N_lt_pow : N ≤ 2^n := h_n_bounds.1.le
  refine ⟨modmult_eigenstate_combined a r N n anc,
          shor_orbit_state a r N m n anc, ?_, rfl, h_qpe_semantics⟩
  intros j j'
  exact modmult_eigenstate_combined_orthonormal a r N n anc h_r_pos h_arN h_min
    h_N_gt_one h_N_lt_pow j j'

/-! ## Single-orbit action of the modular multiplier (toward the
modmult eigenstate eigenvalue theorem)

This section provides the smallest piece toward proving the
modular-multiplier EIGENSTATE eigenvalue relation
`uc_eval (f i) * ψ_k = exp(...) • ψ_k`: the action of `f i =
U^{a^{2^i}}` on a single orbit basis vector `|a^j mod N⟩|0⟩_anc`.
Combines `ModMulImpl` instantiated at `f i` with the power-product
identity `a^{2^i} · a^j = a^{2^i + j}`. -/

/-- **Single-orbit-basis-vector action**: `f i` (the QPE-i-th
controlled-power gadget, per `ModMulImpl`) applied to the orbit basis
state `|a^j mod N⟩ ⊗ |0⟩_anc` shifts the orbit position by `2^i`.

Specifically: `f i · |a^j mod N⟩ ⊗ |0⟩_anc = |a^(2^i + j) mod N⟩ ⊗ |0⟩_anc`.

This is the lifting of `MultiplyCircuitProperty (a^{2^i})` at the
orbit-input `x = a^j mod N` (which is always `< N` since `0 < N`),
plus the algebraic simplification `(a^{2^i}) · (a^j) % N = a^{2^i + j} % N`
via `Nat.mul_mod` + `pow_add`. -/
theorem MultiplyCircuitProperty_acts_on_orbit_basis
    (a N n anc i j : Nat)
    (f : Nat → BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_N_pos : 0 < N) :
    uc_eval (f i) (basis_vector (2^(n+anc)) ((a^j % N) * 2^anc))
    = basis_vector (2^(n+anc)) ((a^(2^i + j) % N) * 2^anc) := by
  have h_mcp := h_modmul i
  have h_lt : a^j % N < N := Nat.mod_lt _ h_N_pos
  have h_action := h_mcp (a^j % N) h_lt
  rw [h_action]
  congr 2
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← pow_add]

end FormalRV.SQIRPort
