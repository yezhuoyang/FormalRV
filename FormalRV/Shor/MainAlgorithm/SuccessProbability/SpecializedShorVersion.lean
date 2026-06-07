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
import FormalRV.QPE.QPE
import FormalRV.QPE.QPEAmplitude
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

end FormalRV.SQIRPort
