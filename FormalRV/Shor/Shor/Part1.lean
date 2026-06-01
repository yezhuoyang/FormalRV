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

namespace FormalRV.SQIRPort


/-! # Review status (as of 2026-05-24 01:08 PDT)

This file's headline theorems `Shor_correct_var` (Tier 2) and
`Shor_correct` (Tier 1) currently stand on the following custom
axioms (per `lean_verify`):

**`Shor_correct_var` (6 customs)**:
- `QPE_MMI_correct` — QPE outcome distribution bound; deep quantum
  complexity result, multi-day SQIR `QPEGeneral.v` port.
- `phi_n_over_n_lowerbound` — Euler totient lower bound `ϕ(r)/r ≥
  exp(-2)/(log N)^4`; Mertens-style, exact form lacks in mathlib.
- `r_found_1` — Continued-fraction recovery for coprime k. Mathlib-side
  chain assembled (Khinchin + denominator bound), but the cf_aux ↔
  GenContFract.of bridge for our `def ContinuedFraction` remains stuck.
- `Shor_final_state` — Post-QPE quantum state; opaque type-level axiom.
- `prob_partial_meas` — Born's-rule partial-measurement probability;
  opaque type-level axiom (honest Born's rule definition requires
  tensor products + projection — multi-tick effort).
- `prob_partial_meas_nonneg` — `0 ≤ prob_partial_meas`; trivial once
  prob_partial_meas is operationally defined.

**`Shor_correct` adds 3 more customs**:
- `f_modmult_circuit` — RCIR-derived modular-multiplier circuit;
  multi-week port from SQIR's `RCIR.v` + `ModMult.v`.
- `f_modmult_circuit_MMI` — Semantic correctness of the above;
  follows from RCIR port.
- `f_modmult_circuit_uc_well_typed` — Well-typedness of the above;
  trivial once f_modmult_circuit has a constructive def.

**Honest closures already done in this session** (Phase 1, 2, and most of
Phase 4 type-level): `Order_r_lt_N`, `s_closest_ub`, `s_closest_injective`,
`ContinuedFraction`, `ord`, `ord_Order`, `modinv`, `modinv_upper_bound`,
`Order_modinv_correct`, `BaseUCom`, `QState`, `basis_vector`,
`uc_well_typed`, `modmult_rev_anc`, `MultiplyCircuitProperty` (concrete
operational Prop), `uc_eval`. Net: 14 axioms → 6 axioms for Shor_correct_var.

**Mathlib-side r_found_1 infrastructure** (~280 lines): all helpers from
`s_closest_close_to_k_over_r` through `mathlib_OF_post_step_nat_mono_le`
+ `OF_post'_zero_or_modexp` + `OF_post'_dvd_r` + step-0 bridge. The
chain is complete EXCEPT for the cf_aux ↔ GenContFract.of bridge.
-/

/-! ## §1. QuantumLib primitives, axiomatised. -/

/-- A base unitary circuit on `n` qubits (Coq: `base_ucom n` from SQIR.UnitaryOps).
**Closed 2026-05-23**: realized as `FormalRV.Framework.BaseUCom`. -/
def BaseUCom (n : Nat) : Type := FormalRV.Framework.BaseUCom n

/-- Well-typedness predicate for unitary circuits (Coq: `uc_well_typed`).
**Closed 2026-05-23**: realized as `FormalRV.Framework.UCom.WellTyped`. -/
def uc_well_typed {n : Nat} (c : BaseUCom n) : Prop :=
  FormalRV.Framework.UCom.WellTyped n c

/-- A pure quantum state on a `dim`-dimensional Hilbert space.
**Closed 2026-05-23**: realized as a column vector (Matrix (Fin dim) (Fin 1) ℂ). -/
def QState (dim : Nat) : Type := Matrix (Fin dim) (Fin 1) ℂ

/-- Computational basis vector `|k⟩` on a `dim`-dimensional space
(Coq: `QuantumLib.basis_vector dim k`).
**Closed 2026-05-23**: realized as `FormalRV.Framework.basis_vector`. -/
def basis_vector (dim k : Nat) : QState dim :=
  FormalRV.Framework.basis_vector dim k

/-- Unitary action: turn a `BaseUCom n` into a state transformation
(Coq: `uc_eval c`).
**Closed 2026-05-23**: realized as matrix-vector multiplication using
`FormalRV.Framework.uc_eval` (which returns the unitary matrix). -/
noncomputable def uc_eval {n : Nat} (c : BaseUCom n) (ψ : QState (2^n)) :
    QState (2^n) :=
  let U : Matrix (Fin (2^n)) (Fin (2^n)) ℂ := FormalRV.Framework.uc_eval c
  let v : Matrix (Fin (2^n)) (Fin 1) ℂ := ψ
  U * v

/-- Partial-measurement probability: probability of observing the
"first register" outcome `ψ : QState m_dim` when the joint state is
`φ : QState full_dim` (Coq: `prob_partial_meas`).

**Closed 2026-05-24 as an operational Born's-rule definition.** For
`m_dim ∣ full_dim` (the physically meaningful regime), let `k :=
full_dim / m_dim` (the size of the unmeasured second register). Then
`prob_partial_meas ψ φ = ∑_{y : Fin k} |⟨ψ ⊗ |y⟩ | φ⟩|²`, where the
inner product collapses to `∑_{x : Fin m_dim} conj(ψ_x) · φ_{x·k+y}`
(the `|y⟩` factor of the tensored bra selects index `y` on the second
register). For `¬ (m_dim ∣ full_dim)` (no meaningful tensor split), the
probability is `0`.

Indexing convention matches `Framework.QuantumLib.kron_vec`: the
first-register index occupies the high bits (`i = x · k + y`). -/
noncomputable def prob_partial_meas {m_dim full_dim : Nat}
    (ψ : QState m_dim) (φ : QState full_dim) : ℝ :=
  if h : m_dim ∣ full_dim then
    let k := full_dim / m_dim
    ∑ y : Fin k, Complex.normSq (
      ∑ x : Fin m_dim,
        starRingEnd ℂ (ψ x 0) *
        φ (Fin.cast (Nat.mul_div_cancel' h) ⟨x.val * k + y.val, by
          have hx : x.val < m_dim := x.isLt
          have hy : y.val < k := y.isLt
          calc x.val * k + y.val
              < x.val * k + k := by omega
            _ = (x.val + 1) * k := by ring
            _ ≤ m_dim * k := Nat.mul_le_mul_right k hx⟩) 0)
  else 0

/-- Shift qubit indices in a `UCom` AST. Purely structural: the `dim`
parameter is just a type-level annotation, and the gate constructors
themselves are not constrained by it, so we may freely change the
output dim. Used below to lift `f i : BaseUCom anc` (acting on the
data register) to `BaseUCom (m + anc)` (acting on positions [m, m+anc)
of the combined precision+data register) for `QPE_var`. -/
def map_qubits {U : Nat → Type} {dim dim' : Nat} (g : Nat → Nat) :
    FormalRV.Framework.UCom U dim → FormalRV.Framework.UCom U dim'
  | FormalRV.Framework.UCom.seq c₁ c₂ =>
      FormalRV.Framework.UCom.seq (map_qubits g c₁) (map_qubits g c₂)
  | FormalRV.Framework.UCom.app1 u n =>
      FormalRV.Framework.UCom.app1 u (g n)
  | FormalRV.Framework.UCom.app2 u m n =>
      FormalRV.Framework.UCom.app2 u (g m) (g n)
  | FormalRV.Framework.UCom.app3 u m n p =>
      FormalRV.Framework.UCom.app3 u (g m) (g n) (g p)

/-- Variable-multiplier quantum phase estimation
(Coq: `SQIR.QPEGeneral.QPE_var m anc f`).  Returns a unitary on
`m + anc` qubits given a family of `anc`-qubit unitaries indexed by
the precision register.

**Closed 2026-05-24 as an operational definition.** Realized via
the existing `Framework.QPE.QPE` (which takes a family on the
combined register) by shift-lifting each `f i : BaseUCom anc` to
`BaseUCom (m + anc)` with qubit indices remapped `q ↦ m + q`. This
places the data-register action at positions `[m, m + anc)` of the
combined register, matching SQIR's
`QPE_var = npar_H m ; controlled_powers (map_qubits (·+m) ∘ f) m ; QFTinv m`. -/
noncomputable def QPE_var (m anc : Nat) (f : Nat → BaseUCom anc) :
    BaseUCom (m + anc) :=
  FormalRV.Framework.BaseUCom.QPE m anc
    (fun i => map_qubits (fun q => m + q) (f i))

/-- **Reverse index** `revIndex m j := m - 1 - j`. Used by `QPE_var_lsb`
to pre-reverse the oracle family so the underlying MSB-first QPE
machinery sees the original LSB-first family in reversed order.

Moved here from `PostQFT.lean` (2026-05-27) to allow `Shor_final_state`
to be defined in terms of `QPE_var_lsb` without an import cycle. -/
def revIndex (m j : Nat) : Nat := m - 1 - j

/-- `revIndex m j < m` when `j < m`. -/
theorem revIndex_lt (m j : Nat) (hj : j < m) : revIndex m j < m := by
  unfold revIndex; omega

/-- **LSB-compatible variable-multiplier quantum phase estimation.**
Pre-reverses the oracle family so the underlying MSB-first QPE
machinery (built on `qpeEigenvalue m i θ = exp(2π·I · 2^(m-i-1) · θ)`)
sees the original LSB-first family in reversed order. Concretely:
`QPE_var_lsb m anc f := QPE_var m anc (fun j => f (revIndex m j))`.

This is the QPE circuit that Shor's algorithm uses (with LSB-first
oracle family `ModMulImpl a N n anc f`, i.e., `f i = U^{a^{2^i}}`).

Moved here from `PostQFT.lean` (2026-05-27) so `Shor_final_state` can
be defined in terms of it. -/
noncomputable def QPE_var_lsb (m anc : Nat) (f : Nat → BaseUCom anc) :
    BaseUCom (m + anc) :=
  QPE_var m anc (fun j => f (revIndex m j))

/-! ## §2. Number-theoretic primitives. -/

/-- `r` is the (multiplicative) order of `a` mod `N`: `a^r ≡ 1 (mod N)`
and `r` is the least such positive exponent. -/
def Order (a r N : Nat) : Prop :=
  0 < r ∧ a^r % N = 1 ∧ ∀ s, 0 < s → s < r → a^s % N ≠ 1

/-- Modular exponentiation (Coq: `Shor.v` line 48 `modexp`). -/
def modexp (a x N : Nat) : Nat := a^x % N

/-- Helper for `ContinuedFraction`: iterates the Euclidean step,
maintaining the two-back convergent numerators/denominators.
Standard CF recursion: `p_k = a_k * p_{k-1} + p_{k-2}` and
similarly for `q_k`. Initial state `(p_prev, p_curr, q_prev, q_curr)
= (0, 1, 1, 0)` encodes `p_{-2}/q_{-2}` placeholders. -/
def cf_aux : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, _, _, p_curr, _, q_curr => (p_curr, q_curr)
  | n+1, o, m, p_prev, p_curr, q_prev, q_curr =>
      if m = 0 then (p_curr, q_curr)
      else
        let a := o / m
        cf_aux n m (o % m) p_curr (a * p_curr + p_prev)
                                 q_curr (a * q_curr + q_prev)

/-- One step of continued-fraction expansion: `(numerator, denominator)`
of the `step`-th convergent of `o / m`.

**Closed 2026-05-23 as a constructive def** (Phase 2 axiom #1, the
only Phase 2 axiom in `Shor_correct_var`'s chain):
Replaces the previous `axiom` with an explicit Euclidean-step
recursion. Verified on small inputs: `ContinuedFraction k 5 3`
gives convergents `(1,1), (2,1), (5,3)` matching `[1; 1, 2]` for `5/3`.

**Note on spec**: this def's semantic correctness (does it actually
return the k-th convergent of `o/m` for every k?) would be a Phase 3
theorem to discharge `r_found_1`. Here we only replace the axiom with
SOME computable function, eliminating it from the axiom hygiene of
`Shor_correct_var`. The remaining `r_found_1` axiom abstracts over
the semantics. -/
def ContinuedFraction (step o m : Nat) : Nat × Nat :=
  cf_aux (step + 1) o m 0 1 1 0

/-- **`cf_aux` definitional unfold at 0**: returns `(p_curr, q_curr)`. -/
theorem cf_aux_zero (o m p_prev p_curr q_prev q_curr : Nat) :
    cf_aux 0 o m p_prev p_curr q_prev q_curr = (p_curr, q_curr) := rfl

/-- **`cf_aux` definitional unfold at successor with `m > 0`**: one Euclidean
step. Useful for unfolding cf_aux step-by-step in proofs without re-deriving
the case split each time. -/
theorem cf_aux_succ_pos (n o m p_prev p_curr q_prev q_curr : Nat)
    (h_m_pos : 0 < m) :
    cf_aux (n+1) o m p_prev p_curr q_prev q_curr
      = cf_aux n m (o % m) p_curr ((o/m) * p_curr + p_prev)
                                  q_curr ((o/m) * q_curr + q_prev) := by
  show (if m = 0 then (p_curr, q_curr)
        else cf_aux n m (o % m) p_curr ((o/m) * p_curr + p_prev)
                                         q_curr ((o/m) * q_curr + q_prev))
      = cf_aux n m (o % m) p_curr ((o/m) * p_curr + p_prev)
                                  q_curr ((o/m) * q_curr + q_prev)
  rw [if_neg h_m_pos.ne']

/-- **`cf_aux` definitional unfold at successor with `m = 0`**: returns
`(p_curr, q_curr)` (terminates on 0 denominator). -/
theorem cf_aux_succ_zero (n o p_prev p_curr q_prev q_curr : Nat) :
    cf_aux (n+1) o 0 p_prev p_curr q_prev q_curr = (p_curr, q_curr) := by
  show (if (0 : Nat) = 0 then (p_curr, q_curr) else _) = (p_curr, q_curr)
  rfl

/-- **Full-state cf_aux** (Phase 3 r_found_1 infrastructure, added
2026-05-24 tick 66): cf_aux that returns ALL FOUR state values
`(p_prev, p_curr, q_prev, q_curr)` at termination, rather than just
`(p_curr, q_curr)`. Needed for the joint induction proof because the
inductive step requires knowing BOTH the current AND previous convergent
pair to apply mathlib's `nums_recurrence`/`dens_recurrence`. -/
def cf_aux_full : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat × Nat × Nat
  | 0, _, _, p_prev, p_curr, q_prev, q_curr => (p_prev, p_curr, q_prev, q_curr)
  | n+1, o, m, p_prev, p_curr, q_prev, q_curr =>
      if m = 0 then (p_prev, p_curr, q_prev, q_curr)
      else
        let a := o / m
        cf_aux_full n m (o % m) p_curr (a * p_curr + p_prev)
                                       q_curr (a * q_curr + q_prev)

/-- The pair-output cf_aux equals the projection of the full-state version. -/
theorem cf_aux_eq_cf_aux_full_proj (n o m p_prev p_curr q_prev q_curr : Nat) :
    cf_aux n o m p_prev p_curr q_prev q_curr =
      ((cf_aux_full n o m p_prev p_curr q_prev q_curr).2.1,
       (cf_aux_full n o m p_prev p_curr q_prev q_curr).2.2.2) := by
  induction n generalizing o m p_prev p_curr q_prev q_curr with
  | zero => rfl
  | succ k ih =>
    unfold cf_aux cf_aux_full
    by_cases h : m = 0
    · simp [h]
    · simp [h]
      exact ih _ _ _ _ _ _

/-- **`cf_aux_full 2` unfold for non-divisible case** (Phase 3 r_found_1
n=0 base case prep, added 2026-05-24 tick 72): explicit value when
`m > 0` and `o % m ≠ 0`. Two cf_aux steps with the Euclidean transition
fill the state to `(o/m, (m/(o%m))*(o/m)+1, 1, m/(o%m))`. -/
theorem cf_aux_full_2_nondiv (o m : Nat) (h_m_pos : 0 < m)
    (h_mod : o % m ≠ 0) :
    cf_aux_full 2 o m 0 1 1 0
      = (o / m, m / (o % m) * (o / m) + 1, 1, m / (o % m)) := by
  unfold cf_aux_full
  simp [h_m_pos.ne']
  unfold cf_aux_full
  simp [h_mod]
  rfl

/-- **`cf_aux_full 3` unfold for non-divisible chain** (Phase 3 r_found_1
n=1 case prep, added 2026-05-24 tick 75): explicit value when both `o%m ≠ 0`
AND `m%(o%m) ≠ 0`. Three cf_aux steps fill the state. Matches mathlib's
`(nums 1, nums 2, dens 1, dens 2)` for v = o/m by hand-verification of the
conts_recurrence with b_0 = m/(o%m) and b_1 = (o%m)/(m%(o%m)). -/
theorem cf_aux_full_3_nondiv2 (o m : Nat) (h_m_pos : 0 < m)
    (h_mod1 : o % m ≠ 0) (h_mod2 : m % (o % m) ≠ 0) :
    cf_aux_full 3 o m 0 1 1 0 =
      (m / (o % m) * (o / m) + 1,
       (o % m) / (m % (o % m)) * (m / (o % m) * (o / m) + 1) + (o / m),
       m / (o % m),
       (o % m) / (m % (o % m)) * (m / (o % m)) + 1) := by
  unfold cf_aux_full
  simp [h_m_pos.ne']
  unfold cf_aux_full
  simp [h_mod1]
  unfold cf_aux_full
  simp [h_mod2]
  rfl

/-- **Euclidean iteration on `(o, m)` pairs** (Phase 3 r_found_1 helper,
added 2026-05-24 tick 77): captures the state transition `(o, m) ↦
(m, o % m)` that cf_aux performs in its recursive call. At iteration
`k`, returns the k-th Euclidean iterate of the initial `(o, m)`. Stops
if `m = 0` (terminated). -/
def euclidean_iter : Nat → Nat → Nat → Nat × Nat
  | 0, o, m => (o, m)
  | n+1, o, m => if m = 0 then (o, m) else euclidean_iter n m (o % m)

/-- **cf_aux_full stabilizes when m_arg = 0** (added 2026-05-24):
Structural property of cf_aux_full's recursion — once the m parameter hits 0,
the function returns the current state unchanged regardless of remaining depth.

Both base case (n=0) and the m=0 guard in the recursive case yield the
same constant output `(p_prev, p_curr, q_prev, q_curr)`. Useful for the
terminated-case proof in `TODO_non_div_terminated_stable`. -/
theorem cf_aux_full_terminate (n o p_prev p_curr q_prev q_curr : Nat) :
    cf_aux_full n o 0 p_prev p_curr q_prev q_curr = (p_prev, p_curr, q_prev, q_curr) := by
  cases n with
  | zero => rfl
  | succ k =>
    show (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr) else _) = _
    rfl

/-- **cf_aux stabilizes when m_arg = 0** (added 2026-05-24): the pair-output
version. Corollary of `cf_aux_full_terminate` + `cf_aux_eq_cf_aux_full_proj`. -/
theorem cf_aux_terminate (n o p_prev p_curr q_prev q_curr : Nat) :
    cf_aux n o 0 p_prev p_curr q_prev q_curr = (p_curr, q_curr) := by
  rw [cf_aux_eq_cf_aux_full_proj, cf_aux_full_terminate]

/-- **Euclidean iteration terminates** (added 2026-05-24): the standard
Euclidean algorithm always reaches `.2 = 0` after at most `m` iterations
(strict decrease of the second component). Concretely:
`∃ j ≤ m, (euclidean_iter j o m).2 = 0`.

Used downstream to bridge cf_aux termination with mathlib's GenContFract
termination in the terminated case of `TODO_non_div_terminated_stable`. -/
theorem eucl_iter_terminates (o m : Nat) :
    ∃ j, j ≤ m ∧ (euclidean_iter j o m).2 = 0 := by
  -- Strong induction on m.
  induction m using Nat.strong_induction_on generalizing o with
  | _ m ih =>
    by_cases h_m : m = 0
    · refine ⟨0, by omega, ?_⟩
      simp [euclidean_iter, h_m]
    · have h_m_pos : 0 < m := Nat.pos_of_ne_zero h_m
      have h_mod_lt : o % m < m := Nat.mod_lt _ h_m_pos
      obtain ⟨j, h_le, h_eq⟩ := ih (o % m) h_mod_lt m
      refine ⟨j + 1, by omega, ?_⟩
      show (if m = 0 then (o, m) else euclidean_iter j m (o % m)).2 = 0
      rw [if_neg h_m]
      exact h_eq

/-- **cf_aux_full's "step at end" expression** (added 2026-05-24): when the
Euclidean iteration hasn't terminated at step N (i.e., `.2 > 0`), one extra
iteration `cf_aux_full (N+1)` equals applying ONE cf_aux step to the output
of `cf_aux_full N`. The step's `a = oN/mN` where `(oN, mN) = euclidean_iter N o m`.

This is the "peel from end" lemma needed to extend bridges past the
non-terminated boundary in the terminated case of TODO_non_div_terminated_stable. -/
theorem cf_aux_full_succ_step :
    ∀ (N o m p_prev p_curr q_prev q_curr : Nat),
      0 < (euclidean_iter N o m).2 →
      cf_aux_full (N + 1) o m p_prev p_curr q_prev q_curr =
        let s := cf_aux_full N o m p_prev p_curr q_prev q_curr
        let oN := (euclidean_iter N o m).1
        let mN := (euclidean_iter N o m).2
        (s.2.1, (oN / mN) * s.2.1 + s.1, s.2.2.2, (oN / mN) * s.2.2.2 + s.2.2.1) := by
  intro N
  induction N with
  | zero =>
    intros o m p_prev p_curr q_prev q_curr h_eucl_pos
    -- h_eucl_pos : 0 < (eucl_iter 0 o m).2 = m. So m > 0.
    have h_m_pos : 0 < m := h_eucl_pos
    -- cf_aux_full 1 o m S = step S (since m > 0).
    -- cf_aux_full 0 o m S = S. step-at-end of S using (eucl_iter 0 o m) = (o, m).
    show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
          else cf_aux_full 0 m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                       q_curr ((o / m) * q_curr + q_prev))
        = (p_curr, (o / m) * p_curr + p_prev, q_curr, (o / m) * q_curr + q_prev)
    rw [if_neg h_m_pos.ne']
    rfl
  | succ N' ih =>
    intros o m p_prev p_curr q_prev q_curr h_eucl_pos
    -- h_eucl_pos : (eucl_iter (N'+1) o m).2 > 0.
    -- Need: m > 0 (else eucl_iter would be (o, m) with .2 = m).
    have h_m_pos : 0 < m := by
      by_contra h_m_zero
      push_neg at h_m_zero
      interval_cases m
      simp [euclidean_iter] at h_eucl_pos
    -- Unfold (eucl_iter (N'+1) o m) using m > 0.
    have h_eucl_shift : euclidean_iter (N' + 1) o m = euclidean_iter N' m (o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter N' m (o % m)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_eucl_shift] at h_eucl_pos
    -- h_eucl_pos : (eucl_iter N' m (o%m)).2 > 0.
    -- Apply IH at (m, o%m).
    have h_ih := ih m (o % m) p_curr ((o / m) * p_curr + p_prev)
                    q_curr ((o / m) * q_curr + q_prev) h_eucl_pos
    -- Unfold LHS via cf_aux_full's recursion.
    show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
          else cf_aux_full (N' + 1) m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                              q_curr ((o / m) * q_curr + q_prev))
        = _
    rw [if_neg h_m_pos.ne']
    -- Now LHS = cf_aux_full (N'+1) m (o%m) (mutated state).
    -- By IH: this = step-at-end of cf_aux_full N' m (o%m) (mutated state).
    rw [h_ih]
    -- Unfold RHS's cf_aux_full N+1 = cf_aux_full (N'+1+1) using its def at top level.
    -- Actually RHS = step-at-end of cf_aux_full (N'+1) o m S. And cf_aux_full (N'+1) o m S
    -- = cf_aux_full N' m (o%m) (mutated). So RHS step-at-end is on cf_aux_full N' m (o%m) (mutated).
    -- The (eucl_iter (N'+1) o m) = (eucl_iter N' m (o%m)) by h_eucl_shift. Same a value.
    show (let s := cf_aux_full N' m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                            q_curr ((o / m) * q_curr + q_prev)
          let oN := (euclidean_iter N' m (o % m)).1
          let mN := (euclidean_iter N' m (o % m)).2
          (s.2.1, oN / mN * s.2.1 + s.1, s.2.2.2, oN / mN * s.2.2.2 + s.2.2.1))
        = (let s := cf_aux_full (N' + 1) o m p_prev p_curr q_prev q_curr
           let oN := (euclidean_iter (N' + 1) o m).1
           let mN := (euclidean_iter (N' + 1) o m).2
           (s.2.1, oN / mN * s.2.1 + s.1, s.2.2.2, oN / mN * s.2.2.2 + s.2.2.1))
    -- Both sides have the same structure. Show that cf_aux_full N' m (o%m) (mutated)
    -- = cf_aux_full (N'+1) o m S, and the eucl_iters match by h_eucl_shift.
    have h_unfold : cf_aux_full (N' + 1) o m p_prev p_curr q_prev q_curr
        = cf_aux_full N' m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                   q_curr ((o / m) * q_curr + q_prev) := by
      show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
            else cf_aux_full N' m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                          q_curr ((o / m) * q_curr + q_prev)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_unfold]
    rw [h_eucl_shift]

/-- **cf_aux_full's output is invariant under extra depth, post-termination**
(added 2026-05-24): if there exists `j ≤ N` with `(euclidean_iter j o m).2 = 0`
(cf_aux's Euclidean reaches termination within `N` steps), then adding one
more depth (`N+1`) doesn't change the output.

Proof by induction on N, exploiting that cf_aux's `m = 0` guard returns the
state regardless of remaining depth. The IH at the shifted `(m, o%m)` state
uses the Euclidean shift: if j ≥ 1, then `(euclidean_iter j o m).2 = 0`
implies `(euclidean_iter (j-1) m (o%m)).2 = 0`. -/
theorem cf_aux_full_depth_invariant :
    ∀ N o m p_prev p_curr q_prev q_curr,
      (∃ j, j ≤ N ∧ (euclidean_iter j o m).2 = 0) →
      cf_aux_full (N + 1) o m p_prev p_curr q_prev q_curr
        = cf_aux_full N o m p_prev p_curr q_prev q_curr := by
  intro N
  induction N with
  | zero =>
    -- Condition: ∃ j ≤ 0 with (eucl_iter j o m).2 = 0 → j = 0 → m = 0.
    rintro o m p_prev p_curr q_prev q_curr ⟨j, h_le, h_eq⟩
    have h_j : j = 0 := by omega
    subst h_j
    -- h_eq : (eucl_iter 0 o m).2 = m = 0.
    have h_m : m = 0 := h_eq
    subst h_m
    -- cf_aux_full 1 o 0 = cf_aux_full 0 o 0 = state.
    show (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr) else _)
        = (p_prev, p_curr, q_prev, q_curr)
    rfl
  | succ N' ih =>
    rintro o m p_prev p_curr q_prev q_curr ⟨j, h_le, h_eq⟩
    by_cases h_m : m = 0
    · subst h_m
      -- m = 0: both sides return state via the m=0 guard.
      show (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr) else _)
          = (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr) else _)
      rfl
    · -- m > 0: unfold both sides, apply IH at (m, o%m, mutated state).
      have h_m_pos : 0 < m := Nat.pos_of_ne_zero h_m
      -- Derive condition for IH at (m, o%m): ∃ j' ≤ N', (eucl_iter j' m (o%m)).2 = 0.
      have h_j_pos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h_j0 | h_jp
        · subst h_j0
          -- h_eq : (eucl_iter 0 o m).2 = m = 0. Contradicts m > 0.
          exact absurd h_eq h_m
        · exact h_jp
      have h_eucl_shift : (euclidean_iter (j - 1) m (o % m)).2 = 0 := by
        have h_unfold : euclidean_iter j o m = euclidean_iter (j - 1) m (o % m) := by
          have h_j_eq : j = (j - 1) + 1 := by omega
          conv_lhs => rw [h_j_eq]
          show (if m = 0 then (o, m) else euclidean_iter (j - 1) m (o % m))
              = euclidean_iter (j - 1) m (o % m)
          rw [if_neg h_m]
        rw [h_unfold] at h_eq
        exact h_eq
      have h_ih_cond : ∃ j', j' ≤ N' ∧ (euclidean_iter j' m (o % m)).2 = 0 :=
        ⟨j - 1, by omega, h_eucl_shift⟩
      -- Unfold both sides.
      show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
            else cf_aux_full (N' + 1) m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                   q_curr ((o / m) * q_curr + q_prev))
          = (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
             else cf_aux_full N' m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                   q_curr ((o / m) * q_curr + q_prev))
      rw [if_neg h_m, if_neg h_m]
      exact ih m (o % m) p_curr ((o / m) * p_curr + p_prev)
              q_curr ((o / m) * q_curr + q_prev) h_ih_cond

/-- **Euclidean iteration is monotone-terminating** (added 2026-05-24):
once `(euclidean_iter j o m).2 = 0` (cf_aux's m_arg hit 0 at step j),
the iteration stays terminated at all subsequent steps `j + k`. Proven by
induction on `j` with universal quantification over `o` and `m` (allowing
the inductive hypothesis to apply to the shifted state `(m, o%m)`). -/
theorem eucl_iter_stable :
    ∀ (j : Nat) (o m k : Nat),
      (euclidean_iter j o m).2 = 0 → (euclidean_iter (j + k) o m).2 = 0 := by
  intro j
  induction j with
  | zero =>
    intros o m k h
    -- h : (euclidean_iter 0 o m).2 = m = 0
    have h_m : m = 0 := h
    subst h_m
    -- Need: (euclidean_iter k o 0).2 = 0
    induction k with
    | zero => rfl
    | succ k' _ =>
      show (if (0 : Nat) = 0 then (o, 0) else _).2 = 0
      rfl
  | succ j' ih =>
    intros o m k h
    by_cases h_m : m = 0
    · -- m = 0: subst and recurse.
      subst h_m
      induction k with
      | zero => exact h
      | succ k' _ =>
        show (if (0 : Nat) = 0 then (o, 0) else _).2 = 0
        rfl
    · -- m > 0: unfold via the (n+1) pattern at both ends, apply ih.
      have h_unfold_lhs : euclidean_iter (j' + 1) o m = euclidean_iter j' m (o % m) := by
        show (if m = 0 then (o, m) else euclidean_iter j' m (o % m)) = _
        rw [if_neg h_m]
      rw [h_unfold_lhs] at h
      -- h : (euclidean_iter j' m (o%m)).2 = 0
      have h_succ : (euclidean_iter (j' + k) m (o % m)).2 = 0 := ih m (o % m) k h
      -- Target: (euclidean_iter (j' + 1 + k) o m).2 = 0
      have h_assoc : j' + 1 + k = (j' + k) + 1 := by ring
      rw [h_assoc]
      show (if m = 0 then (o, m) else euclidean_iter (j' + k) m (o % m)).2 = 0
      rw [if_neg h_m]
      exact h_succ

/-- **Structural insight for the joint induction succ case** (Phase 3
r_found_1, documentation tick 76):

The cf_aux_full recursion `(p_prev, p_curr) → (p_curr, a · p_curr + p_prev)`
EXACTLY mirrors mathlib's `conts_recurrence`:
`conts (n+2) = ⟨b · (conts (n+1)).a + a · (conts n).a, ...⟩` with `a = 1`
for SimpContFract.of (i.e., `GenContFract.of`).

The matching: cf_aux's `a` parameter at iteration k = mathlib's `b_k`
(the k-th partial denominator). cf_aux's state (p_prev, p_curr, q_prev,
q_curr) at iteration k = mathlib's (conts(k-1), conts(k)) for v = original
o/m.

**To make the joint induction work**, the invariant needs to be stated in
the most general form: for ANY state and ANY Euclidean shift of the
inputs, cf_aux's K-step result matches mathlib's contsAux applied K times
from the corresponding mathlib starting state. This is the form that
makes induction on K succeed.

**Formalization is multi-tick**: requires (a) stating the predicate
"cf_aux state matches mathlib at offset k for v" precisely, (b) proving
this predicate is preserved under one cf_aux_full step, (c) showing the
initial state (0, 1, 1, 0) at (o, m) matches mathlib at offset "before
the first step", which after one cf_aux iteration becomes offset 0. -/
def cf_aux_general_invariant_intent : Prop := True  -- design docs

/-- **Derive `o % m ≠ 0` from non-termination at step 0** (Phase 3
r_found_1 base case prep, added 2026-05-24 tick 73): when
`GenContFract.of (o/m)` is not terminated at step 0 (i.e., the stream
hasn't ended), the fractional part is non-zero, which for `v = o/m`
means `o % m ≠ 0`. -/
theorem nondiv_of_not_terminated_zero (o m : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0) :
    o % m ≠ 0 := by
  intro h_mod
  apply h_not_term
  rw [GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none]
  have h_stream_0 : GenContFract.IntFractPair.stream
      (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 0
      = some (GenContFract.IntFractPair.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) := rfl
  apply GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero h_stream_0
  show Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) = 0
  rw [Int.fract_div_natCast_eq_div_natCast_mod, h_mod]
  simp

-- (cf_aux_full_matches_mathlib_zero moved later — depends on mathlib_*_eq_* defs.)
-- (The old scaffold `TODO_cf_aux_full_matches_mathlib` was deleted 2026-05-24 —
--  superseded by the proven `cf_aux_full_matches_mathlib_strong` after the
--  general bridge invariant landed.)

/-- **Base case for slice 2 bridge** (Phase 3, r_found_1 prep, added
2026-05-23): the 0-th convergent of `o/m` (with `m > 0`) is `(o/m, 1)`.
Matches mathlib's `GenContFract.of`'s zeroth convergent which is the
integer part `⌊o/m⌋`. -/
theorem ContinuedFraction_zero (o m : Nat) (_h_m_pos : 0 < m) :
    ContinuedFraction 0 o m = (o / m, 1) := by
  unfold ContinuedFraction cf_aux
  split
  · omega
  · unfold cf_aux; simp

/-- **n=0 bridge to mathlib's `GenContFract`** (Phase 3, r_found_1 prep,
added 2026-05-23): the 0-th numerator of `GenContFract.of ((o:ℚ)/m)`
matches our `(ContinuedFraction 0 o m).1` cast to ℚ. Uses
`GenContFract.zeroth_num_eq_h` + `GenContFract.of_h_eq_floor` +
`Rat.floor_natCast_div_natCast`. -/
theorem cf_bridge_nums_zero (o m : Nat) (h_m_pos : 0 < m) :
    let q : ℚ := (o : ℚ) / m
    let g := GenContFract.of q
    g.nums 0 = (((ContinuedFraction 0 o m).1 : Nat) : ℚ) := by
  intro q g
  rw [ContinuedFraction_zero o m h_m_pos]
  rw [GenContFract.zeroth_num_eq_h]
  show g.h = ((o / m : Nat) : ℚ)
  rw [GenContFract.of_h_eq_floor]
  rw [Rat.floor_natCast_div_natCast]
  rfl

/-- **n=0 bridge for denominator** (Phase 3, r_found_1 prep, added
2026-05-23): the 0-th denominator of `GenContFract.of` is always 1,
matching our `(ContinuedFraction 0 o m).2 = 1`. -/
theorem cf_bridge_dens_zero (o m : Nat) (h_m_pos : 0 < m) :
    let q : ℚ := (o : ℚ) / m
    let g := GenContFract.of q
    g.dens 0 = (((ContinuedFraction 0 o m).2 : Nat) : ℚ) := by
  intro q g
  rw [ContinuedFraction_zero o m h_m_pos]
  rw [GenContFract.zeroth_den_eq_one]
  simp

/-- **Inductive step of the slice-2 bridge** (Phase 3, r_found_1 prep,
added 2026-05-23): The `(n+1)`-th element of `GenContFract.of (o/m).s`
equals the `n`-th element of `GenContFract.of (m / (o%m)).s` — exactly
the Euclidean step our `cf_aux` performs. Uses
`GenContFract.of_s_succ` + `Int.fract_div_natCast_eq_div_natCast_mod`. -/
theorem cf_of_div_succ_step (o m n : Nat) (h_mod_pos : 0 < o % m) :
    (GenContFract.of ((o:ℚ)/m)).s.get? (n+1) =
      (GenContFract.of ((m:ℚ)/((o % m : Nat) : ℚ))).s.get? n := by
  rw [GenContFract.of_s_succ]
  congr 2
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]

/-- **Joint base case** (Phase 3, r_found_1 prep, added 2026-05-23):
combines `cf_bridge_nums_zero` and `cf_bridge_dens_zero` into the
conjunction form needed by the joint induction (`cf_bridge_full` below). -/
theorem cf_bridge_full_zero (o m : Nat) (h_m_pos : 0 < m) :
    let q : ℚ := (o : ℚ) / m
    let g := GenContFract.of q
    g.nums 0 = (((ContinuedFraction 0 o m).1 : Nat) : ℚ) ∧
    g.dens 0 = (((ContinuedFraction 0 o m).2 : Nat) : ℚ) :=
  ⟨cf_bridge_nums_zero o m h_m_pos, cf_bridge_dens_zero o m h_m_pos⟩

/-- **n=1 denominator bridge** (Phase 3, r_found_1 prep, added 2026-05-23):
For `o, m > 0` with `o % m > 0` (CF doesn't terminate at step 1),
`(GenContFract.of ((o:ℚ)/m)).dens 1 = m/(o%m)` (Nat division), matching
the structure of our `cf_aux` after one Euclidean step. Uses
`GenContFract.of_s_head` (head of stream = `{a:=1, b:=⌊(Int.fract v)⁻¹⌋}`)
+ `Int.fract_div_natCast_eq_div_natCast_mod` + `Rat.floor_natCast_div_natCast`
+ `GenContFract.first_den_eq`. -/
theorem cf_bridge_dens_one (o m : Nat) (h_m_pos : 0 < m)
    (h_mod_pos : 0 < o % m) :
    let q : ℚ := (o : ℚ) / m
    let g := GenContFract.of q
    g.dens 1 = ((m / (o % m) : Nat) : ℚ) := by
  intro q g
  have h_fract : Int.fract q ≠ 0 := by
    show Int.fract ((o : ℚ) / m) ≠ 0
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_m_ne : (m : ℚ) ≠ 0 := by exact_mod_cast h_m_pos.ne'
    intro h_zero
    have : (m : ℚ) * (((o % m : Nat) : ℚ) / m) = (m : ℚ) * 0 := by rw [h_zero]
    rw [mul_div_cancel₀ _ h_m_ne] at this
    simp at this
    exact h_mod_pos.ne' (by exact_mod_cast this)
  have h_head : g.s.get? 0 = some { a := 1, b := ((m / (o % m) : Nat) : ℚ) } := by
    have := GenContFract.of_s_head (v := q) h_fract
    rw [show g.s.get? 0 = g.s.head from rfl, this]
    congr 1
    rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
    rw [Rat.floor_natCast_div_natCast]
    rfl
  rw [GenContFract.first_den_eq h_head]

/-- **n=1 numerator bridge** (Phase 3, r_found_1 prep, added 2026-05-23):
For `o, m > 0` with `o % m > 0`, `(GenContFract.of ((o:ℚ)/m)).nums 1
= (m/(o%m)) · (o/m) + 1` (Nat arithmetic), matching `ContinuedFraction 1 o m`.
Uses `GenContFract.first_num_eq` (`nums 1 = b · h + a` for the head pair) +
the same head computation as `cf_bridge_dens_one` + `Rat.floor_natCast_div_natCast`. -/
theorem cf_bridge_nums_one (o m : Nat) (h_m_pos : 0 < m)
    (h_mod_pos : 0 < o % m) :
    let q : ℚ := (o : ℚ) / m
    let g := GenContFract.of q
    g.nums 1 = (((m / (o % m)) * (o / m) + 1 : Nat) : ℚ) := by
  intro q g
  have h_fract : Int.fract q ≠ 0 := by
    show Int.fract ((o : ℚ) / m) ≠ 0
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_m_ne : (m : ℚ) ≠ 0 := by exact_mod_cast h_m_pos.ne'
    intro h_zero
    have : (m : ℚ) * (((o % m : Nat) : ℚ) / m) = (m : ℚ) * 0 := by rw [h_zero]
    rw [mul_div_cancel₀ _ h_m_ne] at this
    simp at this
    exact h_mod_pos.ne' (by exact_mod_cast this)
  have h_head : g.s.get? 0 = some { a := 1, b := ((m / (o % m) : Nat) : ℚ) } := by
    have := GenContFract.of_s_head (v := q) h_fract
    rw [show g.s.get? 0 = g.s.head from rfl, this]
    congr 1
    rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
    rw [Rat.floor_natCast_div_natCast]
    rfl
  rw [GenContFract.first_num_eq h_head, GenContFract.of_h_eq_floor]
  have h_floor_int : ⌊q⌋ = ((o / m : Nat) : ℤ) := Rat.floor_natCast_div_natCast o m
  have h_floor_R : ((⌊q⌋ : ℤ) : ℚ) = ((o / m : Nat) : ℚ) := by
    rw [h_floor_int]; push_cast; rfl
  rw [show ((⌊q⌋ : ℤ) : ℚ) = ((o / m : Nat) : ℚ) from h_floor_R]
  push_cast
  ring

-- (cf_bridge_full ℚ-version scaffold deleted 2026-05-24 — superseded by the
--  proven ℝ-version `cf_aux_full_matches_mathlib_strong` after the general
--  bridge invariant landed. The ℚ form was unused scaffolding.)

/-- The denominator of the `step`-th continued-fraction convergent of
`o / 2^m` (Coq: `Shor.v` line 47 `OF_post_step`). -/
noncomputable def OF_post_step (step o m : Nat) : Nat :=
  (ContinuedFraction step o (2^m)).2

/-- Iterated continued-fraction post-processor (Coq: `Shor.v` line 49
`OF_post'`).  Walks the convergents; returns the first denominator
that classically verifies as the order, or 0. -/
noncomputable def OF_post' : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, _ => 0
  | step + 1, a, N, o, m =>
      let pre := OF_post' step a N o m
      if pre = 0 then
        (if modexp a (OF_post_step step o m) N = 1
         then OF_post_step step o m
         else 0)
      else pre

/-- The order-finding post-processor (Coq: `Shor.v` line 58 `OF_post`):
runs `2m+2` continued-fraction iterations. -/
noncomputable def OF_post (a N o m : Nat) : Nat := OF_post' (2 * m + 2) a N o m

/-- Did the post-processor recover the order `r` from measurement
outcome `o`? (Coq: `Shor.v` line 63 `r_found`.)  Real-valued 0/1
indicator so it can be summed against measurement probabilities. -/
noncomputable def r_found (o m r a N : Nat) : ℝ :=
  if OF_post a N o m = r then 1 else 0

/-! ## §3. SQIR `Shor.v` definitions (lines 14–65). -/

/-- **`BasicSetting a r N m n`** (`Shor.v:14`).  The Shor parameter
regime: `a ∈ (0, N)` has order `r` mod `N`, the QPE precision register
satisfies `N² < 2^m ≤ 2N²`, and the data register satisfies
`N < 2^n ≤ 2N`. -/
def BasicSetting (a r N m n : Nat) : Prop :=
  (0 < a ∧ a < N) ∧
  Order a r N ∧
  (N^2 < 2^m ∧ 2^m ≤ 2 * N^2) ∧
  (N < 2^n ∧ 2^n ≤ 2 * N)

/-- **`MultiplyCircuitProperty a N n anc c`** (`Shor.v:28`).  Spec
that `c` is a faithful "multiply-by-`a` mod `N`" oracle: for every
`x ∈ [0, N)`, `c · |x⟩|0_anc⟩ = |a·x mod N⟩|0_anc⟩`.

**Closed 2026-05-24**: realized as a Prop-level operational equality on
`uc_eval c`. The encoding `|x⟩|0_anc⟩ = basis_vector (2^(n+anc)) (x · 2^anc)`
uses the integer factorization of the combined-register Hilbert space
(n-qubit "data" + anc-qubit "ancilla" → joint basis state `|x · 2^anc⟩`
when the ancilla starts at zero). -/
def MultiplyCircuitProperty (a N n anc : Nat) (c : BaseUCom (n + anc)) : Prop :=
  ∀ x : Nat, x < N →
    uc_eval c (basis_vector (2^(n + anc)) (x * 2^anc))
      = basis_vector (2^(n + anc)) ((a * x % N) * 2^anc)

/-- **`ModMulImpl a N n anc f`** (`Shor.v:35`).  For every iterate `i`,
the supplied unitary `f i` implements multiplication by `a^(2^i)`
mod `N`.  This is the full set of "squared-power" oracles QPE
consumes. -/
def ModMulImpl (a N n anc : Nat) (f : Nat → BaseUCom (n + anc)) : Prop :=
  ∀ i : Nat, MultiplyCircuitProperty (a^(2^i)) N n anc (f i)

/-- Cast a `QState a` to `QState b` along a dimensional equality `a = b`.
Reindexes the underlying column vector via `Fin.cast`; preserves entries
at corresponding numerical indices. Used to bridge between the `2^(m+(n+anc))`
form produced by `uc_eval ∘ QPE_var` and the `2^m * 2^n * 2^anc` form
required by `Shor_final_state`'s signature. -/
noncomputable def QState.cast {a b : Nat} (h : a = b) (ψ : QState a) : QState b :=
  fun i _ => ψ (Fin.cast h.symm i) 0

/-- The Shor input state `|0⟩_m ⊗ |1⟩_n ⊗ |0⟩_anc` on `(m + (n + anc))` qubits.
Built from `Framework.QuantumLib.kron_vec`; casted from the
left-associative form `2^((m+n)+anc)` to the right-associative form
`2^(m+(n+anc))` (which matches `BaseUCom (m + (n + anc))`). -/
noncomputable def Shor_initial_state (m n anc : Nat) :
    QState (2^(m + (n + anc))) :=
  QState.cast (by rw [Nat.add_assoc])
    (FormalRV.Framework.kron_vec
      (FormalRV.Framework.kron_vec
        (FormalRV.Framework.kron_zeros m)
        (FormalRV.Framework.basis_vector (2^n) 1))
      (FormalRV.Framework.kron_zeros anc))

/-- **`Shor_final_state`** (`Shor.v:39`).  The post-circuit pure state
before measurement: QPE applied to the modular-multiplication oracle
family `f`, on input `|0⟩_m ⊗ |1⟩_n ⊗ |0⟩_anc`.

**Closed 2026-05-24 as an operational definition.** Realized as
`uc_eval (QPE_var m (n + anc) f) (Shor_initial_state m n anc)`, casted
from the unitary-acting dimension `2^(m + (n + anc))` to the
constructor-product dimension `2^m * 2^n * 2^anc` via `QState.cast`
(value-preserving on corresponding numerical indices).

`QPE_var` itself remains axiomatized (separate Phase-3 obligation), but
`Shor_final_state` is no longer a free symbol — it is now a concrete
function of `(m, n, anc, f)`. -/
noncomputable def Shor_final_state (m n anc : Nat)
    (f : Nat → BaseUCom (n + anc)) : QState (2^m * 2^n * 2^anc) :=
  QState.cast (by rw [pow_add, pow_add, mul_assoc])
    (uc_eval (QPE_var_lsb m (n + anc) f) (Shor_initial_state m n anc))

/-- **`probability_of_success a r N m n anc f`** (`Shor.v:64`).  Sum
over all `2^m` measurement outcomes `x` of
`r_found(x) · P(measure x on first register)`.  This is the headline
quantity SQIR bounds. -/
noncomputable def probability_of_success
    (a r N m n anc : Nat) (f : Nat → BaseUCom (n + anc)) : ℝ :=
  ∑ x ∈ Finset.range (2^m),
    r_found x m r a N *
      prob_partial_meas (basis_vector (2^m) x) (Shor_final_state m n anc f)

/-! ## §4. The headline theorems (statements only; proofs = `sorry`). -/

/-- **The Shor success-probability constant** `κ = 4·exp(−2) / π²
≈ 0.0548` (Coq: `Shor.v:1073`). -/
noncomputable def κ : ℝ := 4 * Real.exp (-2) / Real.pi^2

/-- κ is strictly positive: `exp(−2) > 0`, `π² > 0`. -/
theorem κ_pos : κ > 0 := by
  unfold κ
  have h1 : Real.exp (-2) > 0 := Real.exp_pos (-2)
  have h2 : Real.pi^2 > 0 := pow_pos Real.pi_pos 2
  positivity

/-! ### Tier-2 quantitative axioms used by `Shor_correct_var`'s proof.

Each axiom corresponds to a substantial lemma in SQIR (Coq) that
would itself be a multi-hundred-line Lean port.  We use them as
black-box facts here; Tier-3 work will replace them with Lean
proofs.  -/

/-- **`Order_r_lt_N`** (Coq: `NumTheory.v`).  The multiplicative order
of `a` mod `N` is strictly less than `N` (when `N > 0` and `a` has an
order).  Standard number-theoretic fact.

**Closed 2026-05-23 via Euler's theorem** (Phase 1 axiom #1):
- N = 1 case: `a^r % 1 = 0 ≠ 1` contradicts the order definition.
- N ≥ 2 case: derive `Nat.Coprime a N` from `a^r % N = 1` via
  `Nat.dvd_mod_iff`. Apply `Nat.pow_totient_mod_eq_one` (Euler) to
  get `a^(totient N) % N = 1`. By the minimality clause of `Order`,
  this forces `totient N ≥ r`. Combined with `Nat.totient_lt`
  (`totient N < N` for N ≥ 2), conclude `r ≤ totient N < N`. -/
theorem Order_r_lt_N (a r N : Nat) (h_N : 0 < N) (h_ord : Order a r N) : r < N := by
  obtain ⟨h_r_pos, h_arN, h_min⟩ := h_ord
  rcases Nat.lt_or_eq_of_le h_N with h_N_ge_2 | h_N_eq_1
  · -- N ≥ 2 case: Euler + minimality
    have h_coprime : Nat.Coprime a N := by
      rw [Nat.Coprime]
      have h1 : Nat.gcd a N ∣ a := Nat.gcd_dvd_left a N
      have h2 : Nat.gcd a N ∣ N := Nat.gcd_dvd_right a N
      have h3 : Nat.gcd a N ∣ a^r := dvd_pow h1 (Nat.pos_iff_ne_zero.mp h_r_pos)
      have h4 : Nat.gcd a N ∣ a^r % N := (Nat.dvd_mod_iff h2).mpr h3
      rw [h_arN] at h4
      exact Nat.eq_one_of_dvd_one h4
    have h_euler : a^(Nat.totient N) % N = 1 :=
      Nat.pow_totient_mod_eq_one h_N_ge_2 h_coprime
    have h_tot_pos : 0 < Nat.totient N := Nat.totient_pos.mpr h_N
    have h_tot_lt : Nat.totient N < N := Nat.totient_lt N h_N_ge_2
    by_contra h_r_ge_N
    exact h_min (Nat.totient N) h_tot_pos
      (lt_of_lt_of_le h_tot_lt (not_lt.mp h_r_ge_N)) h_euler
  · -- N = 1 case: a^r % 1 = 0 ≠ 1, contradiction with h_arN
    subst h_N_eq_1
    simp [Nat.mod_one] at h_arN

/-- **`s_closest m k r`** (Coq: `Shor.v:594`).  The closest integer
to `k · 2^m / r`, used as the measurement outcome that is "as close
as possible" to the rational `k/r`. -/
noncomputable def s_closest (m k r : Nat) : Nat :=
  (k * 2^m + r / 2) / r

/-- **`s_closest_ub`** (Coq: `Shor.v:634`).  When the QPE precision
satisfies `BasicSetting`, the closest-outcome `s_closest m k r` lies
in `[0, 2^m)`.

**Closed 2026-05-23 via Nat arithmetic** (Phase 1 axiom #2):
Unpack `BasicSetting` to get `0 < r`, `r < N` (via `Order_r_lt_N`),
`N² < 2^m`. Chain `r < N ≤ N² < 2^m`. Then `s_closest m k r =
(k·2^m + r/2)/r < 2^m` iff `k·2^m + r/2 < 2^m · r` (via
`Nat.div_lt_iff_lt_mul`); the latter follows from `(k+1)·2^m ≤ r·2^m`
and `r/2 < 2^m`. -/
theorem s_closest_ub (a r N m n k : Nat) (h_basic : BasicSetting a r N m n)
    (h_k_lt : k < r) : s_closest m k r < 2^m := by
  obtain ⟨⟨h_a_pos, h_a_lt_N⟩, h_ord, ⟨h_Nsq_lt, _⟩, _⟩ := h_basic
  have h_r_pos : 0 < r := h_ord.1
  have h_N_pos : 0 < N := by omega
  have h_r_lt_N : r < N := Order_r_lt_N a r N h_N_pos h_ord
  have h_N_le_Nsq : N ≤ N^2 := by nlinarith
  have h_r_lt_2m : r < 2^m := by omega
  unfold s_closest
  rw [Nat.div_lt_iff_lt_mul h_r_pos]
  have h_k_succ : k + 1 ≤ r := h_k_lt
  have h_k_mul : (k + 1) * 2^m ≤ r * 2^m := Nat.mul_le_mul_right _ h_k_succ
  have h_r_half : r / 2 < 2^m := by omega
  have h_expand : (k + 1) * 2^m = k * 2^m + 2^m := by ring
  have h_comm : r * 2^m = 2^m * r := Nat.mul_comm _ _
  omega

/-- **`s_closest_injective`** (Coq: `Shor.v:670`).  Distinct `k`s in
`[0, r)` produce distinct `s_closest m k r` outcomes.

**Closed 2026-05-23 via Nat arithmetic** (Phase 1 axiom #3):
After unpacking `BasicSetting` to get `r < N ≤ N² < 2^m`, decompose
both `i*2^m + r/2` and `j*2^m + r/2` via `Nat.div_add_mod`. The
hypothesis `s_closest m i r = s_closest m j r` says both share the
same quotient `r * Q`; substituting yields
`i*2^m + j_mod = j*2^m + i_mod` (the symmetric rearrangement). With
`i_mod, j_mod < r`, this forces `|i*2^m - j*2^m| < r`. But for any
`i ≠ j`, `|i*2^m - j*2^m| ≥ 2^m > r`. Contradiction (case-split
on `Nat.lt_trichotomy`); closed by `omega` after providing
`(j-i)·2^m ≥ 2^m` via `nlinarith`. -/
theorem s_closest_injective (a r N m n : Nat)
    (h_basic : BasicSetting a r N m n) :
    ∀ i j : Nat, i < r → j < r → s_closest m i r = s_closest m j r → i = j := by
  intros i j h_i h_j h_eq
  obtain ⟨⟨h_a_pos, h_a_lt_N⟩, h_ord, ⟨h_Nsq_lt, _⟩, _⟩ := h_basic
  have h_r_pos : 0 < r := h_ord.1
  have h_N_pos : 0 < N := by omega
  have h_r_lt_N : r < N := Order_r_lt_N a r N h_N_pos h_ord
  have h_N_le_Nsq : N ≤ N^2 := by nlinarith
  have h_r_lt_2m : r < 2^m := by omega
  unfold s_closest at h_eq
  have h_i_div : r * ((i * 2^m + r/2) / r) + (i * 2^m + r/2) % r = i * 2^m + r/2 :=
    Nat.div_add_mod (i * 2^m + r/2) r
  have h_j_div : r * ((j * 2^m + r/2) / r) + (j * 2^m + r/2) % r = j * 2^m + r/2 :=
    Nat.div_add_mod (j * 2^m + r/2) r
  have h_i_mod_lt : (i * 2^m + r/2) % r < r := Nat.mod_lt _ h_r_pos
  have h_j_mod_lt : (j * 2^m + r/2) % r < r := Nat.mod_lt _ h_r_pos
  -- Identify the shared quotient via h_eq
  rw [h_eq] at h_i_div
  rcases Nat.lt_trichotomy i j with h_lt | h_eq_ij | h_gt
  · exfalso
    have h_ij_step : i * 2^m + 2^m ≤ j * 2^m := by
      have h1 : i + 1 ≤ j := h_lt
      nlinarith
    have h_rearrange : i * 2^m + (j * 2^m + r/2) % r
                       = j * 2^m + (i * 2^m + r/2) % r := by omega
    omega
  · exact h_eq_ij
  · exfalso
    have h_ij_step : j * 2^m + 2^m ≤ i * 2^m := by
      have h1 : j + 1 ≤ i := h_gt
      nlinarith
    have h_rearrange : i * 2^m + (j * 2^m + r/2) % r
                       = j * 2^m + (i * 2^m + r/2) % r := by omega
    omega

/-! ## Bridge from `s_closest` to the analytic QPE peak bound

The Shor-specific connector between the integer-valued `s_closest`
post-processor and the abstract analytic `qpe_prob_peak_bound` from
`Framework.QPEAmplitude`. At phase `θ = k/r`, the chosen measurement
outcome `s_closest m k r` is the integer closest to `k · 2^m / r`, so
the phase discrepancy `2^m · θ - s_closest` is bounded by `1/2`. This
makes `qpe_prob_peak_bound` directly applicable, yielding `qpe_prob ≥ 4/π²`. -/

/-- **Closest-integer property of `s_closest`** (added 2026-05-24):
the QPE phase discrepancy at `θ = k/r` and outcome `s_closest m k r` is
bounded by `1/2`. Combinatorial Nat fact: `s_closest m k r = (k·2^m + r/2)/r`
(Nat div), so `r · s_closest = k·2^m + (r/2:ℕ) - R` with `R = (k·2^m + r/2)
% r ∈ [0, r)`. Hence `k·2^m / r - s_closest = (R - (r/2:ℕ)) / r`, and
since `(r/2:ℕ) ∈ {(r-1)/2, r/2}` and `R ≤ r - 1`, the numerator's
absolute value is bounded by `r/2`. -/
theorem qpe_phase_discrepancy_s_closest_le_half
    (m k r : Nat) (h_r_pos : 0 < r) :
    |FormalRV.Framework.qpe_phase_discrepancy m (s_closest m k r)
        ((k : ℝ) / (r : ℝ))| ≤ 1 / 2 := by
  unfold FormalRV.Framework.qpe_phase_discrepancy s_closest
  set K : ℕ := k * 2^m with h_K_def
  set S : ℕ := (K + r/2) / r with h_S_def
  set R : ℕ := (K + r/2) % r with h_R_def
  -- Nat side: the round-to-nearest divmod facts.
  have h_R_lt : R < r := Nat.mod_lt _ h_r_pos
  have h_R_le : R + 1 ≤ r := h_R_lt
  have h_div_mod : r * S + R = K + r/2 := Nat.div_add_mod _ _
  have h_r_div_2_le : 2 * (r/2) ≤ r := by omega
  have h_r_div_2_ge : r ≤ 2 * (r/2) + 1 := by omega
  -- Real-cast versions.
  have h_r_pos_R : (0 : ℝ) < r := by exact_mod_cast h_r_pos
  have h_div_mod_R : (r : ℝ) * S + R = K + (r/2 : ℕ) := by exact_mod_cast h_div_mod
  have h_R_le_R : (R : ℝ) + 1 ≤ r := by exact_mod_cast h_R_le
  have h_R_nn : (0 : ℝ) ≤ R := by exact_mod_cast (Nat.zero_le _)
  have h_2div2_le_R : 2 * ((r/2 : ℕ) : ℝ) ≤ r := by exact_mod_cast h_r_div_2_le
  have h_2div2_ge_R : (r : ℝ) ≤ 2 * ((r/2 : ℕ) : ℝ) + 1 := by exact_mod_cast h_r_div_2_ge
  -- Express 2^m · (k/r) - S as (R - (r/2:ℕ)) / r using the divmod identity.
  have h_eq : (2 : ℝ)^m * ((k : ℝ) / r) - (S : ℝ)
            = ((R : ℝ) - ((r/2 : ℕ) : ℝ)) / r := by
    have h_K_real : (K : ℝ) = (k : ℝ) * (2 : ℝ)^m := by
      show ((k * 2^m : ℕ) : ℝ) = (k : ℝ) * (2 : ℝ)^m
      push_cast; ring
    field_simp
    linarith
  rw [h_eq, abs_div, abs_of_pos h_r_pos_R, div_le_iff₀ h_r_pos_R, abs_le]
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-- **Shor-specific QPE peak bound**: the ideal-amplitude probability at
outcome `s_closest m k r` for true phase `k/r` satisfies `qpe_prob ≥
4/π²`. Combines `qpe_phase_discrepancy_s_closest_le_half` (closest-
integer property) with the analytic `qpe_prob_peak_bound` from
`Framework.QPEAmplitude`. -/
theorem qpe_prob_at_s_closest_ge
    (m k r : Nat) (h_r_pos : 0 < r) :
    FormalRV.Framework.qpe_prob m (s_closest m k r) ((k : ℝ) / (r : ℝ))
      ≥ 4 / Real.pi ^ 2 :=
  FormalRV.Framework.qpe_prob_peak_bound m _ _
    (qpe_phase_discrepancy_s_closest_le_half m k r h_r_pos)

-- The `QPE_MMI_correct` axiom was DELETED on 2026-05-27 and replaced
-- by a theorem of the same name in `PostQFT.lean`. The replacement
-- chains through `QPE_MMI_correct_modulo_qpe_semantics` (proved here in
-- Shor.lean) + the LSB-pipeline state equality
-- `Shor_final_state_lsb_eq_shor_orbit_state` (proved in PostQFT.lean).
-- The proof is enabled by the design change to `Shor_final_state`,
-- which now uses `QPE_var_lsb` (the LSB-compatible QPE wrapper).
-- `Shor_correct_var` and `Shor_correct` are now also defined in
-- PostQFT.lean for the same reason.

/-- **`QPE_MMI_correct_conditional`** (added 2026-05-24): the
kernel-clean form of the QPE+modular-multiplication peak bound,
parameterized by a hypothesis-form QPE-MMI peak statement. Mirrors
the `Shor_correct_var_conditional` pattern: the deep external
obligation enters as an explicit universally-quantified argument,
so this theorem's own axiom dependence is the standard kernel only.

**Mathematical content hidden in the axiom.** The full proof in SQIR
(`QPEGeneral.v` + `Shor.v:861`) decomposes into three layers:

1. **QPE circuit semantics** (`Framework.QPE.QPE_semantics_full` shape):
   For any unitary `U` with eigenstate `|ψ⟩` at eigenvalue `exp(2πi·θ)`,
   the QPE circuit on `|0⟩_m ⊗ |ψ⟩` produces a state of the form
   `(∑_y α_y(θ) |y⟩) ⊗ |ψ⟩`, with the amplitudes `α_y(θ)` given
   explicitly by the inverse-QFT Dirichlet kernel.

2. **Modular-multiplication eigenstate decomposition** (orbit-state
   construction): the data-register input `|1⟩_n` decomposes as
   `(1/√r) · ∑_{k<r} |ψ_k⟩`, where each `|ψ_k⟩` is a joint eigenstate
   of all the powers `f i = U_a^{2^i}` with eigenvalue
   `exp(2πi · k · 2^i / r)` (the standard orbit-state construction
   from the cyclic action of multiplication-by-`a` mod `N`).

3. **Analytic QPE peak bound** (Dirichlet-kernel arithmetic):
   for `θ` within `1/2^(m+1)` of `k/r`, the amplitude
   `α_{s_closest m k r}(θ)` has squared magnitude `≥ 4/π²`.

Combining (1) × (2) × (3): linearity of `uc_eval` over the sum in
(2), per-component QPE semantics from (1), Born's-rule partial
measurement (`prob_partial_meas` def), orthogonality of distinct
`|ψ_k⟩` to drop cross-terms, then the peak bound (3) on the
diagonal component. The combined factor `(1/r) · (4/π²) = 4/(π²·r)`
matches the conclusion.

The combination proof requires Hilbert-space linear-algebra
infrastructure not yet in `Framework.QuantumLib` (vector-space
linearity of `uc_eval` over arbitrary sums, partial-measurement on
sums of states, joint-eigenstate sum projection); each is multi-tick
on its own. Once that infrastructure exists, this conditional can
be restated with the three layer-hypotheses separately and proved
by combining them. -/
theorem QPE_MMI_correct_conditional
    (a r N m n anc k : Nat) (f : Nat → BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_mmi : ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_QPE_MMI_peak :
      ∀ (a' r' N' m' n' anc' k' : Nat) (f' : Nat → BaseUCom (n' + anc')),
        BasicSetting a' r' N' m' n' →
        ModMulImpl a' N' n' anc' f' →
        (∀ i, i < m' → uc_well_typed (f' i)) →
        k' < r' →
        prob_partial_meas (basis_vector (2^m') (s_closest m' k' r'))
            (Shor_final_state m' n' anc' f')
          ≥ 4 / (Real.pi^2 * (r' : ℝ))) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) :=
  h_QPE_MMI_peak a r N m n anc k f h_basic h_mmi h_wt h_k_lt

/-! ### Phase-3 building blocks for `r_found_1` (added 2026-05-23)

These two private lemmas establish that `s_closest m k r / 2^m` is a
sufficiently-close rational approximation of `k / r` to satisfy
Khinchin's hypothesis (`Real.exists_convs_eq_rat`), which would then
let us conclude `k/r` is a convergent of `s_closest / 2^m`. The
remaining work (slices 2, 3 per `notes/sqir-shor-axiom-closure.md`)
is bridging our `def ContinuedFraction` to mathlib's
`Real.convergent` / `GenContFract.of`. -/

/-- `s_closest m k r / 2^m` is within `1/(2·2^m)` of `k/r`.

**Proof**: With `q := s_closest m k r = (k·2^m + r/2)/r` and
`m_r := (k·2^m + r/2) % r`, we have `r·q + m_r = k·2^m + r/2` and
`m_r < r`. Casting to ℝ: `q·r - k·2^m = (r/2 : ℕ) - m_r`. The Nat
floor `(r/2 : ℕ)` satisfies `r/2 - 1 ≤ (r/2 : ℕ) ≤ r/2` (Real). With
`0 ≤ m_r ≤ r - 1`, we get `|q·r - k·2^m| ≤ r/2`. Divide through by
`2^m · r > 0` to get the stated bound. -/
theorem s_closest_close_to_k_over_r (m k r : Nat) (h_r_pos : 0 < r) :
    |(s_closest m k r : ℝ) / (2^m : ℝ) - (k : ℝ) / (r : ℝ)|
      ≤ 1 / (2 * (2^m : ℝ)) := by
  have h_r_R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h_r_pos
  have h_2m_pos : (0 : ℝ) < (2^m : ℝ) := by positivity
  unfold s_closest
  set q := (k * 2^m + r / 2) / r
  set m_r := (k * 2^m + r / 2) % r
  have h_div_nat : r * q + m_r = k * 2^m + r / 2 := Nat.div_add_mod _ _
  have h_mod_lt : m_r < r := Nat.mod_lt _ h_r_pos
  have h_half_le : ((r / 2 : Nat) : ℝ) ≤ (r : ℝ) / 2 := by
    have h_nat : (r / 2 : Nat) * 2 ≤ r := Nat.div_mul_le_self r 2
    have h_R : ((r / 2 : Nat) : ℝ) * 2 ≤ (r : ℝ) := by exact_mod_cast h_nat
    linarith
  have h_half_ge : ((r / 2 : Nat) : ℝ) ≥ (r : ℝ) / 2 - 1 := by
    have h_nat : r ≤ 2 * (r / 2) + 1 := by omega
    have h_R : (r : ℝ) ≤ 2 * ((r / 2 : Nat) : ℝ) + 1 := by exact_mod_cast h_nat
    linarith
  have h_abs_bound : |(q : ℝ) * r - (k : ℝ) * 2^m| ≤ (r : ℝ) / 2 := by
    have h_step : (r : ℝ) * q + (m_r : ℝ) = (k : ℝ) * 2^m + ((r / 2 : Nat) : ℝ) := by
      exact_mod_cast h_div_nat
    have h_diff : (q : ℝ) * r - (k : ℝ) * 2^m = ((r / 2 : Nat) : ℝ) - (m_r : ℝ) := by
      have : (r : ℝ) * q = (q : ℝ) * r := by ring
      linarith
    rw [h_diff, abs_sub_le_iff]
    have h_m_r_nonneg : (0 : ℝ) ≤ (m_r : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_m_r_lt : (m_r : ℝ) ≤ (r : ℝ) - 1 := by
      have h1 : m_r + 1 ≤ r := h_mod_lt
      have h2 : ((m_r + 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast h1
      push_cast at h2
      linarith
    exact ⟨by linarith, by linarith⟩
  have h_denom : (q : ℝ) / (2^m : ℝ) - (k : ℝ) / (r : ℝ) =
                  ((q : ℝ) * r - (k : ℝ) * 2^m) / ((2^m : ℝ) * r) := by
    field_simp
  rw [h_denom, abs_div]
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2^m : ℝ) * r)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h_abs_bound, h_2m_pos, h_r_R]

/-- The Khinchin-precondition: under `BasicSetting`, `1/(2·2^m) ≤ 1/(2·r²)`.
Together with `s_closest_close_to_k_over_r`, this gives
`|s_closest/2^m - k/r| < 1/(2r²)`, which is `Real.exists_convs_eq_rat`'s
hypothesis — establishing `k/r` is a convergent of `s_closest/2^m`. -/
theorem khinchin_precond (r N m : Nat) (h_r_pos : 0 < r)
    (h_r_lt_N : r < N) (h_Nsq_lt : N^2 < 2^m) :
    1 / (2 * (2^m : ℝ)) ≤ 1 / (2 * (r : ℝ)^2) := by
  have h_r_R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h_r_pos
  have h_Nsq_R : (N : ℝ)^2 < (2^m : ℝ) := by exact_mod_cast h_Nsq_lt
  have h_r_le_N : (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt h_r_lt_N
  have h_r_sq_lt : (r : ℝ)^2 < (2^m : ℝ) := by
    have : (r : ℝ)^2 ≤ (N : ℝ)^2 := by nlinarith
    linarith
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  linarith

/-- **Khinchin precondition fully assembled** (Phase 3, r_found_1 prep,
added 2026-05-23): under `BasicSetting`, the rational `s_closest m k r / 2^m`
approximates `k/r` strictly better than `1/(2r²)`. This is exactly the
hypothesis of mathlib's `Real.exists_convs_eq_rat` (Khinchin). Combining
`s_closest_close_to_k_over_r` (`≤ 1/(2·2^m)`) with the strict
`2^m > r²` from BasicSetting+Order_r_lt_N. -/
theorem khinchin_applies_to_s_closest
    (a r N m n k : Nat) (h_basic : BasicSetting a r N m n) (h_k_lt : k < r) :
    |(s_closest m k r : ℝ) / (2^m : ℝ) - (k : ℝ) / (r : ℝ)| < 1 / (2 * (r : ℝ)^2) := by
  obtain ⟨⟨h_a_pos, h_a_lt_N⟩, h_ord, ⟨h_Nsq_lt, _⟩, _⟩ := h_basic
  have h_r_pos : 0 < r := h_ord.1
  have h_N_pos : 0 < N := by omega
  have h_r_lt_N : r < N := Order_r_lt_N a r N h_N_pos h_ord
  have h_r_R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h_r_pos
  have h_2m_pos : (0 : ℝ) < (2^m : ℝ) := by positivity
  have h_Nsq_R : (N : ℝ)^2 < (2^m : ℝ) := by exact_mod_cast h_Nsq_lt
  have h_r_le_N : (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt h_r_lt_N
  have h_r_sq_lt : (r : ℝ)^2 < (2^m : ℝ) := by
    have : (r : ℝ)^2 ≤ (N : ℝ)^2 := by nlinarith
    linarith
  have h_bound := s_closest_close_to_k_over_r m k r h_r_pos
  have h_strict : 1 / (2 * (2^m : ℝ)) < 1 / (2 * (r : ℝ)^2) := by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    linarith
  linarith

/-- **Khinchin recovery: `k/r` is a convergent of `s_closest/2^m`** (Phase
3, r_found_1 prep, added 2026-05-23): direct application of
`Real.exists_convs_eq_rat` using `khinchin_applies_to_s_closest` as the
hypothesis. The denominator handling: `((k:ℚ)/r).den = r` when `gcd(k,r)=1`
(via `Rat.den_div_eq_of_coprime`). Now we know some convergent of mathlib's
`GenContFract.of` equals `k/r` — the cf_bridge work would translate this
to our `OF_post_step`. -/
theorem k_over_r_is_convergent
    (a r N m n k : Nat) (h_basic : BasicSetting a r N m n) (h_k_lt : k < r)
    (h_coprime : Nat.gcd k r = 1) :
    ∃ N_step, (GenContFract.of ((s_closest m k r : ℝ) / (2^m : ℝ))).convs N_step
                = (((k : ℚ) / r : ℚ) : ℝ) := by
  set q : ℚ := (k : ℚ) / r with hq_def
  have h_r_pos : 0 < r := h_basic.2.1.1
  have h_q_den : q.den = r := by
    rw [hq_def]
    have h_r_pos_Z : (0 : ℤ) < (r : ℤ) := by exact_mod_cast h_r_pos
    have h_cop : (Int.natAbs (k : ℤ)).Coprime (Int.natAbs (r : ℤ)) := by
      simp; exact h_coprime
    have h_den := Rat.den_div_eq_of_coprime h_r_pos_Z h_cop
    push_cast at h_den
    exact_mod_cast h_den
  show ∃ N_step, (GenContFract.of ((s_closest m k r : ℝ) / (2^m : ℝ))).convs N_step = (q : ℝ)
  apply Real.exists_convs_eq_rat
  rw [h_q_den]
  show |(s_closest m k r : ℝ) / (2^m : ℝ) - (q : ℝ)| < 1 / (2 * (r : ℝ)^2)
  rw [show (q : ℝ) = (k : ℝ) / r from by rw [hq_def]; push_cast; ring]
  exact khinchin_applies_to_s_closest a r N m n k h_basic h_k_lt

/-- **Denominators of `GenContFract.of v` are integer-valued** (paired
form, Phase 3 r_found_1 slice 4b sub-step 1, added 2026-05-23): joint
induction giving `∃ d : ℤ, dens n = d ∧ ∃ d', dens (n+1) = d'` for all
`n`. The base cases use `zeroth_den_eq_one` and either
`first_den_eq` (if not terminated at 0) or `dens_stable_of_terminated`
(if terminated at 0). The inductive step uses `dens_recurrence` for the
non-terminated case (since `GenContFract.of` has partial-numerator 1 by
`of_partNum_eq_one_and_exists_int_partDen_eq`, the recurrence specializes
to `dens(n+2) = b·dens(n+1) + dens(n)` with `b` integer-valued). -/
theorem dens_int_valued_pair (v : ℝ) :
    ∀ n, (∃ d : ℤ, (GenContFract.of v).dens n = (d : ℝ)) ∧
         (∃ d : ℤ, (GenContFract.of v).dens (n+1) = (d : ℝ)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨⟨1, ?_⟩, ?_⟩
    · simp [GenContFract.zeroth_den_eq_one]
    · by_cases h : (GenContFract.of v).s.get? 0 = none
      · refine ⟨1, ?_⟩
        have h_term : (GenContFract.of v).TerminatedAt 0 := h
        rw [GenContFract.dens_stable_of_terminated (n := 0) (m := 1) (by omega) h_term]
        simp [GenContFract.zeroth_den_eq_one]
      · have h' : ∃ gp, (GenContFract.of v).s.get? 0 = some gp := by
          rcases hopt : (GenContFract.of v).s.get? 0 with _ | gp
          · exact absurd hopt h
          · exact ⟨gp, rfl⟩
        obtain ⟨gp, hgp⟩ := h'
        rw [GenContFract.first_den_eq hgp]
        obtain ⟨_, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp
        exact ⟨z, hz⟩
  | succ k ih =>
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    refine ⟨⟨b, hb⟩, ?_⟩
    by_cases h : (GenContFract.of v).s.get? (k+1) = none
    · refine ⟨b, ?_⟩
      have h_term : (GenContFract.of v).TerminatedAt (k+1) := h
      rw [GenContFract.dens_stable_of_terminated (n := k+1) (m := k+2) (by omega) h_term]
      exact hb
    · have h' : ∃ gp, (GenContFract.of v).s.get? (k+1) = some gp := by
        rcases hopt : (GenContFract.of v).s.get? (k+1) with _ | gp
        · exact absurd hopt h
        · exact ⟨gp, rfl⟩
      obtain ⟨gp, hgp⟩ := h'
      have h_rec := GenContFract.dens_recurrence (g := GenContFract.of v) (n := k)
        hgp ha hb
      obtain ⟨ha_eq, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp
      refine ⟨z * b + a, ?_⟩
      show (GenContFract.of v).dens (k + 1 + 1) = _
      rw [show k + 1 + 1 = k + 2 from rfl]
      rw [h_rec, ha_eq, hz]
      push_cast
      ring

/-- Single-`n` corollary: `dens n` of `GenContFract.of v` is integer-valued. -/
theorem dens_int_valued (v : ℝ) (n : Nat) :
    ∃ d : ℤ, (GenContFract.of v).dens n = (d : ℝ) :=
  (dens_int_valued_pair v n).1

/-- **Numerators of `GenContFract.of v` are integer-valued** (paired
form, Phase 3 r_found_1 slice 4b sub-step 2, added 2026-05-23): analogous
to `dens_int_valued_pair`. The base case n=0 uses
`zeroth_num_eq_h` + `of_h_eq_floor` (so `nums 0 = ⌊v⌋`); the n=1
non-terminated case uses `first_num_eq` (giving `nums 1 = b·h + 1`); the
inductive step uses `nums_recurrence` with `a = 1` from
`of_partNum_eq_one_and_exists_int_partDen_eq`. -/
theorem nums_int_valued_pair (v : ℝ) :
    ∀ n, (∃ d : ℤ, (GenContFract.of v).nums n = (d : ℝ)) ∧
         (∃ d : ℤ, (GenContFract.of v).nums (n+1) = (d : ℝ)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨⟨⌊v⌋, ?_⟩, ?_⟩
    · rw [GenContFract.zeroth_num_eq_h, GenContFract.of_h_eq_floor]
    · by_cases h : (GenContFract.of v).s.get? 0 = none
      · refine ⟨⌊v⌋, ?_⟩
        have h_term : (GenContFract.of v).TerminatedAt 0 := h
        rw [GenContFract.nums_stable_of_terminated (n := 0) (m := 1) (by omega) h_term]
        rw [GenContFract.zeroth_num_eq_h, GenContFract.of_h_eq_floor]
      · have h' : ∃ gp, (GenContFract.of v).s.get? 0 = some gp := by
          rcases hopt : (GenContFract.of v).s.get? 0 with _ | gp
          · exact absurd hopt h
          · exact ⟨gp, rfl⟩
        obtain ⟨gp, hgp⟩ := h'
        rw [GenContFract.first_num_eq hgp]
        obtain ⟨ha_eq, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp
        refine ⟨z * ⌊v⌋ + 1, ?_⟩
        rw [ha_eq, hz, GenContFract.of_h_eq_floor]
        push_cast; ring
  | succ k ih =>
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    refine ⟨⟨b, hb⟩, ?_⟩
    by_cases h : (GenContFract.of v).s.get? (k+1) = none
    · refine ⟨b, ?_⟩
      have h_term : (GenContFract.of v).TerminatedAt (k+1) := h
      rw [GenContFract.nums_stable_of_terminated (n := k+1) (m := k+2) (by omega) h_term]
      exact hb
    · have h' : ∃ gp, (GenContFract.of v).s.get? (k+1) = some gp := by
        rcases hopt : (GenContFract.of v).s.get? (k+1) with _ | gp
        · exact absurd hopt h
        · exact ⟨gp, rfl⟩
      obtain ⟨gp, hgp⟩ := h'
      have h_rec := GenContFract.nums_recurrence (g := GenContFract.of v) (n := k)
        hgp ha hb
      obtain ⟨ha_eq, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp
      refine ⟨z * b + a, ?_⟩
      show (GenContFract.of v).nums (k + 1 + 1) = _
      rw [show k + 1 + 1 = k + 2 from rfl]
      rw [h_rec, ha_eq, hz]
      push_cast; ring

/-- Single-`n` corollary: `nums n` of `GenContFract.of v` is integer-valued. -/
theorem nums_int_valued (v : ℝ) (n : Nat) :
    ∃ d : ℤ, (GenContFract.of v).nums n = (d : ℝ) :=
  (nums_int_valued_pair v n).1

/-- **Determinant identity for `GenContFract.of v`** (Phase 3, r_found_1
slice 4b prep, added 2026-05-23): the standard Bezout-like determinant
identity `p_n q_{n+1} - q_n p_{n+1} = (-1)^(n+1)` for the convergents of
`GenContFract.of v`. Re-stated from mathlib's `SimpContFract.determinant`
via the `SimpContFract.of` packaging — `(SimpContFract.of v : GenContFract)
= GenContFract.of v` definitionally. This is what gives gcd(p_n, q_n) = 1
as integers (modulo upgrading int-valuedness; future tick). -/
theorem of_v_determinant (v : ℝ) (n : Nat)
    (h_not_term : ¬ (GenContFract.of v).TerminatedAt n) :
    (GenContFract.of v).nums n * (GenContFract.of v).dens (n+1)
      - (GenContFract.of v).dens n * (GenContFract.of v).nums (n+1)
        = (-1) ^ (n+1) := by
  let s : SimpContFract ℝ := SimpContFract.of v
  have h_eq : (s : GenContFract ℝ) = GenContFract.of v := rfl
  have h_det := SimpContFract.determinant (s := s) (n := n)
    (by rw [h_eq]; exact h_not_term)
  rw [h_eq] at h_det
  exact h_det

/-- **Coprimality of integer-valued numerators and denominators** (Phase 3
r_found_1 slice 4b sub-step 2b, added 2026-05-23): for `GenContFract.of v`
at any non-terminated step `n`, if `nums n = (a : ℝ)` and `dens n = (b : ℝ)`
with `a b : ℤ`, then `Int.gcd a b = 1`. Proof: extract integer-valued
`a' = nums (n+1)`, `b' = dens (n+1)` (via `nums_int_valued` /
`dens_int_valued`), apply `of_v_determinant` (Bezout-like identity
`a·b' - b·a' = (-1)^(n+1)`), cast to ℤ, then case-split on parity of `n+1`:
either way yields a Bezout combination summing to 1, so `Int.gcd a b ∣ 1`
by `Int.gcd_dvd_iff`. -/
theorem of_v_nums_dens_coprime (v : ℝ) (n : Nat)
    (h_not_term : ¬ (GenContFract.of v).TerminatedAt n)
    (a b : ℤ) (ha : (GenContFract.of v).nums n = (a : ℝ))
    (hb : (GenContFract.of v).dens n = (b : ℝ)) :
    Int.gcd a b = 1 := by
  obtain ⟨a', ha'⟩ := nums_int_valued v (n+1)
  obtain ⟨b', hb'⟩ := dens_int_valued v (n+1)
  have h_det := of_v_determinant v n h_not_term
  rw [ha, hb, ha', hb'] at h_det
  have h_int : a * b' - b * a' = (-1) ^ (n + 1) := by
    have h_cast : ((a * b' - b * a' : ℤ) : ℝ) = (((-1 : ℤ) ^ (n + 1) : ℤ) : ℝ) := by
      push_cast
      convert h_det using 1
    exact_mod_cast h_cast
  rcases (Nat.even_or_odd (n+1)) with hev | hod
  · have h_pow : ((-1 : ℤ) ^ (n + 1)) = 1 := Even.neg_one_pow hev
    rw [h_pow] at h_int
    have h2 : a * b' + b * (-a') = 1 := by linarith
    have hdiv : Int.gcd a b ∣ 1 :=
      Int.gcd_dvd_iff.mpr ⟨b', -a', by exact_mod_cast h2.symm⟩
    exact Nat.eq_one_of_dvd_one hdiv
  · have h_pow : ((-1 : ℤ) ^ (n + 1)) = -1 := Odd.neg_one_pow hod
    rw [h_pow] at h_int
    have h2 : a * (-b') + b * a' = 1 := by linarith
    have hdiv : Int.gcd a b ∣ 1 :=
      Int.gcd_dvd_iff.mpr ⟨-b', a', by exact_mod_cast h2.symm⟩
    exact Nat.eq_one_of_dvd_one hdiv

end FormalRV.SQIRPort
