/-
  FormalRV.SQIRPort.Shor — Lean port of SQIR's `Shor.v` statements.

  **Tier 1 port (statements only; proofs = `sorry`, supporting
  QuantumLib primitives = `axiom`).**

  Source: `SQIR/examples/shor/Shor.v`, headline lemmas
  `Shor_correct_var` (l. 1193) and `Shor_correct` (l. 1295).

  Goal of this Tier-1 port: make the framework's L1 anchor
  (`rsa_correct` in `Framework/L1_Algorithm.lean`) point at a
  concrete Lean theorem whose statement matches SQIR's, with
  axiomatic placeholders for the QuantumLib primitives
  (`base_ucom`, `prob_partial_meas`, `uc_eval`, …) and for the
  number-theoretic post-processor (`ContinuedFraction`).

  Tier-2 / Tier-3 future obligations are inline-flagged with
  `TIER2` / `TIER3` comments.  Tier 2 = prove `Shor_correct_var`
  in Lean assuming the three quantitative axioms
  (`QPE_pi_squared_bound`, `ContinuedFraction_recovers_r`,
  `Euler_totient_bound`).  Tier 3 = discharge those three axioms
  by porting `QPEGeneral.v` / `ContFrac.v` / `EulerTotient.v` to
  Lean.
-/

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
private def cf_aux : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat
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
private theorem cf_aux_zero (o m p_prev p_curr q_prev q_curr : Nat) :
    cf_aux 0 o m p_prev p_curr q_prev q_curr = (p_curr, q_curr) := rfl

/-- **`cf_aux` definitional unfold at successor with `m > 0`**: one Euclidean
step. Useful for unfolding cf_aux step-by-step in proofs without re-deriving
the case split each time. -/
private theorem cf_aux_succ_pos (n o m p_prev p_curr q_prev q_curr : Nat)
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
private theorem cf_aux_succ_zero (n o p_prev p_curr q_prev q_curr : Nat) :
    cf_aux (n+1) o 0 p_prev p_curr q_prev q_curr = (p_curr, q_curr) := by
  show (if (0 : Nat) = 0 then (p_curr, q_curr) else _) = (p_curr, q_curr)
  rfl

/-- **Full-state cf_aux** (Phase 3 r_found_1 infrastructure, added
2026-05-24 tick 66): cf_aux that returns ALL FOUR state values
`(p_prev, p_curr, q_prev, q_curr)` at termination, rather than just
`(p_curr, q_curr)`. Needed for the joint induction proof because the
inductive step requires knowing BOTH the current AND previous convergent
pair to apply mathlib's `nums_recurrence`/`dens_recurrence`. -/
private def cf_aux_full : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat × Nat × Nat
  | 0, _, _, p_prev, p_curr, q_prev, q_curr => (p_prev, p_curr, q_prev, q_curr)
  | n+1, o, m, p_prev, p_curr, q_prev, q_curr =>
      if m = 0 then (p_prev, p_curr, q_prev, q_curr)
      else
        let a := o / m
        cf_aux_full n m (o % m) p_curr (a * p_curr + p_prev)
                                       q_curr (a * q_curr + q_prev)

/-- The pair-output cf_aux equals the projection of the full-state version. -/
private theorem cf_aux_eq_cf_aux_full_proj (n o m p_prev p_curr q_prev q_curr : Nat) :
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
private theorem cf_aux_full_2_nondiv (o m : Nat) (h_m_pos : 0 < m)
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
private theorem cf_aux_full_3_nondiv2 (o m : Nat) (h_m_pos : 0 < m)
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
private def euclidean_iter : Nat → Nat → Nat → Nat × Nat
  | 0, o, m => (o, m)
  | n+1, o, m => if m = 0 then (o, m) else euclidean_iter n m (o % m)

/-- **cf_aux_full stabilizes when m_arg = 0** (added 2026-05-24):
Structural property of cf_aux_full's recursion — once the m parameter hits 0,
the function returns the current state unchanged regardless of remaining depth.

Both base case (n=0) and the m=0 guard in the recursive case yield the
same constant output `(p_prev, p_curr, q_prev, q_curr)`. Useful for the
terminated-case proof in `TODO_non_div_terminated_stable`. -/
private theorem cf_aux_full_terminate (n o p_prev p_curr q_prev q_curr : Nat) :
    cf_aux_full n o 0 p_prev p_curr q_prev q_curr = (p_prev, p_curr, q_prev, q_curr) := by
  cases n with
  | zero => rfl
  | succ k =>
    show (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr) else _) = _
    rfl

/-- **cf_aux stabilizes when m_arg = 0** (added 2026-05-24): the pair-output
version. Corollary of `cf_aux_full_terminate` + `cf_aux_eq_cf_aux_full_proj`. -/
private theorem cf_aux_terminate (n o p_prev p_curr q_prev q_curr : Nat) :
    cf_aux n o 0 p_prev p_curr q_prev q_curr = (p_curr, q_curr) := by
  rw [cf_aux_eq_cf_aux_full_proj, cf_aux_full_terminate]

/-- **Euclidean iteration terminates** (added 2026-05-24): the standard
Euclidean algorithm always reaches `.2 = 0` after at most `m` iterations
(strict decrease of the second component). Concretely:
`∃ j ≤ m, (euclidean_iter j o m).2 = 0`.

Used downstream to bridge cf_aux termination with mathlib's GenContFract
termination in the terminated case of `TODO_non_div_terminated_stable`. -/
private theorem eucl_iter_terminates (o m : Nat) :
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
private theorem cf_aux_full_succ_step :
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
private theorem cf_aux_full_depth_invariant :
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
private theorem eucl_iter_stable :
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
private def cf_aux_general_invariant_intent : Prop := True  -- design docs

/-- **Derive `o % m ≠ 0` from non-termination at step 0** (Phase 3
r_found_1 base case prep, added 2026-05-24 tick 73): when
`GenContFract.of (o/m)` is not terminated at step 0 (i.e., the stream
hasn't ended), the fractional part is non-zero, which for `v = o/m`
means `o % m ≠ 0`. -/
private theorem nondiv_of_not_terminated_zero (o m : Nat)
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
private theorem ContinuedFraction_zero (o m : Nat) (_h_m_pos : 0 < m) :
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
private theorem cf_bridge_nums_zero (o m : Nat) (h_m_pos : 0 < m) :
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
private theorem cf_bridge_dens_zero (o m : Nat) (h_m_pos : 0 < m) :
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
private theorem cf_of_div_succ_step (o m n : Nat) (h_mod_pos : 0 < o % m) :
    (GenContFract.of ((o:ℚ)/m)).s.get? (n+1) =
      (GenContFract.of ((m:ℚ)/((o % m : Nat) : ℚ))).s.get? n := by
  rw [GenContFract.of_s_succ]
  congr 2
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]

/-- **Joint base case** (Phase 3, r_found_1 prep, added 2026-05-23):
combines `cf_bridge_nums_zero` and `cf_bridge_dens_zero` into the
conjunction form needed by the joint induction (`cf_bridge_full` below). -/
private theorem cf_bridge_full_zero (o m : Nat) (h_m_pos : 0 < m) :
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
private theorem cf_bridge_dens_one (o m : Nat) (h_m_pos : 0 < m)
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
private theorem cf_bridge_nums_one (o m : Nat) (h_m_pos : 0 < m)
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
private theorem s_closest_close_to_k_over_r (m k r : Nat) (h_r_pos : 0 < r) :
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
private theorem khinchin_precond (r N m : Nat) (h_r_pos : 0 < r)
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
private theorem khinchin_applies_to_s_closest
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
private theorem k_over_r_is_convergent
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
private theorem dens_int_valued_pair (v : ℝ) :
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
private theorem dens_int_valued (v : ℝ) (n : Nat) :
    ∃ d : ℤ, (GenContFract.of v).dens n = (d : ℝ) :=
  (dens_int_valued_pair v n).1

/-- **Numerators of `GenContFract.of v` are integer-valued** (paired
form, Phase 3 r_found_1 slice 4b sub-step 2, added 2026-05-23): analogous
to `dens_int_valued_pair`. The base case n=0 uses
`zeroth_num_eq_h` + `of_h_eq_floor` (so `nums 0 = ⌊v⌋`); the n=1
non-terminated case uses `first_num_eq` (giving `nums 1 = b·h + 1`); the
inductive step uses `nums_recurrence` with `a = 1` from
`of_partNum_eq_one_and_exists_int_partDen_eq`. -/
private theorem nums_int_valued_pair (v : ℝ) :
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
private theorem nums_int_valued (v : ℝ) (n : Nat) :
    ∃ d : ℤ, (GenContFract.of v).nums n = (d : ℝ) :=
  (nums_int_valued_pair v n).1

/-- **Determinant identity for `GenContFract.of v`** (Phase 3, r_found_1
slice 4b prep, added 2026-05-23): the standard Bezout-like determinant
identity `p_n q_{n+1} - q_n p_{n+1} = (-1)^(n+1)` for the convergents of
`GenContFract.of v`. Re-stated from mathlib's `SimpContFract.determinant`
via the `SimpContFract.of` packaging — `(SimpContFract.of v : GenContFract)
= GenContFract.of v` definitionally. This is what gives gcd(p_n, q_n) = 1
as integers (modulo upgrading int-valuedness; future tick). -/
private theorem of_v_determinant (v : ℝ) (n : Nat)
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
private theorem of_v_nums_dens_coprime (v : ℝ) (n : Nat)
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

/-- **Denominator equals `r` at the Khinchin-recovered step** (Phase 3
r_found_1 slice 4b sub-step 3, added 2026-05-23): if `convs n = (k/r : ℚ)`
(in ℝ) at a non-terminated step with `gcd(k, r) = 1` and `r > 0`, then
`dens n = (r : ℝ)`. Proof: extract integer-valued `a = nums n`,
`b = dens n`; show `b > 0` via Fibonacci lower bound; coprimality from
`of_v_nums_dens_coprime`; cross-multiply `a/b = k/r` to get the integer
identity `a·r = b·k`; from coprimality of `(a,b)` and `(k,r)` plus
positivity, conclude `b = r` by mutual divisibility. -/
private theorem dens_eq_r_at_convs_eq_kr (v : ℝ) (n : Nat) (k r : Nat)
    (h_not_term : ¬ (GenContFract.of v).TerminatedAt n)
    (h_r_pos : 0 < r) (h_coprime : Nat.gcd k r = 1)
    (h_convs : (GenContFract.of v).convs n = (((k:ℚ)/r : ℚ) : ℝ)) :
    (GenContFract.of v).dens n = (r : ℝ) := by
  obtain ⟨a, ha⟩ := nums_int_valued v n
  obtain ⟨b, hb⟩ := dens_int_valued v n
  have h_not_term' : n = 0 ∨ ¬ (GenContFract.of v).TerminatedAt (n - 1) := by
    by_cases h : n = 0
    · left; exact h
    · right
      intro h_term
      have h_le : n - 1 ≤ n := by omega
      exact h_not_term (GenContFract.terminated_stable h_le h_term)
  have h_fib_le := GenContFract.succ_nth_fib_le_of_nth_den (v := v) (n := n) h_not_term'
  rw [hb] at h_fib_le
  have h_fib_pos : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
  have h_b_pos : 0 < b := by
    have h_pos_R : (0 : ℝ) < (b : ℝ) := by
      calc (0 : ℝ) < (Nat.fib (n + 1) : ℝ) := by exact_mod_cast h_fib_pos
        _ ≤ (b : ℝ) := h_fib_le
    exact_mod_cast h_pos_R
  have h_cop_ab : Int.gcd a b = 1 := of_v_nums_dens_coprime v n h_not_term a b ha hb
  have h_conv : (GenContFract.of v).convs n = (a : ℝ) / (b : ℝ) := by
    rw [GenContFract.conv_eq_num_div_den, ha, hb]
  rw [h_conv] at h_convs
  have h_rhs : ((((k : ℚ) / r : ℚ) : ℝ)) = (k : ℝ) / (r : ℝ) := by push_cast; ring
  rw [h_rhs] at h_convs
  have h_b_ne : (b : ℝ) ≠ 0 := by exact_mod_cast h_b_pos.ne'
  have h_r_ne : (r : ℝ) ≠ 0 := by exact_mod_cast h_r_pos.ne'
  have h_eq : (a : ℝ) * r = (b : ℝ) * k := by
    field_simp at h_convs
    linarith
  have h_int : a * r = b * k := by exact_mod_cast h_eq
  have h_iscop_ab : IsCoprime a b := (Int.isCoprime_iff_gcd_eq_one).mpr h_cop_ab
  have h_b_dvd : b ∣ (r : ℤ) := by
    have h_dvd : b ∣ a * r := ⟨k, by linarith⟩
    exact h_iscop_ab.symm.dvd_of_dvd_mul_left h_dvd
  have h_iscop_kr : IsCoprime (k : ℤ) (r : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    show Int.gcd (k : ℤ) (r : ℤ) = 1
    simp [Int.gcd]; exact h_coprime
  have h_r_dvd : (r : ℤ) ∣ b := by
    have h_dvd : (r : ℤ) ∣ k * b := ⟨a, by linarith⟩
    exact h_iscop_kr.symm.dvd_of_dvd_mul_left h_dvd
  have h_r_pos_Z : (0 : ℤ) < (r : ℤ) := by exact_mod_cast h_r_pos
  have h_b_eq_r : b = (r : ℤ) :=
    Int.dvd_antisymm (Int.le_of_lt h_b_pos) (Int.le_of_lt h_r_pos_Z) h_b_dvd h_r_dvd
  rw [hb, h_b_eq_r]
  push_cast; rfl

/-- **Fibonacci step bound** (Phase 3, r_found_1 prep, added 2026-05-23):
direct restatement of mathlib's `GenContFract.succ_nth_fib_le_of_nth_den` —
if the `N_step`-th denominator of `GenContFract.of v` equals `r`, then
`fib (N_step + 1) ≤ r`. Used downstream to bound `N_step ≤ 2m+1` once we
know `r ≤ N < 2^m`. -/
private theorem dens_eq_fib_bound (v : ℝ) (r N_step : Nat)
    (h_dens : (GenContFract.of v).dens N_step = (r : ℝ))
    (h_not_term : N_step = 0 ∨ ¬ (GenContFract.of v).TerminatedAt (N_step - 1)) :
    (Nat.fib (N_step + 1) : ℝ) ≤ (r : ℝ) := by
  have h := GenContFract.succ_nth_fib_le_of_nth_den (v := v) (n := N_step) h_not_term
  rw [h_dens] at h
  exact h

/-- **Fibonacci grows at least as fast as `2^m`** (Phase 3 r_found_1 slice
4c, added 2026-05-23): `2^m ≤ Nat.fib (2m + 2)`. Proven by induction;
inductive step uses `fib_add_two` + monotonicity `fib_lt_fib_succ`. -/
private theorem pow_two_le_fib (m : Nat) : 2 ^ m ≤ Nat.fib (2 * m + 2) := by
  induction m with
  | zero => simp [Nat.fib]
  | succ k ih =>
    have h_succ : 2 * (k + 1) + 2 = (2 * k + 2) + 2 := by ring
    rw [h_succ]
    rw [Nat.fib_add_two]
    have h_ge_fib : Nat.fib (2*k+2) ≤ Nat.fib (2*k+2+1) := by
      have h2 : (2 : Nat) ≤ 2 * k + 2 := by omega
      exact (Nat.fib_lt_fib_succ h2).le
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≤ 2 * Nat.fib (2 * k + 2) := by omega
      _ ≤ Nat.fib (2 * k + 2) + Nat.fib (2 * k + 2 + 1) := by omega

/-- **Step bound from Fibonacci** (Phase 3 r_found_1 slice 4c, added
2026-05-23): if `fib(N_step + 1) ≤ r < 2^m`, then `N_step ≤ 2m + 1`.
Proof: contradiction; if N_step ≥ 2m + 2, monotonicity gives
`fib(N_step + 1) ≥ fib(2m + 2) ≥ 2^m > r`, contradicting `fib ≤ r`. -/
private theorem fib_step_bound (N_step r m : Nat)
    (h_fib : Nat.fib (N_step + 1) ≤ r) (h_r_lt : r < 2^m) :
    N_step ≤ 2 * m + 1 := by
  by_contra h_not
  push_neg at h_not
  have h_mono : Nat.fib (2 * m + 2) ≤ Nat.fib (N_step + 1) :=
    Nat.fib_mono (by omega)
  have h_pow : 2 ^ m ≤ Nat.fib (2 * m + 2) := pow_two_le_fib m
  omega

/-- **Assembled step bound** (Phase 3 r_found_1 slice 4c, added 2026-05-23):
if `(GenContFract.of v).dens N_step = (r : ℝ)` (with non-termination), and
`r < 2^m`, then `N_step ≤ 2m + 1`. Combines `dens_eq_fib_bound` with the
elementary Fib growth `pow_two_le_fib`. -/
private theorem N_step_le_2m_plus_1 (v : ℝ) (N_step r m : Nat)
    (h_dens : (GenContFract.of v).dens N_step = (r : ℝ))
    (h_not_term : N_step = 0 ∨ ¬ (GenContFract.of v).TerminatedAt (N_step - 1))
    (h_r_lt : r < 2^m) :
    N_step ≤ 2 * m + 1 := by
  have h_fib_R := dens_eq_fib_bound v r N_step h_dens h_not_term
  have h_fib : Nat.fib (N_step + 1) ≤ r := by exact_mod_cast h_fib_R
  exact fib_step_bound N_step r m h_fib h_r_lt

/-- **Order-divides-exponent iff `modexp = 1`** (Phase 3 r_found_1 prep,
added 2026-05-23): standard number-theory fact, `a^d ≡ 1 (mod N) ↔ r ∣ d`,
where `r` is the multiplicative order of `a` mod `N`. Proven elementarily
using division-with-remainder (`d = r * q + s`, `0 ≤ s < r`); the (⇒)
direction uses minimality of `r` to force `s = 0`. Needed downstream for
the OF_post' walking argument: it says the FIRST positive denominator
satisfying `modexp` is a multiple of `r`, and combined with our
denominator monotonicity argument, that first valid denominator IS `r`
itself. -/
private theorem modexp_eq_one_iff_dvd (a N d : Nat) (h_pos : 0 < a) (h_lt : a < N)
    (r : Nat) (h_ord : Order a r N) :
    modexp a d N = 1 ↔ r ∣ d := by
  obtain ⟨h_r_pos, h_r_one, h_r_min⟩ := h_ord
  have h_N : 1 < N := by omega
  unfold modexp
  constructor
  · intro h_eq
    have h_dec : r * (d / r) + d % r = d := Nat.div_add_mod d r
    have h_s_lt : d % r < r := Nat.mod_lt _ h_r_pos
    have h_split : a^d = (a^r)^(d/r) * a^(d % r) := by
      conv_lhs => rw [← h_dec]
      rw [pow_add, pow_mul]
    have h_pow_q : (a^r)^(d/r) % N = 1 := by
      rw [Nat.pow_mod, h_r_one, one_pow]
      exact Nat.one_mod_eq_one.mpr (by omega)
    have h_s_mod : a^(d % r) % N = 1 := by
      have h1 : a^d % N = ((a^r)^(d/r) % N * (a^(d%r) % N)) % N := by
        rw [h_split, Nat.mul_mod]
      rw [h_pow_q, one_mul, Nat.mod_mod] at h1
      rw [← h1]; exact h_eq
    by_contra h_not_dvd
    rw [Nat.dvd_iff_mod_eq_zero] at h_not_dvd
    have h_s_pos : 0 < d % r := by omega
    exact h_r_min (d % r) h_s_pos h_s_lt h_s_mod
  · intro ⟨q, hq⟩
    rw [hq, pow_mul]
    rw [Nat.pow_mod, h_r_one, one_pow]
    exact Nat.one_mod_eq_one.mpr (by omega)

/-- **`OF_post'` returns 0 or a valid denominator** (Phase 3 r_found_1
prep, added 2026-05-23): structural induction on `OF_post'`'s walk. Says:
either `OF_post' step a N o m = 0`, or its value `d` satisfies
`modexp a d N = 1`. By design of the walk: any nonzero return path goes
through an `if modexp a ... = 1` check. This is independent of the
cf_aux ↔ mathlib bridge — pure structural property of the walk. -/
private theorem OF_post'_zero_or_modexp (step a N o m : Nat) :
    OF_post' step a N o m = 0 ∨ modexp a (OF_post' step a N o m) N = 1 := by
  induction step with
  | zero => left; rfl
  | succ k ih =>
    unfold OF_post'
    by_cases h_pre : OF_post' k a N o m = 0
    · rw [h_pre]
      simp only [if_true]
      by_cases h_modexp : modexp a (OF_post_step k o m) N = 1
      · right; rw [if_pos h_modexp]; exact h_modexp
      · left; rw [if_neg h_modexp]
    · simp only [h_pre, if_false]
      rcases ih with hpre0 | hmod
      · exact absurd hpre0 h_pre
      · right; exact hmod

/-- **`OF_post'` returns 0 or a multiple of `r`** (Phase 3 r_found_1
prep, added 2026-05-23): one-line corollary combining
`OF_post'_zero_or_modexp` with `modexp_eq_one_iff_dvd`. Any nonzero
return value of `OF_post'` must be a multiple of the order `r`. Combined
with the denominator bound `≤ r` (from monotonicity at the right step),
the only valid nonzero return is `r` itself. -/
private theorem OF_post'_dvd_r (step a N o m : Nat)
    (h_pos : 0 < a) (h_lt : a < N) (r : Nat) (h_ord : Order a r N) :
    OF_post' step a N o m = 0 ∨ r ∣ OF_post' step a N o m := by
  rcases OF_post'_zero_or_modexp step a N o m with hzero | hmod
  · left; exact hzero
  · right; exact (modexp_eq_one_iff_dvd a N _ h_pos h_lt r h_ord).mp hmod

/-- **`OF_post'_nonzero_pre`** (added 2026-05-24, port of SQIR `Shor.v:989`):
if `OF_post' step` is nonzero, then it equals `OF_post_step x o m` for some
`x < step` (the walk found a step where modexp passed). By induction on step. -/
private theorem OF_post'_nonzero_pre (step a N o m : Nat)
    (h_ne : OF_post' step a N o m ≠ 0) :
    ∃ x, x < step ∧ OF_post_step x o m = OF_post' step a N o m := by
  induction step with
  | zero => exact absurd rfl h_ne
  | succ k ih =>
    show ∃ x, x < k + 1 ∧ OF_post_step x o m = OF_post' (k+1) a N o m
    by_cases h_pre : OF_post' k a N o m = 0
    · -- At step k+1, pre = 0. Result is OF_post_step k (if modexp passes) or 0.
      have h_unfold : OF_post' (k+1) a N o m
          = (if modexp a (OF_post_step k o m) N = 1
             then OF_post_step k o m else 0) := by
        show (let pre := OF_post' k a N o m
              if pre = 0 then
                (if modexp a (OF_post_step k o m) N = 1
                 then OF_post_step k o m else 0)
              else pre) = _
        simp [h_pre]
      rw [h_unfold] at h_ne ⊢
      by_cases h_mod : modexp a (OF_post_step k o m) N = 1
      · refine ⟨k, by omega, ?_⟩
        rw [if_pos h_mod]
      · exact absurd (by rw [if_neg h_mod]) h_ne
    · -- At step k+1, pre ≠ 0. Result = pre. Apply IH.
      have h_unfold : OF_post' (k+1) a N o m = OF_post' k a N o m := by
        show (let pre := OF_post' k a N o m
              if pre = 0 then _ else pre) = _
        simp [h_pre]
      rw [h_unfold] at h_ne ⊢
      obtain ⟨x, h_x_lt, h_x_eq⟩ := ih h_ne
      exact ⟨x, by omega, h_x_eq⟩

/-- **`OF_post'` stable once nonzero** (added 2026-05-24, port of SQIR
`Shor.v:979`): once `OF_post'` is nonzero at some depth `step`, it stays
equal for all higher depths `x + step`. By induction on x: the def's
"if pre = 0 then check else pre" guard preserves the nonzero value. -/
private theorem OF_post'_nonzero_equal (x step a N o m : Nat)
    (h_ne : OF_post' step a N o m ≠ 0) :
    OF_post' (x + step) a N o m = OF_post' step a N o m := by
  induction x with
  | zero =>
    show OF_post' (0 + step) a N o m = OF_post' step a N o m
    rw [Nat.zero_add]
  | succ x' ih =>
    have h_eq : x' + 1 + step = (x' + step) + 1 := by ring
    rw [h_eq]
    show (let pre := OF_post' (x' + step) a N o m
          if pre = 0 then
            (if modexp a (OF_post_step (x' + step) o m) N = 1
             then OF_post_step (x' + step) o m else 0)
          else pre) = OF_post' step a N o m
    have h_ih_ne : OF_post' (x' + step) a N o m ≠ 0 := by rw [ih]; exact h_ne
    simp only [if_neg h_ih_ne]
    exact ih

/-- **Mathlib-side OF_post_step** (Phase 3 r_found_1 bridge target, added
2026-05-23): integer-valued analog of our `OF_post_step` (which uses
`cf_aux`-based `ContinuedFraction`), defined via mathlib's `GenContFract.of`
with `dens_int_valued`. Bridges to our `OF_post_step` will be the
remaining work. -/
noncomputable def mathlib_OF_post_step (step o m : Nat) : ℤ :=
  Classical.choose (dens_int_valued ((o : ℝ) / (2 ^ m : ℝ)) step)

/-- Spec for `mathlib_OF_post_step`: equals the mathlib `dens` value. -/
private theorem mathlib_OF_post_step_spec (step o m : Nat) :
    (GenContFract.of ((o : ℝ) / (2 ^ m : ℝ))).dens step =
      ((mathlib_OF_post_step step o m : ℤ) : ℝ) :=
  Classical.choose_spec (dens_int_valued ((o : ℝ) / (2 ^ m : ℝ)) step)

/-- `mathlib_OF_post_step` is non-negative: convergent denominators are
non-negative (`zero_le_of_den`), so the integer extraction is ≥ 0. -/
private theorem mathlib_OF_post_step_nonneg (step o m : Nat) :
    0 ≤ mathlib_OF_post_step step o m := by
  have h_nn := GenContFract.zero_le_of_den (v := (o : ℝ) / (2^m : ℝ)) (n := step)
  rw [mathlib_OF_post_step_spec step o m] at h_nn
  exact_mod_cast h_nn

/-- The Nat-valued version of `mathlib_OF_post_step`, via `Int.toNat`. -/
noncomputable def mathlib_OF_post_step_nat (step o m : Nat) : Nat :=
  (mathlib_OF_post_step step o m).toNat

/-- Spec connecting the Nat version to the Int version: equal when
non-negative, which is always true (`mathlib_OF_post_step_nonneg`). -/
private theorem mathlib_OF_post_step_nat_int (step o m : Nat) :
    ((mathlib_OF_post_step_nat step o m : Nat) : ℤ) = mathlib_OF_post_step step o m := by
  unfold mathlib_OF_post_step_nat
  exact Int.toNat_of_nonneg (mathlib_OF_post_step_nonneg step o m)

/-- **Monotonicity of integer-valued `mathlib_OF_post_step`** (Phase 3
r_found_1, added 2026-05-24): direct from mathlib's `of_den_mono`. -/
private theorem mathlib_OF_post_step_mono (step o m : Nat) :
    mathlib_OF_post_step step o m ≤ mathlib_OF_post_step (step+1) o m := by
  have h_mono := GenContFract.of_den_mono
    (v := ((o : ℝ) / (2^m : ℝ))) (n := step)
  rw [mathlib_OF_post_step_spec step o m,
      mathlib_OF_post_step_spec (step+1) o m] at h_mono
  exact_mod_cast h_mono

/-- **Monotonicity of `mathlib_OF_post_step_nat`** — Nat-level. -/
private theorem mathlib_OF_post_step_nat_mono (step o m : Nat) :
    mathlib_OF_post_step_nat step o m ≤ mathlib_OF_post_step_nat (step+1) o m := by
  have h := mathlib_OF_post_step_mono step o m
  have h_nn1 := mathlib_OF_post_step_nonneg step o m
  have h_nn2 := mathlib_OF_post_step_nonneg (step+1) o m
  have h_int1 := mathlib_OF_post_step_nat_int step o m
  have h_int2 := mathlib_OF_post_step_nat_int (step+1) o m
  have : ((mathlib_OF_post_step_nat step o m : Nat) : ℤ) ≤
         ((mathlib_OF_post_step_nat (step+1) o m : Nat) : ℤ) := by
    rw [h_int1, h_int2]; exact h
  exact_mod_cast this

/-- **Generalized step-by-step monotonicity for `mathlib_OF_post_step_nat`**
(transitive closure of the one-step version): `i ≤ j → dens_nat i ≤ dens_nat j`. -/
private theorem mathlib_OF_post_step_nat_mono_le (o m i j : Nat) (h : i ≤ j) :
    mathlib_OF_post_step_nat i o m ≤ mathlib_OF_post_step_nat j o m := by
  induction j with
  | zero =>
    interval_cases i
    exact Nat.le_refl _
  | succ k ih =>
    by_cases h_eq : i = k + 1
    · subst h_eq; exact Nat.le_refl _
    · have h_le_k : i ≤ k := by omega
      exact Nat.le_trans (ih h_le_k) (mathlib_OF_post_step_nat_mono k o m)

/-- **Fibonacci lower bound on `mathlib_OF_post_step`** (Phase 3 r_found_1
infrastructure, added 2026-05-24): direct restatement of mathlib's
`succ_nth_fib_le_of_nth_den` in terms of our integer-valued
`mathlib_OF_post_step`. When the continued fraction has not terminated
before step `n`, the n-th convergent denominator is at least `fib(n+1)`. -/
private theorem mathlib_OF_post_step_fib_ge (o m n : Nat)
    (h_not_term : n = 0 ∨ ¬ (GenContFract.of ((o : ℝ) / (2^m : ℝ))).TerminatedAt (n - 1)) :
    (Nat.fib (n + 1) : ℤ) ≤ mathlib_OF_post_step n o m := by
  have h := GenContFract.succ_nth_fib_le_of_nth_den
    (v := ((o : ℝ) / (2^m : ℝ))) (n := n) h_not_term
  rw [mathlib_OF_post_step_spec n o m] at h
  exact_mod_cast h

/-- **Fibonacci lower bound on `mathlib_OF_post_step_nat`** — Nat-level. -/
private theorem mathlib_OF_post_step_nat_fib_ge (o m n : Nat)
    (h_not_term : n = 0 ∨ ¬ (GenContFract.of ((o : ℝ) / (2^m : ℝ))).TerminatedAt (n - 1)) :
    Nat.fib (n + 1) ≤ mathlib_OF_post_step_nat n o m := by
  have h := mathlib_OF_post_step_fib_ge o m n h_not_term
  have h_int := mathlib_OF_post_step_nat_int n o m
  have : ((Nat.fib (n + 1) : Nat) : ℤ) ≤ ((mathlib_OF_post_step_nat n o m : Nat) : ℤ) := by
    rw [h_int]; exact h
  exact_mod_cast this

/-- **Positivity of `mathlib_OF_post_step_nat`** (when not terminated):
denominators are at least 1, since `fib(n+1) ≥ 1` for all `n`. -/
private theorem mathlib_OF_post_step_nat_pos (o m n : Nat)
    (h_not_term : n = 0 ∨ ¬ (GenContFract.of ((o : ℝ) / (2^m : ℝ))).TerminatedAt (n - 1)) :
    0 < mathlib_OF_post_step_nat n o m := by
  have h_fib_pos : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
  have h_fib_le := mathlib_OF_post_step_nat_fib_ge o m n h_not_term
  omega

/-- **`OF_post_step` at step 0 is 1** (Phase 3 r_found_1 bridge, added
2026-05-23): direct unfold of `cf_aux 1 o (2^m) 0 1 1 0`. Since `2^m ≠ 0`,
one cf_aux step yields `(a, 1)` and the depth-0 base case returns
`(p_curr, q_curr) = (a, 1)`, giving denominator 1. -/
private theorem OF_post_step_zero (o m : Nat) : OF_post_step 0 o m = 1 := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux 1 o (2^m) 0 1 1 0).2 = 1
  unfold cf_aux
  simp
  rfl

/-- **`OF_post_step` at step 1 when divisible**: if `o % 2^m = 0` then
`OF_post_step 1 o m = 1`. cf_aux unfolding: first step gives `(a, 1)`
then depth-0 with `m = 0` returns `(p_curr, q_curr) = (a, 1)`. -/
private theorem OF_post_step_one_div (o m : Nat) (h_mod : o % (2^m) = 0) :
    OF_post_step 1 o m = 1 := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux 2 o (2^m) 0 1 1 0).2 = 1
  unfold cf_aux
  simp
  unfold cf_aux
  simp [h_mod]

/-- **`OF_post_step` at step 1 when not divisible**: if `o % 2^m ≠ 0`
then `OF_post_step 1 o m = (2^m) / (o % 2^m)`. -/
private theorem OF_post_step_one_nondiv (o m : Nat) (h_mod : o % (2^m) ≠ 0) :
    OF_post_step 1 o m = (2^m) / (o % 2^m) := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux 2 o (2^m) 0 1 1 0).2 = (2^m) / (o % 2^m)
  unfold cf_aux
  simp
  unfold cf_aux
  simp [h_mod]
  rfl

/-- **`OF_post_step` at step 2 when divisible**: if `o % 2^m = 0` then
`OF_post_step 2 o m = 1`. cf_aux unfolds 3 times; the m=0 case in the
inner Euclidean step returns `q_curr = 1`. -/
private theorem OF_post_step_two_div (o m : Nat) (h_mod : o % (2^m) = 0) :
    OF_post_step 2 o m = 1 := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux 3 o (2^m) 0 1 1 0).2 = 1
  unfold cf_aux
  simp
  unfold cf_aux
  simp [h_mod]

/-- **`OF_post_step` for general n when divisible** (Phase 3 r_found_1,
added 2026-05-24): if `o % 2^m = 0` then `OF_post_step n o m = 1` for
ALL n. cf_aux unfolds once, then the inner state has `m = 0` which
terminates with `q_curr = 1` at any depth ≥ 1. The depth-0 case
specializes to `(cf_aux 0 ...).2 = q_curr = 1`. -/
private theorem OF_post_step_div_general (n o m : Nat) (h_mod : o % (2^m) = 0) :
    OF_post_step n o m = 1 := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux (n + 1) o (2^m) 0 1 1 0).2 = 1
  unfold cf_aux
  simp
  cases n with
  | zero => rfl
  | succ k =>
    rw [h_mod]
    unfold cf_aux
    simp

/-- **`OF_post_step` step 1 specialized to `o < 2^m`** (Shor use case,
added 2026-05-24 tick 62): when `o < 2^m` and `o > 0`, the cf_aux step-1
output simplifies via `o % 2^m = o` to `OF_post_step 1 o m = 2^m / o`.
This is the typical case for s_closest (which is < 2^m). -/
private theorem OF_post_step_one_shor (o m : Nat) (h_o_pos : 0 < o)
    (h_o_lt : o < 2^m) :
    OF_post_step 1 o m = (2^m) / o := by
  have h_mod_eq : o % (2^m) = o := Nat.mod_eq_of_lt h_o_lt
  unfold OF_post_step ContinuedFraction
  show (cf_aux 2 o (2^m) 0 1 1 0).2 = (2^m) / o
  unfold cf_aux
  simp
  unfold cf_aux
  rw [h_mod_eq]
  simp [h_o_pos.ne']
  rfl

/-- **Shor-case bridge analysis observation** (Phase 3 r_found_1, tick 63):
For `o < 2^m` (the Shor use case for s_closest), cf_aux's first step is
"trivial" (a = o/(2^m) = 0): from initial `(0, 1, 1, 0)` it transitions to
`(1, 0, 0, 1)` and then runs `cf_aux n (2^m) o 1 0 0 1`. This is cf_aux on
the SWAPPED rational `2^m/o` but with a SWAPPED initial state — NOT the
standard ContinuedFraction call. The swap maps cf_aux dens output to
mathlib's nums output for the inverted ratio. Captured as design intent;
formalization is multi-tick. -/
private def shor_case_cf_aux_swap_intent : Prop := True  -- placeholder doc

/-- **Mathlib's `dens 1` for `o/2^m`, divisible case**: when `o % 2^m = 0`,
the input is an integer, the stream terminates immediately, and
`dens 1 = dens 0 = 1`. -/
private theorem mathlib_dens_one_div (o m : Nat) (h_mod : o % (2^m) = 0) :
    (GenContFract.of (((o : ℝ)) / ((2^m : Nat) : ℝ))).dens 1 = 1 := by
  have h_pow_pos : 0 < 2^m := Nat.two_pow_pos m
  have h_dvd : (2^m : Nat) ∣ o := Nat.dvd_of_mod_eq_zero h_mod
  have h_pow_ne : ((2^m : Nat) : ℝ) ≠ 0 := by exact_mod_cast h_pow_pos.ne'
  have h_int_eq : (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) = (((o / 2^m : Nat) : ℤ) : ℝ) := by
    have h1 : ((o / 2^m : Nat) : ℝ) = ((o : Nat) : ℝ) / ((2^m : Nat) : ℝ) :=
      Nat.cast_div h_dvd h_pow_ne
    rw [show (((o / 2^m : Nat) : ℤ) : ℝ) = ((o / 2^m : Nat) : ℝ) from by push_cast; rfl]
    exact h1.symm
  rw [h_int_eq]
  have h_s_nil := GenContFract.of_s_of_int ℝ ((o / 2^m : Nat) : ℤ)
  have h_term : (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).TerminatedAt 0 := by
    rw [GenContFract.terminatedAt_iff_s_terminatedAt]
    show (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).s.get? 0 = none
    rw [h_s_nil]
    rfl
  rw [GenContFract.dens_stable_of_terminated (n := 0) (m := 1) (by omega) h_term]
  exact GenContFract.zeroth_den_eq_one

/-- **Mathlib's `dens 1` for `o/2^m`, non-divisible case**: when
`o % 2^m ≠ 0`, applying `of_s_head` + `first_den_eq` +
`Int.fract_div_natCast_eq_div_natCast_mod` + `Rat.floor_natCast_div_natCast`
gives `dens 1 = ⌊2^m / (o % 2^m)⌋ = (2^m) / (o % 2^m)`. -/
private theorem mathlib_dens_one_nondiv (o m : Nat) (h_mod : o % (2^m) ≠ 0) :
    (GenContFract.of (((o : ℝ)) / ((2^m : Nat) : ℝ))).dens 1
      = (((2^m) / (o % 2^m) : Nat) : ℝ) := by
  have h_pow_pos : 0 < 2^m := Nat.two_pow_pos m
  have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) ≠ 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_mod_pos : 0 < o % (2^m) := Nat.pos_of_ne_zero h_mod
    have h_num_pos : (0 : ℝ) < ((o % (2^m) : Nat) : ℝ) := by exact_mod_cast h_mod_pos
    have h_pow_pos_R : (0 : ℝ) < ((2^m : Nat) : ℝ) := by exact_mod_cast h_pow_pos
    positivity
  have h_head := GenContFract.of_s_head (K := ℝ)
    (v := (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ))) h_fract_ne
  have h_first := GenContFract.first_den_eq
    (g := GenContFract.of (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ)))
    (gp := { a := 1, b := ↑⌊(Int.fract (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ)))⁻¹⌋ })
    (zeroth_s_eq := by
      show (GenContFract.of (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ))).s.get? 0 = some _
      rw [show (GenContFract.of (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ))).s.get? 0
           = (GenContFract.of (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ))).s.head from rfl]
      exact h_head)
  rw [h_first]
  show (↑⌊(Int.fract ((↑o : ℝ) / ((2 ^ m : Nat) : ℝ)))⁻¹⌋ : ℝ)
       = ((2 ^ m / (o % 2 ^ m) : Nat) : ℝ)
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
  have h_eq : (((2^m : Nat) : ℝ) / ((o % 2^m : Nat) : ℝ))
            = ((((2^m : Nat) : ℚ) / ((o % 2^m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  rw [h_eq, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  push_cast
  rfl

/-- **Cast normalization for the GenContFract.of argument**: the two forms
`(o : ℝ) / (2^m : ℝ)` and `(o : ℝ) / ((2^m : Nat) : ℝ)` are equal. Used
to convert between the form needed by mathlib_OF_post_step_spec and the
form produced by GenContFract.of unfolding. -/
private theorem of_arg_cast_norm (o m : Nat) :
    (((o : ℝ)) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) := by push_cast; rfl

/-- **Mathlib's `dens 2` for `o/2^m`, divisible case**: when `o % 2^m = 0`,
the input is an integer, the stream terminates immediately, and
`dens 2 = dens 0 = 1`. Same proof as step-1 divisible case but with
`dens_stable_of_terminated` extended to step 2. -/
private theorem mathlib_dens_two_div (o m : Nat) (h_mod : o % (2^m) = 0) :
    (GenContFract.of (((o : ℝ)) / ((2^m : Nat) : ℝ))).dens 2 = 1 := by
  have h_pow_pos : 0 < 2^m := Nat.two_pow_pos m
  have h_dvd : (2^m : Nat) ∣ o := Nat.dvd_of_mod_eq_zero h_mod
  have h_pow_ne : ((2^m : Nat) : ℝ) ≠ 0 := by exact_mod_cast h_pow_pos.ne'
  have h_int_eq : (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) = (((o / 2^m : Nat) : ℤ) : ℝ) := by
    have h1 : ((o / 2^m : Nat) : ℝ) = ((o : Nat) : ℝ) / ((2^m : Nat) : ℝ) :=
      Nat.cast_div h_dvd h_pow_ne
    rw [show (((o / 2^m : Nat) : ℤ) : ℝ) = ((o / 2^m : Nat) : ℝ) from by push_cast; rfl]
    exact h1.symm
  rw [h_int_eq]
  have h_s_nil := GenContFract.of_s_of_int ℝ ((o / 2^m : Nat) : ℤ)
  have h_term : (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).TerminatedAt 0 := by
    rw [GenContFract.terminatedAt_iff_s_terminatedAt]
    show (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).s.get? 0 = none
    rw [h_s_nil]
    rfl
  rw [GenContFract.dens_stable_of_terminated (n := 0) (m := 2) (by omega) h_term]
  exact GenContFract.zeroth_den_eq_one

/-- **Mathlib's `dens n` for `o/2^m`, divisible case (general n)**: when
`o % 2^m = 0`, the input is an integer, the stream terminates immediately,
and `dens n = 1` for all n. Generalization of mathlib_dens_two_div. -/
private theorem mathlib_dens_div_general (o m : Nat) (n : Nat) (h_mod : o % (2^m) = 0) :
    (GenContFract.of (((o : ℝ)) / ((2^m : Nat) : ℝ))).dens n = 1 := by
  have h_pow_pos : 0 < 2^m := Nat.two_pow_pos m
  have h_dvd : (2^m : Nat) ∣ o := Nat.dvd_of_mod_eq_zero h_mod
  have h_pow_ne : ((2^m : Nat) : ℝ) ≠ 0 := by exact_mod_cast h_pow_pos.ne'
  have h_int_eq : (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) = (((o / 2^m : Nat) : ℤ) : ℝ) := by
    have h1 : ((o / 2^m : Nat) : ℝ) = ((o : Nat) : ℝ) / ((2^m : Nat) : ℝ) :=
      Nat.cast_div h_dvd h_pow_ne
    rw [show (((o / 2^m : Nat) : ℤ) : ℝ) = ((o / 2^m : Nat) : ℝ) from by push_cast; rfl]
    exact h1.symm
  rw [h_int_eq]
  have h_s_nil := GenContFract.of_s_of_int ℝ ((o / 2^m : Nat) : ℤ)
  have h_term : (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).TerminatedAt 0 := by
    rw [GenContFract.terminatedAt_iff_s_terminatedAt]
    show (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).s.get? 0 = none
    rw [h_s_nil]
    rfl
  by_cases h_n : n = 0
  · rw [h_n]; exact GenContFract.zeroth_den_eq_one
  · rw [GenContFract.dens_stable_of_terminated (n := 0) (m := n) (by omega) h_term]
    exact GenContFract.zeroth_den_eq_one

/-- **KEY RECURRENCE: mathlib's stream Euclidean shift = cf_aux's Euclidean
step** (Phase 3 r_found_1, added 2026-05-24): for `o, m : Nat` with `m > 0`
and `o % m ≠ 0`, mathlib's `IntFractPair.stream` at step `n+1` for `o/m`
equals the stream at step `n` for `m/(o%m)`. This is the structural bridge
between mathlib's `(Int.fract v)⁻¹` recursion and our cf_aux's Euclidean
state update `(o, m) ↦ (m, o%m)`. With this recurrence, the cf_aux ↔
mathlib bridge becomes provable by induction. -/
private theorem stream_succ_euclidean (o m : Nat) (h_m_pos : 0 < m)
    (h_mod : o % m ≠ 0) (n : Nat) :
    GenContFract.IntFractPair.stream (((o : ℝ)) / ((m : Nat) : ℝ)) (n+1)
      = GenContFract.IntFractPair.stream (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ)) n := by
  have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) ≠ 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_mod_pos : 0 < o % m := Nat.pos_of_ne_zero h_mod
    have h_num_pos : (0 : ℝ) < ((o % m : Nat) : ℝ) := by exact_mod_cast h_mod_pos
    have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
    positivity
  rw [GenContFract.IntFractPair.stream_succ h_fract_ne n]
  congr 1
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]

/-- **Generalized mathlib int-valued dens for arbitrary `(o, m)`**: extracts
the integer-valued denominator of `(GenContFract.of (o/m))` at step `n` for
arbitrary m (not just powers of 2). Needed for the non-divisible-case bridge
which recurses through arbitrary Euclidean states. -/
noncomputable def mathlib_dens_int_gen (n o m : Nat) : ℤ :=
  Classical.choose (dens_int_valued (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) n)

/-- Spec for `mathlib_dens_int_gen`. -/
private theorem mathlib_dens_int_gen_spec (n o m : Nat) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).dens n =
      ((mathlib_dens_int_gen n o m : ℤ) : ℝ) :=
  Classical.choose_spec (dens_int_valued (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) n)

/-- **`mathlib_dens_int_gen 0 o m = 1`**: base case for the generalized
mathlib int-valued dens at step 0 (independent of `o, m`). Follows
directly from mathlib's `zeroth_den_eq_one`. -/
private theorem mathlib_dens_int_gen_zero (o m : Nat) :
    mathlib_dens_int_gen 0 o m = 1 := by
  have h_spec := mathlib_dens_int_gen_spec 0 o m
  rw [GenContFract.zeroth_den_eq_one] at h_spec
  exact_mod_cast h_spec.symm

/-- **`mathlib_dens_int_gen n o m ≥ 0`**: non-negativity of the generalized
int-valued dens. From `GenContFract.zero_le_of_den`. -/
private theorem mathlib_dens_int_gen_nonneg (n o m : Nat) :
    0 ≤ mathlib_dens_int_gen n o m := by
  have h_nn := GenContFract.zero_le_of_den
    (v := (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) (n := n)
  rw [mathlib_dens_int_gen_spec n o m] at h_nn
  exact_mod_cast h_nn

/-- **`mathlib_dens_int_gen` Fibonacci lower bound** (general version of
`mathlib_OF_post_step_fib_ge`): when not terminated before step `n`,
`fib (n+1) ≤ mathlib_dens_int_gen n o m`. -/
private theorem mathlib_dens_int_gen_fib_ge (o m n : Nat)
    (h_not_term : n = 0 ∨
      ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt (n - 1)) :
    (Nat.fib (n + 1) : ℤ) ≤ mathlib_dens_int_gen n o m := by
  have h := GenContFract.succ_nth_fib_le_of_nth_den
    (v := (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) (n := n) h_not_term
  rw [mathlib_dens_int_gen_spec n o m] at h
  exact_mod_cast h

/-- **Mathlib's `nums 0` for `o/m`** (ℝ-version): direct from
`zeroth_num_eq_h` + `of_h_eq_floor` + `Rat.floor_natCast_div_natCast` +
`Rat.floor_cast`. The 0-th convergent numerator equals `o / m` as Nat. -/
private theorem mathlib_nums_zero_eq (o m : Nat) (_h_m_pos : 0 < m) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).nums 0
      = ((o / m : Nat) : ℝ) := by
  rw [GenContFract.zeroth_num_eq_h, GenContFract.of_h_eq_floor]
  rw [show ((((o : Nat) : ℝ) / ((m : Nat) : ℝ)) : ℝ)
      = ((((o : Nat) : ℚ) / ((m : Nat) : ℚ) : ℚ) : ℝ) from by push_cast; ring]
  rw [Rat.floor_cast, Rat.floor_natCast_div_natCast]
  push_cast; rfl

/-- **Mathlib's `dens 0` for `o/m`** (ℝ-version): direct from
`zeroth_den_eq_one`. The 0-th convergent denominator is always 1. -/
private theorem mathlib_dens_zero_eq (o m : Nat) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).dens 0 = 1 :=
  GenContFract.zeroth_den_eq_one

/-- **Mathlib's `dens 1` for `o/m`, non-terminated** (ℝ-version): when
`o % m ≠ 0`, `dens 1 = m/(o%m)`. Via `of_s_head` + `first_den_eq` +
`Int.fract_div_natCast_eq_div_natCast_mod` + `Rat.floor_natCast_div_natCast`. -/
private theorem mathlib_dens_one_eq_nondiv (o m : Nat) (h_m_pos : 0 < m)
    (h_mod : o % m ≠ 0) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).dens 1
      = ((m / (o % m) : Nat) : ℝ) := by
  have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
  have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) ≠ 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_mod_pos : 0 < o % m := Nat.pos_of_ne_zero h_mod
    have h_num_pos : (0 : ℝ) < ((o % m : Nat) : ℝ) := by exact_mod_cast h_mod_pos
    positivity
  have h_head := GenContFract.of_s_head (K := ℝ)
    (v := (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))) h_fract_ne
  have h_first := GenContFract.first_den_eq
    (g := GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ)))
    (gp := { a := 1, b := ↑⌊(Int.fract (((o : ℕ) : ℝ) / ((m : Nat) : ℝ)))⁻¹⌋ })
    (zeroth_s_eq := by
      show (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.get? 0 = some _
      rw [show (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.get? 0
           = (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.head from rfl]
      exact h_head)
  rw [h_first]
  show (↑⌊(Int.fract ((↑o : ℝ) / ((m : Nat) : ℝ)))⁻¹⌋ : ℝ)
       = ((m / (o % m) : Nat) : ℝ)
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
  have h_eq : (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))
            = ((((m : Nat) : ℚ) / ((o % m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  rw [h_eq, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  push_cast
  rfl

/-- **Mathlib's `nums 1` for `o/m`, non-terminated** (ℝ-version): when
`o % m ≠ 0`, `nums 1 = (m/(o%m)) * (o/m) + 1` (Nat-cast). Uses
`first_num_eq` (which gives `nums 1 = b·h + 1` where `a=1` from
SimpContFract) + floor computations + `norm_cast` to clean up Int/Nat
division mismatches. -/
private theorem mathlib_nums_one_eq_nondiv (o m : Nat) (h_m_pos : 0 < m)
    (h_mod : o % m ≠ 0) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).nums 1
      = ((m / (o % m) * (o / m) + 1 : Nat) : ℝ) := by
  have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) ≠ 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_mod_pos : 0 < o % m := Nat.pos_of_ne_zero h_mod
    have h_num_pos : (0 : ℝ) < ((o % m : Nat) : ℝ) := by exact_mod_cast h_mod_pos
    have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
    positivity
  have h_head := GenContFract.of_s_head (K := ℝ)
    (v := (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))) h_fract_ne
  have h_first := GenContFract.first_num_eq
    (g := GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ)))
    (gp := { a := 1, b := ↑⌊(Int.fract (((o : ℕ) : ℝ) / ((m : Nat) : ℝ)))⁻¹⌋ })
    (zeroth_s_eq := by
      show (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.get? 0 = some _
      rw [show (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.get? 0
           = (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.head from rfl]
      exact h_head)
  rw [h_first]
  rw [GenContFract.of_h_eq_floor]
  show (↑⌊(Int.fract ((↑o : ℝ) / ((m : Nat) : ℝ)))⁻¹⌋ : ℝ) *
       ⌊((↑o : ℝ) / ((m : Nat) : ℝ))⌋ + 1
       = ((m / (o % m) * (o / m) + 1 : Nat) : ℝ)
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
  have h_eq1 : (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))
            = ((((m : Nat) : ℚ) / ((o % m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  have h_eq2 : (((o : Nat) : ℝ) / ((m : Nat) : ℝ))
            = ((((o : Nat) : ℚ) / ((m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  rw [h_eq1, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  rw [h_eq2, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  norm_cast

/-- **n=0 base case of the joint state-tracking invariant** (Phase 3
r_found_1, added 2026-05-24 tick 73): when `m > 0` and the CF isn't
terminated at step 0, cf_aux_full's depth-2 state matches mathlib's
(nums 0, nums 1, dens 0, dens 1). Combines `cf_aux_full_2_nondiv` (LHS
explicit value) with the four mathlib step-0/step-1 helpers. -/
private theorem cf_aux_full_matches_mathlib_zero (o m : Nat) (h_m_pos : 0 < m)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0) :
    (GenContFract.of ((o : ℝ) / m)).nums 0 = (((cf_aux_full 2 o m 0 1 1 0).1 : Nat) : ℝ) ∧
    (GenContFract.of ((o : ℝ) / m)).nums 1 = (((cf_aux_full 2 o m 0 1 1 0).2.1 : Nat) : ℝ) ∧
    (GenContFract.of ((o : ℝ) / m)).dens 0 = (((cf_aux_full 2 o m 0 1 1 0).2.2.1 : Nat) : ℝ) ∧
    (GenContFract.of ((o : ℝ) / m)).dens 1 = (((cf_aux_full 2 o m 0 1 1 0).2.2.2 : Nat) : ℝ) := by
  have h_mod : o % m ≠ 0 := nondiv_of_not_terminated_zero o m h_not_term
  have h_cast : ((o : ℝ) / m) = (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) := by push_cast; rfl
  rw [cf_aux_full_2_nondiv o m h_m_pos h_mod]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_cast]; exact mathlib_nums_zero_eq o m h_m_pos
  · rw [h_cast]; exact mathlib_nums_one_eq_nondiv o m h_m_pos h_mod
  · rw [h_cast, mathlib_dens_zero_eq]; simp
  · rw [h_cast]; exact mathlib_dens_one_eq_nondiv o m h_m_pos h_mod

/-- **Parametric general bridge invariant** (Phase 3 r_found_1, added
2026-05-24 by direction "focus on Legendre_ContinuedFraction sorries"):
The CRUX of the cf_aux ↔ mathlib bridge.

For any `n`, any current cf_aux Euclidean state `(o, m)` (with `m > 0`),
and any initial cf_aux_full state `(p_prev, p_curr, q_prev, q_curr)`
matching mathlib's `contsAux` at indices `(K, K+1)` for some `v0`, and
provided the Euclidean iteration of `(o, m)` produces the right partial
denominators `b_K, b_{K+1}, ...` of `v0`'s continued fraction, then after
`n` cf_aux steps the state matches mathlib's `contsAux` at `(K+n, K+n+1)`.

This is the GENERAL form that subsumes the specific-initial-state versions.
The succ case proof uses `contsAux_recurrence` (mathlib) and `cf_aux_succ_pos`
(local) — they have STRUCTURALLY identical recurrences modulo a Nat ↔ ℝ cast.

Succ case is the SINGLE remaining cf_aux ↔ mathlib structural sorry. -/
private theorem cf_aux_full_general_match
    (n : Nat) (o m : Nat) (h_m_pos : 0 < m)
    (v0 : ℝ) (K : Nat)
    (p_prev p_curr q_prev q_curr : Nat)
    (h_state :
      ((p_prev : ℝ) = ((GenContFract.of v0).contsAux K).a) ∧
      ((p_curr : ℝ) = ((GenContFract.of v0).contsAux (K+1)).a) ∧
      ((q_prev : ℝ) = ((GenContFract.of v0).contsAux K).b) ∧
      ((q_curr : ℝ) = ((GenContFract.of v0).contsAux (K+1)).b))
    (_h_eucl : ∀ i : ℕ, ¬ (GenContFract.of v0).TerminatedAt (K + i) →
      (GenContFract.of v0).s.get? (K + i) =
        some ⟨1, (((euclidean_iter i o m).1 / (euclidean_iter i o m).2 : Nat) : ℝ)⟩)
    (_h_not_term : ¬ (GenContFract.of v0).TerminatedAt (K + n)) :
    (((cf_aux_full n o m p_prev p_curr q_prev q_curr).1 : Nat) : ℝ)
        = ((GenContFract.of v0).contsAux (K + n)).a ∧
    (((cf_aux_full n o m p_prev p_curr q_prev q_curr).2.1 : Nat) : ℝ)
        = ((GenContFract.of v0).contsAux (K + n + 1)).a ∧
    (((cf_aux_full n o m p_prev p_curr q_prev q_curr).2.2.1 : Nat) : ℝ)
        = ((GenContFract.of v0).contsAux (K + n)).b ∧
    (((cf_aux_full n o m p_prev p_curr q_prev q_curr).2.2.2 : Nat) : ℝ)
        = ((GenContFract.of v0).contsAux (K + n + 1)).b := by
  induction n generalizing o m p_prev p_curr q_prev q_curr K with
  | zero =>
    -- n=0: cf_aux_full 0 returns the initial state directly; h_state matches.
    simp only [cf_aux_full, Nat.add_zero]
    exact ⟨h_state.1, h_state.2.1, h_state.2.2.1, h_state.2.2.2⟩
  | succ k ih =>
    -- Step 1: Unfold cf_aux_full (k+1) o m (...) using m > 0.
    rw [show cf_aux_full (k+1) o m p_prev p_curr q_prev q_curr
          = cf_aux_full k m (o%m) p_curr ((o/m)*p_curr + p_prev)
                                  q_curr ((o/m)*q_curr + q_prev) from by
      show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
            else cf_aux_full k m (o%m) p_curr ((o/m)*p_curr + p_prev)
                                       q_curr ((o/m)*q_curr + q_prev)) = _
      rw [if_neg h_m_pos.ne']]
    -- Step 2: Case split on o%m. If 0, mathlib terminates at K+1 contradicting
    -- h_not_term at K+k+1 ≥ K+1 (assuming k can be anything; but we still need
    -- to prove this rigorously, hence the sub-sorry). If > 0, apply IH at k
    -- with shifted parameters.
    by_cases h_om : o % m = 0
    · -- o%m = 0: derive contradiction.
      -- Strategy: case split on Terminated at (K+1).
      -- - If Terminated: by terminated_stable + K+1 ≤ K+(k+1), contradicts h_not_term.
      -- - If ¬ Terminated: h_eucl @ 1 forces s.get? (K+1) = some ⟨1, m/0 = 0⟩.
      --   But mathlib's IntFractPair.one_le_succ_nth_stream_b says b ≥ 1. Contradiction.
      exfalso
      by_cases h_term_K1 : (GenContFract.of v0).TerminatedAt (K + 1)
      · -- Case 1: Terminated at K+1 → Terminated at K+(k+1) by stable → contradicts h_not_term.
        apply _h_not_term
        exact GenContFract.terminated_stable (by omega : K + 1 ≤ K + (k + 1)) h_term_K1
      · -- Case 2: ¬ Terminated at K+1 → derive impossible stream value.
        have h_eucl_1 := _h_eucl 1 (by
          show ¬ (GenContFract.of v0).TerminatedAt (K + 1)
          have : K + 1 = K + 1 := rfl
          exact h_term_K1)
        -- h_eucl_1 : s.get? (K+1) = some ⟨1, ((euclidean_iter 1 o m).1 / .2 : Nat) : ℝ⟩.
        -- With o%m = 0 and m > 0: euclidean_iter 1 o m = (m, 0), quotient = m/0 = 0.
        have h_iter_1 : euclidean_iter 1 o m = (m, 0) := by
          show (if m = 0 then (o, m) else euclidean_iter 0 m (o%m)) = _
          rw [if_neg h_m_pos.ne', h_om]
          rfl
        rw [h_iter_1] at h_eucl_1
        simp at h_eucl_1
        -- h_eucl_1 : s.get? (K+1) = some ⟨1, 0⟩.
        -- Extract: ∃ ifp, stream v0 (K+2) = some ifp ∧ ↑ifp.b = 0.
        obtain ⟨ifp, h_stream, h_b_eq⟩ :=
          GenContFract.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some h_eucl_1
        -- h_b_eq : (↑ifp.b : ℝ) = (⟨1, 0⟩ : GenContFract.Pair ℝ).b
        simp only [show ((⟨1, 0⟩ : GenContFract.Pair ℝ).b) = (0 : ℝ) from rfl] at h_b_eq
        have h_ifp_b_zero : ifp.b = 0 := by exact_mod_cast h_b_eq
        -- Mathlib: stream v (n+1) = some ifp → 1 ≤ ifp.b. Contradiction.
        have h_one_le := GenContFract.IntFractPair.one_le_succ_nth_stream_b h_stream
        omega
    · -- o%m > 0: apply IH with new (o', m') := (m, o%m), K' := K+1.
      have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
      -- Step (a): get s.get? K from h_eucl at i=0.
      have h_K_lt : K ≤ K + (k+1) := by omega
      have h_not_term_K : ¬ (GenContFract.of v0).TerminatedAt K := fun h =>
        _h_not_term (GenContFract.terminated_stable h_K_lt h)
      have h_eucl_0 := _h_eucl 0 h_not_term_K
      -- Simplify euclidean_iter 0 o m = (o, m).
      have h_iter_0 : euclidean_iter 0 o m = (o, m) := rfl
      rw [Nat.add_zero, h_iter_0] at h_eucl_0
      -- h_eucl_0 : s.get? K = some ⟨1, ((o/m : Nat) : ℝ)⟩
      -- Step (b): compute contsAux (K+2) via contsAux_recurrence with gp := ⟨1, o/m⟩.
      have h_contsAux_K : (GenContFract.of v0).contsAux K = ⟨(p_prev : ℝ), (q_prev : ℝ)⟩ :=
        GenContFract.Pair.mk.injEq .. |>.mpr ⟨h_state.1.symm, h_state.2.2.1.symm⟩
      have h_contsAux_K1 : (GenContFract.of v0).contsAux (K + 1) =
          ⟨(p_curr : ℝ), (q_curr : ℝ)⟩ :=
        GenContFract.Pair.mk.injEq .. |>.mpr ⟨h_state.2.1.symm, h_state.2.2.2.symm⟩
      have h_contsAux_K2 := GenContFract.contsAux_recurrence
        (g := GenContFract.of v0) (n := K) h_eucl_0 h_contsAux_K h_contsAux_K1
      -- h_contsAux_K2 : contsAux (K+2) = ⟨(o/m)·p_curr + 1·p_prev, (o/m)·q_curr + 1·q_prev⟩
      -- Step (c): build h_eucl' for new (m, o%m) at K+1, via h_eucl@(i+1).
      have h_eucl' : ∀ i : ℕ, ¬ (GenContFract.of v0).TerminatedAt (K + 1 + i) →
          (GenContFract.of v0).s.get? (K + 1 + i) =
            some ⟨1, (((euclidean_iter i m (o%m)).1 / (euclidean_iter i m (o%m)).2 : Nat) : ℝ)⟩ := by
        intros i h_nt
        have h_shift : K + 1 + i = K + (i + 1) := by ring
        rw [h_shift] at h_nt ⊢
        have h := _h_eucl (i+1) h_nt
        -- euclidean_iter (i+1) o m = euclidean_iter i m (o%m) (since m > 0).
        have h_iter_shift : euclidean_iter (i+1) o m = euclidean_iter i m (o%m) := by
          show (if m = 0 then (o, m) else euclidean_iter i m (o%m)) = euclidean_iter i m (o%m)
          rw [if_neg h_m_pos.ne']
        rw [h_iter_shift] at h
        exact h
      -- Step (d): build h_not_term' at K+1+k = K+(k+1).
      have h_not_term' : ¬ (GenContFract.of v0).TerminatedAt (K + 1 + k) := by
        have : K + 1 + k = K + (k + 1) := by ring
        rw [this]; exact _h_not_term
      -- Step (e): build h_state' for new state.
      have h_state' :
          (((p_curr : Nat) : ℝ) = ((GenContFract.of v0).contsAux (K+1)).a) ∧
          ((((o/m)*p_curr + p_prev : Nat) : ℝ) = ((GenContFract.of v0).contsAux (K+1+1)).a) ∧
          (((q_curr : Nat) : ℝ) = ((GenContFract.of v0).contsAux (K+1)).b) ∧
          ((((o/m)*q_curr + q_prev : Nat) : ℝ) = ((GenContFract.of v0).contsAux (K+1+1)).b) := by
        refine ⟨h_state.2.1, ?_, h_state.2.2.2, ?_⟩
        · -- ((o/m)*p_curr + p_prev : Nat) : ℝ = contsAux (K+2) .a
          have : K + 1 + 1 = K + 2 := by ring
          rw [this, h_contsAux_K2]
          push_cast; ring
        · -- ((o/m)*q_curr + q_prev : Nat) : ℝ = contsAux (K+2) .b
          have : K + 1 + 1 = K + 2 := by ring
          rw [this, h_contsAux_K2]
          push_cast; ring
      -- Apply IH.
      have h_apply :=
        ih m (o%m) h_om_pos (K+1) p_curr ((o/m)*p_curr + p_prev) q_curr ((o/m)*q_curr + q_prev)
            h_state' h_eucl' h_not_term'
      -- Goal: cf_aux_full k m (o%m) ... matches contsAux at (K+(k+1), K+(k+1)+1).
      -- IH gives matching at (K+1+k, K+1+k+1). Just rewrite K+(k+1) → K+1+k.
      have h_idx : K + (k + 1) = K + 1 + k := by ring
      rw [h_idx]
      exact h_apply

/-- **ℝ-version of `cf_of_div_succ_step`** (added 2026-05-24): the (n+1)-th
stream entry of `GenContFract.of (o/m : ℝ)` equals the n-th of
`GenContFract.of (m/(o%m) : ℝ)`. Same proof as the ℚ version. -/
private theorem cf_of_div_succ_step_R (o m n : Nat) (_h_mod_pos : 0 < o % m) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.get? (n+1) =
      (GenContFract.of (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))).s.get? n := by
  rw [GenContFract.of_s_succ]
  congr 2
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]

/-- **Terminated at 0 when `o % m = 0`** (added 2026-05-24): when the
remainder is 0 (including the m = 0 case, where o % 0 = o ≠ 0 doesn't
hold but v = 0/0 = 0 ℝ still gives terminated), mathlib's CF for v = o/m
terminates at step 0. Extracted from the inline proof in
`eucl_iter_match_stream`. -/
private theorem terminated_at_0_when_mod_zero (o m : Nat) (h_om : o % m = 0) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0 := by
  rw [GenContFract.terminatedAt_iff_s_none]
  have h_fract_eq : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) = 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod, h_om]
    simp
  have h_stream_none : GenContFract.IntFractPair.stream
      (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 1 = none :=
    GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero (n := 0) rfl h_fract_eq
  rw [GenContFract.of_s_head_aux, h_stream_none]
  rfl

/-- **Converse base case** (added 2026-05-24): when mathlib's CF terminates
at step 0 for v=o/m with m > 0, then o%m = 0.

This is the j=0 base case of the eventual `eucl_terminated_of_mathlib_terminated`
helper. Direct from `nondiv_of_not_terminated_zero`'s contrapositive. -/
private theorem mod_zero_of_terminated_at_0 (o m : Nat) (_h_m_pos : 0 < m)
    (h_term : (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0) :
    o % m = 0 := by
  by_contra h_om_ne
  -- nondiv_of_not_terminated_zero: ¬ Terminated at 0 → o%m ≠ 0.
  -- We have Terminated at 0 and want o%m = 0.
  -- The lemma's contrapositive (o%m = 0 → Terminated at 0) goes the wrong way.
  -- Need direct proof: Terminated at 0 → fract v = 0 → o%m = 0.
  apply h_om_ne
  -- Goal: o % m = 0.
  -- From Terminated at 0: s.get? 0 = none → stream 1 = none → fract v = 0 → o%m = 0.
  rw [GenContFract.terminatedAt_iff_s_none] at h_term
  rw [GenContFract.of_s_head_aux] at h_term
  -- h_term : Option.bind (stream v 1) ... = none
  -- So stream v 1 = none.
  have h_stream_1 : GenContFract.IntFractPair.stream
      (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 1 = none := by
    rcases h_eq : GenContFract.IntFractPair.stream
        (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 1 with _ | ifp
    · rfl
    · rw [h_eq] at h_term; exact absurd h_term (by simp)
  -- stream 1 = none → fract v = 0.
  rw [GenContFract.IntFractPair.succ_nth_stream_eq_none_iff] at h_stream_1
  -- h_stream_1 : stream 0 = none ∨ ∃ ifp, stream 0 = some ifp ∧ ifp.fr = 0
  rcases h_stream_1 with h_s0_none | ⟨ifp, h_s0, h_fr⟩
  · -- stream 0 = none: impossible (stream 0 is always some).
    have : GenContFract.IntFractPair.stream
        (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 0 =
        some (GenContFract.IntFractPair.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) := rfl
    rw [this] at h_s0_none
    exact absurd h_s0_none (by simp)
  · -- stream 0 = some ifp, ifp.fr = 0.
    -- stream 0 = some {b=⌊v⌋, fr=fract v}, so ifp.fr = fract v = 0.
    have h_s0_val : GenContFract.IntFractPair.stream
        (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 0 =
        some (GenContFract.IntFractPair.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) := rfl
    rw [h_s0_val] at h_s0
    have h_ifp_eq : ifp = GenContFract.IntFractPair.of
        (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) := by
      exact (Option.some_inj.mp h_s0).symm
    rw [h_ifp_eq] at h_fr
    -- h_fr : (intFractPair.of v).fr = 0 = fract v = 0.
    have h_fr_eq : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) = 0 := h_fr
    rw [Int.fract_div_natCast_eq_div_natCast_mod] at h_fr_eq
    -- h_fr_eq : (o % m : ℝ) / (m : ℝ) = 0
    have h_m_ne : ((m : Nat) : ℝ) ≠ 0 := by
      exact_mod_cast _h_m_pos.ne'
    have : ((o % m : Nat) : ℝ) = 0 := by
      field_simp at h_fr_eq
      linarith
    exact_mod_cast this

/-- **Converse direction: mathlib-terminated → Euclidean-terminated** (added
2026-05-24): when mathlib's CF terminates at step j for v=o/m (m > 0),
cf_aux's Euclidean iteration has hit `.2 = 0` by step j+1.

Proof: induction on j. Base via `mod_zero_of_terminated_at_0`. Succ uses
`cf_of_div_succ_step_R` to shift mathlib's view + IH at (m, o%m). -/
private theorem eucl_terminated_of_mathlib_terminated (o m : Nat) (h_m_pos : 0 < m)
    (j : Nat) (h_term : (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt j) :
    (euclidean_iter (j+1) o m).2 = 0 := by
  induction j generalizing o m with
  | zero =>
    have h_om : o % m = 0 := mod_zero_of_terminated_at_0 o m h_m_pos h_term
    show (if m = 0 then (o, m) else euclidean_iter 0 m (o % m)).2 = 0
    rw [if_neg h_m_pos.ne']
    exact h_om
  | succ j' ih =>
    by_cases h_om : o % m = 0
    · -- o%m = 0: mathlib already terminated at 0, so euclidean_iter 1 hits 0.
      -- Use stability to extend.
      have h_eucl_1 : (euclidean_iter 1 o m).2 = 0 := by
        show (if m = 0 then (o, m) else euclidean_iter 0 m (o % m)).2 = 0
        rw [if_neg h_m_pos.ne']
        exact h_om
      have h_assoc : j' + 2 = 1 + (j' + 1) := by ring
      rw [h_assoc]
      exact eucl_iter_stable 1 o m (j' + 1) h_eucl_1
    · -- o%m > 0: shift via cf_of_div_succ_step_R + apply IH at (m, o%m).
      have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
      have h_term' : (GenContFract.of (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))).TerminatedAt j' := by
        rw [GenContFract.terminatedAt_iff_s_none] at h_term ⊢
        rw [← cf_of_div_succ_step_R o m j' h_om_pos]
        exact h_term
      have h_ih := ih m (o % m) h_om_pos h_term'
      -- h_ih : (euclidean_iter (j'+1) m (o%m)).2 = 0
      -- Need: (euclidean_iter (j'+2) o m).2 = 0
      have h_assoc : j' + 2 = (j' + 1) + 1 := by ring
      rw [h_assoc]
      show (if m = 0 then (o, m) else euclidean_iter (j' + 1) m (o % m)).2 = 0
      rw [if_neg h_m_pos.ne']
      exact h_ih

/-- **Mathlib-terminated ↔ Euclidean-terminated bridge** (added 2026-05-24):
when cf_aux's Euclidean iteration hits `.2 = 0` at step `j+1`, mathlib's
CF stream for `v = o/m` terminates at step `j`. This is the last piece
needed to close the terminated-case bridge in `TODO_non_div_terminated_stable`.

Proof: induction on `j`. The base case uses `terminated_at_0_when_mod_zero`.
The succ case shifts via `cf_of_div_succ_step_R` and applies IH at the
shifted Euclidean state. -/
private theorem mathlib_terminated_of_eucl_terminated (o m : Nat) (h_m_pos : 0 < m)
    (j : Nat) (h_eucl : (euclidean_iter (j+1) o m).2 = 0) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt j := by
  induction j generalizing o m with
  | zero =>
    -- h_eucl : (euclidean_iter 1 o m).2 = (m, o%m).2 = o%m = 0 (since m > 0)
    have h_eucl_unfold : euclidean_iter 1 o m = (m, o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter 0 m (o%m)) = _
      rw [if_neg h_m_pos.ne']; rfl
    rw [h_eucl_unfold] at h_eucl
    -- h_eucl : o % m = 0
    exact terminated_at_0_when_mod_zero o m h_eucl
  | succ j' ih =>
    -- h_eucl : (euclidean_iter (j'+2) o m).2 = 0
    have h_assoc : j' + 2 = (j' + 1) + 1 := by ring
    rw [h_assoc] at h_eucl
    have h_unfold : euclidean_iter ((j' + 1) + 1) o m = euclidean_iter (j' + 1) m (o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter (j' + 1) m (o % m)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_unfold] at h_eucl
    -- h_eucl : (euclidean_iter (j'+1) m (o%m)).2 = 0
    by_cases h_om : o % m = 0
    · -- o%m = 0: TerminatedAt 0 + terminated_stable.
      have h_term_0 : (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0 :=
        terminated_at_0_when_mod_zero o m h_om
      exact GenContFract.terminated_stable (by omega : 0 ≤ j' + 1) h_term_0
    · -- o%m > 0: shift via cf_of_div_succ_step_R + apply IH.
      have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
      have h_ih := ih m (o % m) h_om_pos h_eucl
      -- h_ih : TerminatedAt j' for v' = m/(o%m).
      -- Want: TerminatedAt (j'+1) for v = o/m. Bridge via cf_of_div_succ_step_R.
      rw [GenContFract.terminatedAt_iff_s_none] at h_ih ⊢
      rw [cf_of_div_succ_step_R o m j' h_om_pos]
      exact h_ih

/-- **Eucl iter ↔ mathlib stream correspondence** (added 2026-05-24):
For `v = o/m` with `m > 0`, mathlib's `s.get? i = some ⟨1, x⟩` where
`x = quotient of the (i+1)-th Euclidean iterate of (o, m)`. By induction
on i using `cf_of_div_succ_step_R` and the i=0 case from `of_s_head` +
floor computations.

This is the `h_eucl` hypothesis the general lemma needs, computed for the
specific case where v0 = o/m and the cf_aux call uses (m, o%m) as initial
Euclidean state. -/
private theorem eucl_iter_match_stream (o m : Nat) (h_m_pos : 0 < m) (i : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt i) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.get? i =
      some ⟨1, (((euclidean_iter (i+1) o m).1 / (euclidean_iter (i+1) o m).2 : Nat) : ℝ)⟩ := by
  induction i generalizing o m with
  | zero =>
    -- Base case: s.get? 0 = some ⟨1, ⌊1/Int.fract v⌋⟩ via of_s_head.
    -- ¬ Terminated at 0 → o%m ≠ 0 → fract v ≠ 0 → use of_s_head.
    have h_om : o % m ≠ 0 := nondiv_of_not_terminated_zero o m h_not_term
    have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
    have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
    have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) ≠ 0 := by
      rw [Int.fract_div_natCast_eq_div_natCast_mod]
      have h_num_pos : (0 : ℝ) < ((o % m : Nat) : ℝ) := by exact_mod_cast h_om_pos
      positivity
    have h_head := GenContFract.of_s_head (K := ℝ)
      (v := (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))) h_fract_ne
    -- h_head : s.head = some ⟨1, ⌊(Int.fract v)⁻¹⌋⟩
    rw [show (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.get? 0
         = (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.head from rfl,
        h_head]
    congr 2
    -- Goal: ⌊(Int.fract (o/m))⁻¹⌋ = ((euclidean_iter 1 o m).1 / .2 : Nat) : ℝ
    have h_iter_1 : (euclidean_iter 1 o m) = (m, o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter 0 m (o%m)) = _
      rw [if_neg h_m_pos.ne']; rfl
    rw [h_iter_1]
    -- Goal: ↑⌊(Int.fract (o/m))⁻¹⌋ = ((m / (o%m) : Nat) : ℝ)
    rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
    -- Goal: ↑⌊(m : ℝ) / (o%m : ℝ)⌋ = ((m / (o%m) : Nat) : ℝ)
    have h_eq : (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))
              = ((((m : Nat) : ℚ) / ((o % m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
    rw [h_eq, Rat.floor_cast, Rat.floor_natCast_div_natCast]
    push_cast; rfl
  | succ j ih =>
    -- Inductive case: use cf_of_div_succ_step_R to shift to (m, o%m), apply IH.
    -- Need ¬ Terminated at j+1 for v=o/m. By stream_succ_eq_none_iff, if Terminated at 0
    -- (o%m = 0), then Terminated at j+1 too. So ¬ Terminated at j+1 → o%m ≠ 0.
    have h_om : o % m ≠ 0 := by
      intro h
      apply h_not_term
      apply GenContFract.terminated_stable (by omega : 0 ≤ j + 1)
      -- Show TerminatedAt 0 for v=o/m when o%m = 0.
      rw [GenContFract.terminatedAt_iff_s_none]
      -- s.get? 0 = none. Use of_s_head_aux + stream_eq_none_of_fr_eq_zero.
      have h_fract_eq : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) = 0 := by
        rw [Int.fract_div_natCast_eq_div_natCast_mod, h]
        simp
      have h_stream_none : GenContFract.IntFractPair.stream
          (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 1 = none :=
        GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero (n := 0) rfl h_fract_eq
      rw [GenContFract.of_s_head_aux, h_stream_none]
      rfl
    have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
    -- Shift: s.get? (j+1) for o/m = s.get? j for m/(o%m).
    rw [cf_of_div_succ_step_R o m j h_om_pos]
    -- Apply IH at (m, o%m) at index j.
    have h_not_term_shifted :
        ¬ (GenContFract.of (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))).TerminatedAt j := by
      intro h_term
      apply h_not_term
      -- TerminatedAt at j+1 for o/m ↔ s.get? (j+1) for o/m = none.
      rw [GenContFract.terminatedAt_iff_s_none] at h_term ⊢
      rw [cf_of_div_succ_step_R o m j h_om_pos]
      exact h_term
    have h_ih := ih m (o%m) h_om_pos h_not_term_shifted
    rw [h_ih]
    congr 2
    -- Goal: euclidean_iter (j+1) m (o%m) = euclidean_iter (j+2) o m.
    have h_shift : euclidean_iter (j+2) o m = euclidean_iter (j+1) m (o%m) := by
      show (if m = 0 then (o, m) else euclidean_iter (j+1) m (o%m)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_shift]

/-- **`cf_aux_full_matches_mathlib_strong`** (Phase 3 r_found_1, added
2026-05-24 via bridge-consolidation tick): cf_aux_full's depth-(n+2) output
on `(o, m, 0, 1, 1, 0)` matches mathlib's `(nums n, nums (n+1), dens n,
dens (n+1))` for `v = o/m`.

Hypothesis: `¬ Terminated at (n+1)` (stronger than the weaker variant — this
makes the proof go through cleanly via the general lemma without needing
case analysis on whether matlibs's CF terminates exactly at n+1).

Proof: peel off Stage A's first cf_aux step (uses m > 0); state matches
`contsAux 0/1` for v = o/m; apply `cf_aux_full_general_match` at K=0, depth
n+1, with `eucl_iter_match_stream` providing h_eucl. -/
private theorem cf_aux_full_matches_mathlib_strong (o m : Nat) (h_m_pos : 0 < m)
    (n : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt (n+1)) :
    (((cf_aux_full (n+2) o m 0 1 1 0).1 : Nat) : ℝ) =
        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (n+1)).a ∧
    (((cf_aux_full (n+2) o m 0 1 1 0).2.1 : Nat) : ℝ) =
        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (n+2)).a ∧
    (((cf_aux_full (n+2) o m 0 1 1 0).2.2.1 : Nat) : ℝ) =
        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (n+1)).b ∧
    (((cf_aux_full (n+2) o m 0 1 1 0).2.2.2 : Nat) : ℝ) =
        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (n+2)).b := by
  -- Stage A peel: cf_aux_full (n+2) o m 0 1 1 0 = cf_aux_full (n+1) m (o%m) 1 (o/m) 0 1.
  have h_peel : cf_aux_full (n+2) o m 0 1 1 0
      = cf_aux_full (n+1) m (o%m) 1 (o/m) 0 1 := by
    show (if m = 0 then _ else cf_aux_full (n+1) m (o%m) 1 ((o/m)*1+0) 0 ((o/m)*0+1)) = _
    rw [if_neg h_m_pos.ne']
    simp [Nat.mul_zero, Nat.mul_one]
  rw [h_peel]
  -- Apply general lemma. v0 := o/m, K := 0, (o', m') := (m, o%m), n' := n+1.
  -- Need: m' = o%m > 0. Derive from ¬ Terminated at (n+1) → ¬ Terminated at 0 → o%m > 0.
  have h_not_term_0 : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0 :=
    fun h => h_not_term (GenContFract.terminated_stable (by omega : 0 ≤ n+1) h)
  have h_om : o % m ≠ 0 := nondiv_of_not_terminated_zero o m h_not_term_0
  have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
  -- Build h_state: initial state (1, o/m, 0, 1) matches contsAux 0/1 for v=o/m.
  have h_zero_contsAux : ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 0).a = 1 ∧
                        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 0).b = 0 := by
    rw [GenContFract.zeroth_contAux_eq_one_zero]; exact ⟨rfl, rfl⟩
  -- contsAux 1 = ⟨h, 1⟩ where h = ⌊v⌋ = o/m (Nat-div).
  have h_one_contsAux_a : ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).a
                          = ((o / m : Nat) : ℝ) := by
    -- Use nth_cont_eq_succ_nth_contAux + zeroth_num_eq_h equivalent reasoning.
    -- Actually mathlib_nums_zero_eq gives nums 0 = o/m as ℝ.
    have := mathlib_nums_zero_eq o m h_m_pos
    -- nums 0 = (g.contsAux 1).a (by definitions). So we can rewrite.
    show ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).a
       = ((o / m : Nat) : ℝ)
    rw [show ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).a
         = (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).nums 0 from rfl]
    exact this
  have h_one_contsAux_b : ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).b
                          = 1 := by
    show ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).b = 1
    rw [show ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).b
         = (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).dens 0 from rfl]
    exact GenContFract.zeroth_den_eq_one
  have h_state :
      (((1 : Nat) : ℝ) = ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 0).a) ∧
      ((((o/m : Nat) : ℝ)) = ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (0+1)).a) ∧
      (((0 : Nat) : ℝ) = ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 0).b) ∧
      (((1 : Nat) : ℝ) = ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (0+1)).b) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_zero_contsAux.1]; push_cast; rfl
    · rw [h_one_contsAux_a]
    · rw [h_zero_contsAux.2]; push_cast; rfl
    · rw [h_one_contsAux_b]; push_cast; rfl
  -- Build h_eucl: at iter i ¬ Terminated at i → s.get? i = some ⟨1, eucl_iter i m (o%m)⟩.
  have h_eucl : ∀ i : ℕ,
      ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt (0 + i) →
      (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.get? (0 + i) =
        some ⟨1, (((euclidean_iter i m (o%m)).1 / (euclidean_iter i m (o%m)).2 : Nat) : ℝ)⟩ := by
    intros i h_nt
    rw [Nat.zero_add] at h_nt ⊢
    rw [eucl_iter_match_stream o m h_m_pos i h_nt]
    -- Goal: some ⟨1, ↑((euclidean_iter (i+1) o m).1/.2)⟩ = some ⟨1, ↑((euclidean_iter i m (o%m)).1/.2)⟩
    have h_shift : euclidean_iter (i+1) o m = euclidean_iter i m (o%m) := by
      show (if m = 0 then (o, m) else euclidean_iter i m (o%m))
          = euclidean_iter i m (o%m)
      rw [if_neg h_m_pos.ne']
    rw [h_shift]
  -- Apply general lemma.
  have h_not_term' : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt (0 + (n+1)) := by
    rw [Nat.zero_add]; exact h_not_term
  have h_general := cf_aux_full_general_match (n+1) m (o%m) h_om_pos
    (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 0 1 (o/m) 0 1 h_state h_eucl h_not_term'
  -- h_general's RHS uses index `0 + (n+1)` and `0 + (n+1) + 1`. Simplify.
  rw [Nat.zero_add] at h_general
  exact h_general

/-- **Convergent recurrence for `GenContFract.of`** (Phase 3 r_found_1
infrastructure, added 2026-05-24 tick 59): the n+1-th convergent of v
equals `⌊v⌋ + 1/(n-th convergent of (Int.fract v)⁻¹)`. Direct from
mathlib's `Real.convergent_succ` + `Real.convs_eq_convergent` (which
bridges `Real.convergent` Rat-valued and `GenContFract.convs` Real-valued).
This is the building block for the dens/nums recurrence relations
needed by the cf_aux ↔ mathlib bridge. -/
private theorem of_convs_succ_via_fract (v : ℝ) (n : Nat) :
    (GenContFract.of v).convs (n + 1) =
      (⌊v⌋ : ℝ) + ((GenContFract.of (Int.fract v)⁻¹).convs n)⁻¹ := by
  rw [Real.convs_eq_convergent v, Real.convs_eq_convergent (Int.fract v)⁻¹]
  rw [Real.convergent_succ]
  push_cast
  ring

/-- **Specialized convs swap when `0 < o < m`** (Phase 3 r_found_1,
added 2026-05-24 tick 60): when `o < m`, `⌊o/m⌋ = 0`, so the convergent
recurrence simplifies to a pure SWAP — the (n+1)th convergent of `o/m`
is the inverse of the n-th convergent of `m/o`. Crucial structural
property for the bridge when starting in the "fractional" regime. -/
private theorem of_convs_succ_lt (o m : Nat) (h_lt : o < m) (h_o_pos : 0 < o)
    (n : Nat) :
    (GenContFract.of (((o : ℝ)) / ((m : Nat) : ℝ))).convs (n + 1) =
      ((GenContFract.of (((m : Nat) : ℝ) / ((o : Nat) : ℝ))).convs n)⁻¹ := by
  have h_m_pos : 0 < m := by omega
  have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
  have h_o_pos_R : (0 : ℝ) < ((o : Nat) : ℝ) := by exact_mod_cast h_o_pos
  rw [Real.convs_eq_convergent, Real.convs_eq_convergent, Real.convergent_succ]
  have h_floor : ⌊((o : ℕ) : ℝ) / ((m : ℕ) : ℝ)⌋ = 0 := by
    apply Int.floor_eq_zero_iff.mpr
    constructor
    · positivity
    · rw [show (1 : ℝ) = (m : ℝ) / m by field_simp]
      apply div_lt_div_of_pos_right (by exact_mod_cast h_lt) h_pow_pos_R
  have h_fract : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ))
                = ((o : Nat) : ℝ) / ((m : Nat) : ℝ) := by
    unfold Int.fract
    rw [h_floor]
    simp
  rw [h_floor, h_fract, inv_div]
  push_cast
  ring

/-- **`of_correctness_of_terminatedAt` accessor**: when `GenContFract.of v`
terminates at step `n`, the n-th convergent equals `v` exactly. Used
for rational-input correctness — once the CF terminates, we recover the
input rational. -/
private theorem mathlib_convs_at_term (v : ℝ) (n : Nat)
    (h_term : (GenContFract.of v).TerminatedAt n) :
    (GenContFract.of v).convs n = v :=
  (GenContFract.of_correctness_of_terminatedAt h_term).symm

/-- Connect `mathlib_dens_int_gen` (general) to `mathlib_OF_post_step`
(specialized to `m = 2^bit`): they agree by spec uniqueness when both
extract the same dens value. -/
private theorem mathlib_dens_int_gen_eq_OF_post_step (n o m : Nat) :
    mathlib_dens_int_gen n o (2^m) = mathlib_OF_post_step n o m := by
  have h1 := mathlib_dens_int_gen_spec n o (2^m)
  have h2 := mathlib_OF_post_step_spec n o m
  have h_cast : (((o : ℝ)) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) := by push_cast; rfl
  rw [h_cast] at h1
  have h_eq : ((mathlib_dens_int_gen n o (2^m) : ℤ) : ℝ) =
              ((mathlib_OF_post_step n o m : ℤ) : ℝ) := by
    rw [← h1, ← h2]
  exact_mod_cast h_eq

/-- **Strategy for the cf_aux ↔ mathlib bridge** (Phase 3 r_found_1,
documentation):

The bridge `mathlib_dens_int_gen n o m = cf_aux's q_curr after evolving from
initial state via n Euclidean steps` cannot be proved by simple induction on `n`
because cf_aux's recursive call uses NEW inputs `(m, o % m)` while
mathlib's `dens (n+1)` for `o/m` involves the SAME `o/m`. The connection
is via mathlib's `of_s_succ`: `(GenContFract.of (o/m)).s.get? (n+1) =
(GenContFract.of (m/(o%m))).s.get? n`, plus our `stream_succ_euclidean`.

The right joint invariant tracks cf_aux's running state `(p_prev, p_curr,
q_prev, q_curr)` against mathlib's (nums offset, nums (offset+1), dens
offset, dens (offset+1)) for an evolving offset. Each Euclidean step of
cf_aux advances offset by 1 in mathlib's framework. The succ case of the
joint induction then uses `nums_recurrence`/`dens_recurrence` to extend
both sides by one more step.

This invariant is mechanically constructable but proof-wise complex
(multi-tick effort). For now, captured here as design intent. -/
private def cf_aux_bridge_invariant : Prop := True  -- placeholder docs

/-- **Empirical bridge validation by case enumeration**: hand-traced
proof that step-2 cf_aux output and mathlib dens(2) match for both
sub-cases (verified informally in tick 55 PROGRESS.md notes).

Case A (`o%2^m ≠ 0` AND `(2^m)%(o%2^m) = 0`): both sides give `(2^m)/(o%2^m)`.
  - cf_aux: a' = (2^m)/(o%2^m), stream terminates at step 1, dens(2) = dens(1) = a'.
Case B (`o%2^m ≠ 0` AND `(2^m)%(o%2^m) ≠ 0`): both sides give `a''·a' + 1`.
  - cf_aux: returns (a''·(a'·a+1)+a, a''·a'+1).
  - mathlib: b_0 = a', b_1 = a'', dens(2) = b_1·dens(1) + dens(0) = a''·a' + 1.

This case-enumeration validates the proof pattern. The general n-step proof
follows the SAME mechanism but inducted: cf_aux's "current after Euclidean
shift" matches mathlib's "dens at corresponding shifted offset". The
inductive step uses `dens_recurrence` + the Euclidean shift via
`stream_succ_euclidean`. Mechanical but ~50-100 lines. -/
private def cf_aux_step_2_validated : Prop := True  -- empirical validation marker

-- (General bridge scaffold moved later — needs `mathlib_OF_post_step_nat_eq_OF_post_step_div_general`.)

/-- **Bridge for general n in the divisible case** (Phase 3 r_found_1
breakthrough, added 2026-05-24): when `o % 2^m = 0`, both sides equal 1
for all n. Combines `OF_post_step_div_general` and `mathlib_dens_div_general`. -/
private theorem mathlib_OF_post_step_nat_eq_OF_post_step_div_general
    (n o m : Nat) (h_mod : o % (2^m) = 0) :
    mathlib_OF_post_step_nat n o m = OF_post_step n o m := by
  unfold mathlib_OF_post_step_nat
  have h_spec := mathlib_OF_post_step_spec n o m
  have h_cast : (((o : ℝ)) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) := by push_cast; rfl
  have h_dens := mathlib_dens_div_general o m n h_mod
  rw [h_cast] at h_dens
  rw [h_dens] at h_spec
  have h_int : mathlib_OF_post_step n o m = 1 := by exact_mod_cast h_spec.symm
  rw [h_int, OF_post_step_div_general n o m h_mod]
  rfl

/-- **Non-boundary bridge** (added 2026-05-24, REPLACES general version per
John's design recommendation): `mathlib_OF_post_step_nat n o m = OF_post_step
n o m` whenever mathlib's CF has NOT terminated by step `(n+1)`. The boundary
case (terminated exactly at `n+1` but not at `n`) is excluded.

The boundary case was proof-engineering debt without conceptual content. For
`r_found_1`'s use, the non-boundary hypothesis is always satisfied (via
N_step + dens_eq_r_at_convs_eq_kr arguments).

Hypothesis `¬ TerminatedAt (n+1)` IMPLIES:
- `¬ TerminatedAt 0` (by terminated_stable contrapositive),
- hence `o % (2^m) ≠ 0` (non-divisibility, via nondiv_of_not_terminated_zero),
- and `¬ TerminatedAt n` (also by contrapositive), letting us apply strong. -/
private theorem mathlib_OF_post_step_nat_eq_OF_post_step_nonboundary
    (n o m : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).TerminatedAt (n+1)) :
    mathlib_OF_post_step_nat n o m = OF_post_step n o m := by
  -- Derive ¬ Terminated at 0 from h_not_term (terminated_stable contrapositive).
  have h_not_term_0 : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).TerminatedAt 0 := by
    intro h
    exact h_not_term (GenContFract.terminated_stable (by omega : 0 ≤ n+1) h)
  -- Derive o % (2^m) ≠ 0 (non-divisibility).
  have h_mod : o % (2^m) ≠ 0 := nondiv_of_not_terminated_zero o (2^m) h_not_term_0
  cases n with
  | zero =>
    -- n = 0: both sides equal 1.
    have h_spec := mathlib_OF_post_step_spec 0 o m
    rw [GenContFract.zeroth_den_eq_one] at h_spec
    have h_int : mathlib_OF_post_step 0 o m = 1 := by exact_mod_cast h_spec.symm
    unfold mathlib_OF_post_step_nat
    rw [h_int]
    rw [OF_post_step_zero]
    rfl
  | succ k =>
    -- n = k+1. Apply strong at n' = k. Need ¬ Terminated at (k+1) = n.
    -- From h_not_term (¬ Terminated at n+1) by stable contrapositive.
    have h_term_n : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).TerminatedAt (k+1) := by
      intro h
      exact h_not_term (GenContFract.terminated_stable (by omega : k+1 ≤ k+2) h)
    have h_2pm : 0 < (2^m : Nat) := Nat.two_pow_pos m
    have h_strong := cf_aux_full_matches_mathlib_strong o (2^m) h_2pm k h_term_n
    -- Bridge gives cf_aux's .2.2.2 = dens (k+1) in ℝ. Combine with spec → Nat equality.
    have h_rhs : OF_post_step (k+1) o m = (cf_aux_full (k+2) o (2^m) 0 1 1 0).2.2.2 := by
      unfold OF_post_step ContinuedFraction
      rw [cf_aux_eq_cf_aux_full_proj]
    have h_lhs_R : ((mathlib_OF_post_step_nat (k+1) o m : Nat) : ℝ)
        = (((cf_aux_full (k+2) o (2^m) 0 1 1 0).2.2.2 : Nat) : ℝ) := by
      have h_spec := mathlib_OF_post_step_spec (k+1) o m
      have h_strong_4 := h_strong.2.2.2
      rw [h_strong_4]
      rw [show ((GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).contsAux (k+2)).b
            = (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).dens (k+1) from rfl]
      rw [show (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) from by
        push_cast; rfl]
      rw [h_spec]
      have h_nat_int := mathlib_OF_post_step_nat_int (k+1) o m
      have : ((mathlib_OF_post_step_nat (k+1) o m : Nat) : ℝ)
           = ((mathlib_OF_post_step (k+1) o m : ℤ) : ℝ) := by
        rw [← h_nat_int]; push_cast; rfl
      rw [this]
    have h_eq_Nat : mathlib_OF_post_step_nat (k+1) o m
        = (cf_aux_full (k+2) o (2^m) 0 1 1 0).2.2.2 := by
      exact_mod_cast h_lhs_R
    rw [h_eq_Nat, h_rhs]

/-- **Strict-at-`n` bridge variant** (added 2026-05-24): like
`mathlib_OF_post_step_nat_eq_OF_post_step_nonboundary` but requires only
`¬ TerminatedAt n` (NOT `n+1`). The `+1` in the nonboundary version was
an artifact of unifying the n=0 case through `terminated_stable`; here we
inline the `n=0` case explicitly. For uses where the smallest convergent
index satisfies `¬ TerminatedAt n` but may have `TerminatedAt (n+1)`
(generic rational case where `k/r` is the final non-terminal convergent),
this variant is what bridges. -/
private theorem mathlib_OF_post_step_nat_eq_OF_post_step_at_n
    (n o m : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).TerminatedAt n) :
    mathlib_OF_post_step_nat n o m = OF_post_step n o m := by
  cases n with
  | zero =>
    -- n = 0: h_not_term IS ¬ TerminatedAt 0.
    have h_mod : o % (2^m) ≠ 0 := nondiv_of_not_terminated_zero o (2^m) h_not_term
    have h_spec := mathlib_OF_post_step_spec 0 o m
    rw [GenContFract.zeroth_den_eq_one] at h_spec
    have h_int : mathlib_OF_post_step 0 o m = 1 := by exact_mod_cast h_spec.symm
    unfold mathlib_OF_post_step_nat
    rw [h_int, OF_post_step_zero]; rfl
  | succ k =>
    -- n = k+1. h_not_term IS ¬ TerminatedAt (k+1). Apply strong at n' = k.
    have h_2pm : 0 < (2^m : Nat) := Nat.two_pow_pos m
    have h_strong := cf_aux_full_matches_mathlib_strong o (2^m) h_2pm k h_not_term
    have h_rhs : OF_post_step (k+1) o m = (cf_aux_full (k+2) o (2^m) 0 1 1 0).2.2.2 := by
      unfold OF_post_step ContinuedFraction
      rw [cf_aux_eq_cf_aux_full_proj]
    have h_lhs_R : ((mathlib_OF_post_step_nat (k+1) o m : Nat) : ℝ)
        = (((cf_aux_full (k+2) o (2^m) 0 1 1 0).2.2.2 : Nat) : ℝ) := by
      have h_spec := mathlib_OF_post_step_spec (k+1) o m
      have h_strong_4 := h_strong.2.2.2
      rw [h_strong_4]
      rw [show ((GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).contsAux (k+2)).b
            = (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).dens (k+1) from rfl]
      rw [show (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) from by
        push_cast; rfl]
      rw [h_spec]
      have h_nat_int := mathlib_OF_post_step_nat_int (k+1) o m
      have : ((mathlib_OF_post_step_nat (k+1) o m : Nat) : ℝ)
           = ((mathlib_OF_post_step (k+1) o m : ℤ) : ℝ) := by
        rw [← h_nat_int]; push_cast; rfl
      rw [this]
    have h_eq_Nat : mathlib_OF_post_step_nat (k+1) o m
        = (cf_aux_full (k+2) o (2^m) 0 1 1 0).2.2.2 := by
      exact_mod_cast h_lhs_R
    rw [h_eq_Nat, h_rhs]

-- (The OBSOLETE "general" theorem with boundary sorry has been DELETED 2026-05-24
--  per John's design recommendation. The non-boundary version above covers all
--  cases needed for r_found_1. The block-commented scaffolding that followed
--  has also been removed 2026-05-24 to eliminate the dead `sorry` text from
--  the source file. Git history preserves the prior scaffolding if needed.)

/-- **Step-1 bridge between cf_aux-based and mathlib-based denominators**
(Phase 3 r_found_1, added 2026-05-24): combines the four step-1 closed
forms to show `mathlib_OF_post_step_nat 1 o m = OF_post_step 1 o m`. -/
private theorem mathlib_OF_post_step_nat_eq_OF_post_step_one (o m : Nat) :
    mathlib_OF_post_step_nat 1 o m = OF_post_step 1 o m := by
  unfold mathlib_OF_post_step_nat
  have h_spec := mathlib_OF_post_step_spec 1 o m
  have h_cast : (((o : ℝ)) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) := by push_cast; rfl
  by_cases h_mod : o % (2^m) = 0
  · -- divisible case
    have h_dens := mathlib_dens_one_div o m h_mod
    rw [h_cast] at h_dens
    rw [h_dens] at h_spec
    have h_int : mathlib_OF_post_step 1 o m = 1 := by exact_mod_cast h_spec.symm
    rw [h_int, OF_post_step_one_div o m h_mod]
    rfl
  · -- non-divisible case
    have h_dens := mathlib_dens_one_nondiv o m h_mod
    rw [h_cast] at h_dens
    rw [h_dens] at h_spec
    have h_int : ((2^m / (o % 2^m) : Nat) : ℤ) = mathlib_OF_post_step 1 o m := by
      have h_cast2 : (((2^m / (o % 2^m) : Nat) : ℤ) : ℝ) = (((2^m / (o % 2^m) : Nat) : ℝ)) := by
        push_cast; rfl
      have h_lhs : (((2^m / (o % 2^m) : Nat) : ℤ) : ℝ) =
                   ((mathlib_OF_post_step 1 o m : ℤ) : ℝ) := by
        rw [h_cast2]; exact h_spec
      exact_mod_cast h_lhs
    rw [OF_post_step_one_nondiv o m h_mod, ← h_int]
    rfl

/-- **`mathlib_OF_post_step` at step 0 is 1** (Phase 3 r_found_1 bridge,
added 2026-05-23): mathlib's `zeroth_den_eq_one` gives
`(GenContFract.of v).dens 0 = 1`, so the integer-valued analog is `1`. -/
private theorem mathlib_OF_post_step_zero (o m : Nat) :
    mathlib_OF_post_step 0 o m = 1 := by
  have h_spec := mathlib_OF_post_step_spec 0 o m
  rw [GenContFract.zeroth_den_eq_one] at h_spec
  exact_mod_cast h_spec.symm

/-- **`mathlib_OF_post_step_nat` at step 0 is 1** — corollary of
`mathlib_OF_post_step_zero`. -/
private theorem mathlib_OF_post_step_nat_zero (o m : Nat) :
    mathlib_OF_post_step_nat 0 o m = 1 := by
  unfold mathlib_OF_post_step_nat
  rw [mathlib_OF_post_step_zero]
  rfl

/-- **Bridge at step 0**: `mathlib_OF_post_step 0 = (OF_post_step 0 : ℤ)`.
This is the first specific-point bridge in the cf_aux ↔ mathlib chain;
future ticks would extend it inductively. -/
private theorem mathlib_OF_post_step_eq_OF_post_step_zero (o m : Nat) :
    mathlib_OF_post_step 0 o m = ((OF_post_step 0 o m : Nat) : ℤ) := by
  rw [mathlib_OF_post_step_zero, OF_post_step_zero]
  rfl

/-- **Nat-level bridge at step 0**: `mathlib_OF_post_step_nat 0 = OF_post_step 0`. -/
private theorem mathlib_OF_post_step_nat_eq_OF_post_step_zero (o m : Nat) :
    mathlib_OF_post_step_nat 0 o m = OF_post_step 0 o m := by
  rw [mathlib_OF_post_step_nat_zero, OF_post_step_zero]

/-- **Arithmetic Lemma A** (added 2026-05-24, exact-rational foundation):
from `s_closest m k r * r = k * 2^m` and `gcd k r = 1`, deduce `r ∣ 2^m`.
Used in the r > 1 subcase of `TODO_r_found_1_core_exact_rational`. -/
private lemma r_dvd_two_pow_of_exact
    (m k r : Nat) (h_coprime : Nat.gcd k r = 1)
    (h_eq : s_closest m k r * r = k * 2^m) :
    r ∣ 2^m := by
  -- r ∣ s_closest * r = k * 2^m. With r coprime to k, r ∣ 2^m.
  have h_cop : r.Coprime k := Nat.coprime_comm.mp h_coprime
  have h_r_dvd_km : r ∣ k * 2^m := by
    rw [← h_eq]; exact dvd_mul_left r (s_closest m k r)
  exact (Nat.Coprime.dvd_mul_left h_cop).mp h_r_dvd_km

/-- **Arithmetic Lemma B** (added 2026-05-24, exact-rational foundation):
the reduced denominator. Under the exact-rational hypothesis,
`gcd (s_closest m k r) (2^m) = 2^m / r`. -/
private lemma gcd_s_closest_two_pow_eq
    (m k r : Nat) (h_r_pos : 0 < r) (h_coprime : Nat.gcd k r = 1)
    (h_eq : s_closest m k r * r = k * 2^m) :
    Nat.gcd (s_closest m k r) (2^m) = 2^m / r := by
  have h_r_dvd : r ∣ 2^m := r_dvd_two_pow_of_exact m k r h_coprime h_eq
  set g := 2^m / r with h_g_def
  -- 2^m = g * r (since r ∣ 2^m).
  have h_2m_eq : 2^m = g * r := (Nat.div_mul_cancel h_r_dvd).symm
  -- s_closest = k * g (cancel r from h_eq).
  have h_s_eq : s_closest m k r = k * g := by
    have h_s_r : s_closest m k r * r = (k * g) * r := by rw [h_eq, h_2m_eq]; ring
    exact Nat.eq_of_mul_eq_mul_right h_r_pos h_s_r
  -- gcd (k*g) (g*r) = g * gcd k r = g * 1 = g.
  rw [h_s_eq, h_2m_eq]
  rw [show g * r = r * g from Nat.mul_comm g r]
  rw [Nat.gcd_mul_right, h_coprime, Nat.one_mul]

/-- **cf_aux_full denominator invariant** (added 2026-05-24, exact-rational
foundation): the quantity `q_curr · o + q_prev · m` is invariant across
cf_aux_full's iterations. After N steps starting from
`(o₀, m₀, p_prev, p_curr, q_prev, q_curr)`, the state's
`(q_curr_N, q_prev_N)` and Euclidean state `(o_N, m_N) = euclidean_iter N o₀ m₀`
satisfy:
  `q_curr_N · o_N + q_prev_N · m_N = q_curr · o₀ + q_prev · m₀`.

Proof by induction on N. The recurrence `q_curr ← (o/m)·q_curr + q_prev`
together with the Euclidean step `(o, m) → (m, o%m)` preserves the
combination via `(o/m)·m + (o%m) = o` (`Nat.div_add_mod`).

At termination (m_N = 0) with initial state `(0, 1, 1, 0)`: the invariant
becomes `q_curr_N · gcd(o₀, m₀) = m₀`, giving the reduced denominator
`q_curr_N = m₀ / gcd(o₀, m₀)`. -/
private theorem cf_aux_full_q_inv :
    ∀ (N o m p_prev p_curr q_prev q_curr : Nat),
      (cf_aux_full N o m p_prev p_curr q_prev q_curr).2.2.2
        * (euclidean_iter N o m).1
      + (cf_aux_full N o m p_prev p_curr q_prev q_curr).2.2.1
        * (euclidean_iter N o m).2
      = q_curr * o + q_prev * m := by
  intro N
  induction N with
  | zero =>
    intros o m p_prev p_curr q_prev q_curr
    -- cf_aux_full 0 returns input state; euclidean_iter 0 = (o, m).
    show q_curr * o + q_prev * m = q_curr * o + q_prev * m
    rfl
  | succ k ih =>
    intros o m p_prev p_curr q_prev q_curr
    by_cases h_m : m = 0
    · subst h_m
      -- m=0: cf_aux_full returns input state, euclidean_iter = (o, 0).
      show (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr)
            else cf_aux_full k 0 (o % 0) p_curr ((o/0)*p_curr+p_prev)
                                          q_curr ((o/0)*q_curr+q_prev)).2.2.2 *
            (if (0 : Nat) = 0 then (o, 0) else euclidean_iter k 0 (o % 0)).1 +
            (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr)
            else cf_aux_full k 0 (o % 0) p_curr ((o/0)*p_curr+p_prev)
                                          q_curr ((o/0)*q_curr+q_prev)).2.2.1 *
            (if (0 : Nat) = 0 then (o, 0) else euclidean_iter k 0 (o % 0)).2
          = q_curr * o + q_prev * 0
      simp
    · have h_m_pos : 0 < m := Nat.pos_of_ne_zero h_m
      have h_cf_unfold :
          cf_aux_full (k+1) o m p_prev p_curr q_prev q_curr
          = cf_aux_full k m (o % m) p_curr ((o/m)*p_curr + p_prev)
                                    q_curr ((o/m)*q_curr + q_prev) := by
        show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
              else cf_aux_full k m (o%m) p_curr ((o/m)*p_curr + p_prev)
                                          q_curr ((o/m)*q_curr + q_prev)) = _
        rw [if_neg h_m]
      have h_eucl_unfold :
          euclidean_iter (k+1) o m = euclidean_iter k m (o % m) := by
        show (if m = 0 then (o, m) else euclidean_iter k m (o % m)) = _
        rw [if_neg h_m]
      rw [h_cf_unfold, h_eucl_unfold]
      rw [ih m (o % m) p_curr ((o/m)*p_curr + p_prev) q_curr ((o/m)*q_curr + q_prev)]
      -- Goal: ((o/m)*q_curr + q_prev) * m + q_curr * (o%m) = q_curr * o + q_prev * m.
      have h_div_mod : (o/m)*m + o%m = o := by
        have h := Nat.div_add_mod o m
        linarith [Nat.mul_comm m (o/m)]
      -- RHS = q_curr * ((o/m)*m + o%m) + q_prev*m  [by h_div_mod]
      rw [show q_curr * o = q_curr * ((o/m)*m + o%m) from by rw [h_div_mod]]
      ring

/-- **Lamé's theorem for cf_aux's Euclidean iteration** (added 2026-05-24,
exact-rational foundation): if the Euclidean iteration `euclidean_iter`
on `(o, m)` (with `m > 0`) terminates at the smallest index `j`, then the
Fibonacci bound `Nat.fib (j + 1) ≤ m` holds.

Proof by strong induction on `m`. The Euclidean step `(o, m) → (m, o%m)`
gives the IH at `m' = o%m < m`. To reach `Fib(j+1)` from `Fib(j) ≤ o%m`,
apply IH a second time at `m'' = m%(o%m) < m` (when `j ≥ 2`), then use
`m = q·(o%m) + m%(o%m) ≥ o%m + m%(o%m) ≥ Fib(j) + Fib(j-1) = Fib(j+1)`.

For `j = 1`: trivial (`Fib(2) = 1 ≤ m`). For `j = 2`: handled by `m ≥ 2`. -/
private theorem eucl_iter_fib_bound :
    ∀ (m : Nat), 0 < m → ∀ (o j : Nat),
      (euclidean_iter j o m).2 = 0 →
      (∀ j' < j, (euclidean_iter j' o m).2 ≠ 0) →
      Nat.fib (j + 1) ≤ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro h_m_pos o j h_term h_min
    -- j > 0 since (eucl_iter 0).2 = m > 0.
    cases j with
    | zero =>
      exfalso
      have h0 : (euclidean_iter 0 o m).2 = m := rfl
      rw [h0] at h_term
      omega
    | succ j' =>
      -- Unfold eucl_iter (j'+1) using m > 0.
      have h_unfold : euclidean_iter (j' + 1) o m = euclidean_iter j' m (o % m) := by
        show (if m = 0 then (o, m) else euclidean_iter j' m (o % m)) = _
        rw [if_neg h_m_pos.ne']
      rw [h_unfold] at h_term
      by_cases h_om_zero : o % m = 0
      · -- o%m = 0: only consistent with j' = 0 by minimality.
        cases j' with
        | zero =>
          -- j = 1. Fib(2) = 1 ≤ m. ✓
          show Nat.fib 2 ≤ m
          rw [show Nat.fib 2 = 1 from rfl]; omega
        | succ _ =>
          exfalso
          have h_min_1 := h_min 1 (by omega)
          have h_eucl_1 : euclidean_iter 1 o m = (m, 0) := by
            show (if m = 0 then (o, m) else euclidean_iter 0 m (o % m)) = _
            rw [if_neg h_m_pos.ne', h_om_zero]; rfl
          rw [h_eucl_1] at h_min_1
          exact h_min_1 rfl
      · -- o%m > 0.
        have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om_zero
        have h_om_lt_m : o % m < m := Nat.mod_lt _ h_m_pos
        -- Shifted minimality (level 1).
        have h_min_shift : ∀ j'' < j', (euclidean_iter j'' m (o % m)).2 ≠ 0 := by
          intro j'' h_j''
          have h_shift : euclidean_iter j'' m (o % m) = euclidean_iter (j'' + 1) o m := by
            symm
            show (if m = 0 then (o, m) else euclidean_iter j'' m (o % m)) = _
            rw [if_neg h_m_pos.ne']
          rw [h_shift]
          exact h_min (j'' + 1) (by omega)
        -- IH at o%m: Fib(j' + 1) ≤ o%m.
        have h_fib_om : Nat.fib (j' + 1) ≤ o % m :=
          ih (o % m) h_om_lt_m h_om_pos m j' h_term h_min_shift
        cases j' with
        | zero =>
          -- j = 1. Fib(2) ≤ m. m ≥ 1.
          show Nat.fib 2 ≤ m
          rw [show Nat.fib 2 = 1 from rfl]; omega
        | succ j'' =>
          -- j = j''+2. Unfold next step: (eucl_iter (j''+1) m (o%m)) = (eucl_iter j'' (o%m) (m%(o%m))).
          have h_unfold_2 : euclidean_iter (j'' + 1) m (o % m)
              = euclidean_iter j'' (o % m) (m % (o % m)) := by
            show (if (o % m) = 0 then (m, o%m) else
                  euclidean_iter j'' (o % m) (m % (o % m))) = _
            rw [if_neg h_om_zero]
          rw [h_unfold_2] at h_term
          by_cases h_mm_zero : m % (o % m) = 0
          · -- m%(o%m) = 0: only consistent with j'' = 0 by minimality at level 2.
            cases j'' with
            | zero =>
              -- j = 2. Fib(3) = 2 ≤ m. m ≥ o%m + 1 ≥ 2.
              show Nat.fib 3 ≤ m
              rw [show Nat.fib 3 = 2 from rfl]; omega
            | succ _ =>
              exfalso
              have h_min_1 := h_min_shift 1 (by omega)
              have h_eucl_1 : euclidean_iter 1 m (o % m) = (o % m, m % (o % m)) := by
                show (if (o%m) = 0 then (m, o%m)
                      else euclidean_iter 0 (o % m) (m % (o % m))) = _
                rw [if_neg h_om_zero]; rfl
              rw [h_eucl_1] at h_min_1
              exact h_min_1 h_mm_zero
          · -- m%(o%m) > 0. Apply IH at m%(o%m) < m.
            have h_mm_pos : 0 < m % (o % m) := Nat.pos_of_ne_zero h_mm_zero
            have h_mm_lt_om : m % (o % m) < o % m := Nat.mod_lt _ h_om_pos
            have h_mm_lt_m : m % (o % m) < m := Nat.lt_trans h_mm_lt_om h_om_lt_m
            -- Shifted-shifted minimality.
            have h_min_shift_2 : ∀ j''' < j'',
                (euclidean_iter j''' (o % m) (m % (o % m))).2 ≠ 0 := by
              intro j''' h_j'''
              have h_shift_2 : euclidean_iter j''' (o % m) (m % (o % m))
                  = euclidean_iter (j''' + 1) m (o % m) := by
                symm
                show (if (o % m) = 0 then (m, o%m)
                      else euclidean_iter j''' (o % m) (m % (o % m))) = _
                rw [if_neg h_om_zero]
              rw [h_shift_2]
              exact h_min_shift (j''' + 1) (by omega)
            -- IH at m%(o%m): Fib(j''+1) ≤ m%(o%m).
            have h_fib_mm : Nat.fib (j'' + 1) ≤ m % (o % m) :=
              ih (m % (o % m)) h_mm_lt_m h_mm_pos (o % m) j'' h_term h_min_shift_2
            -- Bound: m ≥ o%m + m%(o%m).
            have h_q_pos : 1 ≤ m / (o % m) :=
              Nat.div_pos (Nat.le_of_lt h_om_lt_m) h_om_pos
            have h_div_mod_eq : m / (o % m) * (o % m) + m % (o % m) = m := by
              have h := Nat.div_add_mod m (o % m)
              linarith [Nat.mul_comm (m / (o % m)) (o % m)]
            have h_m_ge : o % m + m % (o % m) ≤ m := by
              have h_mul_ge : 1 * (o % m) ≤ m / (o % m) * (o % m) :=
                Nat.mul_le_mul_right _ h_q_pos
              linarith
            -- Goal: Fib(j''+1+2) ≤ m. Rewrite using Fib_add_two.
            show Nat.fib (j'' + 1 + 1 + 1) ≤ m
            have h_fib_eq : Nat.fib (j'' + 1 + 1 + 1)
                          = Nat.fib (j'' + 1 + 1) + Nat.fib (j'' + 1) := by
              rw [show j'' + 1 + 1 + 1 = (j'' + 1) + 2 from by ring]
              rw [Nat.fib_add_two]; ring
            rw [h_fib_eq]
            -- h_fib_om : Fib(j''+1+1) ≤ o%m. h_fib_mm : Fib(j''+1) ≤ m%(o%m).
            calc Nat.fib (j'' + 1 + 1) + Nat.fib (j'' + 1)
                ≤ o % m + m % (o % m) := by omega
              _ ≤ m := h_m_ge

/-- **Euclidean depth bound `j ≤ 2 * m_exp + 1`** (added 2026-05-24):
combines `eucl_iter_fib_bound` with `pow_two_le_fib` and `Nat.fib`
strict monotonicity to bound the Euclidean termination index of
`(o, 2^m_exp)` by `2 * m_exp + 1`. -/
private theorem eucl_iter_le_two_m_plus_one
    (o m_exp j : Nat)
    (h_term : (euclidean_iter j o (2^m_exp)).2 = 0)
    (h_min  : ∀ j' < j, (euclidean_iter j' o (2^m_exp)).2 ≠ 0) :
    j ≤ 2 * m_exp + 1 := by
  have h_pow_pos : 0 < 2^m_exp := Nat.two_pow_pos m_exp
  have h_fib_le : Nat.fib (j + 1) ≤ 2^m_exp :=
    eucl_iter_fib_bound (2^m_exp) h_pow_pos o j h_term h_min
  by_contra h_not
  push_neg at h_not
  have h_j_ge : 2 * m_exp + 2 ≤ j := by omega
  -- Fib monotone at (2*m_exp + 3) ≤ (j + 1)
  have h_fib_mono : Nat.fib (2 * m_exp + 3) ≤ Nat.fib (j + 1) :=
    Nat.fib_mono (by omega)
  -- Fib(2m+2) < Fib(2m+3) since 2m+2 ≥ 2
  have h_fib_strict : Nat.fib (2 * m_exp + 2) < Nat.fib (2 * m_exp + 3) :=
    Nat.fib_lt_fib_succ (by omega)
  -- pow_two_le_fib : 2^m_exp ≤ Fib(2m_exp+2)
  have h_pow_le := pow_two_le_fib m_exp
  omega

/-- **gcd preservation by `euclidean_iter`** (added 2026-05-24): the gcd
of the state pair is invariant under the Euclidean step. By induction
on the iteration depth `d`, peeling one step at a time. -/
private theorem eucl_iter_gcd_preserved :
    ∀ (d o m : Nat),
      Nat.gcd (euclidean_iter d o m).1 (euclidean_iter d o m).2 = Nat.gcd o m := by
  intro d
  induction d with
  | zero => intro o m; rfl
  | succ d ih =>
    intro o m
    by_cases h_m : m = 0
    · subst h_m
      have h_eq : euclidean_iter (d + 1) o 0 = (o, 0) := by
        show (if (0:Nat) = 0 then (o, 0) else euclidean_iter d 0 (o % 0)) = (o, 0)
        rfl
      rw [h_eq]
    · have h_eq : euclidean_iter (d + 1) o m = euclidean_iter d m (o % m) := by
        show (if m = 0 then (o, m) else euclidean_iter d m (o % m)) = _
        rw [if_neg h_m]
      rw [h_eq, ih m (o % m)]
      -- Goal: gcd m (o%m) = gcd o m.
      rw [Nat.gcd_comm m (o % m), Nat.gcd_comm o m]
      exact (Nat.gcd_rec m o).symm

/-- **q_curr bound from cf_aux_full_q_inv** (added 2026-05-24): at any
depth `d` where the Euclidean iteration's first component is positive,
the terminal `q_curr` from `cf_aux_full d o m_arg 0 1 1 0` satisfies
`gcd(o, m_arg) * q_curr ≤ m_arg`. Combines `cf_aux_full_q_inv`
(invariant) with `eucl_iter_gcd_preserved`. Gives `q_curr ≤ m_arg / gcd`
when `gcd > 0`. -/
private theorem cf_aux_full_q_bound (d o m_arg : Nat)
    (h_pos : 0 < (euclidean_iter d o m_arg).1) :
    Nat.gcd o m_arg * (cf_aux_full d o m_arg 0 1 1 0).2.2.2 ≤ m_arg := by
  have h_inv := cf_aux_full_q_inv d o m_arg 0 1 1 0
  -- h_inv: q_curr · s.1 + q_prev · s.2 = 0 · o + 1 · m_arg = m_arg.
  simp only [Nat.zero_mul, Nat.one_mul, Nat.zero_add] at h_inv
  set s := euclidean_iter d o m_arg with h_s_def
  set q_f := (cf_aux_full d o m_arg 0 1 1 0).2.2.2 with h_qf_def
  set q_p := (cf_aux_full d o m_arg 0 1 1 0).2.2.1 with h_qp_def
  -- h_inv: q_f * s.1 + q_p * s.2 = m_arg.
  have h_q_s1_le : q_f * s.1 ≤ m_arg := by
    have h_p_s2_ge : 0 ≤ q_p * s.2 := Nat.zero_le _
    omega
  -- gcd preserved: gcd(s.1, s.2) = gcd(o, m_arg).
  have h_gcd_eq : Nat.gcd s.1 s.2 = Nat.gcd o m_arg :=
    eucl_iter_gcd_preserved d o m_arg
  set g := Nat.gcd o m_arg with h_g_def
  -- g ∣ s.1.
  have h_g_dvd : g ∣ s.1 := by
    rw [← h_gcd_eq]; exact Nat.gcd_dvd_left s.1 s.2
  -- s.1 ≥ g (since g ∣ s.1, s.1 > 0).
  have h_s1_ge_g : g ≤ s.1 := Nat.le_of_dvd h_pos h_g_dvd
  -- q_f * g ≤ q_f * s.1 ≤ m_arg.
  calc g * q_f
      = q_f * g := by ring
    _ ≤ q_f * s.1 := Nat.mul_le_mul_left q_f h_s1_ge_g
    _ ≤ m_arg := h_q_s1_le

/-- **Peel-from-right Euclidean step** (added 2026-05-24): if the
Euclidean state at depth `d` has positive second component, then at
depth `d+1` the first component equals that previous second component.
This is the "step from the right" view of `euclidean_iter`. By
induction on `d`, propagating the positivity through the recursion. -/
private theorem euclidean_iter_succ_first_eq_prev_second :
    ∀ (d o m : Nat),
      0 < (euclidean_iter d o m).2 →
      (euclidean_iter (d + 1) o m).1 = (euclidean_iter d o m).2 := by
  intro d
  induction d with
  | zero =>
    intro o m h_pos
    -- (eucl_iter 0 o m) = (o, m). .2 = m. m > 0.
    have h_m_pos : 0 < m := h_pos
    -- (eucl_iter 1 o m).1 = m, (eucl_iter 0 o m).2 = m.
    have h_eq : euclidean_iter 1 o m = euclidean_iter 0 m (o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter 0 m (o % m)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_eq]
    rfl
  | succ d ih =>
    intro o m h_pos
    by_cases h_m : m = 0
    · subst h_m
      -- (eucl_iter (d+1) o 0) = (o, 0). .2 = 0. Contradicts h_pos.
      have h_eq : euclidean_iter (d + 1) o 0 = (o, 0) := by
        show (if (0:Nat) = 0 then (o, (0:Nat)) else euclidean_iter d 0 (o % 0)) = (o, 0)
        rfl
      rw [h_eq] at h_pos
      simp at h_pos
    · -- m > 0. Unfold: (eucl_iter (d+1) o m) = (eucl_iter d m (o%m)).
      have h_eq_d1 : euclidean_iter (d + 1) o m = euclidean_iter d m (o % m) := by
        show (if m = 0 then (o, m) else euclidean_iter d m (o % m)) = _
        rw [if_neg h_m]
      have h_eq_d2 : euclidean_iter (d + 1 + 1) o m
                   = euclidean_iter (d + 1) m (o % m) := by
        show (if m = 0 then (o, m) else euclidean_iter (d + 1) m (o % m)) = _
        rw [if_neg h_m]
      rw [h_eq_d2, h_eq_d1]
      rw [h_eq_d1] at h_pos
      exact ih m (o % m) h_pos

/-- **Positivity of `.1` under minimality** (added 2026-05-24): if `o > 0`
and the Euclidean iteration's second component is non-zero at every
depth `d' < d`, then the first component at depth `d` is positive.
Used to invoke `cf_aux_full_q_bound` at intermediate depths inside the
exact-rational `r > 1` walking argument. -/
private theorem eucl_iter_first_pos_under_min
    (o m : Nat) (h_o_pos : 0 < o) :
    ∀ d, (∀ d' < d, (euclidean_iter d' o m).2 ≠ 0) →
         0 < (euclidean_iter d o m).1 := by
  intro d
  induction d with
  | zero => intro _; exact h_o_pos
  | succ d _ih =>
    intro h_min
    have h_d_ne : (euclidean_iter d o m).2 ≠ 0 := h_min d (Nat.lt_succ_self d)
    rw [euclidean_iter_succ_first_eq_prev_second d o m (Nat.pos_of_ne_zero h_d_ne)]
    exact Nat.pos_of_ne_zero h_d_ne

/-- **Exact-rational branch of `r_found_1_core`**: case when
`s_closest m k r * r = k * 2^m` (equivalently, `v = k/r` exactly as ℝ,
i.e., `r | 2^m`, i.e., `r` is a power of 2). This is the BOUNDARY case
for mathlib's CF — the CF terminates exactly at k/r, so the smallest
N_step with `convs N_step = k/r` is the termination index. The standard
bridge + `dens_eq_r_at_convs_eq_kr` don't apply directly; needs separate
handling (direct cf_aux computation, or use of mathlib's denominator-at-
termination). Includes the trivial sub-case r=1, a=1, k=0. -/
private theorem TODO_r_found_1_core_exact_rational
    (a r N m n k : Nat)
    (h_basic : BasicSetting a r N m n)
    (h_k_lt : k < r)
    (h_coprime : Nat.gcd k r = 1)
    (h_eq : s_closest m k r * r = k * 2^m) :
    OF_post a N (s_closest m k r) m = r := by
  obtain ⟨⟨h_a_pos, h_a_lt⟩, h_ord, _h_pow_m, _h_pow_n⟩ := h_basic
  by_cases h_r : r = 1
  · -- r = 1 sub-case: trivial. k = 0 (from k < r), a = 1 (from Order a 1 N).
    subst h_r
    have h_k_zero : k = 0 := Nat.lt_one_iff.mp h_k_lt
    subst h_k_zero
    obtain ⟨_, h_a_mod, _⟩ := h_ord
    have h_a_mod' : a % N = 1 := by simpa using h_a_mod
    have h_a_eq_1 : a = 1 := by
      rw [Nat.mod_eq_of_lt h_a_lt] at h_a_mod'
      exact h_a_mod'
    subst h_a_eq_1
    -- s_closest m 0 1 = 0 by direct unfold of (0 * 2^m + 1/2) / 1.
    have h_s_zero : s_closest m 0 1 = 0 := by
      show (0 * 2^m + 1 / 2) / 1 = 0
      simp
    rw [h_s_zero]
    -- Need 1 < N (from a = 1, a < N).
    have h_N_ge_2 : 1 < N := h_a_lt
    -- OF_post' 1 1 N 0 m = 1.
    have h_walk_1 : OF_post' 1 1 N 0 m = 1 := by
      show (let pre := OF_post' 0 1 N 0 m
            if pre = 0 then
              (if modexp 1 (OF_post_step 0 0 m) N = 1
               then OF_post_step 0 0 m else 0)
            else pre) = 1
      have h_pre : OF_post' 0 1 N 0 m = 0 := rfl
      simp only [h_pre, if_true]
      rw [OF_post_step_zero]
      have h_modexp : modexp 1 1 N = 1 := by
        unfold modexp; simp [Nat.mod_eq_of_lt h_N_ge_2]
      rw [if_pos h_modexp]
    -- Extend OF_post' 1 = 1 to OF_post' (2m+2) = 1 via OF_post'_nonzero_equal.
    unfold OF_post
    have h_2m2_decomp : 2 * m + 2 = (2 * m + 2 - 1) + 1 := by omega
    rw [h_2m2_decomp]
    rw [OF_post'_nonzero_equal (2 * m + 2 - 1) 1 1 N 0 m
        (by rw [h_walk_1]; exact Nat.one_ne_zero)]
    exact h_walk_1
  · -- r > 1 sub-case: r ≥ 2 and r ∣ 2^m (so r is a power of 2 > 1).
    -- Strategy: at j_e = min Euclidean termination index, cf_aux's q_curr = r
    -- (terminal value via cf_aux_full_q_inv + gcd). At intermediate depths, q_curr
    -- is bounded by r (via cf_aux_full_q_bound). Walking gives OF_post = r.
    have h_r_pos : 0 < r := h_ord.1
    have h_r_ge_2 : 2 ≤ r := by omega
    have h_N_pos : 0 < N := by omega
    -- Foundation: r ∣ 2^m, gcd(s_closest, 2^m) = 2^m/r.
    have h_r_dvd : r ∣ 2^m := r_dvd_two_pow_of_exact m k r h_coprime h_eq
    have h_gcd_eq : Nat.gcd (s_closest m k r) (2^m) = 2^m / r :=
      gcd_s_closest_two_pow_eq m k r h_r_pos h_coprime h_eq
    set s := s_closest m k r with h_s_def
    set g := 2^m / r with h_g_def
    have h_2m_eq : 2^m = g * r := (Nat.div_mul_cancel h_r_dvd).symm
    have h_2m_pos : 0 < 2^m := Nat.two_pow_pos m
    have h_g_pos : 0 < g := by
      by_contra h_g_neg
      push_neg at h_g_neg
      interval_cases g
      rw [Nat.zero_mul] at h_2m_eq
      omega
    -- s_closest > 0 in r > 1 case (else gcd = 2^m = 2^m/r forces r = 1).
    have h_s_pos : 0 < s := by
      by_contra h_s_neg
      push_neg at h_s_neg
      interval_cases s
      -- gcd(0, 2^m) = 2^m. So 2^m = g, hence r = 1.
      rw [Nat.gcd_zero_left] at h_gcd_eq
      -- h_gcd_eq: 2^m = 2^m/r = g.
      have h_g_eq : g = 2^m := h_gcd_eq.symm
      rw [h_g_eq] at h_2m_eq
      -- 2^m = 2^m * r
      have h_one_eq_r : 1 = r := by
        have h_mul1 : 2^m * 1 = 2^m * r := by linarith
        exact Nat.eq_of_mul_eq_mul_left h_2m_pos h_mul1
      omega
    -- Find j_e := smallest d with .2 = 0.
    have h_term_exists : ∃ d, (euclidean_iter d s (2^m)).2 = 0 := by
      obtain ⟨d, _, h_term⟩ := eucl_iter_terminates s (2^m)
      exact ⟨d, h_term⟩
    set je := Nat.find h_term_exists with h_je_def
    have h_je_term : (euclidean_iter je s (2^m)).2 = 0 := Nat.find_spec h_term_exists
    have h_je_min : ∀ d < je, (euclidean_iter d s (2^m)).2 ≠ 0 := fun d hd =>
      Nat.find_min h_term_exists hd
    have h_je_le : je ≤ 2 * m + 1 :=
      eucl_iter_le_two_m_plus_one s m je h_je_term h_je_min
    have h_je_pos : 0 < je := by
      by_contra h_jzero
      push_neg at h_jzero
      interval_cases je
      have h_eq0 : euclidean_iter 0 s (2^m) = (s, 2^m) := rfl
      rw [h_eq0] at h_je_term
      simp at h_je_term
    -- (eucl_iter je s 2^m).1 = g (gcd preservation + .2 = 0 at termination).
    have h_je_one : (euclidean_iter je s (2^m)).1 = g := by
      have h_p := eucl_iter_gcd_preserved je s (2^m)
      rw [h_je_term, Nat.gcd_zero_right] at h_p
      rw [h_p, h_gcd_eq]
    -- q_curr at depth je = r (from q_inv: q_je · g = 2^m = g · r, and g > 0).
    have h_inv_je := cf_aux_full_q_inv je s (2^m) 0 1 1 0
    simp only [Nat.zero_mul, Nat.one_mul, Nat.zero_add] at h_inv_je
    rw [h_je_term, Nat.mul_zero, Nat.add_zero] at h_inv_je
    rw [h_je_one] at h_inv_je
    -- h_inv_je: (cf_aux_full je s (2^m) 0 1 1 0).2.2.2 * g = 2^m
    have h_q_je_eq_r : (cf_aux_full je s (2^m) 0 1 1 0).2.2.2 = r := by
      have h_qg_eq_gr : (cf_aux_full je s (2^m) 0 1 1 0).2.2.2 * g = r * g := by
        rw [h_inv_je, h_2m_eq]; ring
      exact Nat.eq_of_mul_eq_mul_right h_g_pos h_qg_eq_gr
    -- OF_post_step (je - 1) s m = r (cf_aux at depth je = terminal q_curr = r).
    have h_step_je_minus_1 : OF_post_step (je - 1) s m = r := by
      have h_je_decomp : je - 1 + 1 = je := Nat.sub_add_cancel h_je_pos
      show (cf_aux ((je - 1) + 1) s (2^m) 0 1 1 0).2 = r
      rw [h_je_decomp, cf_aux_eq_cf_aux_full_proj]
      exact h_q_je_eq_r
    -- Walking helper: OF_post_step x s m ≤ r for x + 1 ≤ je.
    -- (This is the analog of "monotonicity" but via cf_aux_full_q_bound.)
    have h_intermediate_le_r : ∀ x, x + 1 ≤ je → OF_post_step x s m ≤ r := by
      intro x h_xp1_le
      -- OF_post_step x s m = (cf_aux (x+1) s (2^m) 0 1 1 0).2 = q_curr at depth x+1.
      have h_step_eq :
          OF_post_step x s m = (cf_aux_full (x + 1) s (2^m) 0 1 1 0).2.2.2 := by
        show (cf_aux (x + 1) s (2^m) 0 1 1 0).2 = _
        rw [cf_aux_eq_cf_aux_full_proj]
      rw [h_step_eq]
      -- For x+1 ≤ je: by minimality of je, .2 ≠ 0 at all d' < x+1 ≤ je.
      have h_min_for_xp1 :
          ∀ d' < x + 1, (euclidean_iter d' s (2^m)).2 ≠ 0 := by
        intro d' h_d'
        exact h_je_min d' (by omega)
      have h_first_pos :
          0 < (euclidean_iter (x + 1) s (2^m)).1 :=
        eucl_iter_first_pos_under_min s (2^m) h_s_pos (x + 1) h_min_for_xp1
      have h_bound := cf_aux_full_q_bound (x + 1) s (2^m) h_first_pos
      -- h_bound: gcd(s, 2^m) · q_curr ≤ 2^m. Substitute gcd via h_gcd_eq.
      rw [h_gcd_eq] at h_bound
      -- h_bound: g · q ≤ 2^m. Convert RHS to g * r without touching q's arg.
      have h_bound2 : g * (cf_aux_full (x + 1) s (2^m) 0 1 1 0).2.2.2 ≤ g * r := by
        rw [← h_2m_eq]; exact h_bound
      exact Nat.le_of_mul_le_mul_left h_bound2 h_g_pos
    -- Walking: OF_post' je a N s m = r.
    have h_modexp_at_r : modexp a r N = 1 := h_ord.2.1
    have h_walk_je : OF_post' je a N s m = r := by
      have h_je_decomp : je - 1 + 1 = je := Nat.sub_add_cancel h_je_pos
      conv_lhs => rw [← h_je_decomp]
      show (let pre := OF_post' (je - 1) a N s m
            if pre = 0 then
              (if modexp a (OF_post_step (je - 1) s m) N = 1
               then OF_post_step (je - 1) s m else 0)
            else pre) = r
      by_cases h_pre : OF_post' (je - 1) a N s m = 0
      · -- Case A: pre = 0. Result = OF_post_step (je-1) = r (modexp passes).
        simp only [h_pre, if_true]
        rw [h_step_je_minus_1, if_pos h_modexp_at_r]
      · -- Case B: pre ≠ 0. Result = pre = r.
        simp only [h_pre, if_false]
        have h_dvd : r ∣ OF_post' (je - 1) a N s m := by
          rcases OF_post'_dvd_r (je - 1) a N s m h_a_pos h_a_lt r h_ord with
            h0 | hd
          · exact absurd h0 h_pre
          · exact hd
        obtain ⟨x, h_x_lt, h_x_eq⟩ :=
          OF_post'_nonzero_pre (je - 1) a N s m h_pre
        -- x < je - 1, so x + 1 ≤ je - 1 ≤ je. Apply intermediate bound.
        have h_xp1_le : x + 1 ≤ je := by omega
        have h_x_step_le : OF_post_step x s m ≤ r :=
          h_intermediate_le_r x h_xp1_le
        rw [← h_x_eq] at h_dvd ⊢
        have h_step_pos : 0 < OF_post_step x s m := by
          rw [h_x_eq]; exact Nat.pos_of_ne_zero h_pre
        obtain ⟨c, hc⟩ := h_dvd
        have h_c_pos : 0 < c := by
          rcases Nat.eq_zero_or_pos c with rfl | h
          · rw [Nat.mul_zero] at hc; omega
          · exact h
        have h_c_eq_1 : c = 1 := by
          by_contra h_c_ne
          have h_c_ge_2 : c ≥ 2 := by omega
          have h_step_ge : 2 * r ≤ OF_post_step x s m := by
            rw [hc]; linarith [Nat.mul_le_mul_left r h_c_ge_2]
          linarith
        rw [hc, h_c_eq_1, Nat.mul_one]
    -- Extend OF_post' je = r to OF_post a N s m = OF_post' (2m+2) a N s m = r.
    have h_walk_ne : OF_post' je a N s m ≠ 0 := by
      rw [h_walk_je]; exact h_r_pos.ne'
    unfold OF_post
    have h_2m2_decomp : 2 * m + 2 = (2 * m + 2 - je) + je := by omega
    rw [h_2m2_decomp]
    rw [OF_post'_nonzero_equal (2 * m + 2 - je) je a N s m h_walk_ne]
    exact h_walk_je

/-- **Generic branch of `r_found_1_core`**: case when
`s_closest m k r * r ≠ k * 2^m` (i.e., `v ≠ k/r` as ℝ). Khinchin returns
a SMALLEST N_step < T_v (CF termination index) with `convs N_step = k/r`.
At this N_step, `¬ TerminatedAt N_step` and (usually) `¬ TerminatedAt
(N_step + 1)`. The spine proof goes through. The two non-termination
TODOs are now scoped to this branch and tractable via smallest-N_step
arguments using `h_ne`. -/
private theorem TODO_r_found_1_core_generic
    (a r N m n k : Nat)
    (h_basic : BasicSetting a r N m n)
    (h_k_lt : k < r)
    (h_coprime : Nat.gcd k r = 1)
    (h_ne : s_closest m k r * r ≠ k * 2^m) :
    OF_post a N (s_closest m k r) m = r := by
  -- Extract BasicSetting components (duplicated from core; could refactor further).
  obtain ⟨⟨h_a_pos, h_a_lt⟩, h_ord, h_pow_m, h_pow_n⟩ := h_basic
  have h_N_pos : 0 < N := by omega
  have h_r_pos : 0 < r := h_ord.1
  have h_r_lt_N : r < N := Order_r_lt_N a r N h_N_pos h_ord
  have h_r_lt_2m : r < 2^m := by
    have h_r_le : r ≤ r * r := by nlinarith
    have h_r_sq_lt : r * r < N * N := by nlinarith
    have h_pow_m_lt : N^2 < 2^m := h_pow_m.1
    have h_N_sq : N^2 = N * N := by ring
    omega
  have h_2pm : 0 < (2^m : Nat) := Nat.two_pow_pos m
  -- Normalize the v form (cast manipulation done once).
  set v : ℝ := ((s_closest m k r : Nat) : ℝ) / ((2^m : Nat) : ℝ) with h_v_def
  have h_v_cast : ((s_closest m k r : ℝ) / (2^m : ℝ)) = v := by
    show ((s_closest m k r : Nat) : ℝ) / ((2 : ℝ) ^ m) = v
    rw [h_v_def]; push_cast; ring
  -- Step 1: Khinchin gives existence of N_step with convs N_step = k/r.
  -- Rewrite to use v directly.
  have h_exists_v : ∃ N_step, (GenContFract.of v).convs N_step
                              = (((k : ℚ) / r : ℚ) : ℝ) := by
    obtain ⟨N_step, h_convs⟩ :=
      k_over_r_is_convergent a r N m n k
        ⟨⟨h_a_pos, h_a_lt⟩, h_ord, h_pow_m, h_pow_n⟩ h_k_lt h_coprime
    rw [h_v_cast] at h_convs
    exact ⟨N_step, h_convs⟩
  -- Step 2: Pick smallest N_step via Nat.find.
  set N_step := Nat.find h_exists_v with h_N_step_def
  have h_convs : (GenContFract.of v).convs N_step = (((k : ℚ) / r : ℚ) : ℝ) :=
    Nat.find_spec h_exists_v
  have h_min_N_step : ∀ j < N_step,
      (GenContFract.of v).convs j ≠ (((k : ℚ) / r : ℚ) : ℝ) :=
    fun j hj hbad => Nat.find_min h_exists_v hj hbad
  -- Step 3: Derive v ≠ k/r in ℝ from h_ne (s_closest * r ≠ k * 2^m as Nat).
  have h_v_ne_kr : v ≠ (((k : ℚ) / r : ℚ) : ℝ) := by
    intro h_eq
    have h_pow_pos_R : (0 : ℝ) < ((2^m : Nat) : ℝ) := by exact_mod_cast h_2pm
    have h_r_pos_R : (0 : ℝ) < ((r : Nat) : ℝ) := by exact_mod_cast h_r_pos
    rw [h_v_def] at h_eq
    have h_rhs : (((k : ℚ) / r : ℚ) : ℝ) = (k : ℝ) / (r : ℝ) := by push_cast; ring
    rw [h_rhs] at h_eq
    have h_cross : (s_closest m k r : ℝ) * (r : ℝ)
                 = (k : ℝ) * ((2^m : Nat) : ℝ) := by
      field_simp at h_eq
      linarith
    have h_2pm_R : ((2^m : Nat) : ℝ) = ((2 : ℝ) ^ m) := by push_cast; rfl
    rw [h_2pm_R] at h_cross
    have h_nat_eq : (s_closest m k r) * r = k * (2^m) := by exact_mod_cast h_cross
    exact h_ne h_nat_eq
  -- Step 4: Derive ¬ TerminatedAt N_step from v ≠ k/r + h_convs N_step = k/r.
  -- Mathlib's of_correctness_of_terminatedAt: if Terminated, convs = v exactly.
  have h_not_term_N_step : ¬ (GenContFract.of v).TerminatedAt N_step := by
    intro h_term
    have h_convs_eq_v := GenContFract.of_correctness_of_terminatedAt h_term
    -- h_convs_eq_v : v = (GenContFract.of v).convs N_step.
    rw [h_convs] at h_convs_eq_v
    exact h_v_ne_kr h_convs_eq_v
  -- Step 3: dens N_step = r (via dens_eq_r_at_convs_eq_kr).
  have h_dens : (GenContFract.of v).dens N_step = (r : ℝ) :=
    dens_eq_r_at_convs_eq_kr v N_step k r h_not_term_N_step h_r_pos h_coprime h_convs
  -- Step 4: N_step ≤ 2m + 1.
  have h_not_term_alt : N_step = 0 ∨ ¬ (GenContFract.of v).TerminatedAt (N_step - 1) := by
    by_cases h : N_step = 0
    · left; exact h
    · right
      intro h_term
      have h_le : N_step - 1 ≤ N_step := by omega
      exact h_not_term_N_step (GenContFract.terminated_stable h_le h_term)
  have h_N_step_bound : N_step ≤ 2 * m + 1 :=
    N_step_le_2m_plus_1 v N_step r m h_dens h_not_term_alt h_r_lt_2m
  -- Step 5: Bridge OF_post_step N_step (s_closest m k r) m = r via the at_n
  -- variant (only needs ¬ TerminatedAt N_step, NOT N_step + 1). This avoids
  -- the boundary case where mathlib's CF may terminate exactly at N_step + 1.
  have h_bridge := mathlib_OF_post_step_nat_eq_OF_post_step_at_n N_step (s_closest m k r) m
    h_not_term_N_step
  -- mathlib_OF_post_step_nat N_step (s_closest m k r) m = OF_post_step N_step (s_closest m k r) m.
  -- We want: OF_post_step N_step (s_closest m k r) m = r.
  -- From h_dens + spec: mathlib_OF_post_step_nat N_step (s_closest m k r) m = r.
  have h_mathlib_eq_r : mathlib_OF_post_step_nat N_step (s_closest m k r) m = r := by
    have h_spec := mathlib_OF_post_step_spec N_step (s_closest m k r) m
    have h_cast_v : ((s_closest m k r : ℝ) / (2^m : ℝ)) = v := h_v_cast
    rw [h_cast_v] at h_spec
    rw [h_dens] at h_spec
    -- h_spec: (r : ℝ) = (mathlib_OF_post_step N_step (s_closest m k r) m : ℤ : ℝ).
    have h_int_eq : (r : ℤ) = mathlib_OF_post_step N_step (s_closest m k r) m := by
      exact_mod_cast h_spec
    have h_nat_int := mathlib_OF_post_step_nat_int N_step (s_closest m k r) m
    -- h_nat_int : ((mathlib_OF_post_step_nat N_step ... : Nat) : ℤ) = mathlib_OF_post_step N_step ...
    rw [← h_int_eq] at h_nat_int
    -- h_nat_int : ((mathlib_OF_post_step_nat N_step ... : Nat) : ℤ) = (r : ℤ).
    exact_mod_cast h_nat_int
  have h_of_step_eq_r : OF_post_step N_step (s_closest m k r) m = r := by
    rw [← h_bridge]; exact h_mathlib_eq_r
  -- Step 6: Walking — OF_post' (N_step + 1) a N (s_closest m k r) m = r.
  have h_modexp_at_r : modexp a r N = 1 := h_ord.2.1
  have h_walk_succ : OF_post' (N_step + 1) a N (s_closest m k r) m = r := by
    show (let pre := OF_post' N_step a N (s_closest m k r) m
          if pre = 0 then
            (if modexp a (OF_post_step N_step (s_closest m k r) m) N = 1
             then OF_post_step N_step (s_closest m k r) m else 0)
          else pre) = r
    by_cases h_pre : OF_post' N_step a N (s_closest m k r) m = 0
    · -- Case A: pre = 0. Result is OF_post_step N_step = r (since modexp a r N = 1).
      simp only [h_pre, if_true]
      rw [h_of_step_eq_r]
      rw [if_pos h_modexp_at_r]
    · -- Case B: pre ≠ 0. Result = pre. Show pre = r via dvd + bound.
      simp only [h_pre, if_false]
      -- r ∣ pre.
      have h_dvd : r ∣ OF_post' N_step a N (s_closest m k r) m := by
        rcases OF_post'_dvd_r N_step a N (s_closest m k r) m h_a_pos h_a_lt r h_ord with
          h0 | hd
        · exact absurd h0 h_pre
        · exact hd
      -- pre = OF_post_step x for some x < N_step.
      obtain ⟨x, h_x_lt, h_x_eq⟩ :=
        OF_post'_nonzero_pre N_step a N (s_closest m k r) m h_pre
      -- Bound OF_post_step x ≤ r via bridge + monotonicity.
      have h_x_succ_le : x + 1 ≤ N_step := by omega
      have h_not_term_x_succ :
          ¬ (GenContFract.of v).TerminatedAt (x + 1) := fun h =>
        h_not_term_N_step (GenContFract.terminated_stable h_x_succ_le h)
      have h_bridge_x := mathlib_OF_post_step_nat_eq_OF_post_step_nonboundary x
        (s_closest m k r) m h_not_term_x_succ
      have h_mono :
          mathlib_OF_post_step_nat x (s_closest m k r) m
          ≤ mathlib_OF_post_step_nat N_step (s_closest m k r) m :=
        mathlib_OF_post_step_nat_mono_le (s_closest m k r) m x N_step (by omega)
      rw [h_mathlib_eq_r, h_bridge_x, h_x_eq] at h_mono
      -- h_mono : OF_post' N_step ... ≤ r.
      have h_pre_pos : 0 < OF_post' N_step a N (s_closest m k r) m :=
        Nat.pos_of_ne_zero h_pre
      obtain ⟨c, hc⟩ := h_dvd
      have h_c_pos : 0 < c := by
        rcases Nat.eq_zero_or_pos c with rfl | h
        · rw [Nat.mul_zero] at hc; omega
        · exact h
      have h_c_eq_1 : c = 1 := by
        by_contra h_c_ne
        have h_c_ge_2 : c ≥ 2 := by omega
        have h_r_mul_ge : r * 2 ≤ r * c := Nat.mul_le_mul_left r h_c_ge_2
        have h_pre_ge : 2 * r ≤ OF_post' N_step a N (s_closest m k r) m := by
          rw [hc]; linarith
        linarith
      rw [hc, h_c_eq_1, Nat.mul_one]
  -- Step 7: Extend OF_post' (N_step + 1) = r to OF_post' (2m+2) = r via OF_post'_nonzero_equal.
  have h_2m2_decomp : 2 * m + 2 = (2 * m + 2 - (N_step + 1)) + (N_step + 1) := by omega
  have h_walk_ne : OF_post' (N_step + 1) a N (s_closest m k r) m ≠ 0 := by
    rw [h_walk_succ]; exact h_r_pos.ne'
  unfold OF_post
  rw [h_2m2_decomp]
  rw [OF_post'_nonzero_equal (2 * m + 2 - (N_step + 1)) (N_step + 1) a N
      (s_closest m k r) m h_walk_ne]
  exact h_walk_succ

/-- **r_found_1_core**: the operational claim — `OF_post` equals `r` on
the `s_closest` input. The `r_found_1` axiom follows by unfolding `r_found`
as an indicator.

Refactored 2026-05-24 per John's recommendation into a case split on
`s_closest m k r * r = k * 2^m`, dispatching to the exact-rational or
generic helper. -/
private theorem TODO_r_found_1_core
    (a r N m n k : Nat)
    (h_basic : BasicSetting a r N m n)
    (h_k_lt : k < r)
    (h_coprime : Nat.gcd k r = 1) :
    OF_post a N (s_closest m k r) m = r := by
  by_cases h_eq : s_closest m k r * r = k * 2^m
  · exact TODO_r_found_1_core_exact_rational a r N m n k h_basic h_k_lt h_coprime h_eq
  · exact TODO_r_found_1_core_generic a r N m n k h_basic h_k_lt h_coprime h_eq

/-- **`r_found_1`** (closed 2026-05-24): The post-processor `r_found`
returns 1 (i.e., recovers the order `r`) when the measurement outcome
is `s_closest m k r` — the integer nearest `k · 2^m / r`.

This is the headline operational claim: classical post-processing on a
"good" QPE outcome reliably extracts the order. Built from
`TODO_r_found_1_core` (which proves `OF_post = r`) by unfolding the
indicator `r_found`. Axiom-clean (propext, Classical.choice, Quot.sound). -/
theorem r_found_1
    (a r N m n k : Nat)
    (h_basic : BasicSetting a r N m n)
    (h_k_lt : k < r)
    (h_coprime : Nat.gcd k r = 1) :
    r_found (s_closest m k r) m r a N = 1 := by
  have h_core := TODO_r_found_1_core a r N m n k h_basic h_k_lt h_coprime
  unfold r_found
  rw [if_pos h_core]

/-- **`phi_n_over_n_lowerbound`** (Coq: `EulerTotient.v`; Lean closure
2026-05-24). Euler's totient lower bound: `ϕ(r) / r ≥ exp(−2) / (log₂ N)^4`
whenever `r ≤ N` and `r > 0`.

**CLOSED** by an elementary distinct-prime-factor argument (no
Mertens-third-theorem needed). The full proof lives in
`SQIRPort/TotientLowerBound.lean` as `phi_n_over_n_lowerbound_proved`;
this is the thin re-export keeping the original name so existing
references resolve. -/
theorem phi_n_over_n_lowerbound (r N : Nat) (h_r_pos : 0 < r) (h_le : r ≤ N) :
    ((Nat.totient r : ℝ) / (r : ℝ))
      ≥ Real.exp (-2) / (Nat.log2 N : ℝ)^4 :=
  phi_n_over_n_lowerbound_proved r N h_r_pos h_le

/-- Probabilities are non-negative.

**Closed 2026-05-24 as a theorem.** Direct consequence of the
operational definition: a sum of `Complex.normSq` values, each of which
is non-negative; the `else 0` branch is also non-negative. -/
theorem prob_partial_meas_nonneg {m_dim full_dim : Nat}
    (ψ : QState m_dim) (φ : QState full_dim) : 0 ≤ prob_partial_meas ψ φ := by
  unfold prob_partial_meas
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  · rfl

/-! ## Partial-measurement API (basis-vector first register)

API lemmas for `prob_partial_meas` when the first register is a
computational basis state `|s⟩`. These reduce the inner-product sum to
a single non-zero contribution (at `x.val = s`), giving a clean closed
form: the partial-measurement probability is the sum of squared
amplitudes over the "selected slice" of the joint state. -/

/-- **Selected-slice index** for partial measurement: maps a "first
register" outcome `s : Fin m_dim` and "second register" basis index
`y : Fin (full_dim / m_dim)` to the joint-register basis index
`s · (full_dim / m_dim) + y` in `Fin full_dim`. The cast through
`Fin (m_dim * (full_dim / m_dim))` uses the divisibility hypothesis. -/
noncomputable def partial_meas_index {m_dim full_dim : Nat}
    (h_dvd : m_dim ∣ full_dim) (s : Fin m_dim)
    (y : Fin (full_dim / m_dim)) : Fin full_dim :=
  Fin.cast (Nat.mul_div_cancel' h_dvd) ⟨s.val * (full_dim / m_dim) + y.val, by
    have hx : s.val < m_dim := s.isLt
    have hy : y.val < full_dim / m_dim := y.isLt
    calc s.val * (full_dim / m_dim) + y.val
        < s.val * (full_dim / m_dim) + (full_dim / m_dim) := by omega
      _ = (s.val + 1) * (full_dim / m_dim) := by ring
      _ ≤ m_dim * (full_dim / m_dim) := Nat.mul_le_mul_right _ hx⟩

/-- **Partial-measurement formula for a basis-vector outcome**: when
the first-register outcome is `basis_vector m_dim s` with `s < m_dim`,
the inner-product sum collapses to a single term (the contribution
at `x.val = s`), and the partial-measurement probability becomes a
sum of squared amplitudes along the selected slice of the joint state.

      prob_partial_meas (basis_vector m_dim s) φ
        = ∑ y : Fin (full_dim / m_dim),
            ‖φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y)‖²
-/
theorem prob_partial_meas_basis_vector
    {m_dim full_dim : Nat} (s : Nat) (h_s_lt : s < m_dim)
    (h_dvd : m_dim ∣ full_dim) (φ : QState full_dim) :
    prob_partial_meas (basis_vector m_dim s) φ
      = ∑ y : Fin (full_dim / m_dim),
          Complex.normSq (φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0) := by
  unfold prob_partial_meas
  rw [dif_pos h_dvd]
  refine Finset.sum_congr rfl ?_
  intro y _
  congr 1
  -- ∑ x : Fin m_dim, conj(basis x 0) · φ(...) = φ(...) at x = s.
  rw [Finset.sum_eq_single (⟨s, h_s_lt⟩ : Fin m_dim)]
  · -- main case: x = ⟨s, h_s_lt⟩, basis_vector at s is 1.
    show starRingEnd ℂ ((basis_vector m_dim s) ⟨s, h_s_lt⟩ 0) *
          φ (Fin.cast (Nat.mul_div_cancel' h_dvd) _) 0
        = φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0
    show starRingEnd ℂ (if (⟨s, h_s_lt⟩ : Fin m_dim).val = s then (1 : ℂ) else 0)
          * φ _ 0 = _
    simp [partial_meas_index]
  · -- other cases: x ≠ ⟨s, h_s_lt⟩, so x.val ≠ s, basis is 0.
    intro x _ h_ne
    show starRingEnd ℂ ((basis_vector m_dim s) x 0) * φ _ 0 = 0
    show starRingEnd ℂ (if x.val = s then (1 : ℂ) else 0) * φ _ 0 = 0
    have h_x_ne : x.val ≠ s := fun heq => h_ne (Fin.ext heq)
    simp [h_x_ne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Partial-measurement of basis-vector on a tensor-product state**:
when the joint state factors as `kron_vec a b`, the partial-measurement
probability at a first-register basis-vector outcome reduces to the
single squared amplitude of `a` at that outcome, multiplied by the
total `‖b‖²` of the second-register state:

      prob_partial_meas (basis_vector (2^p) s) (kron_vec a b)
        = ‖a_s‖² · ∑ y : Fin (2^q), ‖b_y‖²

For a normalized second-register state (`Pure_State_Vector b`), the
sum is `1` and the partial-meas reduces to just `‖a_s‖²` — exactly the
"distribution on the first register, ignoring the second" reading of
partial measurement. Proof: combines `prob_partial_meas_basis_vector`
with the index identity `partial_meas_index = kron_vec_combine` and
`Equiv.sum_comp` for the dimensional reindex. -/
theorem prob_partial_meas_basis_kron_vec
    {p q : Nat} (s : Nat) (h_s_lt : s < 2^p)
    (a : QState (2^p)) (b : QState (2^q)) :
    prob_partial_meas (basis_vector (2^p) s)
        (FormalRV.Framework.kron_vec a b)
      = Complex.normSq (a ⟨s, h_s_lt⟩ 0) *
        ∑ y : Fin (2^q), Complex.normSq (b y 0) := by
  have h_dvd : (2^p : ℕ) ∣ (2^(p+q) : ℕ) := pow_dvd_pow 2 (Nat.le_add_right p q)
  have h_div : (2^(p+q)) / (2^p) = 2^q := by
    rw [pow_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos p)]
  rw [prob_partial_meas_basis_vector s h_s_lt h_dvd]
  -- Step 1: identify partial_meas_index with kron_vec_combine.
  have h_idx_eq : ∀ y : Fin ((2^(p+q))/(2^p)),
      partial_meas_index h_dvd ⟨s, h_s_lt⟩ y
        = FormalRV.Framework.kron_vec_combine ⟨s, h_s_lt⟩ (Fin.cast h_div y) := by
    intro y
    apply Fin.ext
    show s * ((2^(p+q))/(2^p)) + y.val = s * 2^q + y.val
    have : s * ((2^(p+q))/(2^p)) = s * 2^q := by rw [h_div]
    omega
  -- Step 2: apply kron_vec_normSq_apply_combine pointwise.
  rw [show (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq ((FormalRV.Framework.kron_vec a b)
                              (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0))
        = (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq (a ⟨s, h_s_lt⟩ 0) *
            Complex.normSq (b (Fin.cast h_div y) 0)) by
      refine Finset.sum_congr rfl ?_
      intro y _
      rw [h_idx_eq y]
      exact FormalRV.Framework.kron_vec_normSq_apply_combine a b ⟨s, h_s_lt⟩ _]
  -- Step 3: factor out normSq(a_s) and reindex via Fin.castOrderIso h_div.
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Fin.castOrderIso h_div).toEquiv
    (fun y => Complex.normSq (b y 0))

/-- **Partial-measurement of `qpe_phase_state ⊗ eigen` gives the ideal
analytic probability**: when the QPE-output state is the tensor product
of the ideal QPE phase register `qpe_phase_state m θ` and any
data-register state `ψ_eigen`, the partial-measurement probability at
the phase-register outcome `y` is exactly the ideal `qpe_prob m y θ`,
scaled by the total squared amplitude of `ψ_eigen` (which is `1` when
`ψ_eigen` is `Pure_State_Vector`).

      prob_partial_meas (basis_vector (2^m) y)
          (kron_vec (qpe_phase_state m θ) ψ_eigen)
        = qpe_prob m y θ · ∑ z, ‖ψ_eigen_z‖²

This is the kernel-clean connection between the actual
partial-measurement probability (left side, lives in the Shor port) and
the abstract analytic QPE probability (right side, lives in
`Framework.QPEAmplitude`). For normalized `ψ_eigen`, this reduces to
`qpe_prob m y θ`. -/
theorem prob_partial_meas_qpe_phase_state_kron
    {m anc : Nat} (y : Nat) (h_y_lt : y < 2^m) (θ : ℝ)
    (ψ_eigen : QState (2^anc)) :
    prob_partial_meas (basis_vector (2^m) y)
        (FormalRV.Framework.kron_vec
          (FormalRV.Framework.qpe_phase_state m θ) ψ_eigen)
      = FormalRV.Framework.qpe_prob m y θ *
        ∑ z : Fin (2^anc), Complex.normSq (ψ_eigen z 0) := by
  rw [prob_partial_meas_basis_kron_vec y h_y_lt
        (FormalRV.Framework.qpe_phase_state m θ) ψ_eigen]
  rw [FormalRV.Framework.normSq_qpe_phase_state_apply]

/-- **Corollary: normalized eigenstate case**. When `ψ_eigen` is a
`Pure_State_Vector` (`∑ ‖ψ_eigen_z‖² = 1`), the partial-measurement
probability is exactly the ideal analytic `qpe_prob m y θ`. -/
theorem prob_partial_meas_qpe_phase_state_kron_pure
    {m anc : Nat} (y : Nat) (h_y_lt : y < 2^m) (θ : ℝ)
    (ψ_eigen : QState (2^anc))
    (h_pure : FormalRV.Framework.Pure_State_Vector ψ_eigen) :
    prob_partial_meas (basis_vector (2^m) y)
        (FormalRV.Framework.kron_vec
          (FormalRV.Framework.qpe_phase_state m θ) ψ_eigen)
      = FormalRV.Framework.qpe_prob m y θ := by
  rw [prob_partial_meas_qpe_phase_state_kron y h_y_lt θ ψ_eigen]
  unfold FormalRV.Framework.Pure_State_Vector at h_pure
  rw [h_pure, mul_one]

/-- **Orthogonal-superposition partial-measurement formula**: for an
orthonormal family `β : Fin r → QState (2^q)` (the eigenstates of the
unmeasured register) and any family `α : Fin r → QState (2^p)` of
"phase register" outputs, the partial-measurement probability of a
basis outcome on the linear combination

      Ψ = ∑ j : Fin r, kron_vec (α j) (β j)

equals the orthogonality-collapsed sum

      ∑ j : Fin r, ‖α_j ⟨s, _⟩ 0‖².

The cross-terms `α_j · α_j'` (for `j ≠ j'`) vanish by orthonormality
of `β`. Proof: combines `prob_partial_meas_basis_vector` with
`Framework.normSq_sum_apply_orth` (Parseval) and the identification
`partial_meas_index = kron_vec_combine`. -/
theorem prob_partial_meas_basis_sum_kron_orth
    {p q r : Nat} (s : Nat) (h_s_lt : s < 2^p)
    (α : Fin r → QState (2^p)) (β : Fin r → QState (2^q))
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0) :
    prob_partial_meas (basis_vector (2^p) s)
        ((∑ j : Fin r, FormalRV.Framework.kron_vec (α j) (β j) :
           Matrix (Fin (2^(p+q))) (Fin 1) ℂ))
      = ∑ j : Fin r, Complex.normSq ((α j) ⟨s, h_s_lt⟩ 0) := by
  have h_dvd : (2^p : ℕ) ∣ (2^(p+q) : ℕ) := pow_dvd_pow 2 (Nat.le_add_right p q)
  have h_div : (2^(p+q)) / (2^p) = 2^q := by
    rw [pow_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos p)]
  rw [prob_partial_meas_basis_vector s h_s_lt h_dvd]
  -- Step 1: identify partial_meas_index with kron_vec_combine (same as kron_vec lemma).
  have h_idx_eq : ∀ y : Fin ((2^(p+q))/(2^p)),
      partial_meas_index h_dvd ⟨s, h_s_lt⟩ y
        = FormalRV.Framework.kron_vec_combine ⟨s, h_s_lt⟩ (Fin.cast h_div y) := by
    intro y
    apply Fin.ext
    show s * ((2^(p+q))/(2^p)) + y.val = s * 2^q + y.val
    have : s * ((2^(p+q))/(2^p)) = s * 2^q := by rw [h_div]
    omega
  -- Step 2: distribute sum into kron_vec_apply_combine.
  rw [show (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq ((∑ j : Fin r,
              FormalRV.Framework.kron_vec (α j) (β j) :
              Matrix (Fin (2^(p+q))) (Fin 1) ℂ)
              (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0))
        = (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq (∑ j : Fin r,
              (α j) ⟨s, h_s_lt⟩ 0 * (β j) (Fin.cast h_div y) 0)) by
      refine Finset.sum_congr rfl ?_
      intro y _
      congr 1
      simp only [Matrix.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_idx_eq y]
      exact FormalRV.Framework.kron_vec_apply_combine (α j) (β j) ⟨s, h_s_lt⟩ _]
  -- Step 3: reindex sum from Fin ((2^(p+q))/(2^p)) to Fin (2^q).
  rw [show (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq (∑ j : Fin r,
              (α j) ⟨s, h_s_lt⟩ 0 * (β j) (Fin.cast h_div y) 0))
        = (∑ y : Fin (2^q),
            Complex.normSq (∑ j : Fin r,
              (α j) ⟨s, h_s_lt⟩ 0 * (β j) y 0)) from by
      exact Equiv.sum_comp (Fin.castOrderIso h_div).toEquiv
        (fun y => Complex.normSq (∑ j : Fin r,
          (α j) ⟨s, h_s_lt⟩ 0 * (β j) y 0))]
  -- Step 4: apply Parseval.
  exact FormalRV.Framework.normSq_sum_apply_orth β h_orth
    (fun j => (α j) ⟨s, h_s_lt⟩ 0)

/-- **Scalar scaling for partial measurement** (Born-rule homogeneity):
scaling the joint state by `c ∈ ℂ` (applied pointwise as `fun i j =>
c * φ i j`) scales the partial-measurement probability by `‖c‖²`.

      prob_partial_meas ψ (c · φ)  =  ‖c‖² · prob_partial_meas ψ φ

The scaled state is written as `fun i j => c * φ i j` rather than
`c • φ` to avoid the `SMul ℂ (QState dim)` typeclass-synthesis issue
(`QState` is a `def` alias for `Matrix (Fin dim) (Fin 1) ℂ`, so the
Matrix SMul instance doesn't automatically lift). For callers using
`c • φ`, applying `Matrix.smul_apply` recovers the equivalence.

Proof: in the divisibility branch, push the scalar through the inner
sum (via `Finset.mul_sum` + `ring`), then use `Complex.normSq_mul`
to factor `‖c‖²` out of each `normSq` term, then `Finset.mul_sum` to
pull it out of the outer sum. The else-0 branch is trivial (`ring`). -/
theorem prob_partial_meas_smul_right
    {m_dim full_dim : Nat}
    (ψ : QState m_dim) (φ : QState full_dim) (c : ℂ) :
    prob_partial_meas ψ (fun i j => c * φ i j)
      = Complex.normSq c * prob_partial_meas ψ φ := by
  unfold prob_partial_meas
  by_cases h_dvd : m_dim ∣ full_dim
  · rw [dif_pos h_dvd, dif_pos h_dvd]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [show (∑ x : Fin m_dim, starRingEnd ℂ (ψ x 0) *
              (c * φ (Fin.cast (Nat.mul_div_cancel' h_dvd) _) 0))
          = c * ∑ x : Fin m_dim, starRingEnd ℂ (ψ x 0) *
              φ (Fin.cast (Nat.mul_div_cancel' h_dvd) _) 0 from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intros; ring]
    rw [Complex.normSq_mul]
  · rw [dif_neg h_dvd, dif_neg h_dvd]
    ring

/-- **`normSq` of `1/√r`** as a real cast: `‖1/√r‖² = 1/r`. Used to
turn the `(1/√r)`-scaling factor (from the standard orbit-state
normalization `|1⟩_n = (1/√r) · Σ_k |ψ_k⟩`) into the `(1/r)` weight
in the QPE peak-bound chain. -/
private theorem normSq_one_div_sqrt (r : Nat) (h_r_pos : 0 < r) :
    Complex.normSq ((1 / (Real.sqrt r : ℂ))) = 1 / (r : ℝ) := by
  have h_r_R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h_r_pos
  rw [show (1 / (Real.sqrt r : ℂ)) = ((1 / Real.sqrt r : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.normSq_ofReal]
  field_simp
  rw [Real.sq_sqrt h_r_R.le]

/-- **QPE orthogonal-sum bridge with `1/r` factor**: the headline
combination of the scalar lemma + orthogonal-superposition formula +
QPE phase-state evaluation. Given:
* a family `k : Fin r → ℝ` of "true phases" (one per eigenstate),
* an orthonormal family `β : Fin r → QState (2^q)` of unmeasured-
  register eigenstates,

the partial-measurement probability of basis outcome `s` on the
normalized orbit-state-style superposition
`(1/√r) · ∑_j (qpe_phase_state p (k_j)) ⊗ |β_j⟩` equals the
average ideal QPE probability:

      (1/r) · ∑_j, qpe_prob p s (k_j).

Combined with `qpe_prob_peak_bound`, this gives the standard
`(1/r) · 4/π²` per-correctly-aligned-eigenstate lower bound — exactly
the per-outcome contribution at the heart of `QPE_MMI_correct`. -/
theorem prob_partial_meas_qpe_orth_sum
    {p q r : Nat} (s : Nat) (h_s_lt : s < 2^p) (h_r_pos : 0 < r)
    (k : Fin r → ℝ)
    (β : Fin r → QState (2^q))
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0) :
    prob_partial_meas (basis_vector (2^p) s)
        (fun i j => (1 / (Real.sqrt r : ℂ)) *
          ((∑ j_idx : Fin r,
             FormalRV.Framework.kron_vec
               (FormalRV.Framework.qpe_phase_state p (k j_idx)) (β j_idx) :
             Matrix (Fin (2^(p+q))) (Fin 1) ℂ) i j))
      = (1 / (r : ℝ)) * ∑ j_idx : Fin r,
          FormalRV.Framework.qpe_prob p s (k j_idx) := by
  -- Step 1: factor out the (1/√r) scalar via prob_partial_meas_smul_right.
  rw [prob_partial_meas_smul_right]
  -- Step 2: apply the orthogonal-superposition partial-meas formula.
  rw [prob_partial_meas_basis_sum_kron_orth s h_s_lt
        (fun j => FormalRV.Framework.qpe_phase_state p (k j)) β h_orth]
  -- Step 3: ‖qpe_phase_state at index‖² = qpe_prob.
  simp_rw [FormalRV.Framework.normSq_qpe_phase_state_apply]
  -- Step 4: ‖1/√r‖² = 1/r.
  rw [normSq_one_div_sqrt r h_r_pos]

/-- **`QPE_MMI_correct_from_orbit`** (added 2026-05-24): state-
factorization conditional form of `QPE_MMI_correct`. Given an
orthonormal eigenstate family `β j` (for the unmeasured register) and
the orbit-state superposition shape

  `(1/√r) · ∑ j_idx : Fin r,
     (qpe_phase_state m (j_idx/r)) ⊗ (β j_idx)`

for the joint output state, the QPE peak bound `≥ 4/(π²·r)` at outcome
`s_closest m k r` follows. Closes the analytic half of the
`QPE_MMI_correct` axiom; the remaining (semantic / circuit) half is
showing that `Shor_final_state m n anc f` actually has this form,
which requires the circuit semantics of `QPE_var` plus the modular
multiplier's eigenstate spectrum (deferred to Phase 4).

Kernel-clean: depends on `prob_partial_meas_qpe_orth_sum` (the
`(1/r)`-factored partial-meas bridge), `qpe_prob_at_s_closest_ge`
(the analytic `4/π²` peak bound at the matching `k/r` term), and
basic real arithmetic. -/
theorem QPE_MMI_correct_from_orbit
    {m q r : Nat} (k : Nat) (h_k_lt : k < r) (h_r_pos : 0 < r)
    (h_s_lt : s_closest m k r < 2^m)
    (β : Fin r → Matrix (Fin (2^q)) (Fin 1) ℂ)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (fun i j => (1 / (Real.sqrt r : ℂ)) *
          ((∑ j_idx : Fin r,
             FormalRV.Framework.kron_vec
               (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
               (β j_idx) :
             Matrix (Fin (2^(m + q))) (Fin 1) ℂ) i j))
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  rw [prob_partial_meas_qpe_orth_sum (s_closest m k r) h_s_lt h_r_pos
        (fun j_idx => ((j_idx.val : ℝ) / r)) β h_orth]
  have h_r_pos_R : (0 : ℝ) < r := by exact_mod_cast h_r_pos
  have h_simp : (1 / (r : ℝ)) * (4 / Real.pi^2) = 4 / (Real.pi^2 * r) := by
    field_simp
  -- Sum is bounded below by the j_idx = ⟨k, h_k_lt⟩ term, which is ≥ 4/π².
  have h_sum_ge : (4 / Real.pi^2 : ℝ)
      ≤ ∑ j_idx : Fin r,
          FormalRV.Framework.qpe_prob m (s_closest m k r)
                                        ((j_idx.val : ℝ) / r) := by
    have h_term : (4 / Real.pi^2 : ℝ)
        ≤ FormalRV.Framework.qpe_prob m (s_closest m k r) ((k : ℝ) / r) :=
      qpe_prob_at_s_closest_ge m k r h_r_pos
    set g : Fin r → ℝ := fun j_idx =>
        FormalRV.Framework.qpe_prob m (s_closest m k r) ((j_idx.val : ℝ) / r) with hg
    have h_g_nonneg : ∀ j_idx ∈ Finset.univ, 0 ≤ g j_idx :=
      fun _ _ => FormalRV.Framework.qpe_prob_nonneg _ _ _
    have h_single : g ⟨k, h_k_lt⟩ ≤ ∑ j_idx, g j_idx :=
      Finset.single_le_sum h_g_nonneg (Finset.mem_univ _)
    have h_g_k : g ⟨k, h_k_lt⟩ = FormalRV.Framework.qpe_prob m (s_closest m k r) ((k : ℝ) / r) := rfl
    rw [h_g_k] at h_single
    linarith
  have h_lhs_ge : (1 / (r : ℝ)) * (4 / Real.pi^2)
                ≤ (1 / (r : ℝ)) * ∑ j_idx : Fin r,
                    FormalRV.Framework.qpe_prob m (s_closest m k r)
                                                  ((j_idx.val : ℝ) / r) :=
    mul_le_mul_of_nonneg_left h_sum_ge (by positivity)
  linarith

/-- **`QPE_MMI_correct_from_orbit_state_eq`** (added 2026-05-24):
the state-equality form of `QPE_MMI_correct_from_orbit`. Given an
`actual_state` at the natural `Matrix (Fin (2^(m+q))) (Fin 1) ℂ`
type and an equality hypothesis showing that this state is exactly
the orbit-superposition form, the QPE peak bound follows.

This is the cleanest "factor the QPE_MMI_correct axiom through a
state-equality hypothesis" theorem. To recover the public
`QPE_MMI_correct` shape, the remaining work is a separate equality
theorem:

  `Shor_final_state m n anc f = (orbit-superposition state)`

(possibly with a `QState.cast` for the dimension `2^m · 2^n · 2^anc`
vs `2^(m + (n + anc))` mismatch). That equality is the genuine
SQIR/`QPEGeneral.v` semantic obligation; this conditional theorem
closes everything downstream of it. -/
theorem QPE_MMI_correct_from_orbit_state_eq
    {m q r : Nat} (k : Nat) (h_k_lt : k < r) (h_r_pos : 0 < r)
    (h_s_lt : s_closest m k r < 2^m)
    (β : Fin r → Matrix (Fin (2^q)) (Fin 1) ℂ)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0)
    (actual_state : Matrix (Fin (2^(m + q))) (Fin 1) ℂ)
    (h_state : actual_state =
      fun i j => (1 / (Real.sqrt r : ℂ)) *
        ((∑ j_idx : Fin r,
           FormalRV.Framework.kron_vec
             (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
             (β j_idx) :
           Matrix (Fin (2^(m + q))) (Fin 1) ℂ) i j)) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r)) actual_state
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  rw [h_state]
  exact QPE_MMI_correct_from_orbit k h_k_lt h_r_pos h_s_lt β h_orth

/-- **`QPE_MMI_correct_from_Shor_orbit_state`** (added 2026-05-24):
the Shor-shaped wrapper around `QPE_MMI_correct_from_orbit_state_eq`.
Takes the Shor-specific parameters and `BasicSetting`/`ModMulImpl`/
well-typed hypotheses (mirroring `QPE_MMI_correct`'s signature), plus
an explicit state-equality hypothesis showing the joint output state
is the orbit superposition. Derives `0 < r` from `BasicSetting`'s
`Order` field and `s_closest m k r < 2^m` from the existing
`s_closest_ub` helper, then dispatches to
`QPE_MMI_correct_from_orbit_state_eq`.

The conclusion is stated on `actual_state` (not directly on
`Shor_final_state`) to avoid the `QState (2^m * 2^n * 2^anc)` vs
`Matrix (Fin (2^(m + (n + anc))))` dimensional cast — a future tick
can bridge `actual_state` and `Shor_final_state` via `QState.cast` in
a separate equality theorem. The current theorem isolates the QPE-
bound content from that cast bookkeeping.

The `_h_mmi` / `_h_wt` arguments are unused in the proof but kept in
the signature to mirror the public `QPE_MMI_correct`'s shape exactly,
making the final substitution into the full Shor chain mechanical
once the state-factorization equality lands. -/
theorem QPE_MMI_correct_from_Shor_orbit_state
    (a r N m n anc k : Nat)
    (f : Nat → BaseUCom (n + anc))
    (β : Fin r → Matrix (Fin (2^(n + anc))) (Fin 1) ℂ)
    (h_basic : BasicSetting a r N m n)
    (_h_mmi : ModMulImpl a N n anc f)
    (_h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^(n + anc)), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0)
    (actual_state : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ)
    (h_state : actual_state =
      fun i j => (1 / (Real.sqrt r : ℂ)) *
        ((∑ j_idx : Fin r,
           FormalRV.Framework.kron_vec
             (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
             (β j_idx) :
           Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ) i j)) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r)) actual_state
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  have h_r_pos : 0 < r := h_basic.2.1.1
  have h_s_lt : s_closest m k r < 2^m :=
    s_closest_ub a r N m n k h_basic h_k_lt
  exact QPE_MMI_correct_from_orbit_state_eq k h_k_lt h_r_pos h_s_lt
    β h_orth actual_state h_state

/-- **`QPE_MMI_correct_assuming_orbit_factorization`** (added
2026-05-24): the maximal closure of the QPE_MMI_correct axiom that
this codebase currently supports.

Replaces the entire QPE semantic chain with a SINGLE existential
hypothesis `h_orbit_exists`: "there exist orthonormal eigenstates β
and an orbit-form state whose partial-measurement probability matches
`Shor_final_state`'s." Given this hypothesis, the QPE peak bound
follows from the kernel-clean conditional chain
(`QPE_MMI_correct_from_Shor_orbit_state` ∘
`QPE_MMI_correct_from_orbit_state_eq` ∘
`QPE_MMI_correct_from_orbit` ∘ `prob_partial_meas_qpe_orth_sum` ∘
`qpe_prob_peak_bound`) — no axiom is needed downstream of the
existential.

**This theorem cannot replace the `QPE_MMI_correct` axiom directly**
because the existential `h_orbit_exists` is genuinely deep: it
unfolds into the modular-multiplier eigenstate construction +
`QPE_var` circuit semantics, both Phase-4 obligations needing
multi-file infrastructure that does not yet exist in
`Framework.QuantumLib` (linearity of `uc_eval` over arbitrary state
sums, partial-trace machinery, the spectral theorem for unitary
matrices applied to the modular multiplier, etc.).

What this theorem DOES accomplish:
- It witnesses that the analytic / counting / averaging content of
  `QPE_MMI_correct` is fully Lean-proved.
- It pinpoints the EXACT remaining semantic obligation in a single
  named existential hypothesis.
- Replacing this single existential with a theorem-form derivation
  (the Phase-4 work) is sufficient to close the entire QPE chain.

Kernel-clean: `[propext, Classical.choice, Quot.sound]` only. -/
theorem QPE_MMI_correct_assuming_orbit_factorization
    (a r N m n anc k : Nat) (f : Nat → BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_mmi : ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_orbit_exists :
        ∃ (β : Fin r → Matrix (Fin (2^(n + anc))) (Fin 1) ℂ)
          (actual_state : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ),
          ((∀ j j' : Fin r,
             ∑ y : Fin (2^(n + anc)),
                  starRingEnd ℂ ((β j') y 0) * (β j) y 0
             = if j = j' then (1 : ℂ) else 0)
          ∧ (actual_state = fun i j => (1 / (Real.sqrt r : ℂ)) *
              ((∑ j_idx : Fin r,
                 FormalRV.Framework.kron_vec
                   (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
                   (β j_idx) :
                 Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ) i j))
          ∧ (prob_partial_meas (basis_vector (2^m) (s_closest m k r))
                (Shor_final_state m n anc f)
              = prob_partial_meas (basis_vector (2^m) (s_closest m k r))
                                  actual_state))) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  obtain ⟨β, actual_state, h_orth, h_state, h_prob_eq⟩ := h_orbit_exists
  rw [h_prob_eq]
  exact QPE_MMI_correct_from_Shor_orbit_state a r N m n anc k f β
    h_basic h_mmi h_wt h_k_lt h_orth actual_state h_state

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
