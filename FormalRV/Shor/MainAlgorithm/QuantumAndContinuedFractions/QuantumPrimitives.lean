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

end FormalRV.SQIRPort
