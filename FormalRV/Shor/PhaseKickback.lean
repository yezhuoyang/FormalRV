/-
  FormalRV.SQIRPort.PhaseKickback

  Block-disjoint commutation + QPE-specific phase-kickback cascade.

  QPE's `QPE_var m anc f` lifts each `f i : BaseUCom anc` to
  `BaseUCom (m + anc)` via `map_qubits (fun q => m + q) (f i)`,
  placing the data-register action at qubit positions [m, m + anc)
  and leaving the control register at [0, m). This file proves:

  - `is_fresh_map_qubits_shift`: control qubits are fresh in lifted circuits.
  - `wellTyped_map_qubits_shift`: lifted circuits remain well-typed on the
    enlarged register.
  - `uc_eval_map_qubits_shift_commutes_pad_u`: matrix-level block-disjoint
    commutation — the key bridge that validates the abstract cascade's
    `h_comm_all` hypothesis for QPE's layout.
  - `uc_eval_controlled_powers_shifted_on_common_eigenstate`: the QPE-
    specific cascade theorem, derived by discharging the abstract cascade
    theorem's hypotheses with the three lemmas above.

  This file imports both `ControlledGates` (for the abstract cascade) and
  `Shor` (for `map_qubits`). The two have no cyclic dependency: Shor.lean
  imports only `Eigenstate` + `TotientLowerBound`, neither of which uses
  the control-stub fix.
-/

import FormalRV.Shor.ControlledGates
import FormalRV.Shor.Shor

namespace FormalRV.SQIRPort

open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-! ## Shifted-data-register lemmas -/

/-- **Shifted freshness.** Any control qubit `q < m` is fresh in the
shift-lifted circuit `map_qubits (fun x => m + x) c`, because every gate's
qubit index becomes `m + n ≥ m > q`. -/
theorem is_fresh_map_qubits_shift {m anc q : Nat}
    (c : BaseUCom anc) (hq : q < m) :
    is_fresh q (map_qubits (fun x => m + x) c : BaseUCom (m + anc)) := by
  induction c with
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | app1 _ n => show q ≠ m + n; omega
  | app2 _ a b => exact ⟨by show q ≠ m + a; omega, by show q ≠ m + b; omega⟩
  | app3 _ a b c =>
      exact ⟨by show q ≠ m + a; omega,
             by show q ≠ m + b; omega,
             by show q ≠ m + c; omega⟩

/-- **Shifted well-typedness.** A circuit well-typed on `anc` qubits
becomes well-typed on `m + anc` after shifting every index by `+m`. -/
theorem wellTyped_map_qubits_shift {m anc : Nat}
    (c : BaseUCom anc) (h_wt : UCom.WellTyped anc c) :
    UCom.WellTyped (m + anc)
      (map_qubits (fun x => m + x) c : BaseUCom (m + anc)) := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
      cases h_wt with
      | seq h₁ h₂ => exact UCom.WellTyped.seq (ih₁ h₁) (ih₂ h₂)
  | app1 _ n =>
      cases h_wt with
      | app1 hn => exact UCom.WellTyped.app1 (show m + n < m + anc by omega)
  | app2 _ a b =>
      cases h_wt with
      | app2 ha hb hab =>
        exact UCom.WellTyped.app2
          (show m + a < m + anc by omega)
          (show m + b < m + anc by omega)
          (show m + a ≠ m + b by omega)
  | app3 _ a b d =>
      cases h_wt with
      | app3 ha hb hd hab hbd had =>
        exact UCom.WellTyped.app3
          (show m + a < m + anc by omega)
          (show m + b < m + anc by omega)
          (show m + d < m + anc by omega)
          (show m + a ≠ m + b by omega)
          (show m + b ≠ m + d by omega)
          (show m + a ≠ m + d by omega)

/-- **Block-disjoint commutation.** For any control-register qubit
`q < m`, the matrix `pad_u (m + anc) q U` commutes with the matrix
semantics of a shift-lifted data-register circuit. This is the crucial
lemma validating the `h_comm_all` hypothesis of the abstract cascade
theorem for QPE's specific block layout.

Proof by induction on `c`:
- `seq`: by IH on both sides + reassociation;
- `app1 (R θ φ λ) n`: shifted target `m + n` satisfies `q < m ≤ m + n`,
  so `pad_u_disjoint_comm'` applies;
- `app2 CNOT a b`: shifted targets `m + a`, `m + b` both `> q`, so
  `pad_u_pad_ctrl_disjoint_comm` applies;
- `app3`: vacuous since `BaseUnitary 3` is empty. -/
theorem uc_eval_map_qubits_shift_commutes_pad_u {m anc q : Nat}
    (c : BaseUCom anc) (hq : q < m) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u (m + anc) q U *
        FormalRV.Framework.uc_eval
          (map_qubits (fun x => m + x) c : BaseUCom (m + anc))
      = FormalRV.Framework.uc_eval
          (map_qubits (fun x => m + x) c : BaseUCom (m + anc)) *
          pad_u (m + anc) q U := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
      show pad_u (m + anc) q U *
            (FormalRV.Framework.uc_eval
                (map_qubits (fun x => m + x) c₂ : BaseUCom (m + anc)) *
              FormalRV.Framework.uc_eval
                (map_qubits (fun x => m + x) c₁ : BaseUCom (m + anc)))
            = (FormalRV.Framework.uc_eval
                (map_qubits (fun x => m + x) c₂ : BaseUCom (m + anc)) *
              FormalRV.Framework.uc_eval
                (map_qubits (fun x => m + x) c₁ : BaseUCom (m + anc))) *
              pad_u (m + anc) q U
      rw [← Matrix.mul_assoc, ih₂, Matrix.mul_assoc, ih₁, ← Matrix.mul_assoc]
  | app1 u n =>
      cases u with
      | R θ φ lam =>
        show pad_u (m + anc) q U * pad_u (m + anc) (m + n) (rotation θ φ lam) = _
        exact pad_u_disjoint_comm' (m + anc) q (m + n) U (rotation θ φ lam)
                (by omega)
  | app2 u a b =>
      cases u
      show pad_u (m + anc) q U * pad_ctrl (m + anc) (m + a) (m + b) σx = _
      exact pad_u_pad_ctrl_disjoint_comm (m + anc) q (m + a) (m + b) U σx
              (by omega) (by omega)
  | app3 u _ _ _ => cases u

/-! ## QPE-shifted cascade theorem -/

/-- **QPE-SHIFTED CASCADE THEOREM.** The full controlled-powers
phase-kickback identity, specialized to QPE's shift-lifted oracle
family `i ↦ map_qubits (fun x => m + x) (f i)`. All commutation,
freshness, and well-typedness hypotheses of the abstract cascade
theorem are discharged automatically using the three lemmas above;
the caller need only supply the per-oracle well-typedness and the
common eigenstate relation. -/
theorem uc_eval_controlled_powers_shifted_on_common_eigenstate
    {m anc : Nat} (hd : 0 < m + anc)
    (f : Nat → BaseUCom anc)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (ψ : Matrix (Fin (2^(m + anc))) (Fin 1) ℂ) (ζ : Nat → ℂ)
    (h_eig : ∀ i, i < m →
        FormalRV.Framework.uc_eval
          (map_qubits (fun x => m + x) (f i) : BaseUCom (m + anc)) * ψ
          = ζ i • ψ) :
    FormalRV.Framework.uc_eval (controlled_powers
        (fun i => (map_qubits (fun x => m + x) (f i) : BaseUCom (m + anc))) m) * ψ
      = @phase_projector_product (m + anc) ζ m * ψ := by
  let g : Nat → BaseUCom (m + anc) :=
    fun i => map_qubits (fun x => m + x) (f i)
  apply uc_eval_controlled_powers_on_common_eigenstate_recursive hd g ψ ζ m
  · intro i hi; omega
  · intro i hi; exact is_fresh_map_qubits_shift (f i) hi
  · intro i hi; exact wellTyped_map_qubits_shift (f i) (h_wt_all i hi)
  · intro i j hi _ U; exact uc_eval_map_qubits_shift_commutes_pad_u (f j) hi U
  · exact h_eig

/-! ## Pre-QFT QPE composition (conditional)

The next layer up is the pre-QFT composition: H on the control
register, followed by `controlled_powers`, on a common eigenstate.

This composition depends on two pieces of `pad_u`/`kron_vec` interaction
infrastructure that the framework currently lacks:

1. **`KronVecShiftHyp`** — the shifted oracle's action on `kron_vec χ ψ`
   factors through `ψ`: it acts as `f` on the data register and leaves
   the control register `χ` untouched.

2. **`NparHKronZerosUniformHyp`** — `npar_H m` on `kron_zeros m ⊗ᵥ ψ`
   produces the uniform-superposition state on the control register
   while leaving the data register `ψ` untouched.

Both reduce to the same fundamental `pad_u`-on-`kron_vec` interaction
lemma (flagged at `Shor.lean:4843-4845` as a known multi-file gap).
Once that infrastructure is in place, both hypotheses become provable
auxiliary lemmas; until then they are exposed as explicit hypotheses
on the conditional theorems below. -/

/-- **The shifted-oracle / kron-vec interaction hypothesis.**

`pad_u`/`pad_ctrl` on the data-register block `[m, m + anc)` should
act on a `kron_vec` state by leaving the control component `χ`
unchanged and applying the unshifted oracle to the data component `ψ`.

This abbreviation packages the statement so the conditional
theorems below can require it as an explicit hypothesis. Proving it
unconditionally (i.e., for every `f : BaseUCom anc`) requires the
`pad_u`-on-`kron_vec` interaction infrastructure (a known
multi-file gap in the framework). -/
abbrev KronVecShiftHyp (m anc : Nat) (f : FormalRV.Framework.BaseUCom anc)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) : Prop :=
  FormalRV.Framework.uc_eval
      (map_qubits (fun q => m + q) f : FormalRV.Framework.BaseUCom (m + anc))
    * kron_vec χ ψ
    = kron_vec χ (FormalRV.Framework.uc_eval f * ψ)

/-- **Conditional eigen-on-kron-control.** Given the kron-vec
interaction hypothesis and the data-register eigen-relation, the
combined `χ ⊗ᵥ ψ` is an eigenstate of the shifted oracle with the
same eigenvalue. The proof is one rewrite + a scalar pull-out
(`kron_vec_smul_right`). -/
theorem lifted_oracle_eigen_on_kron_control_conditional
    {m anc : Nat}
    (f : FormalRV.Framework.BaseUCom anc)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ)
    (ζ : ℂ)
    (h_eig : FormalRV.Framework.uc_eval f * ψ = ζ • ψ)
    (h_shift_kron : KronVecShiftHyp m anc f χ ψ) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => m + q) f : FormalRV.Framework.BaseUCom (m + anc))
        * kron_vec χ ψ
      = ζ • kron_vec χ ψ := by
  unfold KronVecShiftHyp at h_shift_kron
  rw [h_shift_kron, h_eig, kron_vec_smul_right]

/-- **The H-on-zeros / uniform-superposition hypothesis.** The
column of Hadamards `npar_H m` applied to `kron_vec (kron_zeros m) ψ`
produces the uniform superposition `(1/√2^m) · ∑_x |x⟩ ⊗ ψ` on
the control register, leaving the data register `ψ` untouched. -/
abbrev NparHKronZerosUniformHyp (m anc : Nat)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) : Prop :=
  FormalRV.Framework.uc_eval
      (npar_H m : FormalRV.Framework.BaseUCom (m + anc))
    * kron_vec (kron_zeros m) ψ
    = ((1 : ℂ) / Real.sqrt (2 ^ m)) •
        ∑ x : Fin (2^m),
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ

/-- **CONDITIONAL pre-QFT QPE composition on a common eigenstate.**

Composes `npar_H m` (Hadamard layer on control register) with the
shifted controlled-powers cascade. The eigenvalue carries to the
phase-projector-product form on the uniform-superposition state.

This is the pre-QFT half of QPE; combining it with `QFTinv k` on the
phase-projector-product form yields the `qpe_phase_state k θ ⊗ ψ`
that QPE measurement projects against.

The conditional version takes two explicit hypotheses for the missing
`pad_u`/`kron_vec` infrastructure:

- `h_npar_H : NparHKronZerosUniformHyp m anc ψ` — the H-on-zeros step;
- `h_shift_kron_eig_uniform` — the shifted-oracle eigen-relation on
  the uniform-superposition state. (The latter would follow from
  `h_eig_data` + a `KronVecShiftHyp` lemma for the uniform sum;
  exposed here as a single hypothesis for the conditional form.)

Once the `pad_u`-on-`kron_vec` infrastructure lands, both hypotheses
become provable and the conditional becomes unconditional. -/
theorem QPE_pre_QFT_on_eigenstate_conditional
    {m anc : Nat} (hmanc : 0 < m + anc)
    (f : Nat → FormalRV.Framework.BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) (ζ : Nat → ℂ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (h_shift_kron_eig_uniform : ∀ i, i < m →
      FormalRV.Framework.uc_eval
          (map_qubits (fun q => m + q) (f i) :
            FormalRV.Framework.BaseUCom (m + anc))
        * (((1 : ℂ) / Real.sqrt (2 ^ m)) •
            ∑ x : Fin (2^m),
              kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
        = ζ i • (((1 : ℂ) / Real.sqrt (2 ^ m)) •
            ∑ x : Fin (2^m),
              kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ))
    (h_npar_H : NparHKronZerosUniformHyp m anc ψ) :
    FormalRV.Framework.uc_eval (controlled_powers
        (fun i => (map_qubits (fun q => m + q) (f i) :
          FormalRV.Framework.BaseUCom (m + anc))) m)
      * (FormalRV.Framework.uc_eval
            (npar_H m : FormalRV.Framework.BaseUCom (m + anc))
          * kron_vec (kron_zeros m) ψ)
      = @phase_projector_product (m + anc) ζ m
        * (((1 : ℂ) / Real.sqrt (2 ^ m)) •
            ∑ x : Fin (2^m),
              kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ) := by
  unfold NparHKronZerosUniformHyp at h_npar_H
  rw [h_npar_H]
  exact uc_eval_controlled_powers_shifted_on_common_eigenstate hmanc f h_wt_all
    (((1 : ℂ) / Real.sqrt (2 ^ m)) •
      ∑ x : Fin (2^m),
        kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
    ζ h_shift_kron_eig_uniform

/-! ## Toward the unconditional pad_u-on-kron_vec interaction

The current obstacle to unconditional pre-QFT QPE: prove

    pad_u (m + anc) (m + n) M * kron_vec χ ψ
      = kron_vec χ (pad_u anc n M * ψ)

for arbitrary `χ : Matrix (Fin (2^m)) (Fin 1) ℂ` and
`ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ`. This is hard because:

- `pad_u` is defined via `Matrix.kronecker` + a 3-way `padEquiv` reindex
  splitting `Fin (2^(m+anc))` into `(Fin (2^(m+n)) × Fin 2) × Fin (2^(anc-n-1))`.
- `kron_vec` is defined via a 2-way `kronEquiv` reindex splitting
  `Fin (2^(m+anc))` into `Fin (2^m) × Fin (2^anc)`.
- The two reindexings are compatible but expressing the compatibility
  requires explicit index arithmetic.

The cleanest path forward leverages `Matrix.mul_kronecker_mul`
(`(A ⊗ₖ B) * (v ⊗ₖ w) = (A v) ⊗ₖ (B w)`):

1. Prove `pad_u (m + anc) (m + n) M = reindex_e (Iₙ (2^m) ⊗ₖ pad_u anc n M)`
   for some explicit equiv `e` — the "shifted-pad_u decomposition".
2. Prove `kron_vec χ ψ = reindex_e (χ ⊗ₖ ψ)` for the same `e`.
3. Apply `Matrix.mul_kronecker_mul` and the reindex identity.

Estimated scope: comparable to existing `pad_u_pad_u_disjoint_decomp`
chains in `UnitarySem.lean` (~200-500 LOC of mathlib Kronecker /
reindex work).

Single-deliverable seed proved here: the explicit-basis form of the
kron-of-basis identity, which feeds into the future entry-wise proof. -/

/-- **Kron of two basis vectors = basis of combined index.** The
elementary fact that `|x⟩ ⊗ |y⟩` (on `m + anc` qubits) is the standard
basis vector for the combined index `kron_vec_combine x y`. Used
downstream when the QPE proof reduces actions on `kron_vec` to actions
on individual basis states. -/
theorem kron_vec_basis_eq_basis_combine (a b : Nat) (x : Fin (2^a)) (y : Fin (2^b)) :
    kron_vec (FormalRV.Framework.basis_vector (2^a) x.val)
             (FormalRV.Framework.basis_vector (2^b) y.val)
      = FormalRV.Framework.basis_vector (2^(a+b)) (kron_vec_combine x y).val := by
  ext i col
  fin_cases col
  rw [kron_vec_apply,
      FormalRV.Framework.basis_vector_apply,
      FormalRV.Framework.basis_vector_apply,
      FormalRV.Framework.basis_vector_apply]
  by_cases hi : i = kron_vec_combine x y
  · rw [hi, kron_vec_high_combine, kron_vec_low_combine]
    simp
  · have hi_val : (i : Nat) ≠ (kron_vec_combine x y : Nat) := fun h => hi (Fin.ext h)
    rw [if_neg hi_val]
    by_cases hH : (kron_vec_high i : Nat) = (x : Nat)
    · by_cases hL : (kron_vec_low i : Nat) = (y : Nat)
      · exfalso
        apply hi
        apply kron_vec_high_low_inj
        · apply Fin.ext; rw [kron_vec_high_combine]; exact hH
        · apply Fin.ext; rw [kron_vec_low_combine]; exact hL
      · rw [if_neg hL]; ring
    · rw [if_neg hH]; ring

/-! ## Bridge: padEquiv on combined-kron index

The arithmetic identity at the core of `pad_u_shifted_kron_basis_factors`:
the `padEquiv (m+anc) (m+n)` decomposition of `kron_vec_combine x y`
factors through a `combine_kron(x, y_H)` outer index whenever `y` has
been pre-decomposed via `padEquiv anc n`.

This is the central .val identity. Used to align the `pad_u`-side
3-way splitting with the `kron_vec`-side 2-way splitting.

Proof: unfold padEquiv (chain of `finProdFinEquiv` + `Fin.castOrderIso`)
to expose the Nat-value formulas; reduce to `2^anc = 2^(anc-n-1) * 2 * 2^n`
via `pow_add` arithmetic; close with `ring`. -/
theorem padEquiv_combined_eq_kron_combine
    (m anc n : Nat) (hn : n < anc)
    (h_combined : m + n < m + anc)
    (h_size : m + anc - (m + n) - 1 = anc - n - 1)
    (x : Fin (2^m)) (yH : Fin (2^n)) (yM : Fin 2)
    (yL : Fin (2^(anc-n-1))) :
    (padEquiv (m + anc) (m + n) h_combined
        ((kron_vec_combine x yH, yM), Fin.cast (by rw [h_size]) yL)).val
      = (kron_vec_combine x (padEquiv anc n hn ((yH, yM), yL))).val := by
  unfold padEquiv kron_vec_combine
  show (yL.val + 2^(m+anc-(m+n)-1) * (yM.val + 2 * (x.val * 2^n + yH.val)))
        = x.val * 2^anc + (yL.val + 2^(anc-n-1) * (yM.val + 2 * yH.val))
  have h_size_pow : (2 : Nat) ^ (m+anc-(m+n)-1) = 2^(anc-n-1) := by
    have : m + anc - (m + n) - 1 = anc - n - 1 := by omega
    rw [this]
  rw [h_size_pow]
  have h_pow_anc : (2 : Nat) ^ anc = 2^(anc-n-1) * 2 * 2^n := by
    have h_sum : (anc - n - 1) + 1 + n = anc := by omega
    rw [show (2 : Nat) ^ (anc-n-1) * 2 * 2^n = 2 ^ ((anc-n-1) + 1 + n) from by
          rw [pow_add, pow_add]; ring]
    rw [h_sum]
  rw [h_pow_anc]
  ring

/-- **`pad_u` on `kron_vec` of basis vectors: factorization theorem.**

For the QPE shift convention (control register at qubits `[0, m)`,
data register at `[m, m + anc)`), `pad_u (m + anc) (m + n) M` applied
to a tensor of two basis vectors factors as `kron_vec` of the
control-side basis with the local `pad_u anc n M` action on the
data-side basis.

Proof outline:
1. Rewrite `kron_vec (basis_vector x) (basis_vector y)` as
   `basis_vector (kron_vec_combine x y)` via
   `kron_vec_basis_eq_basis_combine`.
2. After `ext r`, extract column entries using `mul_basis_vector_apply`.
3. Decompose `y` and `kron_vec_low r` via `padEquiv anc n`.
4. Apply the bridge `padEquiv_combined_eq_kron_combine` to express
   both `r` and the combined index in `padEquiv (m+anc) (m+n)` form.
5. Apply `pad_u_apply_reindex` to both LHS entry and RHS pad_u entry.
6. Case split (2x2x2 = 8 cases) on `kron_vec_high r = x`, `lrH = yH`,
   `lrL = yL`. Each case reduces to `combine_kron`-injectivity
   arithmetic + `simp`. -/
theorem pad_u_shifted_kron_basis_factors
    {m anc n : Nat} (hn : n < anc)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (x : Fin (2^m)) (y : Fin (2^anc)) :
    pad_u (m + anc) (m + n) M
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                   (FormalRV.Framework.basis_vector (2^anc) y.val)
      = kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                 (pad_u anc n M *
                   FormalRV.Framework.basis_vector (2^anc) y.val) := by
  have h_combined : m + n < m + anc := by omega
  have h_size : m + anc - (m + n) - 1 = anc - n - 1 := by omega
  rw [kron_vec_basis_eq_basis_combine]
  ext r col
  have hcol : col = (0 : Fin 1) := Subsingleton.elim _ _
  subst hcol
  rw [mul_basis_vector_apply _ _ (kron_vec_combine x y).isLt]
  rw [kron_vec_apply]
  rw [mul_basis_vector_apply _ _ y.isLt]
  obtain ⟨⟨⟨yH, yM⟩, yL⟩, hy⟩ :
      ∃ p, padEquiv anc n hn p = y :=
    ⟨(padEquiv anc n hn).symm y, (padEquiv anc n hn).apply_symm_apply y⟩
  obtain ⟨⟨⟨lrH, lrM⟩, lrL⟩, hlr⟩ :
      ∃ p, padEquiv anc n hn p = kron_vec_low r :=
    ⟨(padEquiv anc n hn).symm (kron_vec_low r),
     (padEquiv anc n hn).apply_symm_apply (kron_vec_low r)⟩
  have hxy_eq :
      (⟨(kron_vec_combine x y).val, (kron_vec_combine x y).isLt⟩ : Fin (2^(m+anc)))
        = padEquiv (m+anc) (m+n) h_combined
            ((kron_vec_combine x yH, yM), Fin.cast (by rw [h_size]) yL) := by
    apply Fin.ext
    rw [padEquiv_combined_eq_kron_combine m anc n hn h_combined h_size
        x yH yM yL, hy]
  rw [hxy_eq]
  have hy_full :
      (⟨y.val, y.isLt⟩ : Fin (2^anc)) = padEquiv anc n hn ((yH, yM), yL) := by
    apply Fin.ext; rw [hy]
  rw [hy_full]
  have h_high_r : FormalRV.Framework.basis_vector (2^m) (x.val) (kron_vec_high r) 0
      = if (kron_vec_high r).val = x.val then (1 : ℂ) else 0 := by
    rw [FormalRV.Framework.basis_vector_apply]
  rw [h_high_r]
  have hr_eq : r = padEquiv (m+anc) (m+n) h_combined
      ((kron_vec_combine (kron_vec_high r) lrH, lrM),
        Fin.cast (by rw [h_size]) lrL) := by
    apply Fin.ext
    rw [padEquiv_combined_eq_kron_combine m anc n hn h_combined h_size
        (kron_vec_high r) lrH lrM lrL, hlr, kron_vec_combine_high_low]
  conv_rhs => rw [← hlr]
  conv_lhs => rw [hr_eq]
  rw [pad_u_apply_reindex h_combined M _ _ lrM yM _ _]
  rw [pad_u_apply_reindex hn M lrH yH lrM yM lrL yL]
  -- Helper: combine_kron is injective on values; combine_kron_ne when high
  -- or low components differ.
  -- 8-way case split.
  by_cases h_hr : (kron_vec_high r).val = x.val
  all_goals by_cases h_lrH : lrH = yH
  all_goals by_cases h_lrL : lrL = yL
  -- Case 1 (TTT): all equal
  · have h_combine : kron_vec_combine (kron_vec_high r) lrH = kron_vec_combine x yH := by
      apply Fin.ext
      unfold kron_vec_combine
      simp [h_hr, Fin.val_inj.mpr h_lrH]
    have h_castL : (Fin.cast (by rw [h_size]) lrL : Fin (2^(m+anc-(m+n)-1)))
                  = Fin.cast (by rw [h_size]) yL := by
      apply Fin.ext; simp [h_lrL]
    rw [if_pos h_combine, if_pos h_castL, if_pos h_hr]
    simp [h_lrH, h_lrL]
  -- Case 2 (TTF): lrL ≠ yL
  · have h_combine : kron_vec_combine (kron_vec_high r) lrH = kron_vec_combine x yH := by
      apply Fin.ext
      unfold kron_vec_combine
      simp [h_hr, Fin.val_inj.mpr h_lrH]
    have h_castL_ne : (Fin.cast (by rw [h_size]) lrL : Fin (2^(m+anc-(m+n)-1)))
                  ≠ Fin.cast (by rw [h_size]) yL := by
      intro h; apply h_lrL
      exact (Fin.cast_inj _).mp h
    rw [if_pos h_combine, if_neg h_castL_ne, if_neg h_lrL]
    ring
  -- Case 3 (TFT): lrH ≠ yH
  · have h_combine_ne : kron_vec_combine (kron_vec_high r) lrH
                          ≠ kron_vec_combine x yH := by
      intro h
      apply h_lrH
      have h_val : ((kron_vec_combine (kron_vec_high r) lrH) : Nat) =
              ((kron_vec_combine x yH) : Nat) := Fin.val_inj.mpr h
      unfold kron_vec_combine at h_val
      simp at h_val
      have h_lrH_lt : lrH.val < 2^n := lrH.isLt
      have h_yH_lt : yH.val < 2^n := yH.isLt
      rw [h_hr] at h_val
      apply Fin.ext; omega
    simp [h_combine_ne, h_lrH]
  -- Case 4 (TFF): lrH ≠ yH (lrL also ≠ yL, but combine_ne suffices)
  · have h_combine_ne : kron_vec_combine (kron_vec_high r) lrH
                          ≠ kron_vec_combine x yH := by
      intro h
      apply h_lrH
      have h_val : ((kron_vec_combine (kron_vec_high r) lrH) : Nat) =
              ((kron_vec_combine x yH) : Nat) := Fin.val_inj.mpr h
      unfold kron_vec_combine at h_val
      simp at h_val
      have h_lrH_lt : lrH.val < 2^n := lrH.isLt
      have h_yH_lt : yH.val < 2^n := yH.isLt
      rw [h_hr] at h_val
      apply Fin.ext; omega
    simp [h_combine_ne, h_lrH]
  -- Case 5 (FTT): high r ≠ x
  · have h_combine_ne : kron_vec_combine (kron_vec_high r) lrH
                          ≠ kron_vec_combine x yH := by
      intro h
      apply h_hr
      have h_val : ((kron_vec_combine (kron_vec_high r) lrH) : Nat) =
              ((kron_vec_combine x yH) : Nat) := Fin.val_inj.mpr h
      unfold kron_vec_combine at h_val
      simp [Fin.val_inj.mpr h_lrH] at h_val
      have h_lrH_lt : lrH.val < 2^n := lrH.isLt
      omega
    simp [h_combine_ne, h_hr]
  -- Case 6 (FTF): high r ≠ x
  · have h_combine_ne : kron_vec_combine (kron_vec_high r) lrH
                          ≠ kron_vec_combine x yH := by
      intro h
      apply h_hr
      have h_val : ((kron_vec_combine (kron_vec_high r) lrH) : Nat) =
              ((kron_vec_combine x yH) : Nat) := Fin.val_inj.mpr h
      unfold kron_vec_combine at h_val
      simp [Fin.val_inj.mpr h_lrH] at h_val
      have h_lrH_lt : lrH.val < 2^n := lrH.isLt
      omega
    simp [h_combine_ne, h_hr]
  -- Case 7 (FFT): high r ≠ x — use kron_vec_high_combine
  · have h_combine_ne : kron_vec_combine (kron_vec_high r) lrH
                          ≠ kron_vec_combine x yH := by
      intro h
      apply h_hr
      have : kron_vec_high (kron_vec_combine (kron_vec_high r) lrH)
              = kron_vec_high (kron_vec_combine x yH) := by rw [h]
      rw [kron_vec_high_combine, kron_vec_high_combine] at this
      exact Fin.val_inj.mpr this
    simp [h_combine_ne, h_hr]
  -- Case 8 (FFF): high r ≠ x — use kron_vec_high_combine
  · have h_combine_ne : kron_vec_combine (kron_vec_high r) lrH
                          ≠ kron_vec_combine x yH := by
      intro h
      apply h_hr
      have : kron_vec_high (kron_vec_combine (kron_vec_high r) lrH)
              = kron_vec_high (kron_vec_combine x yH) := by rw [h]
      rw [kron_vec_high_combine, kron_vec_high_combine] at this
      exact Fin.val_inj.mpr this
    simp [h_combine_ne, h_hr]

/-! ## Vector decomposition + linearity extensions

To extend the basis-state factorization theorem to arbitrary data
vectors `ψ`, we decompose `ψ` as a sum of basis vectors and lift
factorization pointwise. -/

/-- **Vector decomposition into basis.** Any matrix column vector
equals the sum over basis vectors weighted by its entries. The
elementary linear algebra fact `ψ = ∑ y, ψ y 0 • basis_vector y`. -/
theorem vec_eq_sum_basis (n : Nat) (ψ : Matrix (Fin n) (Fin 1) ℂ) :
    ψ = ∑ y : Fin n, ψ y 0 • FormalRV.Framework.basis_vector n y.val := by
  ext i j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst hj
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [FormalRV.Framework.basis_vector_apply_eq _ _ _ _ rfl]; ring
  · intro j _ hj
    have hjv : i.val ≠ j.val := fun h => hj (Fin.ext h.symm)
    rw [FormalRV.Framework.basis_vector_apply, if_neg hjv]; ring
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- Linearity of `kron_vec` on the right over finite sums. -/
theorem kron_vec_sum_right {a b : Nat} (χ : Matrix (Fin (2^a)) (Fin 1) ℂ)
    {ι : Type*} [Fintype ι] (s : ι → Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec χ (∑ y, s y) = ∑ y, kron_vec χ (s y) := by
  ext i j
  rw [Matrix.sum_apply, kron_vec_apply, Matrix.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [kron_vec_apply]

/-- **Single-qubit `pad_u` on basis-control, arbitrary-data kron.**

The basis-state theorem `pad_u_shifted_kron_basis_factors` extends
by linearity over the basis decomposition of `ψ`:

    pad_u (m + anc) (m + n) M * kron_vec (basis_vector x) ψ
      = kron_vec (basis_vector x) (pad_u anc n M * ψ).

Proof: decompose `ψ` as `∑_y ψ(y, 0) • basis_y`, distribute via
`kron_vec_sum_right` and `Matrix.mul_sum`, then apply the basis
theorem pointwise. -/
theorem pad_u_shifted_kron_basis_control_vec {m anc n : Nat} (hn : n < anc)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (x : Fin (2^m)) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    pad_u (m + anc) (m + n) M
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                 (pad_u anc n M * ψ) := by
  conv_lhs => rw [vec_eq_sum_basis (2^anc) ψ]
  conv_rhs => rw [vec_eq_sum_basis (2^anc) ψ]
  rw [kron_vec_sum_right, Matrix.mul_sum, Matrix.mul_sum, kron_vec_sum_right]
  apply Finset.sum_congr rfl
  intro y _
  rw [kron_vec_smul_right (ψ y 0) _ _]
  rw [Matrix.mul_smul]
  rw [pad_u_shifted_kron_basis_factors hn M x y]
  rw [Matrix.mul_smul]
  rw [kron_vec_smul_right]

/-- **`pad_ctrl` (CNOT) on basis-control, arbitrary-data kron.**

The shifted CNOT factors through `kron_vec` for any data state.
Derivable from `pad_u_shifted_kron_basis_control_vec` via
`pad_ctrl`'s projector decomposition. -/
theorem pad_ctrl_shifted_kron_basis_control_vec {m anc a b : Nat}
    (ha : a < anc) (hb : b < anc)
    (x : Fin (2^m)) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    pad_ctrl (m + anc) (m + a) (m + b) σx
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                 (pad_ctrl anc a b σx * ψ) := by
  unfold pad_ctrl
  rw [Matrix.add_mul]
  rw [pad_u_shifted_kron_basis_control_vec ha proj0 x ψ]
  rw [Matrix.mul_assoc]
  rw [pad_u_shifted_kron_basis_control_vec hb σx x ψ]
  rw [pad_u_shifted_kron_basis_control_vec ha proj1 x _]
  rw [← kron_vec_add_right]
  rw [Matrix.add_mul, Matrix.mul_assoc]

/-- **CIRCUIT-LEVEL shifted factorization.** For any well-typed
`BaseUCom anc` circuit `c`, the shifted lift `map_qubits (· + m) c`
acts on `kron_vec (basis_vector x) ψ` by leaving the control-side
basis state intact and applying the local `uc_eval c` to the data
side.

Proof: structural induction on `c`. Each gate case uses the
corresponding shifted basis-control-vec lemma; `seq` chains via IH
and matrix associativity; `app3` is vacuous. -/
theorem uc_eval_map_qubits_shift_kron_basis_control_vec {m anc : Nat}
    (c : FormalRV.Framework.BaseUCom anc)
    (h_wt : UCom.WellTyped anc c)
    (x : Fin (2^m)) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => m + q) c : FormalRV.Framework.BaseUCom (m + anc))
      * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
    = kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
               (FormalRV.Framework.uc_eval c * ψ) := by
  induction c generalizing ψ with
  | seq c₁ c₂ ih₁ ih₂ =>
      cases h_wt with
      | seq h_wt1 h_wt2 =>
        show FormalRV.Framework.uc_eval
              (map_qubits (fun q => m + q) c₂ : FormalRV.Framework.BaseUCom (m + anc))
              * FormalRV.Framework.uc_eval
                  (map_qubits (fun q => m + q) c₁ : FormalRV.Framework.BaseUCom (m + anc))
              * kron_vec
                  (FormalRV.Framework.basis_vector (2^m) x.val) ψ
              = _
        rw [Matrix.mul_assoc]
        rw [ih₁ h_wt1 ψ]
        rw [ih₂ h_wt2 _]
        show kron_vec _ (FormalRV.Framework.uc_eval c₂ *
                          (FormalRV.Framework.uc_eval c₁ * ψ))
              = kron_vec _ (FormalRV.Framework.uc_eval c₂ *
                              FormalRV.Framework.uc_eval c₁ * ψ)
        rw [Matrix.mul_assoc]
  | app1 u n =>
      cases h_wt with
      | app1 hn =>
        cases u with
        | R θ φ lam =>
          exact pad_u_shifted_kron_basis_control_vec hn (rotation θ φ lam) x ψ
  | app2 u a b =>
      cases h_wt with
      | app2 ha hb hab =>
        cases u
        exact pad_ctrl_shifted_kron_basis_control_vec ha hb x ψ
  | app3 u _ _ _ => cases u

/-- **Unconditional lifted-oracle eigen on basis-control kron.**

Given a data-register eigenstate `ψ` of `f` with eigenvalue `ζ`,
the shifted oracle `map_qubits (· + m) f` has `kron_vec (basis_x) ψ`
as eigenstate with the same eigenvalue.

This is the unconditional version of
`lifted_oracle_eigen_on_kron_control_conditional` for basis-control
states. The proof is a 2-line composition of the circuit-level
shifted factorization theorem above with the scalar pull-out via
`kron_vec_smul_right`. -/
theorem lifted_oracle_eigen_on_kron_basis_control_vec {m anc : Nat}
    (f : FormalRV.Framework.BaseUCom anc)
    (x : Fin (2^m)) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) (ζ : ℂ)
    (h_wt : UCom.WellTyped anc f)
    (h_eig : FormalRV.Framework.uc_eval f * ψ = ζ • ψ) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => m + q) f : FormalRV.Framework.BaseUCom (m + anc))
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = ζ • kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  rw [uc_eval_map_qubits_shift_kron_basis_control_vec f h_wt x ψ]
  rw [h_eig, kron_vec_smul_right]

/-! ## Control-side bridge for `pad_u`

For control-register `pad_u` (qubit `n < m`), the `padEquiv (m+anc) n`
decomposition factors through `kron_vec_combine`:

    (padEquiv (m+anc) n ((xH, xM), Fin.cast (combine_kron xL y))).val
      = (kron_vec_combine (padEquiv m n ((xH, xM), xL)) y).val

This is the mirror of `padEquiv_combined_eq_kron_combine` (data-side
bridge) and the central arithmetic identity for any future
control-side basis-state theorem. Proof: unfold padEquiv +
kron_vec_combine, reduce to `2^(m+anc-n-1) = 2^(m-n-1) * 2^anc`, ring. -/
theorem padEquiv_control_eq_kron_combine (m anc n : Nat) (hn : n < m)
    (h_combined : n < m + anc)
    (h_size : m + anc - n - 1 = (m - n - 1) + anc)
    (xH : Fin (2^n)) (xM : Fin 2) (xL : Fin (2^(m-n-1)))
    (y : Fin (2^anc)) :
    (padEquiv (m + anc) n h_combined
        ((xH, xM), Fin.cast (by rw [h_size]) (kron_vec_combine xL y))).val
      = (kron_vec_combine (padEquiv m n hn ((xH, xM), xL)) y).val := by
  unfold padEquiv kron_vec_combine
  show (xL.val * 2^anc + y.val + 2^(m+anc-n-1) * (xM.val + 2 * xH.val))
        = (xL.val + 2^(m-n-1) * (xM.val + 2 * xH.val)) * 2^anc + y.val
  have h_pow : (2 : Nat)^(m+anc-n-1) = 2^(m-n-1) * 2^anc := by
    have hsum : (m-n-1) + anc = m+anc-n-1 := by omega
    rw [← pow_add, hsum]
  rw [h_pow]; ring

/-- **Control-side `pad_u` / `kron_vec` factorization (basis form).**

Mirror of `pad_u_shifted_kron_basis_factors` for control-register
gates. For `pad_u (m + anc) n M` with `n < m` (i.e., the qubit lies in
the control register), the action on a tensor of two basis vectors
factors through the local control-side `pad_u m n M`:

    pad_u (m + anc) n M * kron_vec (basis_x) (basis_y)
      = kron_vec (pad_u m n M * basis_x) (basis_y)

Proof: structurally identical to the data-side theorem, but uses
`padEquiv_control_eq_kron_combine` as the alignment bridge instead
of the data-side bridge, and decomposes `x` and `kron_vec_high r` via
`padEquiv m n` instead of `y` and `kron_vec_low r` via `padEquiv anc n`. -/
theorem pad_u_control_kron_basis_factors
    {m anc n : Nat} (hn : n < m)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (x : Fin (2^m)) (y : Fin (2^anc)) :
    pad_u (m + anc) n M
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                   (FormalRV.Framework.basis_vector (2^anc) y.val)
      = kron_vec (pad_u m n M * FormalRV.Framework.basis_vector (2^m) x.val)
                 (FormalRV.Framework.basis_vector (2^anc) y.val) := by
  have h_combined : n < m + anc := by omega
  have h_size : m + anc - n - 1 = (m - n - 1) + anc := by omega
  rw [kron_vec_basis_eq_basis_combine]
  ext r col
  have hcol : col = (0 : Fin 1) := Subsingleton.elim _ _
  subst hcol
  rw [mul_basis_vector_apply _ _ (kron_vec_combine x y).isLt]
  rw [kron_vec_apply]
  rw [mul_basis_vector_apply _ _ x.isLt]
  obtain ⟨⟨⟨xH, xM⟩, xL⟩, hx⟩ : ∃ p, padEquiv m n hn p = x :=
    ⟨(padEquiv m n hn).symm x, (padEquiv m n hn).apply_symm_apply x⟩
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hrh⟩ : ∃ p, padEquiv m n hn p = kron_vec_high r :=
    ⟨(padEquiv m n hn).symm (kron_vec_high r),
     (padEquiv m n hn).apply_symm_apply (kron_vec_high r)⟩
  have hxy_eq :
      (⟨(kron_vec_combine x y).val, (kron_vec_combine x y).isLt⟩ : Fin (2^(m+anc)))
        = padEquiv (m+anc) n h_combined
            ((xH, xM), Fin.cast (by rw [h_size]) (kron_vec_combine xL y)) := by
    apply Fin.ext
    rw [padEquiv_control_eq_kron_combine m anc n hn h_combined h_size
        xH xM xL y, hx]
  rw [hxy_eq]
  have hx_full :
      (⟨x.val, x.isLt⟩ : Fin (2^m)) = padEquiv m n hn ((xH, xM), xL) := by
    apply Fin.ext; rw [hx]
  rw [hx_full]
  have h_low_y : FormalRV.Framework.basis_vector (2^anc) (y.val) (kron_vec_low r) 0
      = if (kron_vec_low r).val = y.val then (1 : ℂ) else 0 := by
    rw [FormalRV.Framework.basis_vector_apply]
  rw [h_low_y]
  have hr_eq : r = padEquiv (m+anc) n h_combined
      ((rH, rM), Fin.cast (by rw [h_size]) (kron_vec_combine rL (kron_vec_low r))) := by
    apply Fin.ext
    rw [padEquiv_control_eq_kron_combine m anc n hn h_combined h_size
        rH rM rL (kron_vec_low r), hrh, kron_vec_combine_high_low]
  conv_rhs => rw [← hrh]
  conv_lhs => rw [hr_eq]
  rw [pad_u_apply_reindex h_combined M rH xH rM xM _ _]
  rw [pad_u_apply_reindex hn M rH xH rM xM rL xL]
  by_cases h_rH : rH = xH
  all_goals by_cases h_rL : rL = xL
  all_goals by_cases h_low : (kron_vec_low r).val = y.val
  -- Case 1 (TTT)
  · have h_combine_eq : kron_vec_combine rL (kron_vec_low r) =
                          kron_vec_combine xL y := by
      apply Fin.ext
      unfold kron_vec_combine
      simp [Fin.val_inj.mpr h_rL, h_low]
    have h_cast_eq : (Fin.cast (by rw [h_size]) (kron_vec_combine rL (kron_vec_low r)) :
                       Fin (2^(m+anc-n-1)))
                    = Fin.cast (by rw [h_size]) (kron_vec_combine xL y) := by
      apply Fin.ext; simp [h_combine_eq]
    rw [if_pos h_rH, if_pos h_cast_eq, if_pos h_rL, if_pos h_low]
    ring
  -- Case 2 (TTF)
  · have h_combine_ne : kron_vec_combine rL (kron_vec_low r) ≠
                          kron_vec_combine xL y := by
      intro h
      apply h_low
      have : kron_vec_low (kron_vec_combine rL (kron_vec_low r))
              = kron_vec_low (kron_vec_combine xL y) := by rw [h]
      rw [kron_vec_low_combine, kron_vec_low_combine] at this
      exact Fin.val_inj.mpr this
    have h_cast_ne : (Fin.cast (by rw [h_size]) (kron_vec_combine rL (kron_vec_low r)) :
                       Fin (2^(m+anc-n-1)))
                    ≠ Fin.cast (by rw [h_size]) (kron_vec_combine xL y) := by
      intro h; exact h_combine_ne ((Fin.cast_inj _).mp h)
    rw [if_pos h_rH, if_neg h_cast_ne, if_pos h_rL, if_neg h_low]
    ring
  -- Case 3 (TFT)
  · have h_combine_ne : kron_vec_combine rL (kron_vec_low r) ≠
                          kron_vec_combine xL y := by
      intro h
      apply h_rL
      have : kron_vec_high (kron_vec_combine rL (kron_vec_low r))
              = kron_vec_high (kron_vec_combine xL y) := by rw [h]
      rw [kron_vec_high_combine, kron_vec_high_combine] at this
      exact this
    have h_cast_ne : (Fin.cast (by rw [h_size]) (kron_vec_combine rL (kron_vec_low r)) :
                       Fin (2^(m+anc-n-1)))
                    ≠ Fin.cast (by rw [h_size]) (kron_vec_combine xL y) := by
      intro h; exact h_combine_ne ((Fin.cast_inj _).mp h)
    rw [if_pos h_rH, if_neg h_cast_ne, if_neg h_rL]
    ring
  -- Case 4 (TFF)
  · have h_combine_ne : kron_vec_combine rL (kron_vec_low r) ≠
                          kron_vec_combine xL y := by
      intro h
      apply h_rL
      have : kron_vec_high (kron_vec_combine rL (kron_vec_low r))
              = kron_vec_high (kron_vec_combine xL y) := by rw [h]
      rw [kron_vec_high_combine, kron_vec_high_combine] at this
      exact this
    have h_cast_ne : (Fin.cast (by rw [h_size]) (kron_vec_combine rL (kron_vec_low r)) :
                       Fin (2^(m+anc-n-1)))
                    ≠ Fin.cast (by rw [h_size]) (kron_vec_combine xL y) := by
      intro h; exact h_combine_ne ((Fin.cast_inj _).mp h)
    rw [if_pos h_rH, if_neg h_cast_ne, if_neg h_rL]
    ring
  -- Cases 5-8: rH ≠ xH, first factor is 0; simp closes
  all_goals (simp [h_rH])

/-- **Linearity extension: control-side `pad_u` on basis-control,
arbitrary-data `kron_vec`.** Same linearity-over-basis-decomposition
strategy as `pad_u_shifted_kron_basis_control_vec`. -/
theorem pad_u_control_kron_basis_control_vec {m anc n : Nat} (hn : n < m)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (x : Fin (2^m)) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    pad_u (m + anc) n M
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = kron_vec (pad_u m n M * FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  conv_lhs => rw [vec_eq_sum_basis (2^anc) ψ]
  conv_rhs => rw [vec_eq_sum_basis (2^anc) ψ]
  rw [kron_vec_sum_right, Matrix.mul_sum, kron_vec_sum_right]
  apply Finset.sum_congr rfl
  intro y _
  rw [kron_vec_smul_right (ψ y 0) _ _]
  rw [Matrix.mul_smul]
  rw [pad_u_control_kron_basis_factors hn M x y]
  rw [kron_vec_smul_right]

/-! ## Linearity on the control side + npar_H factorization -/

/-- Linearity of `kron_vec` on the LEFT over finite sums.
Companion to `kron_vec_sum_right`. -/
theorem kron_vec_sum_left {a b : Nat}
    {ι : Type*} [Fintype ι] (s : ι → Matrix (Fin (2^a)) (Fin 1) ℂ)
    (φ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec (∑ y, s y) φ = ∑ y, kron_vec (s y) φ := by
  ext i j
  rw [Matrix.sum_apply, kron_vec_apply, Matrix.sum_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [kron_vec_apply]

/-- **Arbitrary control-vector `pad_u` factorization.** Extends
`pad_u_control_kron_basis_control_vec` (basis-control) to arbitrary
`χ` via linearity over the basis decomposition. -/
theorem pad_u_control_kron_vec_factors {m anc n : Nat} (hn : n < m)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    pad_u (m + anc) n M * kron_vec χ ψ
      = kron_vec (pad_u m n M * χ) ψ := by
  conv_lhs => rw [vec_eq_sum_basis (2^m) χ]
  conv_rhs => rw [vec_eq_sum_basis (2^m) χ]
  rw [kron_vec_sum_left, Matrix.mul_sum, Matrix.mul_sum, kron_vec_sum_left]
  apply Finset.sum_congr rfl
  intro x _
  rw [kron_vec_smul_left (χ x 0) _ _]
  rw [Matrix.mul_smul]
  rw [pad_u_control_kron_basis_control_vec hn M x ψ]
  rw [Matrix.mul_smul]
  rw [kron_vec_smul_left]

/-- **App1 control-register wrapper.** Since `BaseUnitary 1` has only
the `R` constructor, this reduces to `pad_u_control_kron_vec_factors`. -/
theorem uc_eval_app1_control_kron_vec {m anc n : Nat} (hn : n < m)
    (u : FormalRV.Framework.BaseUnitary 1)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (UCom.app1 u n : FormalRV.Framework.BaseUCom (m + anc)) * kron_vec χ ψ
      = kron_vec
          (FormalRV.Framework.uc_eval (UCom.app1 u n : FormalRV.Framework.BaseUCom m) * χ) ψ := by
  cases u with
  | R θ φ lam =>
      show pad_u (m + anc) n (rotation θ φ lam) * kron_vec χ ψ = _
      exact pad_u_control_kron_vec_factors hn (rotation θ φ lam) χ ψ

/-- **Auxiliary: `npar_H k` factorization for any `k ≤ m`.** Induction
on `k` with `m` fixed. The H at qubit `k < m` lifts to
`pad_u (m+anc) k hMatrix`, which factors through `kron_vec` via
`pad_u_control_kron_vec_factors`. -/
theorem uc_eval_npar_H_kron_vec_aux (m anc : Nat) (hm : 0 < m)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    ∀ k, k ≤ m →
      FormalRV.Framework.uc_eval
          (npar_H k : FormalRV.Framework.BaseUCom (m + anc)) * kron_vec χ ψ
        = kron_vec
            (FormalRV.Framework.uc_eval (npar_H k : FormalRV.Framework.BaseUCom m) * χ) ψ := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [uc_eval_npar_H_zero_eq_one (by omega : 0 < m + anc)]
      rw [uc_eval_npar_H_zero_eq_one hm]
      rw [Matrix.one_mul, Matrix.one_mul]
  | succ k ih =>
      intro hk
      have hk_lt_m : k < m := by omega
      have hk_le_m : k ≤ m := Nat.le_of_lt hk_lt_m
      rw [uc_eval_npar_H_succ]
      rw [uc_eval_npar_H_succ]
      rw [Matrix.mul_assoc]
      rw [ih hk_le_m]
      rw [pad_u_control_kron_vec_factors hk_lt_m hMatrix _ ψ]
      rw [Matrix.mul_assoc]

/-- **`npar_H m` factors through `kron_vec`.** The full Hadamard column
on `m` control qubits acts on a `kron_vec χ ψ` by applying `npar_H m`
to the control component `χ` and leaving the data component `ψ`
unchanged. Specialization of the auxiliary lemma at `k = m`. -/
theorem uc_eval_npar_H_kron_vec (m anc : Nat) (hm : 0 < m)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (npar_H m : FormalRV.Framework.BaseUCom (m + anc)) * kron_vec χ ψ
      = kron_vec
          (FormalRV.Framework.uc_eval (npar_H m : FormalRV.Framework.BaseUCom m) * χ) ψ :=
  uc_eval_npar_H_kron_vec_aux m anc hm χ ψ m (le_refl m)

/-! ## H-on-zero base case + lower-level helpers -/

/-- For `dim = 1`, `pad_u 1 0 M = M`. The reindex layer collapses
because the high and low padding factors are `Iₙ(1)`. -/
theorem pad_u_one_zero_eq (M : Matrix (Fin 2) (Fin 2) ℂ) : pad_u 1 0 M = M := by
  ext i j
  obtain ⟨⟨⟨iH, iM⟩, iL⟩, hi⟩ : ∃ p, padEquiv 1 0 (by omega) p = i :=
    ⟨(padEquiv 1 0 (by omega)).symm i, (padEquiv 1 0 (by omega)).apply_symm_apply i⟩
  obtain ⟨⟨⟨jH, jM⟩, jL⟩, hj⟩ : ∃ p, padEquiv 1 0 (by omega) p = j :=
    ⟨(padEquiv 1 0 (by omega)).symm j, (padEquiv 1 0 (by omega)).apply_symm_apply j⟩
  rw [← hi, ← hj]
  rw [pad_u_apply_reindex (by omega : 0 < 1) M iH jH iM jM iL jL]
  have h_iH_zero : iH.val = 0 := by have := iH.isLt; omega
  have h_iL_zero : iL.val = 0 := by have := iL.isLt; omega
  have h_jH_zero : jH.val = 0 := by have := jH.isLt; omega
  have h_jL_zero : jL.val = 0 := by have := jL.isLt; omega
  have hiH : iH = jH := by apply Fin.ext; omega
  have hiL : iL = jL := by apply Fin.ext; omega
  rw [if_pos hiH, if_pos hiL, one_mul, mul_one]
  have h_padEq_i : (padEquiv 1 0 (by omega) ((iH, iM), iL)).val = iM.val := by
    unfold padEquiv finProdFinEquiv; simp
  have h_padEq_j : (padEquiv 1 0 (by omega) ((jH, jM), jL)).val = jM.val := by
    unfold padEquiv finProdFinEquiv; simp
  have h_eq_iM : (padEquiv 1 0 (by omega) ((iH, iM), iL) : Fin 2) = iM := by
    apply Fin.ext; rw [h_padEq_i]
  have h_eq_jM : (padEquiv 1 0 (by omega) ((jH, jM), jL) : Fin 2) = jM := by
    apply Fin.ext; rw [h_padEq_j]
  rw [h_eq_iM, h_eq_jM]

/-- `hMatrix * |0⟩ = (√2/2) · (|0⟩ + |1⟩)`. The fundamental Hadamard
identity on the standard zero state. Proved by 2-entry extensionality. -/
theorem hMatrix_mul_basis_zero :
    hMatrix * FormalRV.Framework.basis_vector 2 0
      = ((Real.sqrt 2 / 2 : ℂ)) •
        (FormalRV.Framework.basis_vector 2 0 +
          FormalRV.Framework.basis_vector 2 1) := by
  ext i j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst hj
  fin_cases i
  · simp [hMatrix, FormalRV.Framework.basis_vector_apply,
          Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply]
  · simp [hMatrix, FormalRV.Framework.basis_vector_apply,
          Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply]

/-- **Single-qubit H-on-zero**: `uc_eval (H 0 : BaseUCom 1) * kron_zeros 1
= (√2/2) · (basis_vector 2 0 + basis_vector 2 1)`. The base case of
the m-qubit `npar_H` induction. -/
theorem H_zero_eq_plus :
    FormalRV.Framework.uc_eval
        (FormalRV.Framework.BaseUCom.H 0 : FormalRV.Framework.BaseUCom 1) *
        FormalRV.Framework.kron_zeros 1
      = ((Real.sqrt 2 / 2 : ℂ)) •
        (FormalRV.Framework.basis_vector 2 0 +
          FormalRV.Framework.basis_vector 2 1) := by
  show pad_u 1 0 (FormalRV.Framework.rotation (Real.pi / 2) 0 Real.pi) *
        FormalRV.Framework.kron_zeros 1 = _
  rw [FormalRV.Framework.rotation_H]
  rw [pad_u_one_zero_eq]
  show hMatrix * FormalRV.Framework.basis_vector 2 0 = _
  exact hMatrix_mul_basis_zero

/-! ## H-on-zeros uniform superposition

The H-preparation theorem that establishes the uniform superposition
state at the entry of QPE. Built from the basic identities
`H_zero_eq_plus`, `uc_eval_npar_H_kron_vec`, and the structural
arithmetic helpers below. -/

/-- **Arbitrary-control + arbitrary-data data-side factorization.**
The full generality of `pad_u_shifted_kron_basis_control_vec` — by
linearity over the basis decomposition of χ. -/
theorem pad_u_shifted_kron_vec_factors {m anc n : Nat} (hn : n < anc)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    pad_u (m + anc) (m + n) M * kron_vec χ ψ
      = kron_vec χ (pad_u anc n M * ψ) := by
  conv_lhs => rw [vec_eq_sum_basis (2^m) χ]
  conv_rhs => rw [vec_eq_sum_basis (2^m) χ]
  rw [kron_vec_sum_left, Matrix.mul_sum, kron_vec_sum_left]
  apply Finset.sum_congr rfl
  intro x _
  rw [kron_vec_smul_left (χ x 0) _ _]
  rw [Matrix.mul_smul]
  rw [pad_u_shifted_kron_basis_control_vec hn M x ψ]
  rw [kron_vec_smul_left]

/-- **`kron_zeros (m+1) = kron_vec (kron_zeros m) (kron_zeros 1)`.**
Both sides reduce to `basis_vector (2^(m+1)) 0`. -/
theorem kron_zeros_succ (m : Nat) :
    FormalRV.Framework.kron_zeros (m + 1)
      = kron_vec (FormalRV.Framework.kron_zeros m)
                 (FormalRV.Framework.kron_zeros 1) := by
  unfold FormalRV.Framework.kron_zeros
  rw [kron_vec_basis_eq_basis_combine m 1
        (⟨0, Nat.two_pow_pos m⟩) (⟨0, Nat.two_pow_pos 1⟩)]
  congr 1

/-- **Scalar recurrence:** `(1/√2^m) · (√2/2) = 1/√2^(m+1)`. -/
theorem inv_sqrt_pow_two_succ (m : Nat) :
    ((1 : ℂ) / Real.sqrt (2^m : ℝ)) * ((Real.sqrt 2 / 2 : ℂ))
      = (1 : ℂ) / Real.sqrt (2^(m+1) : ℝ) := by
  have h_pos : (0 : ℝ) < (2^m : ℝ) := by positivity
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h_sqrt_mul : Real.sqrt (2^(m+1) : ℝ) = Real.sqrt (2^m : ℝ) * Real.sqrt 2 := by
    rw [pow_succ, Real.sqrt_mul h_pos.le]
  rw [h_sqrt_mul]
  push_cast
  have h_sqrt_2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr h2_pos
  have h_sqrt_m_pos : (0 : ℝ) < Real.sqrt (2^m : ℝ) := Real.sqrt_pos.mpr h_pos
  have h_sqrt_2_ne_C : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast h_sqrt_2_pos.ne'
  have h_sqrt_m_ne_C : (Real.sqrt (2^m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h_sqrt_m_pos.ne'
  field_simp
  exact_mod_cast Real.sq_sqrt (le_of_lt h2_pos)

/-- **Sum split over the last bit:** the uniform basis sum on `m+1`
qubits splits into pairs along the highest-bit / lowest-bit alternative. -/
theorem uniform_sum_succ_split (m : Nat) :
    ∑ z : Fin (2^(m+1)), FormalRV.Framework.basis_vector (2^(m+1)) z.val
      = ∑ x : Fin (2^m),
          (kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                    (FormalRV.Framework.basis_vector (2^1) 0)
            + kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                       (FormalRV.Framework.basis_vector (2^1) 1)) := by
  rw [← Fintype.sum_equiv (kronEquiv m 1)
      (fun p : Fin (2^m) × Fin (2^1) =>
        FormalRV.Framework.basis_vector (2^(m+1)) (kronEquiv m 1 p).val)
      (fun z => FormalRV.Framework.basis_vector (2^(m+1)) z.val)
      (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  have h0 : (kronEquiv m 1 (x, (⟨0, Nat.two_pow_pos 1⟩ : Fin (2^1)))).val
            = (kron_vec_combine x (⟨0, Nat.two_pow_pos 1⟩ : Fin (2^1))).val := rfl
  have h1 : (kronEquiv m 1 (x, (⟨1, by simp⟩ : Fin (2^1)))).val
            = (kron_vec_combine x (⟨1, by simp⟩ : Fin (2^1))).val := rfl
  show ∑ y : Fin 2,
        FormalRV.Framework.basis_vector (2^(m+1)) (kronEquiv m 1 (x, y)).val = _
  rw [Fin.sum_univ_two]
  rw [show ((0 : Fin 2) : Fin (2^1)) = ⟨0, Nat.two_pow_pos 1⟩ from rfl]
  rw [show ((1 : Fin 2) : Fin (2^1)) = ⟨1, by simp⟩ from rfl]
  rw [h0, h1]
  rw [← kron_vec_basis_eq_basis_combine m 1 x ⟨0, Nat.two_pow_pos 1⟩]
  rw [← kron_vec_basis_eq_basis_combine m 1 x ⟨1, by simp⟩]

/-- Single-qubit `m=1` scalar special case. -/
private theorem inv_sqrt_two_pow_one :
    ((1 : ℂ) / Real.sqrt ((2:ℝ)^1)) = (Real.sqrt 2 / 2 : ℂ) := by
  have h_pos : (0 : ℝ) < 2 := by norm_num
  have h_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h_pos.le
  have hs : Real.sqrt ((2:ℝ)^1) = Real.sqrt 2 := by norm_num
  rw [hs]
  have h_sqrt_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr h_pos).ne'
  field_simp
  exact_mod_cast h_sq.symm

/-- **PURE H-ON-ZEROS UNIFORM SUPERPOSITION.** The Hadamard column
on `m` qubits applied to the all-zeros state produces the uniform
superposition `(1/√2^m) · ∑_x |x⟩`. Requires `0 < m` because at
`m = 0` the framework's `pad_u 0 0` returns zero. Inducts on `m`:
- m=1 base: `H_zero_eq_plus` + scalar special case.
- m+1 step: split via `kron_zeros_succ`, IH for prefix m H-gates via
  `uc_eval_npar_H_kron_vec`, then the final H gate at position m via
  `pad_u_shifted_kron_vec_factors` + `pad_u_one_zero_eq` +
  `hMatrix_mul_basis_zero`; reassemble with kron-vec linearity and
  `uniform_sum_succ_split`. -/
theorem npar_H_kron_zeros_pure_eq_uniform_sum :
    ∀ (m : Nat), 0 < m →
      FormalRV.Framework.uc_eval
          (npar_H m : FormalRV.Framework.BaseUCom m) *
          FormalRV.Framework.kron_zeros m
        = ((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
          ∑ x : Fin (2^m), FormalRV.Framework.basis_vector (2^m) x.val := by
  intro m hm
  induction m with
  | zero => omega
  | succ k ih =>
      by_cases hk : k = 0
      · subst hk
        rw [show (npar_H 1 : FormalRV.Framework.BaseUCom 1) =
              UCom.seq (npar_H 0) (FormalRV.Framework.BaseUCom.H 0) from rfl]
        show FormalRV.Framework.uc_eval _ * FormalRV.Framework.uc_eval _ *
              FormalRV.Framework.kron_zeros 1 = _
        rw [uc_eval_npar_H_zero_eq_one (by omega : 0 < 1)]
        rw [Matrix.mul_one]
        rw [H_zero_eq_plus]
        rw [inv_sqrt_two_pow_one]
        congr 1
        show FormalRV.Framework.basis_vector 2 0 +
              FormalRV.Framework.basis_vector 2 1
            = ∑ x : Fin 2, FormalRV.Framework.basis_vector 2 x.val
        rw [Fin.sum_univ_two]
        rfl
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
        have ih_app := ih hk_pos
        rw [uc_eval_npar_H_succ]
        rw [kron_zeros_succ]
        rw [Matrix.mul_assoc]
        rw [uc_eval_npar_H_kron_vec k 1 hk_pos (FormalRV.Framework.kron_zeros k)
            (FormalRV.Framework.kron_zeros 1)]
        rw [ih_app]
        rw [show pad_u (k + 1) k hMatrix = pad_u (k + 1) (k + 0) hMatrix from by rfl]
        rw [pad_u_shifted_kron_vec_factors (by omega : 0 < 1) hMatrix _ _]
        rw [pad_u_one_zero_eq]
        rw [show (FormalRV.Framework.kron_zeros 1 : Matrix (Fin 2) (Fin 1) ℂ)
              = FormalRV.Framework.basis_vector 2 0 from rfl]
        rw [hMatrix_mul_basis_zero]
        rw [kron_vec_smul_left, kron_vec_smul_right]
        rw [smul_smul]
        rw [inv_sqrt_pow_two_succ k]
        congr 1
        rw [uniform_sum_succ_split k]
        rw [kron_vec_add_right]
        rw [kron_vec_sum_left, kron_vec_sum_left]
        rw [← Finset.sum_add_distrib]
        rfl

/-- **TENSORED H-ON-ZEROS UNIFORM SUPERPOSITION.** The H column on
`m` control qubits applied to `kron_vec (kron_zeros m) ψ` produces
the uniform-superposition state on the control register tensored with
the unchanged data state `ψ`. Combines the pure theorem with
`uc_eval_npar_H_kron_vec` (the m-qubit H factorization across kron). -/
theorem npar_H_kron_zeros_eq_uniform_sum {m anc : Nat} (hm : 0 < m)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval (npar_H m : FormalRV.Framework.BaseUCom (m + anc))
        * kron_vec (FormalRV.Framework.kron_zeros m) ψ
      = ((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
          ∑ x : Fin (2^m),
            kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  rw [uc_eval_npar_H_kron_vec m anc hm (FormalRV.Framework.kron_zeros m) ψ]
  rw [npar_H_kron_zeros_pure_eq_uniform_sum m hm]
  rw [kron_vec_smul_left]
  rw [kron_vec_sum_left]

/-! ## Unconditional pre-QFT QPE eigenstate theorem

The cap of the pre-QFT half of QPE. With the H-preparation and
shifted-cascade infrastructure now in place, the conditional pre-QFT
theorem from earlier sessions becomes fully unconditional. -/

/-- **Shifted oracle eigen on the H-prepared uniform-superposition
state.** For each oracle `f` with data-register eigenstate `ψ` of
eigenvalue `ζ`, the lifted (shifted) oracle has the H-prepared
uniform sum `(1/√2^m) · ∑_x |x⟩ ⊗ ψ` as an eigenstate with the
same eigenvalue. Proved by distributing the matrix-vector
product over the scalar and the sum, applying
`lifted_oracle_eigen_on_kron_basis_control_vec` pointwise, then
reassembling via `smul_comm`. -/
theorem shifted_oracle_eigen_on_uniform_control_sum
    {m anc : Nat}
    (f : FormalRV.Framework.BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ)
    (ζ : ℂ)
    (h_wt : UCom.WellTyped anc f)
    (h_eig_data : FormalRV.Framework.uc_eval f * ψ = ζ • ψ) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => m + q) f : FormalRV.Framework.BaseUCom (m + anc))
      *
    (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
      ∑ x : Fin (2^m),
        kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
    =
    ζ •
    (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
      ∑ x : Fin (2^m),
        kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ) := by
  rw [Matrix.mul_smul]
  rw [Matrix.mul_sum]
  rw [show ∑ x : Fin (2^m),
        FormalRV.Framework.uc_eval
            (map_qubits (fun q => m + q) f :
              FormalRV.Framework.BaseUCom (m + anc))
          * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
        = ∑ x : Fin (2^m),
            ζ • kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ from by
    apply Finset.sum_congr rfl
    intro x _
    exact lifted_oracle_eigen_on_kron_basis_control_vec f x ψ ζ h_wt h_eig_data]
  rw [← Finset.smul_sum]
  rw [smul_comm]

/-- **UNCONDITIONAL PRE-QFT QPE EIGENSTATE THEOREM.**

The full pre-QFT QPE composition on a data-register eigenstate `ψ`:
applying `npar_H m` then `controlled_powers` to `|0^m⟩ ⊗ ψ` produces
the phase-projector-product form acting on the uniform-superposition
state `(1/√2^m) · ∑_x |x⟩ ⊗ ψ`.

Composition of:
1. `npar_H_kron_zeros_eq_uniform_sum` — H prepares the uniform sum.
2. `shifted_oracle_eigen_on_uniform_control_sum` — establishes the
   common-eigenstate hypothesis for each lifted oracle on the
   uniform sum.
3. `uc_eval_controlled_powers_shifted_on_common_eigenstate` —
   the QPE-shifted cascade theorem, which now applies because (2)
   discharges its eigen hypothesis.

This is the cap of the pre-QFT half of QPE. The conditional
theorem `QPE_pre_QFT_on_eigenstate_conditional` from earlier
sessions is now subsumed by this unconditional version. -/
theorem QPE_pre_QFT_on_eigenstate
    {m anc : Nat} (hmanc : 0 < m + anc) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) (ζ : Nat → ℂ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (h_eig_data : ∀ i, i < m → FormalRV.Framework.uc_eval (f i) * ψ = ζ i • ψ) :
    FormalRV.Framework.uc_eval (controlled_powers
        (fun i => (map_qubits (fun q => m + q) (f i) :
          FormalRV.Framework.BaseUCom (m + anc))) m)
      * (FormalRV.Framework.uc_eval
            (npar_H m : FormalRV.Framework.BaseUCom (m + anc))
          * kron_vec (FormalRV.Framework.kron_zeros m) ψ)
    = @phase_projector_product (m + anc) ζ m
        * (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
            ∑ x : Fin (2^m),
              kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ) := by
  rw [npar_H_kron_zeros_eq_uniform_sum hm ψ]
  apply uc_eval_controlled_powers_shifted_on_common_eigenstate hmanc f h_wt_all _ ζ
  intro i hi
  exact shifted_oracle_eigen_on_uniform_control_sum (f i) ψ (ζ i)
        (h_wt_all i hi) (h_eig_data i hi)

/-! ## Explicit phase-weighted form of `phase_projector_product`

Converts the abstract `phase_projector_product ζ m` matrix into an
explicit phase-weighted sum over basis-control states. This is the
state shape that QFTinv will consume in the next pass. -/

/-- **Control bit at position `i`.** Boolean indicator of whether the
`i`-th qubit of `x : Fin (2^m)` (viewed via the framework's `padEquiv`
decomposition) is 1. Defined via `padEquiv m i hi` so it aligns with
`pad_u_proj{0,1}_on_basis_vector_{zero,one}`. -/
noncomputable def controlBit (m i : Nat) (hi : i < m) (x : Fin (2^m)) : Bool :=
  (((padEquiv m i hi).symm x).1.2 : Fin 2) = 1

/-- **Control bit ↔ binary digit.** The `controlBit m i hi x` Boolean is
true exactly when the `(m-i-1)`-th bit of `x.val` is set; this is the
MSB-first convention coming from `padEquiv`. -/
theorem controlBit_eq_digit (m i : Nat) (hi : i < m) (x : Fin (2^m)) :
    controlBit m i hi x = ((x.val / 2^(m-i-1)) % 2 = 1) := by
  unfold controlBit
  obtain ⟨⟨⟨xH, xM⟩, xL⟩, hx⟩ : ∃ p, padEquiv m i hi p = x :=
    ⟨(padEquiv m i hi).symm x, (padEquiv m i hi).apply_symm_apply x⟩
  rw [← hx]
  rw [Equiv.symm_apply_apply]
  have h_padEqv : (padEquiv m i hi ((xH, xM), xL)).val
                = xL.val + 2^(m-i-1) * (xM.val + 2 * xH.val) := by
    unfold padEquiv finProdFinEquiv
    simp
  rw [h_padEqv]
  have hxL : xL.val < 2^(m-i-1) := xL.isLt
  have hxM : xM.val < 2 := xM.isLt
  have h_div : (xL.val + 2^(m-i-1) * (xM.val + 2 * xH.val)) / 2^(m-i-1)
              = xM.val + 2 * xH.val := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos (m-i-1))]
    rw [Nat.div_eq_of_lt hxL]
    omega
  rw [h_div]
  have h_mod : (xM.val + 2 * xH.val) % 2 = xM.val := by
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hxM
  rw [h_mod]
  simp [Fin.ext_iff]

/-- **Numeric form of `controlBit`.** Returns the actual `Nat` digit
(0 or 1) of `x` at position `i` under the MSB-first convention. -/
noncomputable def controlBitNat (m i : Nat) (hi : i < m) (x : Fin (2^m)) : Nat :=
  if controlBit m i hi x then 1 else 0

/-- **Numeric `controlBit` equals the binary digit.** -/
theorem controlBitNat_eq_digit (m i : Nat) (hi : i < m) (x : Fin (2^m)) :
    controlBitNat m i hi x = (x.val / 2^(m-i-1)) % 2 := by
  unfold controlBitNat
  have h_eq := controlBit_eq_digit m i hi x
  by_cases h : controlBit m i hi x
  · rw [if_pos h]
    rw [h_eq] at h
    omega
  · rw [if_neg h]
    rw [h_eq] at h
    have h2 : (x.val / 2^(m-i-1)) % 2 < 2 := Nat.mod_lt _ (by omega)
    omega

/-- **Recursive phase prefix.** The scalar accumulated by applying the
first `k` phase projectors to the basis-control state `|x⟩`. Matches
the order of `phase_projector_product`. -/
noncomputable def phase_prefix (ζ : Nat → ℂ) (m : Nat) (x : Fin (2^m)) :
    Nat → ℂ
  | 0 => 1
  | k+1 =>
    (if h : k < m then
       (if controlBit m k h x then ζ k else 1)
     else 1) * phase_prefix ζ m x k

/-- Unfolding equation for `phase_prefix` at the successor case when
`k < m`. -/
theorem phase_prefix_succ {ζ : Nat → ℂ} {m : Nat} (x : Fin (2^m)) (k : Nat)
    (hk : k < m) :
    phase_prefix ζ m x (k+1) =
      (if controlBit m k hk x then ζ k else 1) * phase_prefix ζ m x k := by
  show (if h : k < m then if controlBit m k h x then ζ k else 1 else 1)
        * phase_prefix ζ m x k = _
  rw [dif_pos hk]

/-- **Single phase projector on basis-control kron.** The phase
projector `P0_i + ζ_i · P1_i` lifted to the combined `(m + anc)`-qubit
register acts on `kron_vec (basis_vector x) ψ` by leaving the data
register `ψ` unchanged and multiplying by `ζ_i` (when bit `i` of `x`
is 1) or `1` (when it is 0). -/
theorem phase_projector_on_kron_basis
    {m anc i : Nat} (hi : i < m)
    (ζi : ℂ)
    (x : Fin (2^m))
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    @phase_projector (m + anc) i ζi
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = (if controlBit m i hi x then ζi else 1) •
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  unfold phase_projector
  rw [Matrix.add_mul]
  rw [Matrix.smul_mul ζi (pad_u (m+anc) i proj1)
        (kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)]
  rw [pad_u_control_kron_vec_factors hi proj0 _ ψ]
  rw [pad_u_control_kron_vec_factors hi proj1 _ ψ]
  obtain ⟨⟨⟨xH, xM⟩, xL⟩, hx⟩ : ∃ p, padEquiv m i hi p = x :=
    ⟨(padEquiv m i hi).symm x, (padEquiv m i hi).apply_symm_apply x⟩
  subst hx
  rcases Fin.exists_fin_two.mp ⟨xM, rfl⟩ with rfl | rfl
  · rw [pad_u_proj0_on_basis_vector_zero hi xH xL]
    rw [pad_u_proj1_on_basis_vector_zero hi xH xL]
    have h_ctrl : controlBit m i hi (padEquiv m i hi ((xH, 0), xL)) = false := by
      unfold controlBit; rw [Equiv.symm_apply_apply]; simp
    rw [h_ctrl]
    rw [show kron_vec (0 : Matrix (Fin (2^m)) (Fin 1) ℂ) ψ = 0 from
        kron_vec_zero_left ψ]
    rw [smul_zero, add_zero]
    simp
  · rw [pad_u_proj0_on_basis_vector_one hi xH xL]
    rw [pad_u_proj1_on_basis_vector_one hi xH xL]
    have h_ctrl : controlBit m i hi (padEquiv m i hi ((xH, 1), xL)) = true := by
      unfold controlBit; rw [Equiv.symm_apply_apply]; simp
    rw [h_ctrl]
    rw [show kron_vec (0 : Matrix (Fin (2^m)) (Fin 1) ℂ) ψ = 0 from
        kron_vec_zero_left ψ]
    rw [zero_add]
    simp

/-- **Phase-projector-product prefix on basis-control kron.** Induction
on the inner index `k` (with `m` fixed): the prefix of `k` phase
projectors applied to `kron_vec (basis_vector x) ψ` yields the
`phase_prefix ζ m x k` scalar acting on the same kron state. -/
theorem phase_projector_product_prefix_on_kron_basis
    {m anc : Nat}
    (ζ : Nat → ℂ)
    (x : Fin (2^m))
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    ∀ k, k ≤ m →
      @phase_projector_product (m + anc) ζ k
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = phase_prefix ζ m x k •
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  intro k
  induction k with
  | zero =>
      intro _
      show (1 : Matrix (Fin (2^(m+anc))) (Fin (2^(m+anc))) ℂ) *
            kron_vec _ ψ = _
      rw [Matrix.one_mul]
      show kron_vec _ _ = (1 : ℂ) • _
      rw [one_smul]
  | succ k ih =>
      intro hk
      have hk_lt_m : k < m := hk
      have hk_le_m : k ≤ m := Nat.le_of_lt hk_lt_m
      show phase_projector k (ζ k) *
            @phase_projector_product (m + anc) ζ k *
            kron_vec _ _ = _
      rw [Matrix.mul_assoc]
      rw [ih hk_le_m]
      rw [Matrix.mul_smul]
      rw [phase_projector_on_kron_basis hk_lt_m (ζ k) x ψ]
      rw [smul_smul]
      rw [phase_prefix_succ x k hk_lt_m]
      ring_nf

/-- **Full phase-projector product on basis-control kron**: specialization
of the prefix theorem at `k = m`. -/
theorem phase_projector_product_on_kron_basis
    {m anc : Nat}
    (ζ : Nat → ℂ)
    (x : Fin (2^m))
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    @phase_projector_product (m + anc) ζ m
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = phase_prefix ζ m x m •
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ :=
  phase_projector_product_prefix_on_kron_basis ζ x ψ m (le_refl m)

/-- **PHASE-WEIGHTED FORM OF THE UNIFORM CONTROL SUM.** Applying the
phase-projector product to the H-prepared uniform superposition yields
the phase-weighted sum over basis-control states. This is the state
shape that QFTinv will consume in the next pass.

Proof: `Matrix.mul_smul` pulls the prefactor through, `Matrix.mul_sum`
distributes over the sum, then `phase_projector_product_on_kron_basis`
gives the per-term phase weight. -/
theorem phase_projector_product_on_uniform_control_sum
    {m anc : Nat}
    (ζ : Nat → ℂ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    @phase_projector_product (m + anc) ζ m
      * (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
          ∑ x : Fin (2^m),
            kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
    = ((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
        ∑ x : Fin (2^m),
          phase_prefix ζ m x m •
            kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  rw [Matrix.mul_smul]
  rw [Matrix.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact phase_projector_product_on_kron_basis ζ x ψ

/-- **LSB-first binary expansion.** Any `n < 2^m` is the sum of its
binary digits times the corresponding powers of two, with index `i`
weighted by `2^i`. -/
lemma binary_expansion_lsb (m n : Nat) (hn : n < 2^m) :
    n = ∑ i ∈ Finset.range m, ((n / 2^i) % 2) * 2^i := by
  induction m generalizing n with
  | zero => simp at hn; simp [hn]
  | succ k ih =>
      rw [Finset.sum_range_succ']
      have h_half : n/2 < 2^k := by
        have : 2^(k+1) = 2 * 2^k := by ring
        rw [this] at hn; omega
      have h_rec := ih (n/2) h_half
      simp only [pow_zero, Nat.div_one, pow_succ]
      have h_sum_eq : (∑ i ∈ Finset.range k, n / (2^i * 2) % 2 * (2^i * 2)) =
             2 * ∑ i ∈ Finset.range k, (n/2) / 2^i % 2 * 2^i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        have hki : n / (2^i * 2) = n/2 / 2^i := by
          rw [mul_comm, ← Nat.div_div_eq_div_mul]
        rw [hki]; ring
      rw [h_sum_eq, ← h_rec]
      omega

/-- **MSB-first binary expansion.** Same as `binary_expansion_lsb`
but reindexed so the `i`-th term is weighted by `2^(m-i-1)`, i.e.
the most-significant bit comes first (matching `padEquiv`'s
MSB-first decomposition). -/
lemma binary_expansion_msb (m n : Nat) (hn : n < 2^m) :
    n = ∑ i ∈ Finset.range m, ((n / 2^(m-i-1)) % 2) * 2^(m-i-1) := by
  conv_lhs => rw [binary_expansion_lsb m n hn]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have h_eq : m - 1 - i = m - i - 1 := by omega
  rw [h_eq]

/-- **Weighted control index.** The integer reconstructed from the
control bits of `x` under the MSB-first weighting. -/
noncomputable def controlWeightedIndex (m : Nat) (x : Fin (2^m)) : Nat :=
  ∑ i ∈ Finset.range m,
    (if h : i < m then controlBitNat m i h x else 0) * 2^(m-i-1)

/-- **Weighted control index equals `x.val`.** The phase-kickback
"weighted index" is exactly the underlying natural number — the
abstract bit-by-bit accumulation reassembles the binary expansion. -/
theorem controlWeightedIndex_eq_val (m : Nat) (x : Fin (2^m)) :
    controlWeightedIndex m x = x.val := by
  unfold controlWeightedIndex
  rw [binary_expansion_msb m x.val x.isLt]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [dif_pos hi]
  rw [controlBitNat_eq_digit m i hi x]

/-! ### Bridge from `phase_prefix` to the standard QPE phase

Specialize the abstract phase-prefix scalar to the QPE-eigenstate setting:
when the per-qubit eigenvalue at position `i` is `exp(2πi · 2^(m-i-1) · θ)`
(MSB-first weight, matching `padEquiv`'s middle-slot convention),
the accumulated phase factor collapses to `exp(2πi · x.val · θ)`. -/

/-- **QPE eigenvalue at qubit `i`.** The eigenvalue that the `i`-th
controlled-power gadget would impart on a phase-`θ` eigenstate, under
the MSB-first weighting `2^(m-i-1)`. -/
noncomputable def qpeEigenvalue (m i : Nat) (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (2^(m-i-1) : ℂ) * (θ : ℂ))

/-- **Partial weighted index.** Sum of `controlBitNat · 2^(m-i-1)` over
the first `k` qubits. At `k = m` this equals `controlWeightedIndex` and
hence `x.val`. -/
noncomputable def partialWeightedIndex (m k : Nat) (x : Fin (2^m)) : Nat :=
  ∑ i ∈ Finset.range k,
    (if h : i < m then controlBitNat m i h x else 0) * 2^(m-i-1)

/-- At `k = m`, the partial weighted index recovers `x.val`. -/
theorem partialWeightedIndex_at_m (m : Nat) (x : Fin (2^m)) :
    partialWeightedIndex m m x = x.val := by
  unfold partialWeightedIndex
  show (∑ i ∈ Finset.range m,
    (if h : i < m then controlBitNat m i h x else 0) * 2^(m-i-1)) = x.val
  exact controlWeightedIndex_eq_val m x

/-- Successor unfolding for the partial weighted index. -/
theorem partialWeightedIndex_succ (m k : Nat) (hk : k < m) (x : Fin (2^m)) :
    partialWeightedIndex m (k+1) x
      = partialWeightedIndex m k x
        + controlBitNat m k hk x * 2^(m-k-1) := by
  unfold partialWeightedIndex
  rw [Finset.sum_range_succ]
  congr 1
  rw [dif_pos hk]

/-- **Phase-prefix on QPE eigenvalues equals exp of weighted partial index.**
The accumulating phase factor for the QPE-specific eigenvalues collapses
to a single complex exponential whose argument is `2πi · θ · (partial sum)`. -/
theorem phase_prefix_qpe_eq_exp_partial (m : Nat) (θ : ℝ) (x : Fin (2^m)) :
    ∀ k, k ≤ m →
      phase_prefix (qpeEigenvalue m · θ) m x k
        = Complex.exp (2 * Real.pi * Complex.I *
            (partialWeightedIndex m k x : ℂ) * (θ : ℂ)) := by
  intro k
  induction k with
  | zero =>
      intro _
      unfold phase_prefix partialWeightedIndex
      simp
  | succ k ih =>
      intro hk
      have hk_lt_m : k < m := hk
      have hk_le_m : k ≤ m := Nat.le_of_lt hk_lt_m
      rw [phase_prefix_succ x k hk_lt_m]
      rw [ih hk_le_m]
      rw [partialWeightedIndex_succ m k hk_lt_m x]
      by_cases h : controlBit m k hk_lt_m x
      · rw [if_pos h]
        unfold qpeEigenvalue controlBitNat
        rw [if_pos h]
        push_cast
        rw [← Complex.exp_add]
        congr 1
        ring
      · rw [if_neg h]
        unfold controlBitNat
        rw [if_neg h]
        simp

/-- **Phase-prefix at full length equals `exp(2πi · x.val · θ)`.**
Combines `phase_prefix_qpe_eq_exp_partial` at `k = m` with
`partialWeightedIndex_at_m`. This is the bridge from the abstract
phase-projector cascade to the standard QPE phase-weighted form. -/
theorem phase_prefix_qpe_eq_exp_val (m : Nat) (θ : ℝ) (x : Fin (2^m)) :
    phase_prefix (qpeEigenvalue m · θ) m x m
      = Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) := by
  rw [phase_prefix_qpe_eq_exp_partial m θ x m (le_refl m)]
  rw [partialWeightedIndex_at_m m x]

/-! ### Explicit Fourier-form pre-QFT QPE theorem

Bundles the previous infrastructure into a single statement: the pre-QFT
half of QPE on a phase-`θ` eigenstate produces the standard QPE
phase-weighted superposition `(1/√2^m) · ∑_x exp(2πi · x · θ) |x⟩ ⊗ |ψ⟩`. -/

/-- **Pre-QFT QPE eigenstate result in explicit Fourier form.**

Given a data-register `ψ` such that each oracle `f i` (`i < m`) acts on
`ψ` as the QPE eigenvalue `exp(2πi · 2^(m-i-1) · θ)` (MSB-first
weighting), the composition `H^⊗m ; controlled_powers (shifted f) m`
applied to `|0^m⟩ ⊗ |ψ⟩` produces the phase-weighted Fourier
superposition `(1/√2^m) · ∑_x exp(2πi · x · θ) · |x⟩ ⊗ |ψ⟩`.

This is the state shape that a *real* `QFTinv` would consume to produce
`qpe_phase_state m θ ⊗ ψ`. The current `QFTinv` in
`Framework/QPE.lean` is a stub (see `QFTinv_is_stub` below); closing
`QPE_MMI_correct` further requires either implementing the real QFTinv
circuit or porting a QFT semantic axiom. -/
theorem QPE_pre_QFT_on_eigenstate_fourier_form
    {m anc : Nat} (hmanc : 0 < m + anc) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ)
    (θ : ℝ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (h_eig_data : ∀ i, i < m →
      FormalRV.Framework.uc_eval (f i) * ψ =
        qpeEigenvalue m i θ • ψ) :
    FormalRV.Framework.uc_eval (controlled_powers
        (fun i => (map_qubits (fun q => m + q) (f i) :
          FormalRV.Framework.BaseUCom (m + anc))) m)
      * (FormalRV.Framework.uc_eval
            (npar_H m : FormalRV.Framework.BaseUCom (m + anc))
          * kron_vec (FormalRV.Framework.kron_zeros m) ψ)
    = ((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
        ∑ x : Fin (2^m),
          Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
            kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  rw [QPE_pre_QFT_on_eigenstate hmanc hm f ψ (qpeEigenvalue m · θ)
        h_wt_all h_eig_data]
  rw [phase_projector_product_on_uniform_control_sum (qpeEigenvalue m · θ) ψ]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [phase_prefix_qpe_eq_exp_val m θ x]

/-! ### Status of QFTinv: currently a stub

The `QFTinv` definition at `Framework/QPE.lean:36` is `invert (QFT n)`,
where `QFT n` is itself a stub equal to `npar_H n`. Consequently
`QFTinv n = invert (npar_H n)`, which is *not* the inverse quantum
Fourier transform — it is just inverted Hadamards.

The following two theorems document this honestly. Any post-QFT
theorem that pretended to convert the Fourier-weighted superposition
above into `qpe_phase_state m θ` would be unsound until `QFT`/`QFTinv`
are replaced with their real circuit definitions. -/

-- HISTORICAL: `QFTinv_is_stub` proved `QFTinv n = invert (npar_H n)`
-- when `QFTinv` was a stub. Replaced 2026-05-26: `QFTinv n :=
-- real_QFTinv_layer n`, the actual recursive inverse-QFT circuit. The
-- correctness theorem is now `uc_eval_real_QFTinv_layer_eq_IQFT_matrix`
-- in `PostQFT.lean`.

/-! ### Control-register factorization infrastructure

When the real QFTinv is implemented, it will be a `BaseUCom m`
acting only on the control register (qubits `0..m-1`). Its lift via
`map_qubits (fun q => q)` to `BaseUCom (m + anc)` must commute with
`kron_vec`. The two theorems below provide that infrastructure.

This infrastructure is also independently useful: any future
control-side circuit (QFT, bit reversal, classical post-processing)
will need exactly these factorization lemmas. -/

/-- **Control-register `pad_ctrl` (CNOT) factorization.** When both
the control qubit `a` and the target qubit `b` lie in the control
register (`a, b < m`), the CNOT factors through `kron_vec` and only
affects the control component `χ`. -/
theorem pad_ctrl_control_kron_vec_factors {m anc a b : Nat}
    (ha : a < m) (hb : b < m)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    pad_ctrl (m + anc) a b σx * kron_vec χ ψ
      = kron_vec (pad_ctrl m a b σx * χ) ψ := by
  unfold pad_ctrl
  rw [Matrix.add_mul]
  rw [pad_u_control_kron_vec_factors ha proj0 χ ψ]
  rw [Matrix.mul_assoc]
  rw [pad_u_control_kron_vec_factors hb σx χ ψ]
  rw [pad_u_control_kron_vec_factors ha proj1 _ ψ]
  rw [← kron_vec_add_left]
  rw [Matrix.add_mul, Matrix.mul_assoc]

/-- **Generic control-register circuit factorization.** Any well-typed
`BaseUCom m` circuit, lifted via `map_qubits (· + 0) = id` to
`BaseUCom (m + anc)`, factors through `kron_vec` and acts only on the
control component `χ`. Structural induction on the circuit; each gate
case dispatches to the corresponding control-side factorization lemma. -/
theorem uc_eval_control_register_circuit_kron_vec
    {m anc : Nat}
    (c : FormalRV.Framework.BaseUCom m)
    (h_wt : UCom.WellTyped m c)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => q) c : FormalRV.Framework.BaseUCom (m + anc))
      * kron_vec χ ψ
    = kron_vec (FormalRV.Framework.uc_eval c * χ) ψ := by
  induction c generalizing χ with
  | seq c₁ c₂ ih₁ ih₂ =>
      cases h_wt with
      | seq h_wt1 h_wt2 =>
        show FormalRV.Framework.uc_eval
              (map_qubits (fun q => q) c₂ : FormalRV.Framework.BaseUCom (m + anc))
              * FormalRV.Framework.uc_eval
                  (map_qubits (fun q => q) c₁ : FormalRV.Framework.BaseUCom (m + anc))
              * kron_vec χ ψ = _
        rw [Matrix.mul_assoc]
        rw [ih₁ h_wt1 χ]
        rw [ih₂ h_wt2 _]
        show kron_vec (FormalRV.Framework.uc_eval c₂ *
                       (FormalRV.Framework.uc_eval c₁ * χ)) ψ
              = kron_vec (FormalRV.Framework.uc_eval c₂ *
                          FormalRV.Framework.uc_eval c₁ * χ) ψ
        rw [Matrix.mul_assoc]
  | app1 u n =>
      cases h_wt with
      | app1 hn =>
        cases u with
        | R θ φ lam =>
          exact pad_u_control_kron_vec_factors hn (rotation θ φ lam) χ ψ
  | app2 u a b =>
      cases h_wt with
      | app2 ha hb _ =>
        cases u
        exact pad_ctrl_control_kron_vec_factors ha hb χ ψ
  | app3 u _ _ _ => cases u

end FormalRV.SQIRPort
