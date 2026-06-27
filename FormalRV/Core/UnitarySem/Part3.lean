/- UnitarySem — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Core.UnitarySem.Part2

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker  -- enables `A ⊗ₖ B` notation for Matrix.kronecker

/-! ## Helpers for `pad_u_disjoint_comm` (added 2026-05-23, closes the sorry)

The architecture: a unified 5-block reindex `E_5 : T_5 ≃ Fin(2^dim)` lets
both `pad_u dim m A` and `pad_u dim n B` (for `m < n < dim`) be expressed
as `reindex E_5 E_5` of a 5-block kron matrix. The 5-block matrix product
commutes by `Matrix.mul_kronecker_mul`, and `Matrix.submatrix_mul_equiv`
lifts the commutation through the shared reindex. The two natural
paths to define `E_5` (via combining right 3 blocks for pad_u m, or via
left 3 blocks for pad_u n) yield equivs that agree on every input by
the lex-Nat encoding identity, proven by `Equiv.ext` + Nat arithmetic. -/

private theorem nat_inner_m_of_lt (dim m n : Nat) (hmn : m < n) (hn : n < dim) :
    2^(n-m-1) * 2 * 2^(dim-n-1) = 2^(dim-m-1) := by
  rw [show 2^(n-m-1) * 2 = 2^(n-m-1+1) from (pow_succ 2 _).symm, ← pow_add]
  congr 1; omega

private theorem nat_inner_n_of_lt (m n : Nat) (hmn : m < n) :
    2^m * 2 * 2^(n - m - 1) = 2^n := by
  rw [show 2^m * 2 = 2^(m+1) from (pow_succ 2 _).symm, ← pow_add]
  congr 1; omega

/-- Bridge equiv collapsing the right 3 blocks of `5T` to a single Fin block
    (for the pad_u m direction). -/
private def bridge_m_5to3 (a mid c : Nat) :
    ((((Fin a × Fin 2) × Fin mid) × Fin 2) × Fin c)
      ≃ ((Fin a × Fin 2) × Fin (mid * 2 * c)) :=
  let s1 := Equiv.prodCongr (Equiv.prodAssoc (Fin a × Fin 2) (Fin mid) (Fin 2))
                            (Equiv.refl (Fin c))
  let s2 := Equiv.prodAssoc (Fin a × Fin 2) (Fin mid × Fin 2) (Fin c)
  let s3 := Equiv.prodCongr (Equiv.refl (Fin a × Fin 2))
    (Equiv.prodCongr (finProdFinEquiv : Fin mid × Fin 2 ≃ Fin (mid * 2))
                     (Equiv.refl (Fin c)))
  let s4 := Equiv.prodCongr (Equiv.refl (Fin a × Fin 2))
    (finProdFinEquiv : Fin (mid * 2) × Fin c ≃ Fin (mid * 2 * c))
  s1.trans (s2.trans (s3.trans s4))

private theorem bridge_m_5to3_matrix (a mid c : Nat) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.reindex (bridge_m_5to3 a mid c) (bridge_m_5to3 a mid c)
        ((((Iₙ a ⊗ₖ A) ⊗ₖ Iₙ mid) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ c)
      = (Iₙ a ⊗ₖ A) ⊗ₖ Iₙ (mid * 2 * c) := by
  ext ⟨⟨fa, f2⟩, fmc⟩ ⟨⟨fa', f2'⟩, fmc'⟩
  simp [bridge_m_5to3, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply, Iₙ, Matrix.one_apply,
        Equiv.prodAssoc_symm_apply, Equiv.coe_refl]
  have key : (fmc.divNat.divNat = fmc'.divNat.divNat ∧
              fmc.divNat.modNat = fmc'.divNat.modNat ∧
              fmc.modNat = fmc'.modNat) ↔ fmc = fmc' := by
    refine ⟨?_, fun h => h ▸ ⟨rfl, rfl, rfl⟩⟩
    rintro ⟨h_dd, h_dm, h_m⟩
    rw [← Fin.divNat_mkDivMod_modNat fmc, ← Fin.divNat_mkDivMod_modNat fmc',
        ← Fin.divNat_mkDivMod_modNat fmc.divNat,
        ← Fin.divNat_mkDivMod_modNat fmc'.divNat, h_dd, h_dm, h_m]
  by_cases hfmc : fmc = fmc'
  · subst hfmc
    by_cases hfa : fa = fa' <;> simp [hfa]
  · rw [if_neg hfmc]
    have hnot := key.not.mpr hfmc
    by_cases h1 : fmc.modNat = fmc'.modNat
    · rw [if_pos h1]
      by_cases h2 : fmc.divNat.modNat = fmc'.divNat.modNat
      · rw [if_pos h2]
        by_cases h3 : fmc.divNat.divNat = fmc'.divNat.divNat
        · exact absurd ⟨h3, h2, h1⟩ hnot
        · rw [if_neg h3]
      · rw [if_neg h2]
    · rw [if_neg h1]

/-- Bridge equiv collapsing the left 3 blocks of `5T` to a single Fin block
    (for the pad_u n direction). -/
private def bridge_n_5to3 (a mid c : Nat) :
    ((((Fin a × Fin 2) × Fin mid) × Fin 2) × Fin c)
      ≃ ((Fin (a * 2 * mid) × Fin 2) × Fin c) :=
  Equiv.prodCongr
    (Equiv.prodCongr
      ((finProdFinEquiv.prodCongr (Equiv.refl _)).trans
        (finProdFinEquiv : Fin (a * 2) × Fin mid ≃ Fin (a * 2 * mid)))
      (Equiv.refl _))
    (Equiv.refl _)

private theorem bridge_n_5to3_matrix (a mid c : Nat) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.reindex (bridge_n_5to3 a mid c) (bridge_n_5to3 a mid c)
        ((((Iₙ a ⊗ₖ Iₙ 2) ⊗ₖ Iₙ mid) ⊗ₖ B) ⊗ₖ Iₙ c)
      = (Iₙ (a * 2 * mid) ⊗ₖ B) ⊗ₖ Iₙ c := by
  ext ⟨⟨ffin, f2⟩, fc⟩ ⟨⟨ffin', f2'⟩, fc'⟩
  simp [bridge_n_5to3, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply, Iₙ, Matrix.one_apply, Equiv.coe_refl]
  have key : (ffin.divNat.divNat = ffin'.divNat.divNat ∧
              ffin.divNat.modNat = ffin'.divNat.modNat ∧
              ffin.modNat = ffin'.modNat) ↔ ffin = ffin' := by
    refine ⟨?_, fun h => h ▸ ⟨rfl, rfl, rfl⟩⟩
    rintro ⟨h_dd, h_dm, h_m⟩
    rw [← Fin.divNat_mkDivMod_modNat ffin, ← Fin.divNat_mkDivMod_modNat ffin',
        ← Fin.divNat_mkDivMod_modNat ffin.divNat,
        ← Fin.divNat_mkDivMod_modNat ffin'.divNat, h_dd, h_dm, h_m]
  by_cases hffin : ffin = ffin'
  · subst hffin
    by_cases hf2 : f2 = f2' <;> simp [hf2]
  · have hand : ¬((ffin.divNat.divNat = ffin'.divNat.divNat ∧
                    ffin.divNat.modNat = ffin'.divNat.modNat) ∧
                    ffin.modNat = ffin'.modNat) := by
      rw [and_assoc]; exact key.not.mpr hffin
    simp [hffin, hand]

/-- Core abstract 5-block commutation: A in slot 2 and B in slot 4
    of a 5-factor kron tensor structure commute. Both products reduce
    to `(((Iₙ a ⊗ A) ⊗ Iₙ mid) ⊗ B) ⊗ Iₙ c` via `mul_kronecker_mul` ×8. -/
private theorem kron_5block_disjoint_comm_aux (a mid c : Nat)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    ((((Iₙ a ⊗ₖ A) ⊗ₖ Iₙ mid) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ c)
       * ((((Iₙ a ⊗ₖ Iₙ 2) ⊗ₖ Iₙ mid) ⊗ₖ B) ⊗ₖ Iₙ c)
    = ((((Iₙ a ⊗ₖ Iₙ 2) ⊗ₖ Iₙ mid) ⊗ₖ B) ⊗ₖ Iₙ c)
       * ((((Iₙ a ⊗ₖ A) ⊗ₖ Iₙ mid) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ c) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  unfold Iₙ; simp

private theorem reindex_kron_prodCongr_aux {α α' β β' : Type*} [Fintype α] [Fintype β]
    (e₁ : α ≃ α') (e₂ : β ≃ β')
    (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    Matrix.reindex (Equiv.prodCongr e₁ e₂) (Equiv.prodCongr e₁ e₂) (A ⊗ₖ B)
      = Matrix.reindex e₁ e₁ A ⊗ₖ Matrix.reindex e₂ e₂ B := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]

private theorem cast_inner_Iₙ_aux {α : Type*} [Fintype α]
    (X : Matrix α α ℂ) (K M : Nat) (h : K = M) :
    Matrix.reindex (Equiv.prodCongr (Equiv.refl α) (Fin.castOrderIso h).toEquiv)
                    (Equiv.prodCongr (Equiv.refl α) (Fin.castOrderIso h).toEquiv)
                    (X ⊗ₖ Iₙ K)
      = X ⊗ₖ Iₙ M := by
  subst h; rw [reindex_kron_prodCongr_aux]; simp [Matrix.reindex_apply, Iₙ]

private theorem cast_outer_Iₙ_aux {β : Type*} [Fintype β]
    (X : Matrix β β ℂ) (K M : Nat) (h : K = M) :
    Matrix.reindex (Equiv.prodCongr (Fin.castOrderIso h).toEquiv (Equiv.refl β))
                    (Equiv.prodCongr (Fin.castOrderIso h).toEquiv (Equiv.refl β))
                    (Iₙ K ⊗ₖ X)
      = Iₙ M ⊗ₖ X := by
  subst h; rw [reindex_kron_prodCongr_aux]; simp [Matrix.reindex_apply, Iₙ]

private theorem reindex_trans_eq_aux {α β γ : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β ≃ γ) (M : Matrix α α ℂ) :
    Matrix.reindex (e.trans f) (e.trans f) M
      = Matrix.reindex f f (Matrix.reindex e e M) := by
  ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Combined bridge: collapsing the right 3 blocks of 5block_A (with Iₙ cast)
    yields the 3-block form `(Iₙ(2^m) ⊗ A) ⊗ Iₙ(2^(dim-m-1))`. -/
private theorem combined_bridge_m_aux (dim m n : Nat) (hmn : m < n) (hn : n < dim)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.reindex
        ((bridge_m_5to3 (2^m) (2^(n-m-1)) (2^(dim-n-1))).trans
          (Equiv.prodCongr (Equiv.refl _)
            (Fin.castOrderIso (nat_inner_m_of_lt dim m n hmn hn)).toEquiv))
        ((bridge_m_5to3 (2^m) (2^(n-m-1)) (2^(dim-n-1))).trans
          (Equiv.prodCongr (Equiv.refl _)
            (Fin.castOrderIso (nat_inner_m_of_lt dim m n hmn hn)).toEquiv))
        ((((Iₙ (2^m) ⊗ₖ A) ⊗ₖ Iₙ (2^(n-m-1))) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ (2^(dim-n-1)))
      = (Iₙ (2^m) ⊗ₖ A) ⊗ₖ Iₙ (2^(dim-m-1)) := by
  rw [reindex_trans_eq_aux, bridge_m_5to3_matrix]
  exact cast_inner_Iₙ_aux _ _ _ _

/-- Combined bridge: collapsing the left 3 blocks of 5block_B (with Iₙ cast)
    yields the 3-block form `(Iₙ(2^n) ⊗ B) ⊗ Iₙ(2^(dim-n-1))`. -/
private theorem combined_bridge_n_aux (dim m n : Nat) (hmn : m < n) (hn : n < dim)
    (B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.reindex
        ((bridge_n_5to3 (2^m) (2^(n-m-1)) (2^(dim-n-1))).trans
          (Equiv.prodCongr (Equiv.prodCongr
            (Fin.castOrderIso (nat_inner_n_of_lt m n hmn)).toEquiv (Equiv.refl _))
            (Equiv.refl _)))
        ((bridge_n_5to3 (2^m) (2^(n-m-1)) (2^(dim-n-1))).trans
          (Equiv.prodCongr (Equiv.prodCongr
            (Fin.castOrderIso (nat_inner_n_of_lt m n hmn)).toEquiv (Equiv.refl _))
            (Equiv.refl _)))
        ((((Iₙ (2^m) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ (2^(n-m-1))) ⊗ₖ B) ⊗ₖ Iₙ (2^(dim-n-1)))
      = (Iₙ (2^n) ⊗ₖ B) ⊗ₖ Iₙ (2^(dim-n-1)) := by
  rw [reindex_trans_eq_aux, bridge_n_5to3_matrix, reindex_kron_prodCongr_aux,
      cast_outer_Iₙ_aux]
  simp [Matrix.reindex_apply]

/-- The unified reindex via the pad_u m direction (combining right 3 blocks). -/
private noncomputable def E_m_unified (dim m n : Nat) (hmn : m < n) (hn : n < dim) :
    ((((Fin (2^m) × Fin 2) × Fin (2^(n-m-1))) × Fin 2) × Fin (2^(dim-n-1)))
      ≃ Fin (2^dim) :=
  ((bridge_m_5to3 (2^m) (2^(n-m-1)) (2^(dim-n-1))).trans
      (Equiv.prodCongr (Equiv.refl _)
        (Fin.castOrderIso (nat_inner_m_of_lt dim m n hmn hn)).toEquiv)).trans
    (((finProdFinEquiv.prodCongr (Equiv.refl _)).trans
        (finProdFinEquiv : Fin (2^m * 2) × Fin (2^(dim-m-1)) ≃ Fin (2^m * 2 * 2^(dim-m-1)))).trans
      (Fin.castOrderIso (two_pow_split dim m (lt_trans hmn hn))).toEquiv)

/-- The unified reindex via the pad_u n direction (combining left 3 blocks). -/
private noncomputable def E_n_unified (dim m n : Nat) (hmn : m < n) (hn : n < dim) :
    ((((Fin (2^m) × Fin 2) × Fin (2^(n-m-1))) × Fin 2) × Fin (2^(dim-n-1)))
      ≃ Fin (2^dim) :=
  ((bridge_n_5to3 (2^m) (2^(n-m-1)) (2^(dim-n-1))).trans
      (Equiv.prodCongr (Equiv.prodCongr
        (Fin.castOrderIso (nat_inner_n_of_lt m n hmn)).toEquiv (Equiv.refl _))
        (Equiv.refl _))).trans
    (((finProdFinEquiv.prodCongr (Equiv.refl _)).trans
        (finProdFinEquiv : Fin (2^n * 2) × Fin (2^(dim-n-1)) ≃ Fin (2^n * 2 * 2^(dim-n-1)))).trans
      (Fin.castOrderIso (two_pow_split dim n hn)).toEquiv)

/-- The two unified reindexes are equal as Equivs (proven by Equiv.ext +
    Fin.ext + Nat exponent identity `2^(dim-m-1) = 2^(dim-n-1) · 2^(n-m-1) · 2`). -/
private theorem E_m_eq_E_n_unified (dim m n : Nat) (hmn : m < n) (hn : n < dim) :
    E_m_unified dim m n hmn hn = E_n_unified dim m n hmn hn := by
  ext ⟨⟨⟨⟨xa, x2m⟩, xc⟩, x2n⟩, xe⟩
  simp [E_m_unified, E_n_unified, bridge_m_5to3, bridge_n_5to3, finProdFinEquiv,
        Fin.castOrderIso, Equiv.prodAssoc]
  have key : (2 ^ (dim - m - 1) : Nat) = 2 ^ (dim - n - 1) * 2 ^ (n - m - 1) * 2 := by
    rw [show (2 ^ (dim - n - 1) * 2 ^ (n - m - 1) * 2 : Nat)
          = 2 ^ ((dim - n - 1) + (n - m - 1) + 1) from by
          rw [show ((dim - n - 1) + (n - m - 1) + 1 : Nat)
              = ((dim - n - 1) + ((n - m - 1) + 1)) from by ring,
              pow_add, pow_succ]; ring]
    congr 1; omega
  rw [key]; ring

private theorem pad_u_m_via_E_unified (dim m n : Nat) (hmn : m < n) (hn : n < dim)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u dim m A = Matrix.reindex (E_m_unified dim m n hmn hn) (E_m_unified dim m n hmn hn)
        ((((Iₙ (2^m) ⊗ₖ A) ⊗ₖ Iₙ (2^(n-m-1))) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ (2^(dim-n-1))) := by
  have hm : m < dim := lt_trans hmn hn
  unfold pad_u E_m_unified
  rw [dif_pos hm]
  dsimp only  -- reduce `let` bindings to flat form
  conv_rhs => rw [reindex_trans_eq_aux]
  congr 1
  exact (combined_bridge_m_aux dim m n hmn hn A).symm

private theorem pad_u_n_via_E_unified (dim m n : Nat) (hmn : m < n) (hn : n < dim)
    (B : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u dim n B = Matrix.reindex (E_n_unified dim m n hmn hn) (E_n_unified dim m n hmn hn)
        ((((Iₙ (2^m) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ (2^(n-m-1))) ⊗ₖ B) ⊗ₖ Iₙ (2^(dim-n-1))) := by
  unfold pad_u E_n_unified
  rw [dif_pos hn]
  dsimp only  -- reduce `let` bindings to flat form
  conv_rhs => rw [reindex_trans_eq_aux]
  congr 1
  exact (combined_bridge_n_aux dim m n hmn hn B).symm

/-- The `m < n < dim` case of `pad_u_disjoint_comm`. -/
private theorem pad_u_disjoint_comm_lt (dim m n : Nat)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hmn : m < n) (hn : n < dim) :
    pad_u dim m A * pad_u dim n B = pad_u dim n B * pad_u dim m A := by
  rw [pad_u_m_via_E_unified dim m n hmn hn A,
      pad_u_n_via_E_unified dim m n hmn hn B,
      E_m_eq_E_n_unified dim m n hmn hn]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv _ _ _ (E_n_unified dim m n hmn hn).symm _,
      Matrix.submatrix_mul_equiv _ _ _ (E_n_unified dim m n hmn hn).symm _,
      kron_5block_disjoint_comm_aux]

-- SQIR/QuantumLib/Pad.v analog: `pad_A_B_commutes`.
/-- Disjoint single-qubit `pad_u`'s commute under matrix multiplication
    (closed 2026-05-23 via the 5-block reindex strategy). For `m ≠ n`,
    WLOG `m < n`; both pad_u's factor through the same unified 5-block
    reindex `E_5 : T_5 ≃ Fin(2^dim)`, where the 5-block matrices commute
    via `Matrix.mul_kronecker_mul` ×4 + identity collapses, and the
    commutation lifts through `Matrix.submatrix_mul_equiv`. The unified
    `E_5` is reached via two different bridge paths (combining right 3
    blocks for pad_u m, left 3 blocks for pad_u n) that yield equal Equivs
    by `Equiv.ext` + the Nat identity `2^(dim-m-1) = 2^(dim-n-1)·2^(n-m-1)·2`. -/
theorem pad_u_disjoint_comm (dim m n : Nat) (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hm : m < dim) (hn : n < dim) (hmn : m ≠ n) :
    pad_u dim m A * pad_u dim n B = pad_u dim n B * pad_u dim m A := by
  rcases Nat.lt_or_gt_of_ne hmn with hlt | hgt
  · exact pad_u_disjoint_comm_lt dim m n A B hlt hn
  · exact (pad_u_disjoint_comm_lt dim n m B A hgt hm).symm

/-- Disjoint `pad_u`'s commute (totally unconstrained version: handles
    out-of-range qubits via the `pad_u_ill_typed` zero collapse). -/
theorem pad_u_disjoint_comm' (dim m n : Nat) (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hmn : m ≠ n) :
    pad_u dim m A * pad_u dim n B = pad_u dim n B * pad_u dim m A := by
  by_cases hm : m < dim
  · by_cases hn : n < dim
    · exact pad_u_disjoint_comm dim m n A B hm hn hmn
    · rw [pad_u_ill_typed _ (Nat.le_of_not_lt hn),
          Matrix.zero_mul, Matrix.mul_zero]
  · rw [pad_u_ill_typed _ (Nat.le_of_not_lt hm),
        Matrix.zero_mul, Matrix.mul_zero]

/-- A `pad_u` and a `pad_ctrl` on pairwise-disjoint qubits commute.
    Derived from `pad_u_disjoint_comm'` by unfolding `pad_ctrl`
    (`= pad_u m proj0 + pad_u m proj1 * pad_u n M`) and propagating
    the commutation through the projector decomposition. -/
theorem pad_u_pad_ctrl_disjoint_comm (dim q m n : Nat)
    (U M : Matrix (Fin 2) (Fin 2) ℂ)
    (hq_m : q ≠ m) (hq_n : q ≠ n) :
    pad_u dim q U * pad_ctrl dim m n M
      = pad_ctrl dim m n M * pad_u dim q U := by
  unfold pad_ctrl
  -- pad_u q U * (P0_m + P1_m * M_n) = pad_u q U * P0_m + pad_u q U * P1_m * M_n
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  · -- pad_u q U * pad_u m proj0 = pad_u m proj0 * pad_u q U
    exact pad_u_disjoint_comm' dim q m U proj0 hq_m
  · -- pad_u q U * (pad_u m proj1 * pad_u n M)
    --   = (pad_u m proj1 * pad_u n M) * pad_u q U
    rw [← Matrix.mul_assoc, pad_u_disjoint_comm' dim q m U proj1 hq_m,
        Matrix.mul_assoc, pad_u_disjoint_comm' dim q n U M hq_n,
        ← Matrix.mul_assoc]

/-- Two `pad_ctrl`'s on four pairwise-disjoint qubits commute.
    Same derivation chain as `pad_u_pad_ctrl_disjoint_comm`. -/
theorem pad_ctrl_disjoint_comm (dim m n m' n' : Nat)
    (M M' : Matrix (Fin 2) (Fin 2) ℂ)
    (hmm : m ≠ m') (hmn : m ≠ n') (hnm : n ≠ m') (hnn : n ≠ n') :
    pad_ctrl dim m n M * pad_ctrl dim m' n' M'
      = pad_ctrl dim m' n' M' * pad_ctrl dim m n M := by
  unfold pad_ctrl
  -- Expand both products fully via distributive laws.
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  -- Each of the four expanded LHS terms commutes with the matching RHS
  -- term via pad_u_disjoint_comm'; addition is commutative so `abel`
  -- handles the reordering.
  have h1 : pad_u dim m proj0 * pad_u dim m' proj0
              = pad_u dim m' proj0 * pad_u dim m proj0 :=
    pad_u_disjoint_comm' dim m m' proj0 proj0 hmm
  have h2 : pad_u dim m proj1 * pad_u dim n M * pad_u dim m' proj0
              = pad_u dim m' proj0 * (pad_u dim m proj1 * pad_u dim n M) := by
    rw [Matrix.mul_assoc, pad_u_disjoint_comm' dim n m' M proj0 hnm,
        ← Matrix.mul_assoc, pad_u_disjoint_comm' dim m m' proj1 proj0 hmm,
        Matrix.mul_assoc]
  have h3 : pad_u dim m proj0 * (pad_u dim m' proj1 * pad_u dim n' M')
              = pad_u dim m' proj1 * pad_u dim n' M' * pad_u dim m proj0 := by
    rw [← Matrix.mul_assoc, pad_u_disjoint_comm' dim m m' proj0 proj1 hmm,
        Matrix.mul_assoc, pad_u_disjoint_comm' dim m n' proj0 M' hmn,
        ← Matrix.mul_assoc]
  have h4 : pad_u dim m proj1 * pad_u dim n M
              * (pad_u dim m' proj1 * pad_u dim n' M')
              = pad_u dim m' proj1 * pad_u dim n' M'
                  * (pad_u dim m proj1 * pad_u dim n M) := by
    -- 4-term reordering via 4 pairwise pad_u commutations (P1m↔P1m',
    -- P1m↔Mn', Mn↔P1m', Mn↔Mn').  Calc chain over fully-left-assoc
    -- form `A · B · C · D` lets each commute be a single rewrite.
    calc pad_u dim m proj1 * pad_u dim n M
              * (pad_u dim m' proj1 * pad_u dim n' M')
        = pad_u dim m proj1 * pad_u dim n M
            * pad_u dim m' proj1 * pad_u dim n' M' := by
          rw [Matrix.mul_assoc (pad_u dim m proj1 * pad_u dim n M)]
      _ = pad_u dim m proj1 * (pad_u dim n M * pad_u dim m' proj1)
            * pad_u dim n' M' := by
          rw [Matrix.mul_assoc (pad_u dim m proj1)]
      _ = pad_u dim m proj1 * (pad_u dim m' proj1 * pad_u dim n M)
            * pad_u dim n' M' := by
          rw [pad_u_disjoint_comm' dim n m' M proj1 hnm]
      _ = pad_u dim m proj1 * pad_u dim m' proj1 * pad_u dim n M
            * pad_u dim n' M' := by
          rw [← Matrix.mul_assoc (pad_u dim m proj1)]
      _ = pad_u dim m' proj1 * pad_u dim m proj1 * pad_u dim n M
            * pad_u dim n' M' := by
          rw [pad_u_disjoint_comm' dim m m' proj1 proj1 hmm]
      _ = pad_u dim m' proj1 * pad_u dim m proj1
            * (pad_u dim n M * pad_u dim n' M') := by
          rw [Matrix.mul_assoc (pad_u dim m' proj1 * pad_u dim m proj1)]
      _ = pad_u dim m' proj1 * pad_u dim m proj1
            * (pad_u dim n' M' * pad_u dim n M) := by
          rw [pad_u_disjoint_comm' dim n n' M M' hnn]
      _ = pad_u dim m' proj1 * pad_u dim m proj1
            * pad_u dim n' M' * pad_u dim n M := by
          rw [← Matrix.mul_assoc (pad_u dim m' proj1 * pad_u dim m proj1)]
      _ = pad_u dim m' proj1 * (pad_u dim m proj1 * pad_u dim n' M')
            * pad_u dim n M := by
          rw [Matrix.mul_assoc (pad_u dim m' proj1)]
      _ = pad_u dim m' proj1 * (pad_u dim n' M' * pad_u dim m proj1)
            * pad_u dim n M := by
          rw [pad_u_disjoint_comm' dim m n' proj1 M' hmn]
      _ = pad_u dim m' proj1 * pad_u dim n' M' * pad_u dim m proj1
            * pad_u dim n M := by
          rw [← Matrix.mul_assoc (pad_u dim m' proj1)]
      _ = pad_u dim m' proj1 * pad_u dim n' M'
            * (pad_u dim m proj1 * pad_u dim n M) := by
          rw [Matrix.mul_assoc (pad_u dim m' proj1 * pad_u dim n' M')]
  rw [h1, h2, h3, h4]
  abel

/-! ## Per-base-gate semantic -/

/-- The matrix corresponding to a base 1-qubit unitary applied to qubit `n`. -/
noncomputable def ueval_r (dim n : Nat) (U : BaseUnitary 1) : Square dim :=
  match U with
  | BaseUnitary.R θ ϕ lam => pad_u dim n (rotation θ ϕ lam)

/-- The matrix corresponding to CNOT with control `m`, target `n`. -/
noncomputable def ueval_cnot (dim m n : Nat) : Square dim :=
  pad_ctrl dim m n σx

/-! ## Unitary semantics — the headline function -/

/-- Denote a `BaseUCom dim` as its 2^dim × 2^dim complex matrix.
    Mirrors SQIR's `uc_eval` (UnitarySem.v line 24). -/
noncomputable def uc_eval {dim : Nat} : BaseUCom dim → Square dim
  | UCom.seq c₁ c₂      => uc_eval c₂ * uc_eval c₁
  | UCom.app1 U n       => ueval_r dim n U
  | UCom.app2 _ m n     => ueval_cnot dim m n
  | UCom.app3 _ _ _ _   => 0    -- no 3-qubit primitives in BaseUnitary

/-! ## Equivalence -/

/-- Two unitary circuits are equivalent iff their matrix semantics agree.
    We avoid `≡` because it collides with `Nat.ModEq` notation; use the
    function name `UCom.equiv` directly, or the local `≅` alias below. -/
def UCom.equiv {dim : Nat} (c₁ c₂ : BaseUCom dim) : Prop :=
  uc_eval c₁ = uc_eval c₂

scoped infix:50 " ≅ " => UCom.equiv

/-- Equivalence is reflexive. -/
theorem UCom.equiv_refl {dim : Nat} (c : BaseUCom dim) : UCom.equiv c c := rfl

/-- Equivalence is symmetric. -/
theorem UCom.equiv_symm {dim : Nat} {c₁ c₂ : BaseUCom dim} :
    UCom.equiv c₁ c₂ → UCom.equiv c₂ c₁ := fun h => h.symm

/-- Equivalence is transitive. -/
theorem UCom.equiv_trans {dim : Nat} {c₁ c₂ c₃ : BaseUCom dim} :
    UCom.equiv c₁ c₂ → UCom.equiv c₂ c₃ → UCom.equiv c₁ c₃ :=
  fun h₁₂ h₂₃ => h₁₂.trans h₂₃

/-- Sequential composition is associative.
    The `uc_eval` of `seq c₁ c₂` is `uc_eval c₂ * uc_eval c₁` (right-to-left
    matrix order), so this reduces to associativity of matrix multiplication. -/
theorem useq_assoc {dim : Nat} (c₁ c₂ c₃ : BaseUCom dim) :
    UCom.equiv (UCom.seq (UCom.seq c₁ c₂) c₃) (UCom.seq c₁ (UCom.seq c₂ c₃)) := by
  show uc_eval c₃ * (uc_eval c₂ * uc_eval c₁)
        = (uc_eval c₃ * uc_eval c₂) * uc_eval c₁
  exact (Matrix.mul_assoc _ _ _).symm

/-- `useq` left-associativity (reverse direction): `c₁;(c₂;c₃) ≡ (c₁;c₂);c₃`.
    Direct corollary of `useq_assoc` via `UCom.equiv_symm`. -/
theorem useq_assoc_l {dim : Nat} (c₁ c₂ c₃ : BaseUCom dim) :
    UCom.equiv (UCom.seq c₁ (UCom.seq c₂ c₃)) (UCom.seq (UCom.seq c₁ c₂) c₃) :=
  UCom.equiv_symm (useq_assoc c₁ c₂ c₃)


end FormalRV.Framework
