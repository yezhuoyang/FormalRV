/-
  FormalRV.Framework.DensitySem — density-matrix semantics for `Com`.

  Lean translation of `SQIR/SQIR/DensitySem.v` (148 LOC of Coq).
  Where `NDSem` gives operational/non-deterministic semantics, this gives
  the deterministic density-matrix semantics: each `Com` is interpreted as
  a `Superoperator` (a function on density matrices).

  Status: scaffolding — types and signatures in place, key proofs sorried
  for partial-trace / measurement reasoning.
-/
import FormalRV.Core.UnitaryOps
import FormalRV.Core.PadAction

namespace FormalRV.Framework

/-- A density matrix on a `dim`-qubit system: `2^dim × 2^dim` complex,
    Hermitian, positive semi-definite, trace 1. We don't enforce the
    physical constraints in the type; just use `Square dim`. -/
abbrev DensityMat (dim : Nat) := Square dim

/-- A superoperator: a linear map between density matrices. We model it
    as a plain function for now (not enforcing complete positivity in the
    type). -/
abbrev Superoperator (dim : Nat) := DensityMat dim → DensityMat dim

namespace BaseCom
open BaseUCom

/-- Density-matrix semantics for `Com`. Each program is a superoperator.
    For unitary `u`: ρ ↦ U ρ U†.
    For measurement: ρ ↦ P₀ ρ P₀† + P₁ ρ P₁† (sum over outcomes), with
    each branch's program applied conditionally.

    SQIR/DensitySem.v line ~22. -/
noncomputable def c_eval {dim : Nat} : BaseCom dim → Superoperator dim
  | Com.cskip            => fun ρ => ρ
  | Com.embedU u         => fun ρ => uc_eval u * ρ * (uc_eval u).conjTranspose
  | Com.useq c₁ c₂       => fun ρ => c_eval c₂ (c_eval c₁ ρ)
  | Com.meas n c₁ c₂     => fun ρ =>
      let p₀ := proj n dim false
      let p₁ := proj n dim true
      c_eval c₁ (p₁ * ρ * p₁.conjTranspose) + c_eval c₂ (p₀ * ρ * p₀.conjTranspose)

/-- `Com` equivalence under the density-matrix semantics. -/
def c_equiv {dim : Nat} (c₁ c₂ : BaseCom dim) : Prop :=
  c_eval c₁ = c_eval c₂

scoped infix:50 " ⩮ " => c_equiv

theorem c_equiv_refl {dim : Nat} (c : BaseCom dim) : c_equiv c c := rfl

theorem c_equiv_sym {dim : Nat} {c₁ c₂ : BaseCom dim} :
    c_equiv c₁ c₂ → c_equiv c₂ c₁ := fun h => h.symm

theorem c_equiv_trans {dim : Nat} {c₁ c₂ c₃ : BaseCom dim} :
    c_equiv c₁ c₂ → c_equiv c₂ c₃ → c_equiv c₁ c₃ := fun h₁ h₂ => h₁.trans h₂

/-- `useq` associativity for `Com` (density-matrix version). -/
theorem c_useq_assoc {dim : Nat} (c₁ c₂ c₃ : BaseCom dim) :
    c_equiv (Com.useq (Com.useq c₁ c₂) c₃) (Com.useq c₁ (Com.useq c₂ c₃)) := by
  funext ρ
  simp [c_eval]

/-- `useq` left-associativity (reverse direction): `c₁;(c₂;c₃) ≡ (c₁;c₂);c₃`.
    Direct corollary of `c_useq_assoc` via `c_equiv_sym`. -/
theorem c_useq_assoc_l {dim : Nat} (c₁ c₂ c₃ : BaseCom dim) :
    c_equiv (Com.useq c₁ (Com.useq c₂ c₃)) (Com.useq (Com.useq c₁ c₂) c₃) :=
  c_equiv_sym (c_useq_assoc c₁ c₂ c₃)

/-- Sequential composition is congruent under `c_equiv`.
    -- SQIR/SQIR/DensitySem.v line 60: seq_congruence. -/
theorem c_useq_congr {dim : Nat} (c₁ c₁' c₂ c₂' : BaseCom dim)
    (h₁ : c_equiv c₁ c₁') (h₂ : c_equiv c₂ c₂') :
    c_equiv (Com.useq c₁ c₂) (Com.useq c₁' c₂') := by
  funext ρ
  show c_eval c₂ (c_eval c₁ ρ) = c_eval c₂' (c_eval c₁' ρ)
  rw [h₁, h₂]

/-- `cskip ; c ≡ c` — left identity of useq under c_equiv. -/
theorem c_cskip_useq {dim : Nat} (c : BaseCom dim) :
    c_equiv (Com.useq Com.cskip c) c := rfl

/-- `c ; cskip ≡ c` — right identity of useq under c_equiv. -/
theorem c_useq_cskip {dim : Nat} (c : BaseCom dim) :
    c_equiv (Com.useq c Com.cskip) c := rfl

/-- Measurement is congruent under `c_equiv` on each branch.
    -- SQIR/SQIR/DensitySem.v: `meas_congruence`. -/
theorem c_meas_congr {dim : Nat} (n : Nat) {c₁ c₁' c₂ c₂' : BaseCom dim}
    (h₁ : c_equiv c₁ c₁') (h₂ : c_equiv c₂ c₂') :
    c_equiv (Com.meas n c₁ c₂) (Com.meas n c₁' c₂') := by
  funext ρ
  show c_eval c₁ _ + c_eval c₂ _ = c_eval c₁' _ + c_eval c₂' _
  rw [h₁, h₂]

/-- Definitional unfolding of `c_eval` on a `useq`. -/
@[simp] theorem c_eval_useq {dim : Nat} (c₁ c₂ : BaseCom dim) (ρ : DensityMat dim) :
    c_eval (Com.useq c₁ c₂) ρ = c_eval c₂ (c_eval c₁ ρ) := rfl

/-- Definitional unfolding of `c_eval` on a `meas`. -/
@[simp] theorem c_eval_meas {dim : Nat} (n : Nat) (c₁ c₂ : BaseCom dim)
    (ρ : DensityMat dim) :
    c_eval (Com.meas n c₁ c₂) ρ
      = c_eval c₁ (proj n dim true * ρ * (proj n dim true).conjTranspose)
        + c_eval c₂ (proj n dim false * ρ * (proj n dim false).conjTranspose) := rfl

/-- `c_eval` of a unitary command applied to ρ is U ρ U†. -/
@[simp] theorem c_eval_embedU {dim : Nat} (u : BaseUCom dim) (ρ : DensityMat dim) :
    c_eval (Com.embedU u) ρ = uc_eval u * ρ * (uc_eval u).conjTranspose := rfl

/-- Bridge from unitary semantics to density semantics: if two unitary
    commands are `UCom.equiv` (have equal `uc_eval`), then their embeddings
    into `Com` are `c_equiv`. The natural lifting of unitary equivalence
    through the density-matrix evolution `ρ ↦ U ρ U†`. -/
theorem c_equiv_of_uc_equiv {dim : Nat} {u₁ u₂ : BaseUCom dim}
    (h : UCom.equiv u₁ u₂) :
    c_equiv (Com.embedU u₁) (Com.embedU u₂) := by
  unfold c_equiv
  funext ρ
  rw [c_eval_embedU, c_eval_embedU, h]

/-- Left-position bridge composition: substituting an equivalent unitary
    in the left position of a useq preserves `c_equiv`. 1-line combination
    of `c_equiv_of_uc_equiv` with `c_useq_congr`. -/
theorem c_equiv_useq_embedU_left {dim : Nat} (c : BaseCom dim)
    {u₁ u₂ : BaseUCom dim} (h : UCom.equiv u₁ u₂) :
    c_equiv (Com.useq (Com.embedU u₁) c) (Com.useq (Com.embedU u₂) c) :=
  c_useq_congr _ _ _ _ (c_equiv_of_uc_equiv h) (c_equiv_refl c)

/-- Right-position bridge composition: symmetric to `c_equiv_useq_embedU_left`. -/
theorem c_equiv_useq_embedU_right {dim : Nat} (c : BaseCom dim)
    {u₁ u₂ : BaseUCom dim} (h : UCom.equiv u₁ u₂) :
    c_equiv (Com.useq c (Com.embedU u₁)) (Com.useq c (Com.embedU u₂)) :=
  c_useq_congr _ _ _ _ (c_equiv_refl c) (c_equiv_of_uc_equiv h)

/-- Lifting `invert_invert` through `embedU`: `embedU(invert(invert c)) ⩮
    embedU(c)`. Direct consequence of the syntactic equality
    `invert (invert c) = c`. -/
theorem c_equiv_embedU_invert_invert {dim : Nat} (c : BaseUCom dim) :
    c_equiv (Com.embedU (invert (invert c))) (Com.embedU c) := by
  rw [invert_invert]
  exact c_equiv_refl _

/-- `embedU(ID q)` is a left-identity of `useq` at the density layer
    (when `q < dim`). The identity unitary acts as the identity on
    density matrices: `1 ρ 1† = ρ`. -/
theorem c_equiv_useq_embedU_ID_l {dim : Nat} (q : Nat) (hq : q < dim)
    (c : BaseCom dim) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.ID q)) c) c := by
  funext ρ
  show c_eval c (uc_eval (BaseUCom.ID q) * ρ * (uc_eval (BaseUCom.ID q)).conjTranspose)
        = c_eval c ρ
  rw [uc_eval_ID_eq_one hq, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/-- `embedU(ID q)` is also a right-identity of `useq` at the density layer.
    Symmetric companion of `c_equiv_useq_embedU_ID_l`. -/
theorem c_equiv_useq_embedU_ID_r {dim : Nat} (q : Nat) (hq : q < dim)
    (c : BaseCom dim) :
    c_equiv (Com.useq c (Com.embedU (BaseUCom.ID q))) c := by
  funext ρ
  show uc_eval (BaseUCom.ID q) * (c_eval c ρ) * (uc_eval (BaseUCom.ID q)).conjTranspose
        = c_eval c ρ
  rw [uc_eval_ID_eq_one hq, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/-- Sequencing two embedded unitaries is the embedding of their sequence:
    `useq (embedU u₁) (embedU u₂) ⩮ embedU (u₁ ; u₂)`. The fundamental
    "merge" identity for the density layer, derived from matrix
    associativity and `conjTranspose_mul`. -/
theorem c_equiv_useq_embedU_embedU {dim : Nat} (u₁ u₂ : BaseUCom dim) :
    c_equiv (Com.useq (Com.embedU u₁) (Com.embedU u₂))
            (Com.embedU (UCom.seq u₁ u₂)) := by
  funext ρ
  show uc_eval u₂ * (uc_eval u₁ * ρ * (uc_eval u₁).conjTranspose)
        * (uc_eval u₂).conjTranspose
        = (uc_eval u₂ * uc_eval u₁) * ρ * (uc_eval u₂ * uc_eval u₁).conjTranspose
  rw [Matrix.conjTranspose_mul]
  simp [Matrix.mul_assoc]

/-- Application of the seq-merge identity + bridge:
    `useq (embedU(T q)) (embedU(TDAG q)) ⩮ embedU(ID q)`. Demonstrates the
    seq-merge → bridge composition chain — converts a density-layer
    seq of two embedUs into a unitary identity. -/
theorem c_equiv_useq_embedU_T_TDAG {dim : Nat} (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.T q : BaseUCom dim))
                      (Com.embedU (BaseUCom.TDAG q)))
            (Com.embedU (BaseUCom.ID q)) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (T_TDAG_id q))

/-- Pauli-X involution via seq-merge + bridge. -/
theorem c_equiv_useq_embedU_X_X {dim : Nat} (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.X q : BaseUCom dim))
                      (Com.embedU (BaseUCom.X q)))
            (Com.embedU (BaseUCom.ID q)) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (X_X_id q))

/-- Pauli-Y involution via seq-merge + bridge. -/
theorem c_equiv_useq_embedU_Y_Y {dim : Nat} (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.Y q : BaseUCom dim))
                      (Com.embedU (BaseUCom.Y q)))
            (Com.embedU (BaseUCom.ID q)) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (Y_Y_id q))

/-- Pauli-Z involution via seq-merge + bridge. -/
theorem c_equiv_useq_embedU_Z_Z {dim : Nat} (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.Z q : BaseUCom dim))
                      (Com.embedU (BaseUCom.Z q)))
            (Com.embedU (BaseUCom.ID q)) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (Z_Z_id q))

/-- Hadamard involution via seq-merge + bridge. -/
theorem c_equiv_useq_embedU_H_H {dim : Nat} (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.H q : BaseUCom dim))
                      (Com.embedU (BaseUCom.H q)))
            (Com.embedU (BaseUCom.ID q)) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (H_H_id q))

/-- Toffoli involution via seq-merge + bridge: at the density layer,
    `useq (embedU (CCX a b c)) (embedU (CCX a b c)) ⩮ embedU (ID 0)`
    when `dim ≥ 1`. Mirrors `c_equiv_useq_embedU_X_X` for the 3-qubit
    Toffoli case. -/
theorem c_equiv_useq_embedU_CCX_CCX {dim : Nat} (a b c : Nat) (h0 : 0 < dim)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.CCX a b c : BaseUCom dim))
                      (Com.embedU (BaseUCom.CCX a b c)))
            (Com.embedU (BaseUCom.ID 0)) :=
  (c_equiv_useq_embedU_embedU _ _).trans
    (c_equiv_of_uc_equiv (CCX_CCX_id a b c h0 ha hb hc hab hac hbc))

/-- T†·T inverse pair via seq-merge + bridge. -/
theorem c_equiv_useq_embedU_TDAG_T {dim : Nat} (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.TDAG q : BaseUCom dim))
                      (Com.embedU (BaseUCom.T q)))
            (Com.embedU (BaseUCom.ID q)) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (TDAG_T_id q))

/-- S·S† inverse pair via seq-merge + bridge. -/
theorem c_equiv_useq_embedU_S_SDAG {dim : Nat} (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.S q : BaseUCom dim))
                      (Com.embedU (BaseUCom.SDAG q)))
            (Com.embedU (BaseUCom.ID q)) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (S_SDAG_id q))

/-- S†·S inverse pair via seq-merge + bridge. -/
theorem c_equiv_useq_embedU_SDAG_S {dim : Nat} (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.SDAG q : BaseUCom dim))
                      (Com.embedU (BaseUCom.S q)))
            (Com.embedU (BaseUCom.ID q)) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (SDAG_S_id q))

/-- Hadamard interchange identity at the density layer:
    `useq (embedU H) (embedU Z) ⩮ useq (embedU X) (embedU H)`. Lifts
    `H_comm_Z` via the seq-merge → bridge → seq-merge⁻¹ chain. -/
theorem c_equiv_useq_embedU_H_Z_eq_X_H {dim : Nat} (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.H q : BaseUCom dim))
                      (Com.embedU (BaseUCom.Z q)))
            (Com.useq (Com.embedU (BaseUCom.X q))
                      (Com.embedU (BaseUCom.H q))) :=
  ((c_equiv_useq_embedU_embedU _ _).trans
    (c_equiv_of_uc_equiv (H_comm_Z q))).trans
    (c_equiv_useq_embedU_embedU _ _).symm

/-- Dual Hadamard interchange at the density layer:
    `useq (embedU H) (embedU X) ⩮ useq (embedU Z) (embedU H)`. Lifts
    `H_comm_X` via the same seq-merge chain. -/
theorem c_equiv_useq_embedU_H_X_eq_Z_H {dim : Nat} (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.H q : BaseUCom dim))
                      (Com.embedU (BaseUCom.X q)))
            (Com.useq (Com.embedU (BaseUCom.Z q))
                      (Com.embedU (BaseUCom.H q))) :=
  ((c_equiv_useq_embedU_embedU _ _).trans
    (c_equiv_of_uc_equiv (H_comm_X q))).trans
    (c_equiv_useq_embedU_embedU _ _).symm

/-- Z-rotation composition lifted to density semantics:
    `useq (embedU(Rz θ)) (embedU(Rz θ')) ⩮ embedU(Rz (θ+θ'))`.
    Lifts `Rz_Rz_add` via seq-merge + bridge. -/
theorem c_equiv_useq_embedU_Rz_Rz_add {dim : Nat} (θ θ' : ℝ) (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.Rz θ q : BaseUCom dim))
                      (Com.embedU (BaseUCom.Rz θ' q)))
            (Com.embedU (BaseUCom.Rz (θ + θ') q)) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (Rz_Rz_add q θ θ'))

/-- Parametric Z-rotation cancellation lifted to density:
    `useq (embedU(Rz θ)) (embedU(Rz (-θ))) ⩮ embedU(ID q)`. Generalizes
    the T·T† and S·S† inverse-pair lifts to arbitrary θ. -/
theorem c_equiv_useq_embedU_Rz_neg_id {dim : Nat} (θ : ℝ) (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.Rz θ q : BaseUCom dim))
                      (Com.embedU (BaseUCom.Rz (-θ) q)))
            (Com.embedU (BaseUCom.ID q)) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (Rz_neg_id q θ))

/-- Trivial Z-rotation = ID at density: `embedU(Rz 0 q) ⩮ embedU(ID q)`.
    Direct bridge lift of `Rz_0_id`. Useful for eliminating
    zero-angle rotations from circuits. -/
theorem c_equiv_embedU_Rz_zero_eq_ID {dim : Nat} (q : Nat) :
    c_equiv (Com.embedU (BaseUCom.Rz 0 q : BaseUCom dim))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (Rz_0_id q)

/-- T·T = S lifted to density: `useq (embedU(T q)) (embedU(T q)) ⩮
    embedU(S q)`. Useful T-count reduction primitive. -/
theorem c_equiv_useq_embedU_T_T_eq_S {dim : Nat} (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.T q : BaseUCom dim))
                      (Com.embedU (BaseUCom.T q)))
            (Com.embedU (BaseUCom.S q)) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (T_T_eq_S q))

/-- S·S = Z lifted to density. Same Rz-composition pattern with θ = π/2. -/
theorem c_equiv_useq_embedU_S_S_eq_Z {dim : Nat} (q : Nat) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.S q : BaseUCom dim))
                      (Com.embedU (BaseUCom.S q)))
            (Com.embedU (BaseUCom.Z q)) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (S_S_eq_Z q))

/-- SKIP-as-left-identity lifted to density: `useq (embedU SKIP) (embedU c)
    ⩮ embedU c`. Lifts `useq_SKIP_l` via seq-merge + bridge. -/
theorem c_equiv_useq_embedU_SKIP_l {dim : Nat} (hd : 0 < dim) (c : BaseUCom dim) :
    c_equiv (Com.useq (Com.embedU (BaseUCom.SKIP : BaseUCom dim)) (Com.embedU c))
            (Com.embedU c) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (useq_SKIP_l hd c))

/-- SKIP-as-right-identity lifted to density. -/
theorem c_equiv_useq_embedU_SKIP_r {dim : Nat} (hd : 0 < dim) (c : BaseUCom dim) :
    c_equiv (Com.useq (Com.embedU c) (Com.embedU (BaseUCom.SKIP : BaseUCom dim)))
            (Com.embedU c) :=
  (c_equiv_useq_embedU_embedU _ _).trans (c_equiv_of_uc_equiv (useq_SKIP_r hd c))

/-- Demo of the `c_equiv_of_uc_equiv` bridge: the embedded T·T† circuit
    is density-equivalent to the embedded ID. 1-line application of
    the bridge to `T_TDAG_id`. Same pattern works with any of the rich
    UnitaryOps equivalences (involution-pair identities, niter periodics,
    etc.). -/
theorem c_equiv_embedU_T_TDAG_id {dim : Nat} (q : Nat) :
    c_equiv (Com.embedU (UCom.seq (BaseUCom.T q : BaseUCom dim) (BaseUCom.TDAG q)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (T_TDAG_id q)

/-- Pauli-X involution lifted to density semantics: `embedU(X q ; X q) ⩮
    embedU(ID q)`. 1-line application of the bridge to `X_X_id`. -/
theorem c_equiv_embedU_X_X_id {dim : Nat} (q : Nat) :
    c_equiv (Com.embedU (UCom.seq (BaseUCom.X q : BaseUCom dim) (BaseUCom.X q)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (X_X_id q)

/-- Pauli-Y involution lifted to density semantics. -/
theorem c_equiv_embedU_Y_Y_id {dim : Nat} (q : Nat) :
    c_equiv (Com.embedU (UCom.seq (BaseUCom.Y q : BaseUCom dim) (BaseUCom.Y q)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (Y_Y_id q)

/-- Pauli-Z involution lifted to density semantics. -/
theorem c_equiv_embedU_Z_Z_id {dim : Nat} (q : Nat) :
    c_equiv (Com.embedU (UCom.seq (BaseUCom.Z q : BaseUCom dim) (BaseUCom.Z q)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (Z_Z_id q)

/-- Hadamard involution lifted to density semantics. -/
theorem c_equiv_embedU_H_H_id {dim : Nat} (q : Nat) :
    c_equiv (Com.embedU (UCom.seq (BaseUCom.H q : BaseUCom dim) (BaseUCom.H q)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (H_H_id q)

/-- Toffoli involution lifted to density semantics: at the density layer,
    `embedU(CCX a b c ; CCX a b c) ⩮ embedU(ID 0)` for any `dim ≥ 1`.
    1-line application of `c_equiv_of_uc_equiv` to the unitary-level
    `CCX_CCX_id` in `Framework.PadAction`. -/
theorem c_equiv_embedU_CCX_CCX_id {dim : Nat} (a b c : Nat) (h0 : 0 < dim)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c_equiv (Com.embedU (UCom.seq (BaseUCom.CCX a b c : BaseUCom dim)
                                  (BaseUCom.CCX a b c)))
            (Com.embedU (BaseUCom.ID 0)) :=
  c_equiv_of_uc_equiv (CCX_CCX_id a b c h0 ha hb hc hab hac hbc)

/-- Toffoli control symmetry lifted to density semantics: at the
    density layer, `embedU (CCX a b c) ⩮ embedU (CCX b a c)`. 1-line
    application of `c_equiv_of_uc_equiv` to `CCX_control_symm_equiv`. -/
theorem c_equiv_embedU_CCX_control_symm {dim : Nat} (a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c_equiv (Com.embedU (BaseUCom.CCX a b c : BaseUCom dim))
            (Com.embedU (BaseUCom.CCX b a c)) :=
  c_equiv_of_uc_equiv (CCX_control_symm_equiv a b c ha hb hc hab hac hbc)

/-- T†·T inverse-pair lifted to density semantics. -/
theorem c_equiv_embedU_TDAG_T_id {dim : Nat} (q : Nat) :
    c_equiv (Com.embedU (UCom.seq (BaseUCom.TDAG q : BaseUCom dim) (BaseUCom.T q)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (TDAG_T_id q)

/-- S·S† inverse-pair lifted to density semantics. -/
theorem c_equiv_embedU_S_SDAG_id {dim : Nat} (q : Nat) :
    c_equiv (Com.embedU (UCom.seq (BaseUCom.S q : BaseUCom dim) (BaseUCom.SDAG q)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (S_SDAG_id q)

/-- S†·S inverse-pair lifted to density semantics. -/
theorem c_equiv_embedU_SDAG_S_id {dim : Nat} (q : Nat) :
    c_equiv (Com.embedU (UCom.seq (BaseUCom.SDAG q : BaseUCom dim) (BaseUCom.S q)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (SDAG_S_id q)

/-- niter T period-8 lifted to density semantics: `embedU(T⁸) ⩮ embedU(ID)`.
    1-line application of the bridge to `niter_eight_T_eq_ID`. Demonstrates
    that the niter periodic identities (not just inverse-pair compositions)
    also lift cleanly through the density bridge. -/
theorem c_equiv_embedU_niter_eight_T_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    c_equiv (Com.embedU (niter 8 (BaseUCom.T q : BaseUCom dim)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (niter_eight_T_eq_ID q hq)

/-- niter T† period-8 lifted to density semantics: `embedU(T†⁸) ⩮ embedU(ID)`. -/
theorem c_equiv_embedU_niter_eight_TDAG_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    c_equiv (Com.embedU (niter 8 (BaseUCom.TDAG q : BaseUCom dim)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (niter_eight_TDAG_eq_ID q hq)

/-- niter S period-4 lifted to density semantics: `embedU(S⁴) ⩮ embedU(ID)`. -/
theorem c_equiv_embedU_niter_four_S_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    c_equiv (Com.embedU (niter 4 (BaseUCom.S q : BaseUCom dim)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (niter_four_S_eq_ID q hq)

/-- niter S† period-4 lifted to density semantics: `embedU(S†⁴) ⩮ embedU(ID)`. -/
theorem c_equiv_embedU_niter_four_SDAG_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    c_equiv (Com.embedU (niter 4 (BaseUCom.SDAG q : BaseUCom dim)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (niter_four_SDAG_eq_ID q hq)

/-- niter X involution period-2 lifted to density semantics:
    `embedU(X²) ⩮ embedU(ID)`. First Pauli niter lift. -/
theorem c_equiv_embedU_niter_two_X_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    c_equiv (Com.embedU (niter 2 (BaseUCom.X q : BaseUCom dim)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (niter_two_X_eq_ID q hq)

/-- niter Y involution period-2 lifted to density semantics. -/
theorem c_equiv_embedU_niter_two_Y_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    c_equiv (Com.embedU (niter 2 (BaseUCom.Y q : BaseUCom dim)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (niter_two_Y_eq_ID q hq)

/-- niter Z involution period-2 lifted to density semantics. -/
theorem c_equiv_embedU_niter_two_Z_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    c_equiv (Com.embedU (niter 2 (BaseUCom.Z q : BaseUCom dim)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (niter_two_Z_eq_ID q hq)

/-- niter H involution period-2 lifted to density semantics.
    Completes the Pauli/H period-2 density lift set. -/
theorem c_equiv_embedU_niter_two_H_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    c_equiv (Com.embedU (niter 2 (BaseUCom.H q : BaseUCom dim)))
            (Com.embedU (BaseUCom.ID q)) :=
  c_equiv_of_uc_equiv (niter_two_H_eq_ID q hq)

/-- `c_eval` of skip is identity. -/
@[simp] theorem c_eval_skip {dim : Nat} (ρ : DensityMat dim) :
    c_eval (Com.cskip : BaseCom dim) ρ = ρ := rfl

/-- A simple measurement of qubit `n`: measure, discard outcome.
    -- SQIR/SQIR/DensitySem.v: `Definition measure n := meas n SKIP SKIP`. -/
def measure {dim : Nat} (n : Nat) : BaseCom dim := Com.meas n Com.cskip Com.cskip

/-- Density-matrix semantics of measurement: ρ ↦ P₁ ρ P₁† + P₀ ρ P₀†.
    -- SQIR/SQIR/DensitySem.v line 107: c_eval_measure. -/
theorem c_eval_measure {dim : Nat} (n : Nat) (ρ : DensityMat dim) :
    c_eval (measure n : BaseCom dim) ρ
      = proj n dim true * ρ * (proj n dim true).conjTranspose
        + proj n dim false * ρ * (proj n dim false).conjTranspose := rfl

/-- Additivity of `c_eval` in the density matrix: applying c to (ρ₁+ρ₂)
    gives c_eval c ρ₁ + c_eval c ρ₂. Companion to c_eval_smul; together
    they establish c_eval is a linear functional in ρ. -/
theorem c_eval_add {dim : Nat} (c : BaseCom dim) (ρ₁ ρ₂ : DensityMat dim) :
    c_eval c (ρ₁ + ρ₂) = c_eval c ρ₁ + c_eval c ρ₂ := by
  induction c generalizing ρ₁ ρ₂ with
  | cskip => rfl
  | useq c₁ c₂ ih₁ ih₂ =>
      show c_eval c₂ (c_eval c₁ (ρ₁ + ρ₂))
            = c_eval c₂ (c_eval c₁ ρ₁) + c_eval c₂ (c_eval c₁ ρ₂)
      rw [ih₁, ih₂]
  | embedU u =>
      show uc_eval u * (ρ₁ + ρ₂) * (uc_eval u).conjTranspose
            = uc_eval u * ρ₁ * (uc_eval u).conjTranspose
              + uc_eval u * ρ₂ * (uc_eval u).conjTranspose
      rw [Matrix.mul_add, Matrix.add_mul]
  | meas n c₁ c₂ ih₁ ih₂ =>
      show c_eval c₁ (proj n dim true * (ρ₁ + ρ₂) * (proj n dim true).conjTranspose)
            + c_eval c₂ (proj n dim false * (ρ₁ + ρ₂) * (proj n dim false).conjTranspose)
          = (c_eval c₁ (proj n dim true * ρ₁ * (proj n dim true).conjTranspose)
              + c_eval c₂ (proj n dim false * ρ₁ * (proj n dim false).conjTranspose))
            + (c_eval c₁ (proj n dim true * ρ₂ * (proj n dim true).conjTranspose)
              + c_eval c₂ (proj n dim false * ρ₂ * (proj n dim false).conjTranspose))
      rw [Matrix.mul_add, Matrix.add_mul, ih₁,
          Matrix.mul_add, Matrix.add_mul, ih₂]
      abel

/-- Linearity of `c_eval` in the density matrix: scaling ρ by k scales the
    result by k. Holds for every BaseCom (induction over c).
    -- SQIR/SQIR/DensitySem.v line 100: c_eval_scale. -/
theorem c_eval_smul {dim : Nat} (c : BaseCom dim) (k : ℂ) (ρ : DensityMat dim) :
    c_eval c (k • ρ) = k • c_eval c ρ := by
  induction c generalizing ρ with
  | cskip => rfl
  | useq c₁ c₂ ih₁ ih₂ =>
      show c_eval c₂ (c_eval c₁ (k • ρ)) = k • c_eval c₂ (c_eval c₁ ρ)
      rw [ih₁, ih₂]
  | embedU u =>
      show uc_eval u * (k • ρ) * (uc_eval u).conjTranspose
            = k • (uc_eval u * ρ * (uc_eval u).conjTranspose)
      rw [Matrix.mul_smul, Matrix.smul_mul]
  | meas n c₁ c₂ ih₁ ih₂ =>
      show c_eval c₁ (proj n dim true * (k • ρ) * (proj n dim true).conjTranspose)
            + c_eval c₂ (proj n dim false * (k • ρ) * (proj n dim false).conjTranspose)
          = k • (c_eval c₁ (proj n dim true * ρ * (proj n dim true).conjTranspose)
            + c_eval c₂ (proj n dim false * ρ * (proj n dim false).conjTranspose))
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
          ih₁, ih₂, smul_add]

/-- Negation passes through `c_eval` (corollary of c_eval_smul with k = -1). -/
theorem c_eval_neg {dim : Nat} (c : BaseCom dim) (ρ : DensityMat dim) :
    c_eval c (-ρ) = -c_eval c ρ := by
  rw [show (-ρ : DensityMat dim) = (-1 : ℂ) • ρ from by rw [neg_smul, one_smul]]
  rw [c_eval_smul, neg_smul, one_smul]

/-- Subtraction passes through `c_eval` (corollary of c_eval_add and c_eval_neg). -/
theorem c_eval_sub {dim : Nat} (c : BaseCom dim) (ρ₁ ρ₂ : DensityMat dim) :
    c_eval c (ρ₁ - ρ₂) = c_eval c ρ₁ - c_eval c ρ₂ := by
  simp only [sub_eq_add_neg]
  rw [c_eval_add, c_eval_neg]

/-- The zero density matrix is preserved by every program.
    -- SQIR/SQIR/DensitySem.v line 93: c_eval_0. -/
theorem c_eval_zero {dim : Nat} (c : BaseCom dim) :
    c_eval c (0 : DensityMat dim) = 0 := by
  induction c with
  | cskip => rfl
  | useq c₁ c₂ ih₁ ih₂ =>
      show c_eval c₂ (c_eval c₁ 0) = 0
      rw [ih₁, ih₂]
  | embedU u =>
      show uc_eval u * 0 * (uc_eval u).conjTranspose = 0
      simp [Matrix.mul_zero, Matrix.zero_mul]
  | meas n c₁ c₂ ih₁ ih₂ =>
      show c_eval c₁ (proj n dim true * 0 * (proj n dim true).conjTranspose)
            + c_eval c₂ (proj n dim false * 0 * (proj n dim false).conjTranspose) = 0
      rw [Matrix.mul_zero, Matrix.zero_mul, ih₁, Matrix.mul_zero, Matrix.zero_mul, ih₂,
          add_zero]

/-- `c_eval` distributes over Finset sums. Generalizes `c_eval_add` to
    arbitrary finite sums via Finset induction. -/
theorem c_eval_finset_sum {dim : Nat} (c : BaseCom dim)
    {α : Type*} (s : Finset α) (f : α → DensityMat dim) :
    c_eval c (∑ i ∈ s, f i) = ∑ i ∈ s, c_eval c (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [c_eval_zero]
  · intro x s hx ih
    rw [Finset.sum_insert hx, c_eval_add, ih, Finset.sum_insert hx]

/-- Measurement with identical branches: when both branches are the same
    command `c`, the projections sum first inside, then `c_eval c` is
    applied — i.e., `c` is unconditionally applied to the measure-and-
    forget channel output. Direct application of `c_eval_add`. -/
theorem c_eval_meas_same {dim : Nat} (n : Nat) (c : BaseCom dim)
    (ρ : DensityMat dim) :
    c_eval (Com.meas n c c) ρ
      = c_eval c (proj n dim true * ρ * (proj n dim true).conjTranspose
                  + proj n dim false * ρ * (proj n dim false).conjTranspose) := by
  show c_eval c _ + c_eval c _ = c_eval c (_ + _)
  exact (c_eval_add c _ _).symm

/-- Operational refactoring: `meas n c c ⩮ measure n ; c`. When both
    measurement branches are the same command, the measurement can be
    extracted as a separate prefix and then `c` applied to the result.
    Direct chain of `c_eval_meas_same` with the definitional unfolding
    of useq. -/
theorem c_equiv_meas_same_eq_measure_useq {dim : Nat} (n : Nat) (c : BaseCom dim) :
    c_equiv (Com.meas n c c) (Com.useq (measure n) c) := by
  funext ρ
  rw [c_eval_meas_same]
  rfl

end BaseCom
end FormalRV.Framework
