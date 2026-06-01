/-
  FormalRV.Framework.NDSem — non-deterministic semantics for `Com`.

  Lean translation of `SQIR/SQIR/NDSem.v` (138 LOC of Coq).
  Defines the operational semantics of `Com` (programs with measurement)
  as a relation `nd_eval c ψ ψ'` meaning "starting from state ψ, program c
  can produce state ψ'". The relation is non-deterministic: measurement
  branches.

  Status: scaffolding. The inductive `nd_eval` is defined; key structural
  lemmas (assoc, equiv refl/sym/trans, congruence) are sorried for the
  pieces that need partial-trace / norm reasoning that mathlib's
  matrix-norm API requires.
-/
import FormalRV.Core.UnitaryOps
import FormalRV.Core.PadAction

namespace FormalRV.Framework

/-- A `dim`-qubit pure state vector: a `2^dim`-dimensional complex column. -/
abbrev StateVec (dim : Nat) := Matrix (Fin (2^dim)) (Fin 1) ℂ

/-- The k-th computational basis state |k⟩ for `k : Fin (2^dim)`. -/
noncomputable def basisState {dim : Nat} (k : Fin (2^dim)) : StateVec dim :=
  fun i _ => if i = k then 1 else 0

/-- Probability of observing computational-basis outcome `k` when measuring
    state `ψ`: `|⟨k | ψ⟩|² = |ψ k 0|²`. -/
noncomputable def prob_outcome {dim : Nat} (ψ : StateVec dim) (k : Fin (2^dim)) : ℝ :=
  Complex.normSq (ψ k 0)

/-- The "all zeros" basis state |0...0⟩. -/
noncomputable def zeroState (dim : Nat) : StateVec dim :=
  basisState ⟨0, Nat.two_pow_pos dim⟩

open BaseUCom in
/-- Operational semantics for `Com` (with measurement).
    `nd_eval c ψ ψ'` ↔ "from input ψ, program c can output ψ'".
    Non-deterministic on `meas` branches. -/
inductive nd_eval {dim : Nat} : BaseCom dim → StateVec dim → StateVec dim → Prop
  | cskip {ψ : StateVec dim} : nd_eval Com.cskip ψ ψ
  | embedU (u : BaseUCom dim) (ψ : StateVec dim) :
      nd_eval (Com.embedU u) ψ (uc_eval u * ψ)
  | meas_t {n : Nat} {c₁ c₂ : BaseCom dim} {ψ ψ'' : StateVec dim} :
      nd_eval c₁ (BaseUCom.proj n dim true * ψ) ψ'' →
      nd_eval (Com.meas n c₁ c₂) ψ ψ''
  | meas_f {n : Nat} {c₁ c₂ : BaseCom dim} {ψ ψ'' : StateVec dim} :
      nd_eval c₂ (BaseUCom.proj n dim false * ψ) ψ'' →
      nd_eval (Com.meas n c₁ c₂) ψ ψ''
  | useq {c₁ c₂ : BaseCom dim} {ψ ψ' ψ'' : StateVec dim} :
      nd_eval c₁ ψ ψ' → nd_eval c₂ ψ' ψ'' →
      nd_eval (Com.useq c₁ c₂) ψ ψ''

namespace BaseCom

/-- `Com` equivalence under the non-deterministic semantics. -/
def nd_equiv {dim : Nat} (c₁ c₂ : BaseCom dim) : Prop :=
  ∀ (ψ ψ' : StateVec dim), nd_eval c₁ ψ ψ' ↔ nd_eval c₂ ψ ψ'

scoped infix:50 " ≣ " => nd_equiv

/-- Reflexivity. -/
theorem nd_equiv_refl {dim : Nat} (c : BaseCom dim) : nd_equiv c c :=
  fun _ _ => Iff.rfl

/-- Symmetry. -/
theorem nd_equiv_sym {dim : Nat} {c₁ c₂ : BaseCom dim}
    (h : nd_equiv c₁ c₂) : nd_equiv c₂ c₁ :=
  fun ψ ψ' => (h ψ ψ').symm

/-- Transitivity. -/
theorem nd_equiv_trans {dim : Nat} {c₁ c₂ c₃ : BaseCom dim}
    (h₁₂ : nd_equiv c₁ c₂) (h₂₃ : nd_equiv c₂ c₃) : nd_equiv c₁ c₃ :=
  fun ψ ψ' => (h₁₂ ψ ψ').trans (h₂₃ ψ ψ')

/-- `useq` associativity for `Com`. -/
theorem nd_useq_assoc {dim : Nat} (c₁ c₂ c₃ : BaseCom dim) :
    nd_equiv (Com.useq (Com.useq c₁ c₂) c₃) (Com.useq c₁ (Com.useq c₂ c₃)) := by
  intro ψ ψ'
  constructor
  · intro h
    cases h with
    | useq h_inner h₃ =>
        cases h_inner with
        | useq h₁ h₂ => exact .useq h₁ (.useq h₂ h₃)
  · intro h
    cases h with
    | useq h₁ h_inner =>
        cases h_inner with
        | useq h₂ h₃ => exact .useq (.useq h₁ h₂) h₃

/-- `useq` left-associativity (reverse direction): `c₁;(c₂;c₃) ≡ (c₁;c₂);c₃`.
    Direct corollary of `nd_useq_assoc` via `nd_equiv_sym`. -/
theorem nd_useq_assoc_l {dim : Nat} (c₁ c₂ c₃ : BaseCom dim) :
    nd_equiv (Com.useq c₁ (Com.useq c₂ c₃)) (Com.useq (Com.useq c₁ c₂) c₃) :=
  nd_equiv_sym (nd_useq_assoc c₁ c₂ c₃)

/-- Sequential composition is congruent under `nd_equiv`.
    -- SQIR/SQIR/NDSem.v line 75: nd_seq_congruence. -/
theorem nd_useq_congr {dim : Nat} (c₁ c₁' c₂ c₂' : BaseCom dim)
    (h₁ : nd_equiv c₁ c₁') (h₂ : nd_equiv c₂ c₂') :
    nd_equiv (Com.useq c₁ c₂) (Com.useq c₁' c₂') := by
  intro ψ ψ'
  constructor
  · intro h
    cases h with
    | useq h_left h_right =>
        exact .useq ((h₁ _ _).mp h_left) ((h₂ _ _).mp h_right)
  · intro h
    cases h with
    | useq h_left h_right =>
        exact .useq ((h₁ _ _).mpr h_left) ((h₂ _ _).mpr h_right)

/-- `cskip ; c ≡ c` — left identity of useq under nd_equiv. -/
theorem nd_cskip_useq {dim : Nat} (c : BaseCom dim) :
    nd_equiv (Com.useq Com.cskip c) c := by
  intro ψ ψ'
  constructor
  · intro h
    cases h with
    | useq h_skip h_c =>
        cases h_skip
        exact h_c
  · intro h
    exact .useq .cskip h

/-- `c ; cskip ≡ c` — right identity of useq under nd_equiv. -/
theorem nd_useq_cskip {dim : Nat} (c : BaseCom dim) :
    nd_equiv (Com.useq c Com.cskip) c := by
  intro ψ ψ'
  constructor
  · intro h
    cases h with
    | useq h_c h_skip =>
        cases h_skip
        exact h_c
  · intro h
    exact .useq h .cskip

/-- Inversion lemma: `nd_eval cskip ψ ψ'` iff `ψ = ψ'`. -/
theorem nd_eval_cskip_iff {dim : Nat} (ψ ψ' : StateVec dim) :
    nd_eval (Com.cskip : BaseCom dim) ψ ψ' ↔ ψ = ψ' := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact .cskip

/-- Inversion lemma: `nd_eval (embedU u) ψ ψ'` iff `ψ' = uc_eval u * ψ`.
    Useful for reasoning about unitary commands inside non-deterministic
    semantics — connects the unitary semantics to the operational. -/
theorem nd_eval_embedU_iff {dim : Nat} (u : BaseUCom dim) (ψ ψ' : StateVec dim) :
    nd_eval (Com.embedU u) ψ ψ' ↔ ψ' = uc_eval u * ψ := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact .embedU u ψ

/-- Bridge from unitary semantics to non-deterministic semantics: if two
    unitary commands are `UCom.equiv` (have equal `uc_eval`), then their
    embeddings into `Com` are `nd_equiv`. The natural lifting of unitary
    equivalence through the operational `ψ ↦ U ψ` action. -/
theorem nd_equiv_of_uc_equiv {dim : Nat} {u₁ u₂ : BaseUCom dim}
    (h : UCom.equiv u₁ u₂) :
    nd_equiv (Com.embedU u₁) (Com.embedU u₂) := by
  intro ψ ψ'
  rw [nd_eval_embedU_iff, nd_eval_embedU_iff, h]

/-- Left-position bridge composition: substituting an equivalent unitary
    in the LEFT position of a useq preserves `nd_equiv`. ND analog of
    `c_equiv_useq_embedU_left`. -/
theorem nd_equiv_useq_embedU_left {dim : Nat} (c : BaseCom dim)
    {u₁ u₂ : BaseUCom dim} (h : UCom.equiv u₁ u₂) :
    nd_equiv (Com.useq (Com.embedU u₁) c) (Com.useq (Com.embedU u₂) c) :=
  nd_useq_congr _ _ _ _ (nd_equiv_of_uc_equiv h) (nd_equiv_refl c)

/-- Right-position bridge composition: symmetric companion. -/
theorem nd_equiv_useq_embedU_right {dim : Nat} (c : BaseCom dim)
    {u₁ u₂ : BaseUCom dim} (h : UCom.equiv u₁ u₂) :
    nd_equiv (Com.useq c (Com.embedU u₁)) (Com.useq c (Com.embedU u₂)) :=
  nd_useq_congr _ _ _ _ (nd_equiv_refl c) (nd_equiv_of_uc_equiv h)

/-- Lifting `invert_invert` through `embedU`: `embedU(invert(invert c)) ≣
    embedU(c)` at the ND layer. ND analog of
    `c_equiv_embedU_invert_invert`. -/
theorem nd_equiv_embedU_invert_invert {dim : Nat} (c : BaseUCom dim) :
    nd_equiv (Com.embedU (BaseUCom.invert (BaseUCom.invert c))) (Com.embedU c) := by
  rw [BaseUCom.invert_invert]
  exact nd_equiv_refl _


/-- Demo of the `nd_equiv_of_uc_equiv` bridge: the embedded T·T† circuit
    is ND-equivalent to the embedded ID. 1-line application of the bridge
    to `T_TDAG_id`. Mirror of `c_equiv_embedU_T_TDAG_id` from DensitySem. -/
theorem nd_equiv_embedU_T_TDAG_id {dim : Nat} (q : Nat) :
    nd_equiv (Com.embedU (UCom.seq (BaseUCom.T q : BaseUCom dim) (BaseUCom.TDAG q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (T_TDAG_id q)

/-- T†·T inverse-pair lifted to ND semantics. -/
theorem nd_equiv_embedU_TDAG_T_id {dim : Nat} (q : Nat) :
    nd_equiv (Com.embedU (UCom.seq (BaseUCom.TDAG q : BaseUCom dim) (BaseUCom.T q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (TDAG_T_id q)

/-- S·S† inverse-pair lifted to ND semantics. -/
theorem nd_equiv_embedU_S_SDAG_id {dim : Nat} (q : Nat) :
    nd_equiv (Com.embedU (UCom.seq (BaseUCom.S q : BaseUCom dim) (BaseUCom.SDAG q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (S_SDAG_id q)

/-- S†·S inverse-pair lifted to ND semantics. -/
theorem nd_equiv_embedU_SDAG_S_id {dim : Nat} (q : Nat) :
    nd_equiv (Com.embedU (UCom.seq (BaseUCom.SDAG q : BaseUCom dim) (BaseUCom.S q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (SDAG_S_id q)

/-- Pauli-X involution lifted to ND semantics. -/
theorem nd_equiv_embedU_X_X_id {dim : Nat} (q : Nat) :
    nd_equiv (Com.embedU (UCom.seq (BaseUCom.X q : BaseUCom dim) (BaseUCom.X q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (X_X_id q)

/-- Pauli-Y involution lifted to ND semantics. -/
theorem nd_equiv_embedU_Y_Y_id {dim : Nat} (q : Nat) :
    nd_equiv (Com.embedU (UCom.seq (BaseUCom.Y q : BaseUCom dim) (BaseUCom.Y q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (Y_Y_id q)

/-- Pauli-Z involution lifted to ND semantics. -/
theorem nd_equiv_embedU_Z_Z_id {dim : Nat} (q : Nat) :
    nd_equiv (Com.embedU (UCom.seq (BaseUCom.Z q : BaseUCom dim) (BaseUCom.Z q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (Z_Z_id q)

/-- Hadamard involution lifted to ND semantics. -/
theorem nd_equiv_embedU_H_H_id {dim : Nat} (q : Nat) :
    nd_equiv (Com.embedU (UCom.seq (BaseUCom.H q : BaseUCom dim) (BaseUCom.H q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (H_H_id q)

/-- Toffoli involution lifted to ND semantics: at the non-deterministic
    layer, `embedU(CCX a b c ; CCX a b c) ⩮ embedU(ID 0)` for any
    `dim ≥ 1`. 1-line application of `nd_equiv_of_uc_equiv` to the
    unitary-level `CCX_CCX_id` in `Framework.PadAction`. -/
theorem nd_equiv_embedU_CCX_CCX_id {dim : Nat} (a b c : Nat) (h0 : 0 < dim)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    nd_equiv (Com.embedU (UCom.seq (BaseUCom.CCX a b c : BaseUCom dim)
                                   (BaseUCom.CCX a b c)))
             (Com.embedU (BaseUCom.ID 0)) :=
  nd_equiv_of_uc_equiv (CCX_CCX_id a b c h0 ha hb hc hab hac hbc)

/-- Toffoli control symmetry lifted to ND semantics: at the ND layer,
    `embedU (CCX a b c) ⩮ embedU (CCX b a c)`. 1-line application of
    `nd_equiv_of_uc_equiv` to `CCX_control_symm_equiv`. -/
theorem nd_equiv_embedU_CCX_control_symm {dim : Nat} (a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    nd_equiv (Com.embedU (BaseUCom.CCX a b c : BaseUCom dim))
             (Com.embedU (BaseUCom.CCX b a c)) :=
  nd_equiv_of_uc_equiv (CCX_control_symm_equiv a b c ha hb hc hab hac hbc)

/-- niter T period-8 lifted to ND semantics. -/
theorem nd_equiv_embedU_niter_eight_T_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    nd_equiv (Com.embedU (BaseUCom.niter 8 (BaseUCom.T q : BaseUCom dim)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (BaseUCom.niter_eight_T_eq_ID q hq)

/-- niter T† period-8 lifted to ND semantics. -/
theorem nd_equiv_embedU_niter_eight_TDAG_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    nd_equiv (Com.embedU (BaseUCom.niter 8 (BaseUCom.TDAG q : BaseUCom dim)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (BaseUCom.niter_eight_TDAG_eq_ID q hq)

/-- niter S period-4 lifted to ND semantics. -/
theorem nd_equiv_embedU_niter_four_S_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    nd_equiv (Com.embedU (BaseUCom.niter 4 (BaseUCom.S q : BaseUCom dim)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (BaseUCom.niter_four_S_eq_ID q hq)

/-- niter S† period-4 lifted to ND semantics. -/
theorem nd_equiv_embedU_niter_four_SDAG_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    nd_equiv (Com.embedU (BaseUCom.niter 4 (BaseUCom.SDAG q : BaseUCom dim)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (BaseUCom.niter_four_SDAG_eq_ID q hq)

/-- niter X involution period-2 lifted to ND semantics. -/
theorem nd_equiv_embedU_niter_two_X_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    nd_equiv (Com.embedU (BaseUCom.niter 2 (BaseUCom.X q : BaseUCom dim)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (BaseUCom.niter_two_X_eq_ID q hq)

/-- niter Y involution period-2 lifted to ND semantics. -/
theorem nd_equiv_embedU_niter_two_Y_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    nd_equiv (Com.embedU (BaseUCom.niter 2 (BaseUCom.Y q : BaseUCom dim)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (BaseUCom.niter_two_Y_eq_ID q hq)

/-- niter Z involution period-2 lifted to ND semantics. -/
theorem nd_equiv_embedU_niter_two_Z_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    nd_equiv (Com.embedU (BaseUCom.niter 2 (BaseUCom.Z q : BaseUCom dim)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (BaseUCom.niter_two_Z_eq_ID q hq)

/-- niter H involution period-2 lifted to ND semantics.
    Completes the ND-side niter periodic lift set. -/
theorem nd_equiv_embedU_niter_two_H_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    nd_equiv (Com.embedU (BaseUCom.niter 2 (BaseUCom.H q : BaseUCom dim)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (BaseUCom.niter_two_H_eq_ID q hq)


/-- Inversion lemma for sequence composition: `nd_eval (useq c₁ c₂) ψ ψ''`
    iff there exists an intermediate state `ψ'` reachable from `ψ` via
    `c₁` from which `ψ''` is reachable via `c₂`. -/
theorem nd_eval_useq_iff {dim : Nat} (c₁ c₂ : BaseCom dim)
    (ψ ψ'' : StateVec dim) :
    nd_eval (Com.useq c₁ c₂) ψ ψ''
      ↔ ∃ ψ' : StateVec dim, nd_eval c₁ ψ ψ' ∧ nd_eval c₂ ψ' ψ'' := by
  constructor
  · intro h
    cases h with
    | useq h₁ h₂ => exact ⟨_, h₁, h₂⟩
  · intro ⟨ψ', h₁, h₂⟩
    exact .useq h₁ h₂

/-- Inversion lemma for measurement: `nd_eval (meas n c₁ c₂) ψ ψ''` iff
    one of the two outcomes (true or false) leads to ψ'' via the
    corresponding branch program. -/
theorem nd_eval_meas_iff {dim : Nat} (n : Nat) (c₁ c₂ : BaseCom dim)
    (ψ ψ'' : StateVec dim) :
    nd_eval (Com.meas n c₁ c₂) ψ ψ''
      ↔ nd_eval c₁ (BaseUCom.proj n dim true * ψ) ψ''
        ∨ nd_eval c₂ (BaseUCom.proj n dim false * ψ) ψ'' := by
  constructor
  · intro h
    cases h with
    | meas_t h₁ => exact Or.inl h₁
    | meas_f h₂ => exact Or.inr h₂
  · intro h
    cases h with
    | inl h₁ => exact .meas_t h₁
    | inr h₂ => exact .meas_f h₂

/-- `embedU(ID q)` is a left-identity of `useq` at the ND layer
    (when `q < dim`). ND analog of `c_equiv_useq_embedU_ID_l`. -/
theorem nd_equiv_useq_embedU_ID_l {dim : Nat} (q : Nat) (hq : q < dim)
    (c : BaseCom dim) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.ID q)) c) c := by
  intro ψ ψ''
  rw [nd_eval_useq_iff]
  constructor
  · rintro ⟨ψ', h_embed, h_c⟩
    rw [nd_eval_embedU_iff, uc_eval_ID_eq_one hq, Matrix.one_mul] at h_embed
    subst h_embed
    exact h_c
  · intro h
    exact ⟨ψ, by rw [nd_eval_embedU_iff, uc_eval_ID_eq_one hq, Matrix.one_mul], h⟩

/-- `embedU(ID q)` is also a right-identity of `useq` at the ND layer.
    Symmetric companion of `nd_equiv_useq_embedU_ID_l`. -/
theorem nd_equiv_useq_embedU_ID_r {dim : Nat} (q : Nat) (hq : q < dim)
    (c : BaseCom dim) :
    nd_equiv (Com.useq c (Com.embedU (BaseUCom.ID q))) c := by
  intro ψ ψ''
  rw [nd_eval_useq_iff]
  constructor
  · rintro ⟨ψ', h_c, h_embed⟩
    rw [nd_eval_embedU_iff, uc_eval_ID_eq_one hq, Matrix.one_mul] at h_embed
    subst h_embed
    exact h_c
  · intro h
    exact ⟨ψ'', h, by rw [nd_eval_embedU_iff, uc_eval_ID_eq_one hq, Matrix.one_mul]⟩

/-- Sequencing two embedded unitaries is the embedding of their sequence
    at the ND layer. ND analog of `c_equiv_useq_embedU_embedU`. -/
theorem nd_equiv_useq_embedU_embedU {dim : Nat} (u₁ u₂ : BaseUCom dim) :
    nd_equiv (Com.useq (Com.embedU u₁) (Com.embedU u₂))
             (Com.embedU (UCom.seq u₁ u₂)) := by
  intro ψ ψ''
  rw [nd_eval_useq_iff, nd_eval_embedU_iff]
  constructor
  · rintro ⟨ψ', h1, h2⟩
    rw [nd_eval_embedU_iff] at h1 h2
    subst h1
    rw [h2]
    show uc_eval u₂ * (uc_eval u₁ * ψ) = uc_eval (UCom.seq u₁ u₂) * ψ
    show _ = (uc_eval u₂ * uc_eval u₁) * ψ
    rw [Matrix.mul_assoc]
  · intro h
    refine ⟨uc_eval u₁ * ψ, ?_, ?_⟩
    · rw [nd_eval_embedU_iff]
    · rw [nd_eval_embedU_iff, h]
      show (uc_eval u₂ * uc_eval u₁) * ψ = uc_eval u₂ * (uc_eval u₁ * ψ)
      rw [Matrix.mul_assoc]

/-- T·T† inverse pair via ND seq-merge + bridge. -/
theorem nd_equiv_useq_embedU_T_TDAG {dim : Nat} (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.T q : BaseUCom dim))
                       (Com.embedU (BaseUCom.TDAG q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _) (nd_equiv_of_uc_equiv (T_TDAG_id q))

/-- Pauli-X involution via ND seq-merge + bridge. -/
theorem nd_equiv_useq_embedU_X_X {dim : Nat} (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.X q : BaseUCom dim))
                       (Com.embedU (BaseUCom.X q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _) (nd_equiv_of_uc_equiv (X_X_id q))

/-- Pauli-Y involution via ND seq-merge + bridge. -/
theorem nd_equiv_useq_embedU_Y_Y {dim : Nat} (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.Y q : BaseUCom dim))
                       (Com.embedU (BaseUCom.Y q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _) (nd_equiv_of_uc_equiv (Y_Y_id q))

/-- Pauli-Z involution via ND seq-merge + bridge. -/
theorem nd_equiv_useq_embedU_Z_Z {dim : Nat} (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.Z q : BaseUCom dim))
                       (Com.embedU (BaseUCom.Z q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _) (nd_equiv_of_uc_equiv (Z_Z_id q))

/-- Hadamard involution via ND seq-merge + bridge. -/
theorem nd_equiv_useq_embedU_H_H {dim : Nat} (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.H q : BaseUCom dim))
                       (Com.embedU (BaseUCom.H q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _) (nd_equiv_of_uc_equiv (H_H_id q))

/-- Toffoli involution via ND seq-merge + bridge: at the ND layer,
    `useq (embedU (CCX a b c)) (embedU (CCX a b c)) ⩮ embedU (ID 0)`
    when `dim ≥ 1`. Mirror of `c_equiv_useq_embedU_CCX_CCX` from
    DensitySem; same construction with `nd_equiv_*` primitives. -/
theorem nd_equiv_useq_embedU_CCX_CCX {dim : Nat} (a b c : Nat) (h0 : 0 < dim)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.CCX a b c : BaseUCom dim))
                       (Com.embedU (BaseUCom.CCX a b c)))
             (Com.embedU (BaseUCom.ID 0)) :=
  nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _)
    (nd_equiv_of_uc_equiv (CCX_CCX_id a b c h0 ha hb hc hab hac hbc))

/-- T†·T inverse pair via ND seq-merge + bridge. -/
theorem nd_equiv_useq_embedU_TDAG_T {dim : Nat} (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.TDAG q : BaseUCom dim))
                       (Com.embedU (BaseUCom.T q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _) (nd_equiv_of_uc_equiv (TDAG_T_id q))

/-- S·S† inverse pair via ND seq-merge + bridge. -/
theorem nd_equiv_useq_embedU_S_SDAG {dim : Nat} (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.S q : BaseUCom dim))
                       (Com.embedU (BaseUCom.SDAG q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _) (nd_equiv_of_uc_equiv (S_SDAG_id q))

/-- S†·S inverse pair via ND seq-merge + bridge. -/
theorem nd_equiv_useq_embedU_SDAG_S {dim : Nat} (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.SDAG q : BaseUCom dim))
                       (Com.embedU (BaseUCom.S q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _) (nd_equiv_of_uc_equiv (SDAG_S_id q))

/-- Hadamard interchange at the ND layer: lifts `H_comm_Z` via the
    seq-merge → bridge → seq-merge⁻¹ chain. ND analog of
    `c_equiv_useq_embedU_H_Z_eq_X_H`. -/
theorem nd_equiv_useq_embedU_H_Z_eq_X_H {dim : Nat} (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.H q : BaseUCom dim))
                       (Com.embedU (BaseUCom.Z q)))
             (Com.useq (Com.embedU (BaseUCom.X q))
                       (Com.embedU (BaseUCom.H q))) :=
  nd_equiv_trans
    (nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _)
                    (nd_equiv_of_uc_equiv (H_comm_Z q)))
    (nd_equiv_sym (nd_equiv_useq_embedU_embedU _ _))

/-- Dual Hadamard interchange at the ND layer. -/
theorem nd_equiv_useq_embedU_H_X_eq_Z_H {dim : Nat} (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.H q : BaseUCom dim))
                       (Com.embedU (BaseUCom.X q)))
             (Com.useq (Com.embedU (BaseUCom.Z q))
                       (Com.embedU (BaseUCom.H q))) :=
  nd_equiv_trans
    (nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _)
                    (nd_equiv_of_uc_equiv (H_comm_X q)))
    (nd_equiv_sym (nd_equiv_useq_embedU_embedU _ _))

/-- Z-rotation composition lifted to ND. ND analog of
    `c_equiv_useq_embedU_Rz_Rz_add`. -/
theorem nd_equiv_useq_embedU_Rz_Rz_add {dim : Nat} (θ θ' : ℝ) (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.Rz θ q : BaseUCom dim))
                       (Com.embedU (BaseUCom.Rz θ' q)))
             (Com.embedU (BaseUCom.Rz (θ + θ') q)) :=
  nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _)
                 (nd_equiv_of_uc_equiv (Rz_Rz_add q θ θ'))

/-- Parametric Rz cancellation lifted to ND. ND analog of
    `c_equiv_useq_embedU_Rz_neg_id`. -/
theorem nd_equiv_useq_embedU_Rz_neg_id {dim : Nat} (θ : ℝ) (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.Rz θ q : BaseUCom dim))
                       (Com.embedU (BaseUCom.Rz (-θ) q)))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _)
                 (nd_equiv_of_uc_equiv (Rz_neg_id q θ))

/-- Trivial Z-rotation = ID at ND: `embedU(Rz 0 q) ≣ embedU(ID q)`.
    ND analog of `c_equiv_embedU_Rz_zero_eq_ID`. -/
theorem nd_equiv_embedU_Rz_zero_eq_ID {dim : Nat} (q : Nat) :
    nd_equiv (Com.embedU (BaseUCom.Rz 0 q : BaseUCom dim))
             (Com.embedU (BaseUCom.ID q)) :=
  nd_equiv_of_uc_equiv (Rz_0_id q)

/-- T·T = S at ND: ND analog of `c_equiv_useq_embedU_T_T_eq_S`. -/
theorem nd_equiv_useq_embedU_T_T_eq_S {dim : Nat} (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.T q : BaseUCom dim))
                       (Com.embedU (BaseUCom.T q)))
             (Com.embedU (BaseUCom.S q)) :=
  nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _)
                 (nd_equiv_of_uc_equiv (T_T_eq_S q))

/-- S·S = Z at ND: ND analog of `c_equiv_useq_embedU_S_S_eq_Z`. -/
theorem nd_equiv_useq_embedU_S_S_eq_Z {dim : Nat} (q : Nat) :
    nd_equiv (Com.useq (Com.embedU (BaseUCom.S q : BaseUCom dim))
                       (Com.embedU (BaseUCom.S q)))
             (Com.embedU (BaseUCom.Z q)) :=
  nd_equiv_trans (nd_equiv_useq_embedU_embedU _ _)
                 (nd_equiv_of_uc_equiv (S_S_eq_Z q))

/-- Measurement is congruent under `nd_equiv` on each branch. ND analog of
    `c_meas_congr` from DensitySem. -/
theorem nd_meas_congr {dim : Nat} (n : Nat) {c₁ c₁' c₂ c₂' : BaseCom dim}
    (h₁ : nd_equiv c₁ c₁') (h₂ : nd_equiv c₂ c₂') :
    nd_equiv (Com.meas n c₁ c₂) (Com.meas n c₁' c₂') := by
  intro ψ ψ'
  rw [nd_eval_meas_iff, nd_eval_meas_iff]
  exact ⟨fun h => h.elim (fun h => Or.inl ((h₁ _ _).mp h))
                          (fun h => Or.inr ((h₂ _ _).mp h)),
         fun h => h.elim (fun h => Or.inl ((h₁ _ _).mpr h))
                          (fun h => Or.inr ((h₂ _ _).mpr h))⟩

/-- Operational refactoring: `meas n c c ≣ (measure n) ; c` at the ND
    layer (where `measure n := meas n cskip cskip` per DensitySem). The
    forward direction picks the same branch on the right; the reverse
    direction destructures the cskip witnesses and case-splits on the
    intermediate state. ND analog of `c_equiv_meas_same_eq_measure_useq`. -/
theorem nd_equiv_meas_same_eq_measure_useq {dim : Nat} (n : Nat) (c : BaseCom dim) :
    nd_equiv (Com.meas n c c)
             (Com.useq (Com.meas n Com.cskip Com.cskip) c) := by
  intro ψ ψ''
  rw [nd_eval_meas_iff, nd_eval_useq_iff]
  constructor
  · rintro (h_t | h_f)
    · exact ⟨_, .meas_t .cskip, h_t⟩
    · exact ⟨_, .meas_f .cskip, h_f⟩
  · rintro ⟨ψ', h_meas, h_c⟩
    rw [nd_eval_meas_iff] at h_meas
    rcases h_meas with h_t | h_f
    · rw [nd_eval_cskip_iff] at h_t; subst h_t; exact Or.inl h_c
    · rw [nd_eval_cskip_iff] at h_f; subst h_f; exact Or.inr h_c

end BaseCom
end FormalRV.Framework
