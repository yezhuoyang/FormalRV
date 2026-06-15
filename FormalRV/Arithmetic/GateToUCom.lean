/-
  FormalRV.BQAlgo.GateToUCom — translation from the BQ-Algo `Gate` IR
  (used for cost accounting + optimization) to the Framework `BaseUCom`
  (used for semantic reasoning).

  The translation is faithful in the obvious sense: each `Gate`
  constructor maps to its `BaseUCom` analog, and `seq` becomes
  `UCom.seq`. This enables lifting BQ-Algo optimization theorems
  (tcount/gcount monotonicity) to BaseUCom semantic-preservation
  proofs via the existing `Framework` layer.

  Status: translation function + structural unfolding lemmas. Semantic
  preservation theorems (e.g., `uc_eval (toUCom (optimize_full g)) =
  uc_eval (toUCom g)`) are the natural next milestones.
-/
import FormalRV.Core.Gate
import FormalRV.Core.QuantumGate
import FormalRV.Core.PadAction
-- NOTE: this import is needed for the generic `Gate` optimizer
-- (`optimize_ccx_pair_top`, `optimize_full`, `optimize_to_fixpoint`,
-- `has_ccx_pair`, `assoc_right_step`, ...), which currently lives in
-- the Cuccaro module file. The Cuccaro-specific corollaries of this
-- bridge live in `FormalRV.Arithmetic.Cuccaro.CuccaroUComBridge`.
import FormalRV.Arithmetic.Cuccaro.Cuccaro

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- Translate a BQ-Algo `Gate` into a `BaseUCom dim`. Identity, X, CNOT,
    and Toffoli have direct analogs; `Gate.seq` becomes `UCom.seq`.
    Marked `noncomputable` because `BaseUCom` carries real-valued
    matrix data downstream. -/
noncomputable def Gate.toUCom (dim : Nat) : Gate → BaseUCom dim
  | Gate.I            => BaseUCom.ID 0
  | Gate.X q          => BaseUCom.X q
  | Gate.CX c t       => BaseUCom.CNOT c t
  | Gate.CCX a b c    => BaseUCom.CCX a b c
  | Gate.seq g₁ g₂    => UCom.seq (Gate.toUCom dim g₁) (Gate.toUCom dim g₂)

/-! ## Structural unfolding lemmas (rfl-trivial) -/

@[simp] theorem Gate.toUCom_I (dim : Nat) :
    Gate.toUCom dim Gate.I = (BaseUCom.ID 0 : BaseUCom dim) := rfl

@[simp] theorem Gate.toUCom_X (dim q : Nat) :
    Gate.toUCom dim (Gate.X q) = (BaseUCom.X q : BaseUCom dim) := rfl

@[simp] theorem Gate.toUCom_CX (dim c t : Nat) :
    Gate.toUCom dim (Gate.CX c t) = (BaseUCom.CNOT c t : BaseUCom dim) := rfl

@[simp] theorem Gate.toUCom_CCX (dim a b c : Nat) :
    Gate.toUCom dim (Gate.CCX a b c) = (BaseUCom.CCX a b c : BaseUCom dim) :=
  rfl

@[simp] theorem Gate.toUCom_seq (dim : Nat) (g₁ g₂ : Gate) :
    Gate.toUCom dim (Gate.seq g₁ g₂)
      = UCom.seq (Gate.toUCom dim g₁) (Gate.toUCom dim g₂) := rfl

/-! ## Semantic preservation: the CCX-pair case

    The single most interesting case for `optimize_ccx_pair_top`:
    when it fires on a matching CCX-CCX pair, the output `I` has the
    same `uc_eval` as the input `seq CCX CCX`. The bridge is
    `CCX_CCX_eq_one` from `Framework.PadAction`. -/

/-- Semantic preservation of the top-level CCX-pair rewrite on the
    matching-triple case. uc_eval of the optimized output (which is
    `BaseUCom.ID 0`) equals uc_eval of the input (`UCom.seq CCX CCX`)
    — both reduce to the identity matrix. -/
theorem uc_eval_toUCom_optimize_ccx_pair_top_pair {dim : Nat} (a b c : Nat)
    (h0 : 0 < dim)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    uc_eval (Gate.toUCom dim
      (optimize_ccx_pair_top (Gate.seq (Gate.CCX a b c) (Gate.CCX a b c))))
      = uc_eval (Gate.toUCom dim (Gate.seq (Gate.CCX a b c) (Gate.CCX a b c))) := by
  -- The optimizer fires (triples trivially match), producing Gate.I.
  show uc_eval (Gate.toUCom dim (if a = a ∧ b = b ∧ c = c then Gate.I
                  else Gate.seq (Gate.CCX a b c) (Gate.CCX a b c)))
       = uc_eval (Gate.toUCom dim (Gate.seq (Gate.CCX a b c) (Gate.CCX a b c)))
  rw [if_pos ⟨rfl, rfl, rfl⟩]
  -- LHS: uc_eval (Gate.toUCom dim Gate.I) = uc_eval (BaseUCom.ID 0)
  show uc_eval (BaseUCom.ID 0 : BaseUCom dim)
       = uc_eval (UCom.seq (BaseUCom.CCX a b c : BaseUCom dim) (BaseUCom.CCX a b c))
  rw [uc_eval_ID_eq_one h0]
  -- Goal: 1 = uc_eval (UCom.seq CCX CCX) = uc_eval CCX * uc_eval CCX
  exact (CCX_CCX_eq_one dim a b c ha hb hc hab hac hbc).symm

/-! ## Semantic preservation: the no-op cases (rfl-trivial)

    For all gate shapes EXCEPT a matching CCX-CCX pair at the top
    level, `optimize_ccx_pair_top` returns the input unchanged. So
    uc_eval is rfl-trivially equal. Five such cases below. -/

theorem uc_eval_toUCom_optimize_ccx_pair_top_I {dim : Nat} :
    uc_eval (Gate.toUCom dim (optimize_ccx_pair_top Gate.I))
      = uc_eval (Gate.toUCom dim Gate.I) := rfl

theorem uc_eval_toUCom_optimize_ccx_pair_top_X {dim q : Nat} :
    uc_eval (Gate.toUCom dim (optimize_ccx_pair_top (Gate.X q)))
      = uc_eval (Gate.toUCom dim (Gate.X q)) := rfl

theorem uc_eval_toUCom_optimize_ccx_pair_top_CX {dim a b : Nat} :
    uc_eval (Gate.toUCom dim (optimize_ccx_pair_top (Gate.CX a b)))
      = uc_eval (Gate.toUCom dim (Gate.CX a b)) := rfl

theorem uc_eval_toUCom_optimize_ccx_pair_top_CCX {dim a b c : Nat} :
    uc_eval (Gate.toUCom dim (optimize_ccx_pair_top (Gate.CCX a b c)))
      = uc_eval (Gate.toUCom dim (Gate.CCX a b c)) := rfl

/-- When the two CCXs have differing triples, the optimizer leaves
    the circuit unchanged. -/
theorem uc_eval_toUCom_optimize_ccx_pair_top_pair_diff {dim : Nat}
    (a b c a' b' c' : Nat) (h : ¬ (a = a' ∧ b = b' ∧ c = c')) :
    uc_eval (Gate.toUCom dim
      (optimize_ccx_pair_top (Gate.seq (Gate.CCX a b c) (Gate.CCX a' b' c'))))
      = uc_eval (Gate.toUCom dim (Gate.seq (Gate.CCX a b c) (Gate.CCX a' b' c'))) := by
  show uc_eval (Gate.toUCom dim (if a = a' ∧ b = b' ∧ c = c' then Gate.I
                  else Gate.seq (Gate.CCX a b c) (Gate.CCX a' b' c')))
       = uc_eval (Gate.toUCom dim (Gate.seq (Gate.CCX a b c) (Gate.CCX a' b' c')))
  rw [if_neg h]

/-! ## Well-typedness predicate and the unified preservation theorem -/

/-- A `Gate` is well-typed in `dim`-qubit context iff every contained
    gate-position is within `dim` and CCXs have distinct controls/target. -/
def Gate.WellTyped (dim : Nat) : Gate → Prop
  | Gate.I            => 0 < dim
  | Gate.X q          => q < dim
  | Gate.CX a b       => a < dim ∧ b < dim ∧ a ≠ b
  | Gate.CCX a b c    => a < dim ∧ b < dim ∧ c < dim ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
  | Gate.seq g₁ g₂    => Gate.WellTyped dim g₁ ∧ Gate.WellTyped dim g₂

/-- **Unified semantic preservation** for the top-level CCX-pair rewrite.
    Combines the matching-pair case (uses CCX_CCX_eq_one) with all
    no-op cases (rfl + if_neg). -/
theorem uc_eval_toUCom_optimize_ccx_pair_top {dim : Nat}
    (g : Gate) (h_wt : Gate.WellTyped dim g) :
    uc_eval (Gate.toUCom dim (optimize_ccx_pair_top g))
      = uc_eval (Gate.toUCom dim g) := by
  cases g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ =>
    cases g₁ with
    | CCX a b c =>
      cases g₂ with
      | CCX a' b' c' =>
        by_cases h : a = a' ∧ b = b' ∧ c = c'
        · obtain ⟨ha_eq, hb_eq, hc_eq⟩ := h
          subst ha_eq; subst hb_eq; subst hc_eq
          obtain ⟨⟨ha, hb, hc, hab, hac, hbc⟩, _⟩ := h_wt
          have h0 : 0 < dim := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
          exact uc_eval_toUCom_optimize_ccx_pair_top_pair a b c h0 ha hb hc hab hac hbc
        · exact uc_eval_toUCom_optimize_ccx_pair_top_pair_diff a b c a' b' c' h
      | I => rfl
      | X _ => rfl
      | CX _ _ => rfl
      | seq _ _ => rfl
    | I => rfl
    | X _ => rfl
    | CX _ _ => rfl
    | seq _ _ => rfl

/-! ## Lifting semantic preservation to the deep optimizer -/

/-- Well-typedness is preserved by the top-level CCX-pair rewrite.
    The interesting case: when the optimizer fires on a CCX-CCX pair,
    the output `I` requires `0 < dim`, which we can extract from the
    inner CCXs' well-typedness. -/
theorem Gate.WellTyped_optimize_ccx_pair_top {dim : Nat}
    (g : Gate) (h_wt : Gate.WellTyped dim g) :
    Gate.WellTyped dim (optimize_ccx_pair_top g) := by
  cases g with
  | I => exact h_wt
  | X _ => exact h_wt
  | CX _ _ => exact h_wt
  | CCX _ _ _ => exact h_wt
  | seq g₁ g₂ =>
    cases g₁ with
    | CCX a b c =>
      cases g₂ with
      | CCX a' b' c' =>
        by_cases h : a = a' ∧ b = b' ∧ c = c'
        · obtain ⟨ha_eq, hb_eq, hc_eq⟩ := h
          subst ha_eq; subst hb_eq; subst hc_eq
          obtain ⟨⟨ha, _, _, _, _, _⟩, _⟩ := h_wt
          show Gate.WellTyped dim (if a = a ∧ b = b ∧ c = c then Gate.I
                                    else Gate.seq (Gate.CCX a b c) (Gate.CCX a b c))
          rw [if_pos ⟨rfl, rfl, rfl⟩]
          show 0 < dim
          exact Nat.lt_of_le_of_lt (Nat.zero_le _) ha
        · show Gate.WellTyped dim (if a = a' ∧ b = b' ∧ c = c' then Gate.I
                                    else Gate.seq (Gate.CCX a b c) (Gate.CCX a' b' c'))
          rw [if_neg h]
          exact h_wt
      | I => exact h_wt
      | X _ => exact h_wt
      | CX _ _ => exact h_wt
      | seq _ _ => exact h_wt
    | I => exact h_wt
    | X _ => exact h_wt
    | CX _ _ => exact h_wt
    | seq _ _ => exact h_wt

/-- Well-typedness is preserved by the deep optimizer.
    Inductive on `g`. -/
theorem Gate.WellTyped_optimize_ccx_pairs_deep {dim : Nat}
    (g : Gate) (h_wt : Gate.WellTyped dim g) :
    Gate.WellTyped dim (optimize_ccx_pairs_deep g) := by
  induction g with
  | I => exact h_wt
  | X _ => exact h_wt
  | CX _ _ => exact h_wt
  | CCX _ _ _ => exact h_wt
  | seq g₁ g₂ ih₁ ih₂ =>
    obtain ⟨hwt₁, hwt₂⟩ := h_wt
    -- deep (seq g₁ g₂) = optimize_ccx_pair_top (seq (deep g₁) (deep g₂))
    show Gate.WellTyped dim (optimize_ccx_pair_top
            (Gate.seq (optimize_ccx_pairs_deep g₁) (optimize_ccx_pairs_deep g₂)))
    apply Gate.WellTyped_optimize_ccx_pair_top
    exact ⟨ih₁ hwt₁, ih₂ hwt₂⟩

/-- **Semantic preservation for the deep optimizer.** Inductive on `g`,
    using the top-level unified theorem at each `seq` step. -/
theorem uc_eval_toUCom_optimize_ccx_pairs_deep {dim : Nat}
    (g : Gate) (h_wt : Gate.WellTyped dim g) :
    uc_eval (Gate.toUCom dim (optimize_ccx_pairs_deep g))
      = uc_eval (Gate.toUCom dim g) := by
  induction g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ ih₁ ih₂ =>
    obtain ⟨hwt₁, hwt₂⟩ := h_wt
    -- deep (seq g₁ g₂) = optimize_ccx_pair_top (seq (deep g₁) (deep g₂))
    show uc_eval (Gate.toUCom dim (optimize_ccx_pair_top
            (Gate.seq (optimize_ccx_pairs_deep g₁) (optimize_ccx_pairs_deep g₂))))
         = uc_eval (Gate.toUCom dim (Gate.seq g₁ g₂))
    -- Step 1: top-level optimizer preserves uc_eval on the seq of deep results
    have h_wt_seq : Gate.WellTyped dim
        (Gate.seq (optimize_ccx_pairs_deep g₁) (optimize_ccx_pairs_deep g₂)) :=
      ⟨Gate.WellTyped_optimize_ccx_pairs_deep g₁ hwt₁,
       Gate.WellTyped_optimize_ccx_pairs_deep g₂ hwt₂⟩
    rw [uc_eval_toUCom_optimize_ccx_pair_top _ h_wt_seq]
    -- Step 2: uc_eval (seq (deep g₁) (deep g₂)) = uc_eval (seq g₁ g₂)
    show uc_eval (UCom.seq (Gate.toUCom dim (optimize_ccx_pairs_deep g₁))
                           (Gate.toUCom dim (optimize_ccx_pairs_deep g₂)))
         = uc_eval (UCom.seq (Gate.toUCom dim g₁) (Gate.toUCom dim g₂))
    show uc_eval (Gate.toUCom dim (optimize_ccx_pairs_deep g₂)) *
         uc_eval (Gate.toUCom dim (optimize_ccx_pairs_deep g₁)) = _
    rw [ih₁ hwt₁, ih₂ hwt₂]
    rfl

/-! ## I-elimination preservation: top-level + deep + the full optimizer -/

/-- Semantic preservation for the top-level I-elimination rewrite.
    The interesting cases: `seq I g → g` and `seq g I → g`. Both
    use `uc_eval_ID_eq_one`. -/
theorem uc_eval_toUCom_optimize_I_top {dim : Nat}
    (g : Gate) (h_wt : Gate.WellTyped dim g) :
    uc_eval (Gate.toUCom dim (optimize_I_top g))
      = uc_eval (Gate.toUCom dim g) := by
  cases g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ =>
    cases g₁ with
    | I =>
      -- optimize_I_top (seq I g₂) = g₂
      obtain ⟨h0, _⟩ := h_wt
      show uc_eval (Gate.toUCom dim g₂)
           = uc_eval (UCom.seq (BaseUCom.ID 0 : BaseUCom dim) (Gate.toUCom dim g₂))
      show uc_eval (Gate.toUCom dim g₂)
           = uc_eval (Gate.toUCom dim g₂) * uc_eval (BaseUCom.ID 0 : BaseUCom dim)
      rw [uc_eval_ID_eq_one h0, Matrix.mul_one]
    | X q =>
      cases g₂ with
      | I =>
        obtain ⟨_, h0⟩ := h_wt
        show uc_eval (BaseUCom.X q : BaseUCom dim)
             = uc_eval (BaseUCom.ID 0 : BaseUCom dim) * uc_eval (BaseUCom.X q : BaseUCom dim)
        rw [uc_eval_ID_eq_one h0, Matrix.one_mul]
      | _ => rfl
    | CX c t =>
      cases g₂ with
      | I =>
        obtain ⟨_, h0⟩ := h_wt
        show uc_eval (BaseUCom.CNOT c t : BaseUCom dim)
             = uc_eval (BaseUCom.ID 0 : BaseUCom dim) *
               uc_eval (BaseUCom.CNOT c t : BaseUCom dim)
        rw [uc_eval_ID_eq_one h0, Matrix.one_mul]
      | _ => rfl
    | CCX a b c =>
      cases g₂ with
      | I =>
        obtain ⟨_, h0⟩ := h_wt
        show uc_eval (BaseUCom.CCX a b c : BaseUCom dim)
             = uc_eval (BaseUCom.ID 0 : BaseUCom dim) *
               uc_eval (BaseUCom.CCX a b c : BaseUCom dim)
        rw [uc_eval_ID_eq_one h0, Matrix.one_mul]
      | _ => rfl
    | seq h₁ h₂ =>
      cases g₂ with
      | I =>
        obtain ⟨_, h0⟩ := h_wt
        show uc_eval (Gate.toUCom dim (Gate.seq h₁ h₂))
             = uc_eval (BaseUCom.ID 0 : BaseUCom dim) *
               uc_eval (Gate.toUCom dim (Gate.seq h₁ h₂))
        rw [uc_eval_ID_eq_one h0, Matrix.one_mul]
      | _ => rfl

/-- Well-typedness is preserved by the top-level I-elimination rewrite.
    `seq I g → g` and `seq g I → g` only drop an I (which is well-typed
    iff 0 < dim, propagated from any inner CCX or the seq's other half). -/
theorem Gate.WellTyped_optimize_I_top {dim : Nat}
    (g : Gate) (h_wt : Gate.WellTyped dim g) :
    Gate.WellTyped dim (optimize_I_top g) := by
  cases g with
  | I => exact h_wt
  | X _ => exact h_wt
  | CX _ _ => exact h_wt
  | CCX _ _ _ => exact h_wt
  | seq g₁ g₂ =>
    cases g₁ with
    | I => exact h_wt.2
    | X _ =>
      cases g₂ with
      | I => exact h_wt.1
      | _ => exact h_wt
    | CX _ _ =>
      cases g₂ with
      | I => exact h_wt.1
      | _ => exact h_wt
    | CCX _ _ _ =>
      cases g₂ with
      | I => exact h_wt.1
      | _ => exact h_wt
    | seq _ _ =>
      cases g₂ with
      | I => exact h_wt.1
      | _ => exact h_wt

/-- Well-typedness is preserved by the deep I-elimination optimizer. -/
theorem Gate.WellTyped_optimize_I_pairs_deep {dim : Nat}
    (g : Gate) (h_wt : Gate.WellTyped dim g) :
    Gate.WellTyped dim (optimize_I_pairs_deep g) := by
  induction g with
  | I => exact h_wt
  | X _ => exact h_wt
  | CX _ _ => exact h_wt
  | CCX _ _ _ => exact h_wt
  | seq g₁ g₂ ih₁ ih₂ =>
    obtain ⟨hwt₁, hwt₂⟩ := h_wt
    show Gate.WellTyped dim (optimize_I_top
            (Gate.seq (optimize_I_pairs_deep g₁) (optimize_I_pairs_deep g₂)))
    apply Gate.WellTyped_optimize_I_top
    exact ⟨ih₁ hwt₁, ih₂ hwt₂⟩

/-- Semantic preservation for the deep I-elimination optimizer. -/
theorem uc_eval_toUCom_optimize_I_pairs_deep {dim : Nat}
    (g : Gate) (h_wt : Gate.WellTyped dim g) :
    uc_eval (Gate.toUCom dim (optimize_I_pairs_deep g))
      = uc_eval (Gate.toUCom dim g) := by
  induction g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ ih₁ ih₂ =>
    obtain ⟨hwt₁, hwt₂⟩ := h_wt
    show uc_eval (Gate.toUCom dim (optimize_I_top
            (Gate.seq (optimize_I_pairs_deep g₁) (optimize_I_pairs_deep g₂))))
         = uc_eval (Gate.toUCom dim (Gate.seq g₁ g₂))
    have h_wt_seq : Gate.WellTyped dim
        (Gate.seq (optimize_I_pairs_deep g₁) (optimize_I_pairs_deep g₂)) :=
      ⟨Gate.WellTyped_optimize_I_pairs_deep g₁ hwt₁,
       Gate.WellTyped_optimize_I_pairs_deep g₂ hwt₂⟩
    rw [uc_eval_toUCom_optimize_I_top _ h_wt_seq]
    show uc_eval (Gate.toUCom dim (optimize_I_pairs_deep g₂)) *
         uc_eval (Gate.toUCom dim (optimize_I_pairs_deep g₁)) = _
    rw [ih₁ hwt₁, ih₂ hwt₂]
    rfl

/-- **Semantic preservation for the full optimizer.** Compose the
    CCX-deep and I-deep preservations. -/
theorem uc_eval_toUCom_optimize_full {dim : Nat}
    (g : Gate) (h_wt : Gate.WellTyped dim g) :
    uc_eval (Gate.toUCom dim (optimize_full g))
      = uc_eval (Gate.toUCom dim g) := by
  show uc_eval (Gate.toUCom dim
                  (optimize_I_pairs_deep (optimize_ccx_pairs_deep g)))
       = uc_eval (Gate.toUCom dim g)
  rw [uc_eval_toUCom_optimize_I_pairs_deep _
        (Gate.WellTyped_optimize_ccx_pairs_deep g h_wt)]
  exact uc_eval_toUCom_optimize_ccx_pairs_deep g h_wt

/-- Well-typedness is preserved by `optimize_full`. Compose the two
    deep preservations. -/
theorem Gate.WellTyped_optimize_full {dim : Nat}
    (g : Gate) (h_wt : Gate.WellTyped dim g) :
    Gate.WellTyped dim (optimize_full g) := by
  show Gate.WellTyped dim (optimize_I_pairs_deep (optimize_ccx_pairs_deep g))
  exact Gate.WellTyped_optimize_I_pairs_deep _
          (Gate.WellTyped_optimize_ccx_pairs_deep g h_wt)

/-- Well-typedness is preserved by the WF-recursive fixpoint operator.
    Same shape as the cost-monotonicity proofs: case-split on
    `has_ccx_pair g`, recurse via `_eq_recurse_of_pair`, base case via
    `_eq_self_of_no_pair`. -/
theorem Gate.WellTyped_optimize_to_fixpoint {dim : Nat}
    (g : Gate) (h_wt : Gate.WellTyped dim g) :
    Gate.WellTyped dim (optimize_to_fixpoint g) := by
  by_cases h : has_ccx_pair g = true
  · rw [optimize_to_fixpoint_eq_recurse_of_pair g h]
    exact Gate.WellTyped_optimize_to_fixpoint (optimize_full g)
            (Gate.WellTyped_optimize_full g h_wt)
  · have hf : has_ccx_pair g = false := by
      cases hb : has_ccx_pair g with
      | true => exact absurd hb h
      | false => rfl
    rw [optimize_to_fixpoint_eq_self_of_no_pair g hf]
    exact h_wt
termination_by gcount g
decreasing_by exact gcount_optimize_full_strict g (by assumption)

/-- **Semantic preservation for the WF-recursive fixpoint operator.**
    Closes the certification stack: the unfueled
    `optimize_to_fixpoint` is formally proven to terminate, produce
    pair-free output, decrease both tcount and gcount monotonically,
    AND preserve uc_eval. -/
theorem uc_eval_toUCom_optimize_to_fixpoint {dim : Nat}
    (g : Gate) (h_wt : Gate.WellTyped dim g) :
    uc_eval (Gate.toUCom dim (optimize_to_fixpoint g))
      = uc_eval (Gate.toUCom dim g) := by
  by_cases h : has_ccx_pair g = true
  · rw [optimize_to_fixpoint_eq_recurse_of_pair g h]
    rw [uc_eval_toUCom_optimize_to_fixpoint (optimize_full g)
          (Gate.WellTyped_optimize_full g h_wt)]
    exact uc_eval_toUCom_optimize_full g h_wt
  · have hf : has_ccx_pair g = false := by
      cases hb : has_ccx_pair g with
      | true => exact absurd hb h
      | false => rfl
    rw [optimize_to_fixpoint_eq_self_of_no_pair g hf]
termination_by gcount g
decreasing_by exact gcount_optimize_full_strict g (by assumption)

/-! ## Application corollaries -/

/-- UCom.equiv-form of the WF-fixpoint preservation. Clients reasoning
    in the UCom semantic layer can use this directly. -/
theorem optimize_to_fixpoint_uc_equiv {dim : Nat}
    (g : Gate) (h_wt : Gate.WellTyped dim g) :
    UCom.equiv (Gate.toUCom dim (optimize_to_fixpoint g))
               (Gate.toUCom dim g) :=
  uc_eval_toUCom_optimize_to_fixpoint g h_wt

/-- The single-step associativity rotation `assoc_right_step` preserves
    `uc_eval` semantics. Reduces to `Matrix.mul_assoc` after unfolding
    `UCom.seq`'s right-to-left matrix multiplication. -/
theorem uc_eval_toUCom_assoc_right_step {dim : Nat} (g : Gate) :
    uc_eval (Gate.toUCom dim (assoc_right_step g))
      = uc_eval (Gate.toUCom dim g) := by
  cases g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ =>
    cases g₁ with
    | seq a b =>
      -- assoc_right_step (seq (seq a b) g₂) = seq a (seq b g₂)
      -- LHS: uc_eval (seq a (seq b g₂))
      --    = uc_eval (seq b g₂) * uc_eval a
      --    = (uc_eval g₂ * uc_eval b) * uc_eval a
      -- RHS: uc_eval (seq (seq a b) g₂)
      --    = uc_eval g₂ * uc_eval (seq a b)
      --    = uc_eval g₂ * (uc_eval b * uc_eval a)
      -- Equal by Matrix.mul_assoc.
      show (uc_eval (Gate.toUCom dim g₂) * uc_eval (Gate.toUCom dim b))
           * uc_eval (Gate.toUCom dim a)
           = uc_eval (Gate.toUCom dim g₂)
             * (uc_eval (Gate.toUCom dim b) * uc_eval (Gate.toUCom dim a))
      exact Matrix.mul_assoc _ _ _
    | I => rfl
    | X _ => rfl
    | CX _ _ => rfl
    | CCX _ _ _ => rfl

/-- UCom.equiv form: the rotation produces an equivalent circuit. -/
theorem assoc_right_step_uc_equiv {dim : Nat} (g : Gate) :
    UCom.equiv (Gate.toUCom dim (assoc_right_step g))
               (Gate.toUCom dim g) :=
  uc_eval_toUCom_assoc_right_step g

/-- Iterated rotation preserves uc_eval. Induction on fuel + each
    step's semantic preservation. -/
theorem uc_eval_toUCom_assoc_right_iter {dim : Nat} (n : Nat) (g : Gate) :
    uc_eval (Gate.toUCom dim (assoc_right_iter n g))
      = uc_eval (Gate.toUCom dim g) := by
  induction n generalizing g with
  | zero => rfl
  | succ k ih =>
    show uc_eval (Gate.toUCom dim (assoc_right_iter k (assoc_right_step g)))
         = uc_eval (Gate.toUCom dim g)
    rw [ih, uc_eval_toUCom_assoc_right_step]

end FormalRV.BQAlgo
