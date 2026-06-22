/-
  FormalRV.QEC.Gidney21.QuadraticFrame
  ────────────────────────────────────
  **(completeness) The QUADRATIC Pauli-frame decoder for `correctQ` — and a
  proof it is GENUINELY needed (AND is not XOR-affine).**

  The CCZ-state injection leaves a residual Pauli correction that fires on a
  QUADRATIC parity of measurement outcomes, e.g. `b_i XOR (m_j AND m_k)`.  No
  outcome-affine (XOR-only) Pauli frame can express this, so `correctQ`
  (XOR of AND-monomials, `qParity`) is intrinsic.  This file gives the
  verified decoder properties the `correctQ` frame correction rests on:

    • `qParity` generalizes the affine `correct` (singleton monomials);
    • it expresses the degree-2 CCZ residual exactly;
    • and AND is provably NOT XOR-affine, so the quadratic frame is required —
      an XOR-only decoder is incomplete for CCZ.

  These were absent (`qParity` had no lemmas); the `correctQ` decoder now has
  a verified foundation.
-/
import FormalRV.PPM.Semantics.ProgramSemantics

namespace FormalRV.QEC.Gidney21

open FormalRV.PPM.Prog

/-! ## §1. Basic decoder identities. -/

/-- A single AND-monomial: `qParity` of one monomial is just that monomial. -/
theorem qParity_singleton (outs : List Bool) (mon : List CVar) :
    qParity outs [mon] = andParity outs mon := by
  simp [qParity, andParity]

/-- The empty quadratic correction never fires. -/
theorem qParity_nil (outs : List Bool) : qParity outs [] = false := rfl

/-- Folding one more monomial XORs in its AND. -/
theorem qParity_append (outs : List Bool) (mons : List (List CVar))
    (mon : List CVar) :
    qParity outs (mons ++ [mon]) = (qParity outs mons ^^ andParity outs mon) := by
  simp [qParity, List.foldl_append]

/-! ## §2. `correctQ` generalizes the affine `correct`. -/

/-- A degree-1 (singleton) monomial reads a single outcome slot. -/
theorem andParity_singleton (outs : List Bool) (c : CVar) :
    andParity outs [c] = outs.getD c false := by
  simp [andParity]

/-- **`correctQ` with SINGLETON monomials = `correct`**: the quadratic frame
strictly contains the affine one.  (The XOR of single-slot reads is exactly
the XOR-parity.) -/
theorem qParity_singletons_eq_xorParity (outs : List Bool) (slots : List CVar) :
    qParity outs (slots.map (fun c => [c])) = xorParity outs slots := by
  unfold qParity xorParity
  suffices h : ∀ (acc : Bool) (sl : List CVar),
      (sl.map (fun c => [c])).foldl (fun a mon => a ^^ andParity outs mon) acc
        = sl.foldl (fun a c => a ^^ outs.getD c false) acc from h false slots
  intro acc sl
  induction sl generalizing acc with
  | nil => rfl
  | cons s ss ih =>
      simp only [List.map_cons, List.foldl_cons, andParity, List.all_cons,
        List.all_nil, Bool.and_true]
      exact ih _

/-! ## §3. The degree-2 CCZ residual — exactly expressible. -/

/-- **The CCZ residual pattern**: `correctQ` with monomials `[[i], [j,k]]`
fires on exactly `outs[i] XOR (outs[j] AND outs[k])` — the residual a
degree-3 phase-gate (CCZ) injection leaves behind. -/
theorem qParity_ccz_residual (outs : List Bool) (i j k : CVar) :
    qParity outs [[i], [j, k]]
      = (outs.getD i false ^^ (outs.getD j false && outs.getD k false)) := by
  simp [qParity, andParity]

/-! ## §4. WHY it is needed — AND is NOT XOR-affine. -/

/-- **AND is not XOR-affine**: there is NO affine function
`a XOR (b AND m) XOR (c AND n)` equal to `m AND n` for all inputs.  Hence no
outcome-affine (XOR-only) Pauli frame can express the degree-2 CCZ residual —
`correctQ`'s quadratic frame is genuinely required, an XOR-only decoder is
incomplete for CCZ. -/
theorem and_not_xor_affine :
    ¬ ∃ a b c : Bool, ∀ m n : Bool,
        (m && n) = (a ^^ (b && m) ^^ (c && n)) := by
  decide

/-- Concretely, EVERY affine decoder `a XOR (b AND m) XOR (c AND n)` FAILS to
compute `m AND n` on at least one input — so no affine decoder reproduces the
degree-2 CCZ residual. -/
theorem affine_fails_on_and :
    ∀ a b c : Bool, ∃ m n : Bool, (m && n) ≠ (a ^^ (b && m) ^^ (c && n)) := by
  decide

/-! ## §5. The decoder and its agreement with the semantics. -/

/-- **The `correctQ` frame correction**: evaluate the quadratic parity, choose
the `then`/`else` Pauli — the verified quadratic decoder. -/
def qFrameCorrection (outs : List Bool) (mons : List (List CVar))
    (thn els : PauliProduct) : PauliProduct :=
  if qParity outs mons then thn else els

/-- **The decoder AGREES with the operational semantics**: stepping a
`correctQ` statement folds exactly `qFrameCorrection` into the frame. -/
theorem correctQ_step_uses_decoder (n : Nat) (outcome : Bool) (st : ExecState)
    (mons : List (List CVar)) (thn els : PauliProduct) :
    (stepStmt n outcome st (.correctQ mons thn els)).frame
      = mulF st.frame (qFrameCorrection st.outs mons thn els) := by
  unfold stepStmt qFrameCorrection
  by_cases h : qParity st.outs mons <;> simp [h]

end FormalRV.QEC.Gidney21
