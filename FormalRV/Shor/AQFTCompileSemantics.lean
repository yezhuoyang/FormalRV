/-
  FormalRV.Shor.AQFTCompileSemantics — SEMANTIC correctness of the AQFT
  compiler (the linear-algebra proof, not just the Clifford+T gate-set).

  `compileLadder` is diagonal in the computational basis, so its action is
  fully characterised by a per-basis-state scalar.  We prove, by induction
  on the rotation list, that `compileLadder c rs` multiplies the amplitude
  of basis state `f` by the PRODUCT of the kept controlled-phase scalars
  (each `e^{-iπ/2^m}` when both control and target bits are set), with
  DROPPED rotations contributing `1` (because `SKIP = id`).  This certifies
  that the compiler actually computes the banded inverse-QFT — its
  semantics, not only its gate count or gate set.

  Reuses the repo's already-proven controlled-phase semantics
  (`controlled_Rz_acts_on_basis_correct`) via a `rfl` bridge between the
  Framework `BaseUCom.controlled_Rz` (which `compileRot` emits) and the
  SQIRPort `controlled_Rz` the lemma is stated about.

  ## Honesty boundary
  Stated on `f_to_vec` computational-basis states only (the ladder is
  diagonal, so this fully characterises it); NOT lifted to a full matrix
  equality, and this is the BANDED action — its deviation from the exact
  QFT is the separate `compileLadder_error_budget`.

  Machine-validated; kernel-clean ([propext, Classical.choice, Quot.sound]).
-/
import FormalRV.Shor.AQFTCompile
import FormalRV.Shor.ControlledGates

namespace FormalRV.Framework.AQFTCompile

open FormalRV.Framework
open FormalRV.Framework.BaseUCom
open FormalRV.Framework.CliffordTRotations
open FormalRV.Framework.ApproxQFT

/-- Bridge: the Framework `controlled_Rz` that `compileRot` emits is defeq
    to the SQIRPort `controlled_Rz` that `controlled_Rz_acts_on_basis_correct`
    is stated about.  Closed by `rfl`. -/
theorem controlled_Rz_bridge {dim : Nat} (q t : Nat) (lam : ℝ) :
    (FormalRV.Framework.BaseUCom.controlled_Rz q t lam
        : FormalRV.Framework.BaseUCom dim)
      = FormalRV.SQIRPort.controlled_Rz q t lam := rfl

/-- The per-basis-state scalar of one compiled rotation: the kept
    controlled-phase `e^{-iπ/2^m}` exactly when the rotation survives the
    cutoff (`m < c`) AND both control/target bits are set; otherwise `1`. -/
noncomputable def rotScalar (c : Nat) (r : PhaseRot) (f : Nat → Bool) : ℂ :=
  if r.m < c ∧ f r.q ∧ f r.t then
    Complex.exp ((-(Real.pi / 2 ^ r.m)) * Complex.I)
  else 1

/-- Well-formedness of one rotation against the register dimension. -/
def RotWF (dim : Nat) (r : PhaseRot) : Prop := r.q < dim ∧ r.t < dim ∧ r.q ≠ r.t

/-- **One compiled rotation acts as its controlled-phase scalar** on a
    basis state (kept → controlled-phase, dropped → identity). -/
theorem compileRot_acts_on_basis {dim : Nat} (c : Nat) (r : PhaseRot) (f : Nat → Bool)
    (hpos : 0 < dim) (hq : r.q < dim) (ht : r.t < dim) (hqt : r.q ≠ r.t) :
    uc_eval (compileRot c r : BaseUCom dim) * f_to_vec dim f
      = rotScalar c r f • f_to_vec dim f := by
  unfold compileRot rotScalar
  split
  · rename_i hm
    rw [controlled_Rz_bridge]
    rw [FormalRV.SQIRPort.controlled_Rz_acts_on_basis_correct dim r.q r.t hq ht hqt
          (-(Real.pi / 2 ^ r.m)) f]
    simp only [hm, true_and]
    push_cast
    ring_nf
  · rename_i hm
    rw [f_to_vec_SKIP_uc_eval hpos]
    simp only [hm, false_and, if_false, one_smul]

/-- The product of the per-rotation scalars over the whole ladder. -/
noncomputable def ladderScalar (c : Nat) (rs : List PhaseRot) (f : Nat → Bool) : ℂ :=
  (rs.map (fun r => rotScalar c r f)).prod

/-- **The compiled ladder acts as the product of its kept controlled-phases**
    on every computational-basis state — the compiler's semantic correctness,
    proved by induction over the rotation list. -/
theorem compileLadder_acts_on_basis {dim : Nat} (c : Nat) (rs : List PhaseRot) (f : Nat → Bool)
    (hpos : 0 < dim) (hwf : ∀ r ∈ rs, RotWF dim r) :
    uc_eval (compileLadder c rs : BaseUCom dim) * f_to_vec dim f
      = ladderScalar c rs f • f_to_vec dim f := by
  unfold compileLadder ladderScalar
  induction rs with
  | nil =>
      simp only [List.foldr_nil, List.map_nil, List.prod_nil, one_smul]
      exact f_to_vec_SKIP_uc_eval hpos f
  | cons r rs ih =>
      rw [List.foldr_cons, List.map_cons, List.prod_cons]
      rw [uc_eval_seq_mul]
      have hr : RotWF dim r := hwf r (by simp)
      obtain ⟨hq, ht, hqt⟩ := hr
      have hrest : ∀ r2 ∈ rs, RotWF dim r2 :=
        fun r2 hr2 => hwf r2 (List.mem_cons_of_mem r hr2)
      rw [compileRot_acts_on_basis c r f hpos hq ht hqt]
      rw [Matrix.mul_smul]
      rw [ih hrest]
      rw [smul_smul]

/-- Smoke instance: a 2-rotation banded ladder acts as the product of the
    two per-rotation scalars. -/
theorem compileLadder_two_acts_on_basis {dim : Nat} (c : Nat) (r1 r2 : PhaseRot)
    (f : Nat → Bool) (hpos : 0 < dim) (hwf1 : RotWF dim r1) (hwf2 : RotWF dim r2) :
    uc_eval (compileLadder c [r1, r2] : BaseUCom dim) * f_to_vec dim f
      = (rotScalar c r1 f * rotScalar c r2 f) • f_to_vec dim f := by
  have hwf : ∀ r ∈ [r1, r2], RotWF dim r := by
    rw [List.forall_mem_cons, List.forall_mem_cons]
    exact ⟨hwf1, hwf2, by simp⟩
  rw [compileLadder_acts_on_basis c [r1, r2] f hpos hwf]
  unfold ladderScalar
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

end FormalRV.Framework.AQFTCompile
