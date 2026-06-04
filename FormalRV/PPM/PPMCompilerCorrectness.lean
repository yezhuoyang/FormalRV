-- ===========================================================================
-- FILE HEADER. Place at the very top of FormalRV/PPM/PPMCompilerCorrectness.lean.
--
-- Imports (dependency order; both validated against the real repo):
--   * FormalRV.PPM.PPMDenote      -- gadgetDenote/gadgetDenote_eq, StateVec, the
--                                    ⊗ᵥ notation, and transitively UnitarySem
--                                    (uc_eval, BaseUCom, Square, BaseUnitary).
--   * FormalRV.Core.CliffordTRotations -- IsCliffordT and U_H/U_S/U_T/U_SDAG/
--                                    U_TDAG/U_I.
-- These two imports are SUFFICIENT: do NOT add explicit imports of UnitarySem or
-- MagicStateTeleport — they arrive transitively and the minimal set validated
-- clean (zero diagnostics).
--
-- Opens (verified against repo):
--   * StateVec and ⊗ᵥ live in FormalRV.Framework (Core/NDSem.lean:21,
--     Core/QuantumLib.lean:183); uc_eval/BaseUCom/Square/BaseUnitary in
--     FormalRV.Framework (Core/UnitarySem.lean); IsCliffordT and the U_* gate
--     names in FormalRV.Framework.CliffordTRotations.
-- ===========================================================================
import FormalRV.PPM.PPMDenote
import FormalRV.Core.CliffordTRotations

open scoped Matrix
open FormalRV.Framework
open FormalRV.Framework.CliffordTRotations

namespace FormalRV.PPM.PPMCompilerCorrectness

/-! ## §1. Abstract realization predicate + COMPOSITION lemma.

    [VALIDATED] RealizesUpToFrame, realizes_comp, and realizes_comp_id_lower all
    type-check clean and depend only on [propext, Classical.choice, Quot.sound]. -/

/-- **Deliverable 1.** Abstract realization predicate: `op` realizes the gate
    unitary `U` up to a Pauli/Clifford `frame` unitary, meaning `op = frame * U`.
    Generic over any square-matrix index type `n` (no fixed dimension, no Shor
    content). -/
def RealizesUpToFrame {n : Type*} [Fintype n] [DecidableEq n]
    (op frame U : Matrix n n ℂ) : Prop := op = frame * U

/-- **Deliverable 2 (the heart).** COMPOSITION lemma. If `op1 = f1 * U1` and
    `op2 = f2 * U2`, and the second gate unitary `U2` commutes through `f1` to a
    conjugated frame `f1'` (`U2 * f1 = f1' * U2`, the Gottesman/Heisenberg
    frame-update), then `op2 * op1` realizes `U2 * U1` up to the accumulated frame
    `f2 * f1'`. Pure matrix algebra; chains by induction (see §2). -/
theorem realizes_comp {n : Type*} [Fintype n] [DecidableEq n]
    {op1 op2 f1 f2 f1' U1 U2 : Matrix n n ℂ}
    (h1 : RealizesUpToFrame op1 f1 U1)
    (h2 : RealizesUpToFrame op2 f2 U2)
    (hcomm : U2 * f1 = f1' * U2) :
    RealizesUpToFrame (op2 * op1) (f2 * f1') (U2 * U1) := by
  unfold RealizesUpToFrame at *
  subst h1 h2
  rw [← Matrix.mul_assoc (f2 * U2) f1 U1, Matrix.mul_assoc f2 U2 f1, hcomm,
      ← Matrix.mul_assoc f2 f1' U2, Matrix.mul_assoc (f2 * f1') U2 U1]

/-- Convenience corollary (grafted from Design A; validated axiom-clean):
    trivial LOWER frame (`f1 = 1`) makes the commutation free and the accumulated
    frame is just `f2`. NOTE the *upper*-frame-trivial analogue is UNSOUND (a `1`
    upper frame does NOT remove the commutation obligation), so it is omitted. -/
theorem realizes_comp_id_lower {n : Type*} [Fintype n] [DecidableEq n]
    {op1 op2 f2 U1 U2 : Matrix n n ℂ}
    (h1 : RealizesUpToFrame op1 1 U1)
    (h2 : RealizesUpToFrame op2 f2 U2) :
    RealizesUpToFrame (op2 * op1) f2 (U2 * U1) := by
  have hcomm : U2 * (1 : Matrix n n ℂ) = (1 : Matrix n n ℂ) * U2 := by
    rw [Matrix.mul_one, Matrix.one_mul]
  have := realizes_comp h1 h2 hcomm
  rwa [Matrix.mul_one] at this

/-! ## §2. Per-gate gadget interface + IsCliffordT induction.

    [VALIDATED] PPMGadgetInterface and compileToPPM_correct type-check clean;
    compileToPPM_correct depends only on [propext, Classical.choice, Quot.sound]
    (no sorry, no new axiom). The seq case is discharged exactly by realizes_comp;
    `uc_eval (UCom.seq c₁ c₂)` reduces to `uc_eval c₂ * uc_eval c₁` by defeq, so
    `exact` closes it. -/

/-- Per-gate + frame-conjugation INTERFACE for the PPM compiler at a fixed
    dimension `dim`. Everything the gate-by-gate induction needs is packed as
    fields; each is a Clifford/Pauli/lattice-surgery fact about the gadget set,
    left as an explicit interface so the COMPOSITION is PROVEN modulo it.

    The composite frame is *built* by the interface as
    `frame (seq c₁ c₂) = frame c₂ * conj c₂ (frame c₁)`, exactly the shape
    `realizes_comp` produces, so the seq case closes with no residual goal. -/
structure PPMGadgetInterface (dim : Nat) where
  /-- The PPM-compiled operator for a circuit (lattice-surgery realization). -/
  compile : BaseUCom dim → Square dim
  /-- The accumulated Pauli/Clifford frame for a circuit. -/
  frame   : BaseUCom dim → Square dim
  /-- Conjugation of a frame `f` through a circuit's unitary: the
      Gottesman/Heisenberg byproduct `uc_eval c * f = conj c f * uc_eval c`. -/
  conj    : BaseUCom dim → Square dim → Square dim
  /-- The conjugation law (the per-step Pauli-frame-update rule). -/
  conj_law :
    ∀ (c : BaseUCom dim) (f : Square dim),
      uc_eval c * f = conj c f * uc_eval c
  /-- The compiler composes the compiled pieces (lattice-surgery sequencing). -/
  compile_seq :
    ∀ (c₁ c₂ : BaseUCom dim),
      compile (UCom.seq c₁ c₂) = compile c₂ * compile c₁
  /-- The composite frame is the accumulated frame `realizes_comp` produces. -/
  frame_seq :
    ∀ (c₁ c₂ : BaseUCom dim),
      frame (UCom.seq c₁ c₂) = frame c₂ * conj c₂ (frame c₁)
  /-- Per-gate gadget realization, base case `gate1` (one-qubit gate
      teleportation: H / S / T / S† / T† / I). -/
  realize_gate1 :
    ∀ {u : BaseUnitary 1} {nq : Nat}
      (_ : u = U_H ∨ u = U_S ∨ u = U_T ∨ u = U_SDAG ∨ u = U_TDAG ∨ u = U_I),
      RealizesUpToFrame (compile (UCom.app1 u nq)) (frame (UCom.app1 u nq))
        (uc_eval (UCom.app1 u nq))
  /-- Per-gate gadget realization, base case `cnot` (CNOT lattice surgery). -/
  realize_cnot :
    ∀ {m nq : Nat},
      RealizesUpToFrame (compile (UCom.app2 BaseUnitary.CNOT m nq))
        (frame (UCom.app2 BaseUnitary.CNOT m nq))
        (uc_eval (UCom.app2 BaseUnitary.CNOT m nq))

/-- **Deliverable 3. The PPM compiler-correctness induction (parametric, no Shor
    content).** For any Clifford+T circuit `C`, its PPM compilation realizes the
    circuit's unitary `uc_eval C` up to the accumulated frame — PROVEN by
    induction on `IsCliffordT`. The base cases are the gadget hypotheses; the
    `seq` case is the `realizes_comp` COMPOSITION (§1), with the frame conjugation
    supplied by the interface's `conj_law`. Hence the gate-by-gate composition is
    fully proven modulo the per-gate gadget interface. -/
theorem compileToPPM_correct {dim : Nat} (Iface : PPMGadgetInterface dim)
    {C : BaseUCom dim} (hC : IsCliffordT C) :
    RealizesUpToFrame (Iface.compile C) (Iface.frame C) (uc_eval C) := by
  induction hC with
  | seq _h1 _h2 ih1 ih2 =>
      rename_i c₁ c₂
      rw [Iface.compile_seq c₁ c₂, Iface.frame_seq c₁ c₂]
      exact realizes_comp ih1 ih2 (Iface.conj_law c₂ (Iface.frame c₁))
  | gate1 h =>
      exact Iface.realize_gate1 h
  | cnot =>
      exact Iface.realize_cnot

/-! ## §3. Worked T-gadget instance (REUSES PPMDenote.gadgetDenote_eq).

    [VALIDATED] tGadget_realizes_frame closes by `rfl` (definitional);
    tGadget_denote_eq_frame_apply reuses the repo's already-proven
    PPMDenote.gadgetDenote_eq. Both axiom-clean. -/

/-- **The T-gadget as a `RealizesUpToFrame` instance.** Reusing PPMDenote's
    `gadgetDenote`/`gadgetDenote_eq`, the flattened gadget operator
    `corr * proj * U` realizes its interaction unitary `U` up to the
    measurement-and-correction frame `corr * proj`. Concrete worked instance of
    the abstract predicate: the gadget's denotation IS `frame * U` on the nose.
    Stated generically in `(U, proj, corr)` so it covers BOTH T-outcome branches
    uniformly (outcome 0: `corr = 1`; outcome 1: `corr = Shigh`). -/
theorem tGadget_realizes_frame
    (U proj corr : Matrix (Fin 4) (Fin 4) ℂ) :
    RealizesUpToFrame (corr * proj * U) (corr * proj) U := rfl

/-- **The T-gadget instance, in `gadgetDenote` form.** The PPMDenote gadget
    denotation `gadgetDenote U proj corr ψ res` equals the realized operator
    `(frame * U)` applied to `ψ ⊗ res`, with `frame = corr * proj`. Connects
    PPMDenote's state-vector denotation directly to the §1 predicate, so the
    repo's already-proven `tGadget_denote_outcome_0/1` are instances. -/
theorem tGadget_denote_eq_frame_apply
    (U proj corr : Matrix (Fin 4) (Fin 4) ℂ)
    (ψ res : StateVec 1) :
    FormalRV.PPM.PPMDenote.gadgetDenote U proj corr ψ res
      = ((corr * proj) * U) * (ψ ⊗ᵥ res) := by
  rw [FormalRV.PPM.PPMDenote.gadgetDenote_eq, Matrix.mul_assoc]

/-! ## §4. TRANSFER — realization up to frame ⇒ success preservation
        (CLEAN CONDITIONAL; the repo has NO uc_eval→prob lemma; see honest_gaps).

    [VALIDATED] realizes_trivial_frame and success_transfer type-check clean and
    are axiom-clean. -/

/-- **Frame-trivial realization is exact.** A compilation realizing `U` with
    frame `1` equals `U` on the nose. -/
theorem realizes_trivial_frame {n : Type*} [Fintype n] [DecidableEq n]
    {op U : Matrix n n ℂ}
    (h : RealizesUpToFrame op (1 : Matrix n n ℂ) U) : op = U := by
  rw [show op = (1 : Matrix n n ℂ) * U from h, Matrix.one_mul]

/-- **Deliverable 4. Transfer skeleton (clean conditional).** Given a success
    functional `succ : Square dim → ℝ` (probability-of-success as a function of the
    realized circuit unitary) and an abstract *frame-invariance* hypothesis
    `hframe` (the success functional is unchanged by the residual Pauli/Clifford
    frame — operationally: frame-aware post-processing, or a frame trivial on the
    measured subspace), a compilation realizing `uc_eval C` up to frame `f` has
    the SAME success probability as the verified circuit.

    `hframe` is exactly the missing repo lemma (no `uc_eval C₁ = uc_eval C₂ ⇒
    equal success`, and no frame-tolerant decoding). Stated as a CONDITIONAL on
    it rather than assuming it, so the dependency is explicit and the theorem is
    axiom-free. -/
theorem success_transfer {dim : Nat}
    (succ : Square dim → ℝ)
    {compiledOp f : Square dim} {C : BaseUCom dim}
    (hreal : RealizesUpToFrame compiledOp f (uc_eval C))
    (hframe : ∀ U : Square dim, succ (f * U) = succ U) :
    succ compiledOp = succ (uc_eval C) := by
  rw [show compiledOp = f * uc_eval C from hreal, hframe]

end FormalRV.PPM.PPMCompilerCorrectness