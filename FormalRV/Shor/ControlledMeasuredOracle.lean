/-
  FormalRV.Shor.ControlledMeasuredOracle — closing the `uc_eval`/`applyNat` gap for controlled
  gates, the foundation for putting the MEASURED oracle inside QPE.
  ════════════════════════════════════════════════════════════════════════════════════════════

  The density-QPE refinement (a literal `probability_of_success_measured`) was blocked because
  `control q` produces `uc_eval`/projection-level objects, while the measured-multiplier fold runs
  on basis-level `Gate.applyNat` register facts.  This file bridges the two:

      `uc_eval_control_toUCom_on_basis` :
        on a computational basis state, a reversible gate `G` controlled by a fresh qubit `q` acts
        as `Gate.applyNat G` when `q` is set and as the identity when `q` is clear —

            uc_eval (FormalRV.Framework.BaseUCom.control q (Gate.toUCom dim G)) · |f⟩
              = if f q then |Gate.applyNat G f⟩ else |f⟩ .

  This is the basis-level `applyNat (control q G) = if f q then applyNat G f else f` the closure
  needed: it lets a controlled unitary block be pushed through an encoded superposition exactly the
  way `embedU_gate_on_superposition` pushes an uncontrolled one — now with the `if f q` branch — so
  the controlled measured oracle's fold reuses the existing uncontrolled machinery.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.MeasuredCoherentCircuit
import FormalRV.QPE.ControlledGates
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Core.PadAction.PadActionGateEntry

namespace FormalRV.Shor.ControlledMeasuredOracle

open FormalRV.Framework
open FormalRV.Framework.BaseUCom
open FormalRV.Framework.BaseCom
open FormalRV.BQAlgo
open FormalRV.Shor.MeasuredANDUncompute (conj_outer_product)
open Matrix

noncomputable section

/-- **★ THE BASIS-LEVEL CONTROLLED-GATE BRIDGE ★** — `uc_eval (control q (toUCom G))` acts on a
    computational basis state `|f⟩` as `|applyNat G f⟩` if the control bit `f q` is set, and as
    `|f⟩` otherwise.  Hypotheses: `q` in range, `q` fresh in `G` (the control is disjoint from `G`'s
    qubits), `G` well-typed, and `G` preserves `q` (immediate from freshness — supplied by the
    caller from the QPE register layout).  This is the missing `applyNat`-level semantics of a
    controlled gate; it makes the proj-level `control` usable inside the basis-level multiplier fold. -/
theorem uc_eval_control_toUCom_on_basis {dim : Nat} (q : Nat) (G : Gate)
    (hq : q < dim) (h_fresh : is_fresh q (Gate.toUCom dim G)) (h_wt : Gate.WellTyped dim G)
    (hpres : ∀ f, Gate.applyNat G f q = f q) (f : Nat → Bool) :
    uc_eval (FormalRV.Framework.BaseUCom.control q (Gate.toUCom dim G)) * f_to_vec dim f
      = if f q then f_to_vec dim (Gate.applyNat G f) else f_to_vec dim f := by
  rw [FormalRV.SQIRPort.uc_eval_control_eq_proj_decomp q (Gate.toUCom dim G) hq h_fresh
        (FormalRV.BQAlgo.uc_well_typed_toUCom_of_Gate_WellTyped dim G h_wt),
      Matrix.add_mul,
      Matrix.mul_assoc (pad_u dim q proj1) (uc_eval (Gate.toUCom dim G)) (f_to_vec dim f),
      FormalRV.BQAlgo.uc_eval_toUCom_acts_on_basis dim G h_wt f,
      pad_u_proj0_on_f_to_vec dim q hq f,
      pad_u_proj1_on_f_to_vec dim q hq (Gate.applyNat G f), hpres f]
  by_cases hfq : f q <;> simp [hfq]

/-- **The controlled-gate density push-through** — the controlled analog of
    `MeasuredCoherentUncompute.embedU_gate_on_superposition`.  Embedding a fresh-`q`-controlled
    reversible gate as a density program pushes through an encoded superposition by acting as
    `Gate.applyNat G` on the branches with `q` set and as the identity on the branches with `q`
    clear — coefficients and coherences intact.  This is how a CONTROLLED unitary block of the
    measured oracle propagates through the fold (one `if (g i) q` per branch). -/
theorem embedU_control_gate_on_superposition
    {dim : Nat} {ι : Type*} (q : Nat) (G : Gate)
    (hq : q < dim) (h_fresh : is_fresh q (Gate.toUCom dim G)) (h_wt : Gate.WellTyped dim G)
    (hpres : ∀ f, Gate.applyNat G f q = f q)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool) :
    c_eval (Com.embedU (FormalRV.Framework.BaseUCom.control q (Gate.toUCom dim G)))
        ((∑ i ∈ s, α i • f_to_vec dim (g i)) * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
      = (∑ i ∈ s, α i • f_to_vec dim (if (g i) q then Gate.applyNat G (g i) else g i))
          * (∑ i ∈ s, α i • f_to_vec dim (if (g i) q then Gate.applyNat G (g i) else g i))ᴴ := by
  have hpush : uc_eval (FormalRV.Framework.BaseUCom.control q (Gate.toUCom dim G))
        * (∑ i ∈ s, α i • f_to_vec dim (g i))
      = ∑ i ∈ s, α i • f_to_vec dim (if (g i) q then Gate.applyNat G (g i) else g i) := by
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_smul, uc_eval_control_toUCom_on_basis q G hq h_fresh h_wt hpres (g i)]
    by_cases hgi : (g i) q <;> simp [hgi]
  rw [c_eval_embedU,
      conj_outer_product (uc_eval (FormalRV.Framework.BaseUCom.control q (Gate.toUCom dim G)))
        (∑ i ∈ s, α i • f_to_vec dim (g i)), hpush]

end

end FormalRV.Shor.ControlledMeasuredOracle
