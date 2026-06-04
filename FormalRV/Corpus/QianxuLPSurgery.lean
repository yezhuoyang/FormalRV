/-
  FormalRV.Corpus.QianxuLPSurgery — a lattice-surgery gadget ON THE LP qLDPC CODE
  (closing seam 4: "no SurgeryGadget exists on any LP code; all physical compilation
  was on the surface code").

  Until now every constructed SurgeryGadget (surface3, Steane) was on a SURFACE or
  small-CSS code — never on a code from qianxu's LP family, which is what their
  architecture actually uses for memory.  This module builds a genuine X-type
  lattice-surgery gadget whose DATA CODE is the real [[18,2,d]] bivariate-bicycle code
  `bbSmall` (qianxu LP family, from `LogicalFinder`), measuring its computed logical
  operator X̄₀, and proves:

    • the gadget passes the framework's complete structural verifier (`decide`);
    • the measured target is a GENUINE logical X of the LP code (commutes with every
      Z-check, outside the X-stabilizer rowspace) — connecting to the logical-finder,
      so this measures a real logical qubit, not an arbitrary Pauli;
    • therefore `surgery_implements_logical_measurement` applies: the gadget IMPLEMENTS
      the logical Pauli measurement of X̄₀ — readout (R) = parity of the selected merged
      X-checks equals X̄₀ signed by their outcomes, and non-disturbance (N) = every
      logical commuting with the measured set survives the merge.

  This is the FIRST physical (lattice-surgery) compilation on qianxu's actual code
  family, semantically verified (Gottesman/stabilizer algebra), `decide` at 19 merged
  qubits, kernel-clean.  Distance `d` is a cited input (out of scope), used only for the
  τ_s = Θ(d) cycle criterion.

  No `sorry`, no `axiom`.
-/

import FormalRV.QEC.LogicalFinder
import FormalRV.LatticeSurgery.LDPCSurgery
import FormalRV.LatticeSurgery.SurgeryCorrect

namespace FormalRV.Corpus.QianxuLPSurgery

open FormalRV.QEC.LogicalFinder
open FormalRV.Framework
open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.Framework.SurgeryReadout
open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp

/-! ## §1. The LP code's logical X̄₀, and the surgery gadget measuring it -/

/-- The genuine logical X̄₀ of the bbSmall LP code (computed + symplectically paired in
    `LogicalFinder`), weight 6, length 18. -/
def bbLogX0 : BoolVec := (pairedLogicalX bbSmall).getD 0 []

/-- **An X-type lattice-surgery gadget on the real [[18,2,d]] bivariate-bicycle LP code.**
    Data code = bbSmall (k=2, cited d=6); 1 ancilla qubit with 2 ancilla X-checks forming
    a 1-edge tree (`H_X' = [[1],[1]]`, dim ker H_X'ᵀ = 1, one connected component); the
    connection `f_X'` couples the ancilla to the support of X̄₀; τ_s = 4 cycles
    (3·4 = 12 ≥ 2·6 = 2d). The span witness selects the two ancilla-coupled merged
    X-checks whose GF(2) sum is exactly X̄₀ (extended by 0 on the ancilla). -/
def bb_x_surgery : SurgeryGadget :=
  { data_code          := bbSmall.toQECCode 2 6
  , ancilla_n          := 1
  , ancilla_hx         := [[true], [true]]
  , ancilla_hz         := []
  , conn_x             := [bbLogX0, zero_vec 18]
  , conn_z             := bbSmall.hz.map (fun _ => [false])
  , tau_s              := 4
  , target_pauli       := bbLogX0 ++ [false]
  , span_witness       := (List.replicate bbSmall.hx.length false) ++ [true, true]
  , merged_qldpc_bound := 8 }

/-! ## §2. The gadget passes the structural verifier (component closures + headline) -/

theorem bb_x_surgery_dimensions :
    SurgeryGadget.dimensions_consistent bb_x_surgery = true := by decide

theorem bb_x_surgery_tau_s :
    SurgeryGadget.tau_s_sufficient bb_x_surgery = true := by decide

theorem bb_x_surgery_qldpc :
    SurgeryGadget.merged_is_qldpc bb_x_surgery = true := by decide

theorem bb_x_surgery_targets_correctly :
    SurgeryGadget.targets_logical_correctly bb_x_surgery = true := by decide

/-- **The LP-code surgery gadget passes the framework's complete structural verifier**
    (dimensions + qLDPC + τ_s = Θ(d) + the kernel/row-span condition). `decide` at 19
    merged qubits. -/
theorem bb_x_surgery_verifies :
    SurgeryGadget.verify_surgery_gadget bb_x_surgery = true := by decide

/-! ## §3. The measured target is a GENUINE logical X of the LP code -/

/-- **The surgery target X̄₀ is a genuine logical X of the LP code**: it commutes with
    every Z-check (in ker H_Z) and is outside the X-stabilizer rowspace — exactly the
    `LogicalFinder.logicalX_genuine` predicate, for this operator. So the gadget measures
    a REAL logical qubit of the bbSmall LP code. -/
theorem bb_surgery_target_is_logical :
    (bbSmall.hz.all (fun r => ! gf2dot r bbLogX0) && ! inRowspace bbSmall.hx bbLogX0) = true := by
  decide

/-! ## §4. Semantic correctness: the gadget IMPLEMENTS the logical measurement -/

/-- **The LP-code surgery gadget implements the logical Pauli measurement of X̄₀**
    (R ∧ N), via `surgery_implements_logical_measurement` discharged on the real
    bivariate-bicycle code:

    * (R) the `span_witness`-selected signed product of merged X-checks equals X̄₀ signed
      by the XOR-parity of their ±1 outcomes;
    * (N) every logical commuting with the measured X-check set survives the merge;
    * the measured set is a commuting family.

    Proven for an arbitrary outcome assignment `signs` (length = #merged X-checks). This
    is genuine stabilizer-algebra semantics — the first such on qianxu's LP code family,
    not the surface code. -/
theorem bb_LP_surgery_implements_logical_X
    (signs : List Bool) (hsig : signs.length = bb_x_surgery.merged_hx.length) :
    (selectedSignedProduct bb_x_surgery.span_witness bb_x_surgery.merged_hx signs
        = signedXRow (selectedParity bb_x_surgery.span_witness signs) bb_x_surgery.target_pauli)
    ∧ (∀ (L : PauliString) (s : StabilizerState), L ∈ s →
        (∀ P ∈ merged_stabilizers_X bb_x_surgery, L.commutes P = true) →
        L ∈ measureChecks (merged_stabilizers_X bb_x_surgery) s)
    ∧ (∀ p ∈ merged_stabilizers_X bb_x_surgery, ∀ q ∈ merged_stabilizers_X bb_x_surgery,
        p.commutes q = true) :=
  surgery_implements_logical_measurement bb_x_surgery bb_x_surgery.merged_n signs
    (by decide) (by decide) hsig bb_x_surgery_verifies

/-- **Headline (seam 4 closed).**  There IS a structurally-verified lattice-surgery
    gadget on qianxu's actual LP code family, measuring a genuine logical operator, whose
    logical-measurement action is semantically proven. -/
theorem LP_code_has_verified_surgery :
    SurgeryGadget.verify_surgery_gadget bb_x_surgery = true
    ∧ (bbSmall.hz.all (fun r => ! gf2dot r bbLogX0) && ! inRowspace bbSmall.hx bbLogX0) = true :=
  ⟨bb_x_surgery_verifies, bb_surgery_target_is_logical⟩

end FormalRV.Corpus.QianxuLPSurgery
