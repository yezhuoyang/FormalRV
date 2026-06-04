/-
  FormalRV.Corpus.QianxuGadgetDerivedResource — GROUND the resource constants in a
  CONSTRUCTED, VERIFIED surgery gadget on the LP code (closing seam 7).

  The audit's seam 7: "resource numbers (τ_s, per-Toffoli cost, ancilla) are Nat arithmetic
  over hand-picked constants, not derived from constructed gadgets."  Now that seam 4 gives
  a structurally-verified lattice-surgery gadget `bb_x_surgery` ON the real LP code, its
  resource quantities are no longer free `def`s — they are read off a VERIFIED gadget:

    • the per-logical-measurement TIME = `perToffoli τ_s cycle`, where τ_s is the
      surgery-round count `surgeryRounds bb_x_surgery` of a gadget that PASSES the
      structural verifier (`bb_x_surgery_verifies`) — including the τ_s = Θ(d) criterion;
    • the physical FOOTPRINT (data + surgery ancilla + syndrome ancillas) = 39 qubits,
      `surgeryPhysQubits bb_x_surgery`, derived from the merged-code structure;
    • the standing operation-zone ancilla per surgery = `bb_x_surgery.ancilla_n`.

  So the time bound's per-PPM cost is the cost of a SEMANTICALLY-VERIFIED logical
  measurement (seam 4's `bb_LP_surgery_implements_logical_X`), and the τ_s feeding it is
  the round count of an actual verified gadget — not an asserted `def`.

  Residue (honest): this grounds the per-OPERATION cost at the [[18,2,d]] gadget scale; the
  full lp_20 [[4350,…]] instance scales the SAME structure (τ_s = ⌈2d/3⌉ for its own d),
  the documented compute residue.

  No `sorry`, no `axiom`.
-/

import FormalRV.Corpus.QianxuLPSurgery
import FormalRV.Corpus.QianxuBounds
import FormalRV.Corpus.SurfaceShorResourceCount

namespace FormalRV.Corpus.QianxuGadgetDerivedResource

open FormalRV.Corpus.QianxuLPSurgery
open FormalRV.Corpus.QianxuBounds
open FormalRV.Corpus.SurfaceShorResourceCount
open FormalRV.Framework.LDPC

/-! ## §1. τ_s and the footprint, DERIVED from the verified LP gadget -/

/-- The surgery-round count (τ_s) FEEDING the time bound, read off the verified LP-code
    gadget — not a hand-picked constant. -/
def lpGadgetTauS : Nat := surgeryRounds bb_x_surgery

theorem lpGadgetTauS_eq : lpGadgetTauS = 4 := by decide

/-- The physical footprint of one LP-code logical measurement (data + surgery ancilla +
    one syndrome ancilla per merged check), derived from the gadget = 39 qubits. -/
theorem lpGadget_footprint : surgeryPhysQubits bb_x_surgery = 39 := by decide

/-- Total syndrome measurements over the τ_s-round surgery, derived from the gadget. -/
theorem lpGadget_total_meas : surgeryTotalMeas bb_x_surgery = 80 := by decide

/-! ## §2. The per-PPM time is the cost of a VERIFIED gadget, not a free def -/

/-- **The per-logical-measurement TIME is GROUNDED in the verified gadget.**  The per-PPM
    cost `perToffoli τ_s cycle` uses τ_s = the surgery-round count of `bb_x_surgery`, a
    gadget that PASSES the structural verifier — so this equals `bb_x_surgery.tau_s · cycle`,
    the cost of a structurally-verified surgery on the LP code, for every `cycle`. -/
theorem perPPM_time_from_verified_gadget (cycle : Nat) :
    perToffoli (surgeryRounds bb_x_surgery) cycle = bb_x_surgery.tau_s * cycle := by
  rfl

/-- The τ_s in the resource bound is the round count of a gadget that is BOTH structurally
    verified AND semantically implements the logical measurement (seam 4). -/
theorem lpGadget_tau_is_verified :
    SurgeryGadget.verify_surgery_gadget bb_x_surgery = true
    ∧ surgeryRounds bb_x_surgery = bb_x_surgery.tau_s :=
  ⟨bb_x_surgery_verifies, rfl⟩

/-! ## §3. Headline: seam 7 grounded -/

/-- **Seam 7 (per-operation cost grounded).**  The resource bound's per-PPM time is
    `perToffoli τ_s cycle` with τ_s = `surgeryRounds bb_x_surgery` = 4, the surgery-round
    count of a structurally-VERIFIED lattice-surgery gadget on the real LP code (which also
    semantically implements the logical measurement, seam 4); its physical footprint is the
    derived 39-qubit merged-code count.  The per-operation resource is no longer a
    hand-picked `def` — it is read off a constructed, verified gadget. -/
theorem resource_grounded_in_verified_gadget (cycle : Nat) :
    SurgeryGadget.verify_surgery_gadget bb_x_surgery = true
    ∧ perToffoli (surgeryRounds bb_x_surgery) cycle = bb_x_surgery.tau_s * cycle
    ∧ surgeryPhysQubits bb_x_surgery = 39 :=
  ⟨bb_x_surgery_verifies, perPPM_time_from_verified_gadget cycle, lpGadget_footprint⟩

end FormalRV.Corpus.QianxuGadgetDerivedResource
