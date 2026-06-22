/-
  FormalRV.QEC.Codes.LiftedProduct.LP16Indexing — NAIVE LOGICAL INDEXING of
  the paper-scale lp16 [[2610,744,≤16]] code: the audit convention for
  papers that give no concrete logical layout (John, 2026-06-10).

  One named block `LP0` of lp16 carrying the IMPORTED paired basis
  (`lp16ImportedBasis`, found externally, sequential labeling: virtual
  logical `i` = the `i`-th basis vector).  The structural layout obligations
  (in-range, injective) are kernel-`decide`d here; the basis-validity
  conjunct is the EXPLICITLY ACCEPTED hypothesis (decision 2026-06-10):
  the external solver self-checked all 744 in-kernel memberships and the
  full 744² δ-pairing, k = 744 matches the paper, and the off-path Lean
  certificates (`LP16BasisFullCert.lean` list-level, `LP16BitsCert.lean`
  bitset-level) discharge it when run — until then every theorem that needs
  it carries `(hvalid : lp16ImportedBasis.valid = true)` visibly, the same
  implementer-supplied-input pattern as merged-code distance.

  No `sorry`, no `axiom`; kernel `decide` only.
-/

import FormalRV.QEC.Codes.LiftedProduct.LP16BasisImport
import FormalRV.QEC.BlockAddressing

set_option maxRecDepth 2000000

namespace FormalRV.QEC.Codes.LP

open FormalRV.QEC FormalRV.QEC.BlockLayout

/-- The named lp16 block with the imported, sequentially-indexed basis. -/
def lp16Block : CodeBlock :=
  ⟨"LP0", FormalRV.QEC.Instances.lp16, 744, lp16ImportedBasis⟩

/-- Naive sequential indexing of the first 8 virtual logicals:
    virtual `i` ↦ `LP0(i)`.  (The audit circuits address a handful of
    logicals; extend the map as they grow.) -/
def lp16Layout : BlockLayout :=
  ⟨[lp16Block], (List.range 8).map (fun i => ⟨0, i⟩)⟩

/-- The structural layout obligation: in-range and injective — kernel
    `decide`, cheap even at paper scale. -/
theorem lp16Layout_wfStructural : lp16Layout.wfStructural = true := by decide

/-- The full obligation, conditional on the accepted basis validity. -/
theorem lp16Layout_wf (hvalid : lp16ImportedBasis.valid = true) :
    lp16Layout.wf = true :=
  wf_of lp16Layout lp16Layout_wfStructural
    (by simp [lp16Layout, lp16Block, List.all_cons, hvalid])

/-- The user-style PPM `Measure X[2]Z[3]` on lp16 virtual logicals. -/
def lp16DemoPPM : VirtualPPM := [(2, .x), (3, .z)]

theorem lp16DemoPPM_inRange : lp16Layout.inRange lp16DemoPPM = true := by decide

/-- Explicit block resolution: virtual 2 ↦ LP0's logical 2 (X),
    virtual 3 ↦ LP0's logical 3 (Z) — the naive sequential map. -/
theorem lp16DemoPPM_resolves :
    lp16Layout.resolve lp16DemoPPM = [(⟨0, 2⟩, .x), (⟨0, 3⟩, .z)] := by decide

theorem lp16DemoPPM_renders :
    lp16Layout.render lp16DemoPPM = "Measure X[LP0(2)] Z[LP0(3)] " := by decide

end FormalRV.QEC.Codes.LP
