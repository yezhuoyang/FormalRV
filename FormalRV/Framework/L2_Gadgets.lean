/-
  FormalRV.Framework.L2_Gadgets — Layer 2 (logical arithmetic
  gadgets) interface.

  Phase A.3 of the paper plan (`PAPER_PLAN.md`). This file is the
  uniform re-export point for the verified-tier L2 gadgets the
  framework supplies: the Gidney ripple-carry adder and the
  single-iteration unary lookup. Both semantic-correctness theorems
  already exist in the project (`BQAlgo/RippleCarryAdder.lean`
  Iter 213; `BQAlgo/UnaryLookup.lean` Iter 241), but they were
  proven before the four-layer framework was formalised. Future
  Phase-A ticks will add controlled adder, modular reduction, and
  QFT to this namespace.

  L2 supplies the L2 → L1 contract:
    For each gadget, a per-gadget semantic-correctness theorem
    paired with a `T`-count theorem on the same construction.
-/

import FormalRV.Arithmetic.RippleCarryAdder
import FormalRV.Arithmetic.UnaryLookup
import FormalRV.Framework.L3_PPM

namespace FormalRV.Framework.L2

/-- Re-export: the Gidney ripple-carry adder's parametric semantic-
correctness theorem. Closed at Iter 213 (2026-05-14) in
`BQAlgo/RippleCarryAdder.lean`. -/
abbrev gidney_adder_correct :=
  @FormalRV.BQAlgo.gidney_classical_action_with_reverse

/-- Re-export: the unary-lookup single-iteration semantic-correctness
theorem. Closed at Iter 241 (2026-05-14) in
`BQAlgo/UnaryLookup.lean`. -/
abbrev unary_lookup_iteration_correct :=
  @FormalRV.BQAlgo.Lookup.unary_lookup_iteration_correct

end FormalRV.Framework.L2
