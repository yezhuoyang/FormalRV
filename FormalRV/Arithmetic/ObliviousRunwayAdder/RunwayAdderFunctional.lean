/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
  ──────────────────────────────────────────────────
  Thin re-export shim.  The genuinely functional oblivious-carry-runway adder
  (formerly a single 754-line file) has been split into four submodules — for
  per-file compile memory only — each keeping the SAME module namespace
  `FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional`.  Every
  declaration, statement, name and proof is preserved VERBATIM:

    • `…RunwayAdderFunctional.TwoSegment` — §1–§10: the k = 2 one-runway adder
      (layout, circuit, concrete decodes, operand values, well-typedness,
      `decodeReg` helpers, cross-block frame lemmas, per-segment exactness, the
      headline `runwayAdd2_exact`, and the k = 2 advance bound).
    • `…RunwayAdderFunctional.KSegment` — §11–§13: the uniform k-segment adder
      (`runwayAddK`, k-segment decodes/operands, k-segment frame lemmas, and the
      headline `runwayAddK_exact`).
    • `…RunwayAdderFunctional.Advance` — §14: the k-segment advance bound.
    • `…RunwayAdderFunctional.WellTyped` — §15: k-segment well-typedness.

  Importing `RunwayAdderFunctional` re-exports all four, so existing importers are
  unchanged.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional.TwoSegment
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional.KSegment
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional.Advance
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional.WellTyped
