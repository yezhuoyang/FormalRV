/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd
  ────────────────────────────────────────────────
  Thin re-export shim.  CLOSING THE MULTI-ADD GAP for the oblivious-carry-runway
  adder (formerly a single 599-line file) has been split into three submodules —
  for per-file compile memory only — each keeping the SAME module namespace
  `FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd`.  Every
  declaration, statement, name and proof is preserved VERBATIM:

    • `…RunwayAdderMultiAdd.Preserve`     — §1–§5: gate iteration (`iterGate`), the
      iteration invariant `IterReady`, the cross-segment frame lemmas, the
      `IterReady`-preservation chain, and addend invariance (`runwayAddK_addend_eq`).
    • `…RunwayAdderMultiAdd.MultiAddStep` — §6–§8: the per-segment add step engine,
      iterated preservation over `t` runway adds, and the MAIN per-segment
      multi-add `runwayAddK_iter_segReg`.
    • `…RunwayAdderMultiAdd.Headline`     — §9–§10: the HEADLINE contiguous
      multi-add (`runwayAddK_iter_contiguous`) and the standard `a + t·b`
      corollary `runwayAddK_iter_contiguous_clean`.

  Iterating the runway adder `t` times against the SAME addend register (restored
  bit-for-bit each add) accumulates, in the contiguous reading,
  `contiguousAugend + t·contiguousAddend`, EXACT under per-segment no-overflow.
  This is the deterministic core of the deferred-accumulation deviation.  No
  `sorry`, no `native_decide`, no axioms beyond the prelude.

  Importing `RunwayAdderMultiAdd` re-exports all three, so existing importers are
  unchanged.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd.Preserve
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd.MultiAddStep
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd.Headline
