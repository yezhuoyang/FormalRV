/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth
  ──────────────────────────────────────────────────────
  Thin re-export shim.  A **PARALLEL (ASAP critical-path) depth** measure on the
  `Gate` IR and the oblivious-carry-runway adder's depth advantage proved against
  it (formerly a single 693-line file) has been split into four submodules — for
  per-file compile memory only — each keeping the SAME module namespace
  `FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth`.  Every declaration,
  statement, name and proof is preserved VERBATIM:

    • `…ParallelDepth.Scheduler`      — §1–§5: gate support `supp`, the ASAP
      scheduler (`tick`/`sched`), `maxOver` algebra, the disjoint-`seq` law
      `parallelDepth_seq_disjoint`, and `parallelDepth_le_depth`.
    • `…ParallelDepth.CuccaroSupport` — §6–§7: Cuccaro support containment and
      runway-segment support/disjointness (`runwayAddK_segAdd_disjoint`).
    • `…ParallelDepth.Shift`          — §8–§9: shift-invariance of `parallelDepth`
      and base-independence of the Cuccaro circuit's parallel depth.
    • `…ParallelDepth.Headline`       — §10: the headline `parallelDepth_runwayAddK_eq`.

  `Gate.depth` (in `Core/Gate.lean`) SUMS over `seq`, so it is the SEQUENTIAL gate
  count: a `seq` of `k` disjoint segments costs `k ×` one segment — it can never
  show a parallelism win.  `parallelDepth` here instead schedules every gate
  As-Soon-As-Possible, so two gates on DISJOINT qubits do not delay each other and
  `parallelDepth (runwayAddK gSep k)` equals ONE segment's depth, INDEPENDENT of
  `k` — the realized oblivious-carry depth advantage.  See `Example.lean`.

  Importing `ParallelDepth` re-exports all four, so existing importers are unchanged.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth.Scheduler
import FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth.CuccaroSupport
import FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth.Shift
import FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth.Headline
