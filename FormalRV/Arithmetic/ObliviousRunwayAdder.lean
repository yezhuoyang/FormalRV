/-
  FormalRV.Arithmetic.ObliviousRunwayAdder
  ────────────────────────────────────────
  `runwayAddK gSep k : Gate` is a verified, fully-constructed segmented quantum
  adder. It adds two `k`-segment numbers (each segment `gSep` data bits,
  `n = k·gSep`) with carries DEFERRED into per-segment runway bits rather than
  propagated across the whole register — the core primitive of Gidney's
  oblivious-carry-runway scheme. Import this umbrella to get the whole verified
  adder for auditing any paper that uses oblivious carry runways.

  See `README.md` for the spine (which file holds which headline theorem) and
  the honest-scope ledger.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderAdvance
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderContiguous
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayDeviationFaithful
import FormalRV.Arithmetic.ObliviousRunwayAdder.Example
