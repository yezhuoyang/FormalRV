/-
  FormalRV.Shor.Approx — Phase C: coset / approximate modular arithmetic.

  Umbrella for the approximate-oracle (Zalka coset / Gidney piecewise-adder) layer:
  the graceful-degradation bridge, success-probability stability, the
  `ApproxCosetShor` contract with its two cited quantum obligations, and Gidney's
  combinatorial deviation metric with its subadditivity.
-/
import FormalRV.Shor.Approx.GracefulDegradation
import FormalRV.Shor.Approx.SuccessStable
import FormalRV.Shor.Approx.CosetContract
import FormalRV.Shor.Approx.Deviation
