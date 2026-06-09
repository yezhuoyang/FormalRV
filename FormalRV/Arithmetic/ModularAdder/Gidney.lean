/-
  FormalRV.Arithmetic.ModularAdder.Gidney
  ───────────────────────────────────────
  THE Gidney-based modular adder, `(x + c) mod N`, and its controlled version —
  built on the patched Gidney ripple-carry adder
  (`gidney_adder_full_faithful_no_measurement_patched`, from
  `FormalRV.Arithmetic.RippleCarryAdder`) by the textbook construction:
  add `c` (widened by one bit) → subtract `N` → read the high/borrow bit as a
  comparison flag → conditionally add `N` back → uncompute the flag. Fully
  proven (sorry/axiom-free).

  ⚠️ This is a COMPLETE, verified, but currently STANDALONE implementation: the
  verified modular multiplier and Shor instead use the Cuccaro/SQIR family
  (`FormalRV.Arithmetic.ModularAdder.Cuccaro`). See `ModularAdder/README.md`.

  Headlines:
    • `modAddConstGate bits N c`            — clean `(x + c) mod N`
    • `controlledModAddConstGate …`         — controlled `(x + c) mod N`
    • `modMultConstGate` / `modMultInPlace` — the (also-standalone) Gidney
      modular multiplier built by repeating the controlled modular adder.

  Files: `Gidney/Definitions` (the Gate-IR defs), `Gidney/PowerOfTwoCase`,
  `Gidney/ForwardFaithfulness`, `Gidney/ControlledPipeline`,
  `Gidney/SwapSemantics` (the supporting proofs).
-/
import FormalRV.Arithmetic.ModularAdder.Gidney.Definitions
import FormalRV.Arithmetic.ModularAdder.Gidney.PowerOfTwoCase
import FormalRV.Arithmetic.ModularAdder.Gidney.ForwardFaithfulness
import FormalRV.Arithmetic.ModularAdder.Gidney.ControlledPipeline
import FormalRV.Arithmetic.ModularAdder.Gidney.SwapSemantics
