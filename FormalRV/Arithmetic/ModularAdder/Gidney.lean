/-
  FormalRV.Arithmetic.ModularAdder.Gidney
  ───────────────────────────────────────
  THE Gidney-based modular adder `(x + c) mod N`, built on the patched Gidney
  ripple-carry adder. Follows the Def / Correctness / Resource spine convention:

    • `Gidney/Def.lean`         — THE definitions (`modAddConstGate`,
                                  `controlledModAddConstGate`, and the standalone
                                  modular-multiplier tower). No proofs.
    • `Gidney/Correctness.lean` — `modAddConst_correct`, `controlledModAddConst_correct`.
    • `Gidney/Resource.lean`    — qubit budget (`controlledModAddConst_wellTyped`).

  Supporting proofs (read only if auditing): `Gidney/PowerOfTwoCase.lean`,
  `Gidney/ForwardFaithfulness.lean`, `Gidney/ControlledPipeline.lean`,
  `Gidney/SwapSemantics.lean`.

  ⚠️ Fully verified, but STANDALONE — the verified Shor multiplier uses the
  Cuccaro/SQIR family (`FormalRV.Arithmetic.ModularAdder.Cuccaro`). See
  `ModularAdder/README.md`.
-/
import FormalRV.Arithmetic.ModularAdder.Gidney.Def
import FormalRV.Arithmetic.ModularAdder.Gidney.PowerOfTwoCase
import FormalRV.Arithmetic.ModularAdder.Gidney.ForwardFaithfulness
import FormalRV.Arithmetic.ModularAdder.Gidney.ControlledPipeline
import FormalRV.Arithmetic.ModularAdder.Gidney.SwapSemantics
import FormalRV.Arithmetic.ModularAdder.Gidney.Correctness
import FormalRV.Arithmetic.ModularAdder.Gidney.Resource
