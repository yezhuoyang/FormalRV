/-
  FormalRV.Arithmetic.ModularAdder.Cuccaro
  ────────────────────────────────────────
  THE LIVE modular adder `(x + c) mod N` — the Cuccaro/SQIR-style family the
  verified modular multiplier and Shor actually use. Follows the same
  Def / Correctness / Resource spine as `ModularAdder.Gidney`, but only
  **surfaces** the family: the definitions and proofs stay physically under
  `Cuccaro/CuccaroSQIRDirtyFlag/` (they are built on the Cuccaro adder and are
  imported by `ModMult/`). No definitions or proofs are added here.

    • `Cuccaro/Def.lean`         — re-exports `sqir_style_modAddConst_clean_gate`,
                                   `sqir_style_controlledModAddConst_gate`.
    • `Cuccaro/Correctness.lean` — `cuccaroModAddConst_correct`,
                                   `cuccaroControlledModAddConst_correct`.
    • `Cuccaro/Resource.lean`    — qubit budget (`sqir_modmult_rev_anc bits`).

  Live path:
    `ModMult.modmult_step_gate → sqir_style_controlledModAddConst_gate
       → modmult_MCP_gate (verified multiplier) → VerifiedShor`.
-/
import FormalRV.Arithmetic.ModularAdder.Cuccaro.Def
import FormalRV.Arithmetic.ModularAdder.Cuccaro.Correctness
import FormalRV.Arithmetic.ModularAdder.Cuccaro.Resource
