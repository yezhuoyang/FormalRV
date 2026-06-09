/-
  FormalRV.Arithmetic.ModularAdder.Cuccaro
  ────────────────────────────────────────
  Re-export of THE LIVE modular adder — the one the verified modular multiplier
  and Shor actually use: the Cuccaro/SQIR-style `(x + c) mod N` family.

  The definitions and proofs physically live under
  `FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag` (kept there because they are
  built on the Cuccaro MAJ/UMA adder `cuccaro_n_bit_adder_full`, not the Gidney
  adder); this file only surfaces them under `ModularAdder/` so both modular
  adders are discoverable from one place. **No definitions are added here.**

  Headline: `sqir_style_controlledModAddConst_gate` — the controlled modular
  add-constant that `ModMult.modmult_step_gate` calls, building
  `modmult_MCP_gate` (the verified multiplier) → VerifiedShor. The "dirty-flag"
  construction matches SQIR `ModMult.v`'s qubit layout (`q_start = 2`,
  `flagPos = 1`); the underlying primitive is the project's Cuccaro adder.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
