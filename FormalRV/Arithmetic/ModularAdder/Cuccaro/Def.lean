/-
  FormalRV.Arithmetic.ModularAdder.Cuccaro.Def
  ────────────────────────────────────────────
  THE definitions of the Cuccaro/SQIR-style modular adder `(x + c) mod N` — the
  LIVE one consumed by the verified modular multiplier and Shor.

  **No definitions are added here.** The gates physically live (and stay) under
  `Cuccaro/CuccaroSQIRDirtyFlag/CuccaroModularAddDefinitions.lean`, because they
  are built on the Cuccaro MAJ/UMA adder and are imported by `ModMult/`; this
  file re-exports them so the Cuccaro modular adder follows the same
  Def/Correctness/Resource spine as `ModularAdder.Gidney`.

  THE adder:
    • `sqir_style_modAddConst_clean_gate bits N c`
        — uncontrolled clean `(x + c) mod N`.
    • `sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos`
        — controlled version; at the SQIR layout `q_start = 2, flagPos = 1` this
        is the gate `ModMult.modmult_step_gate` calls.

  Construction: the same textbook pipeline as the Gidney adder (add `c` →
  compareConst `N` (forward-MAJ-only comparator copies `decide(N ≤ x+c)` into a
  flag qubit) → conditional subtract `N` → cleanup uncomputes the flag), but the
  "add" slot is filled by the Cuccaro adder `cuccaro_n_bit_adder_full`.

  Where to look next:
    • Correctness : `Cuccaro/Correctness.lean`
    • Resource    : `Cuccaro/Resource.lean`
    • Proofs (do not edit — consumed by `ModMult/`) :
      `Cuccaro/CuccaroSQIRDirtyFlag/*`.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroModularAddDefinitions
