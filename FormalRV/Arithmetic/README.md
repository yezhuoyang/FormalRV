# FormalRV.Arithmetic

Layer-2 (logical arithmetic) of the FormalRV stack. Each ripple-carry / modular
gadget is encoded as concrete `Gate` IR over the Framework core, given a
classical Boolean specification, and (where claimed Verified) carries a
semantic-correctness theorem proven by induction — gate counts alone never
suffice (CLAUDE.md hard rule). The terminal bridges hand a Boolean-correct
multiplier up to `Shor` as a `MultiplyCircuitProperty`.

## Layout
- `Cuccaro/` — Cuccaro–DKM ripple-carry adder family (MAJ/UMA, compare, add/sub-const, mod-reduce, full adder, SQIR-style cond/mod-add, dirty-flag variant).
- `RippleCarryAdder/` — patched Gidney ripple-carry adder (`Defs` + `Proofs1..5`); forward/reverse cascades and carry-chain induction.
- `ModularAdder/` — `(x+c) mod N` and its controlled form, built on the patched adder (`Defs` + `Proofs1..4`).
- `SQIRModMult/` — constant modular multiplier via shift-and-accumulate over Cuccaro mod-add (`Defs` + `Proofs1..4`).
- `UnaryLookup/` — unary address-decode lookup; indexing landed, gate sequence still a stub.
- `Correctness.lean` — reusable Gate-IR-to-basis-state action lemmas (CCX/CX/X/seq).
- `GateToUCom.lean` — faithful translation `Gate -> BaseUCom` for semantic reasoning.
- `MCPBridge.lean` — promotes a Boolean-correct Gate IR into `MultiplyCircuitProperty` for `Shor`.
- `RCIR.lean` — backward-compat shim: `RCIRGate := Framework.Gate`.

## Key definitions
- `cuccaro_MAJ` / `cuccaro_UMA` (`Cuccaro/Cuccaro.lean`) — the two ripple-carry primitives.
- `gidney_adder_full_faithful_no_measurement_patched` (`RippleCarryAdder/Defs.lean`) — explicit (no-measurement) Gidney adder.
- `controlledModAddConstGate` (`ModularAdder/Defs.lean`) — 8-step controlled `(x+c) mod N` pipeline.
- `sqir_modmult_inplace_shifted` (`SQIRModMult/Defs.lean`) — in-place constant modular multiplier.
- `Gate.toUCom` (`GateToUCom.lean`) — Gate IR to `BaseUCom`.

## Key theorems
- `cuccaro_n_bit_adder_full_correct` (`Cuccaro/CuccaroFull.lean`) — full n-bit Cuccaro adder hits its three positional sum/carry/restore invariants — **Verified**.
- `gidney_adder_full_faithful_no_measurement_patched_correct` (`RippleCarryAdder/Proofs5.lean`) — target register holds the sum bits, reads preserved, carries cleared — **Verified**.
- `controlledModAddConstGate_correct` (`ModularAdder/Proofs3.lean`) — target becomes `(x+c) mod N` iff control set, workspace restored — **Verified**.
- `sqir_modmult_inplace_shifted_correct` (`SQIRModMult/Proofs3.lean`) — output register holds `(a·x) mod N` (given `a·ainv ≡ 1`) — **Verified**.
- `toUCom_satisfies_MultiplyCircuitProperty_of_applyNat` (`MCPBridge.lean`) — a Boolean-correct Gate IR compiles to a `MultiplyCircuitProperty` multiplier — **Verified** (conditional on its two encoding hypotheses).
- `*_meets_paper_claim` T-counts in `Cuccaro/Cuccaro.lean` — gate/T-count equalities by `decide` — **Arithmetic-only**.
- unary-lookup gate sequence (`UnaryLookup/Defs.lean`) — indexing only; circuit body unwritten — **Scaffolded**.

## Status
Cuccaro adder, patched Gidney adder, controlled modular adder, and the in-place
modular multiplier are **Verified** (semantic correctness proven by induction);
their T-counts are **Arithmetic-only** side products. Unary lookup is
**Scaffolded** (indexing only). The `GateToUCom`/`MCPBridge` path is **Verified**
as a reduction but is exercised end-to-end only via the multiplier above.
