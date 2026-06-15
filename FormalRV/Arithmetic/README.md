# FormalRV.Arithmetic

Layer-2 (logical arithmetic) of the FormalRV stack. Each ripple-carry / modular
gadget is encoded as concrete `Gate` IR over the Framework core, given a
classical Boolean specification, and (where claimed Verified) carries a
semantic-correctness theorem proven by induction — gate counts alone never
suffice (CLAUDE.md hard rule). The terminal bridges hand a Boolean-correct
multiplier up to `Shor` as a `MultiplyCircuitProperty`.

> **Auditing a windowed-arithmetic or lookup resource claim?** Go straight to
> the **auditor's routing table** in [`Windowed/README.md`](Windowed/README.md)
> — it maps each paper claim (faithful QROM baseline, Gray-code lookup,
> measurement-based uncompute, windowed exponent, mod-N variant, paper cost
> formulas) to the exact module + headline theorem to import.

## Layout
- `Cuccaro/` — Cuccaro–DKM ripple-carry adder family (MAJ/UMA, compare, add/sub-const, mod-reduce, full adder, SQIR-style cond/mod-add, dirty-flag variant).
- `RippleCarryAdder/` — patched Gidney ripple-carry adder; spine `RippleCarryAdderDef`/`-Correctness`/`-Resource` (+ proof folders `ClassicalBridge/`, `DecideWitnesses/`, `ForwardAndCost/`, `PropagationReverse/`, `UncomputeCascade/`); forward/reverse cascades and carry-chain induction.
- `ModularAdder/` — `(x+c) mod N` and its controlled form, in **two** verified implementations: [`Cuccaro/`](ModularAdder/Cuccaro/README.md) (the **live** one feeding ModMult/Shor) and [`Gidney/`](ModularAdder/Gidney/README.md) (verified, standalone). Head-to-head in [`ModularAdder/README.md`](ModularAdder/README.md).
- `ModMult/` — constant modular multiplier via shift-and-accumulate over the Cuccaro mod-add; spine `ModMultDef`/`-Correctness`/`-Resource` (supporting proofs sealed under `Internal/`; Shor-layout variant under `ShorOracle/`).
- `ModExp/` — modular exponentiation `x → aˣ mod N` (Shor's order-finding oracle), built on the sealed `ModMult` interface; spine `ModExpDef`/`-Correctness`/`-Resource`.
- `Adder.lean` + `Adder/` — the layout-parametric **`Adder` interface** (index functions + decode-level contract) and its two proven instances `cuccaroAdder`/`gidneyAdder` — what windowed arithmetic is generic over. See [`Adder/README.md`](Adder/README.md).
- `UnaryLookup/` — Babbush-style unary-iteration QROM lookup: the faithful iteration circuit **and** the Gray-code/sawtooth read, both with selection + count theorems. See [`UnaryLookup/README.md`](UnaryLookup/README.md).
- `Windowed/` — adder-generic windowed multiplication & exponentiation (Gidney–Ekerå windows) with kernel-level value theorems; home of the auditor's routing table. See [`Windowed/README.md`](Windowed/README.md).
- `Correctness.lean` — reusable Gate-IR-to-basis-state action lemmas (CCX/CX/X/seq).
- `GateToUCom.lean` — faithful translation `Gate -> BaseUCom` for semantic reasoning.
- `MCPBridge.lean` — promotes a Boolean-correct Gate IR into `MultiplyCircuitProperty` for `Shor`.
- `RCIR.lean` — backward-compat shim: `RCIRGate := Framework.Gate`.

## Key definitions
- `cuccaro_MAJ` / `cuccaro_UMA` (`Cuccaro/Cuccaro.lean`) — the two ripple-carry primitives.
- `gidney_adder_full_faithful_no_measurement_patched` (`RippleCarryAdder/RippleCarryAdderDef.lean`) — explicit (no-measurement) Gidney adder.
- `sqir_style_controlledModAddConst_gate` (`ModularAdder/Cuccaro/Def.lean`) — **the** controlled `(x+c) mod N` the verified multiplier and Shor actually use (Cuccaro-based, dirty-flag layout). The Gidney-based `controlledModAddConstGate` (`ModularAdder/Gidney/Def.lean`) is also verified but standalone.
- `modmult_MCP_gate` (`ModMult/ModMultDef.lean`) — the in-place constant modular multiplier (`modmult_inplace_shifted` + encoding adapter).
- `Adder` (`Adder.lean`) — the adder interface; `windowedMulCircuitOf A w …` (`Windowed/WindowedCircuit.lean`) is the windowed multiplier over ANY instance `A`.
- `Gate.toUCom` (`GateToUCom.lean`) — Gate IR to `BaseUCom`.

## Key theorems
- `cuccaro_n_bit_adder_full_correct` (`Cuccaro/CuccaroFull.lean`) — full n-bit Cuccaro adder hits its three positional sum/carry/restore invariants — **Verified**.
- `gidney_adder_full_faithful_no_measurement_patched_correct` (`RippleCarryAdder/UncomputeCascade/Correctness.lean`) — target register holds the sum bits, reads preserved, carries cleared — **Verified**.
- `cuccaroControlledModAddConst_correct` (`ModularAdder/Cuccaro/Correctness.lean`) — the **live** controlled modular adder: target becomes `(x+c) mod N` iff the control is set, flag restored — **Verified**.
- `controlledModAddConst_correct` (`ModularAdder/Gidney/Correctness.lean`) — the same statement for the standalone Gidney pipeline — **Verified**.
- `modmult_correct` (`ModMult/ModMultCorrectness.lean`) — `modmult_MCP_gate` satisfies `MultiplyCircuitProperty a N` (output register holds `(a·x) mod N`, given `a·ainv ≡ 1`) — **Verified**.
- `Lookup.unary_lookup_multi_iteration_correct` (`UnaryLookup/UnaryLookupIterationCorrectness.lean`) — the faithful unary-iteration lookup XORs exactly the addressed contributions into the word register — **Verified**; `grayLookupReadAt_selects_word` (`UnaryLookup/UnaryLookupGrayCode.lean`) — the Gray-code read selects the same row at `2·(2^w−1)` Toffolis — **Verified**.
- `windowedMulCircuitOf_correct` (`Windowed/WindowedCircuitCorrect.lean`) — for ANY `Adder` and window size, the windowed multiplier decodes the accumulator to `(a·y) mod 2^bits` — **Verified**.
- `toUCom_satisfies_MultiplyCircuitProperty_of_applyNat` (`MCPBridge.lean`) — a Boolean-correct Gate IR compiles to a `MultiplyCircuitProperty` multiplier — **Verified** (conditional on its two encoding hypotheses).
- `*_meets_paper_claim` T-counts in `Cuccaro/Cuccaro.lean` — gate/T-count equalities by `decide` — **Arithmetic-only**.

## Status
Cuccaro adder, patched Gidney adder, both controlled modular adders, the
in-place modular multiplier, the modexp oracle family
(`Shor_correct_with_verified_modexp`, `ModExp/ModExpCorrectness.lean`), the
unary-lookup QROM (faithful **and** Gray-code reads), and the adder-generic
windowed multiplier are **Verified** (semantic correctness proven by
induction); their T-counts are **Arithmetic-only** side products. The
`GateToUCom`/`MCPBridge` path is **Verified** as a reduction but is exercised
end-to-end only via the multiplier above. For windowed-arithmetic scope notes
(what is and is not yet proven there), see the honest-scope section of
[`Windowed/README.md`](Windowed/README.md).

## Worked example — the adder and the multiplier, drawn

![3-bit Cuccaro adder](../../docs/diagrams/cuccaro_adder_3bit.png)

`cuccaro_n_bit_adder_full 3 0` is a complete 3-bit ripple-carry adder on 7 qubits
(a forward `MAJ` chain, then a *reverse* `UMA` chain), emitted to OpenQASM 2 by
`scripts/EmitQASM.lean` and drawn above by Qiskit. On the encoded input
(`cuccaro_input_F`: carry-in at `q0`, then interleaved `bᵢ,aᵢ` pairs),
`cuccaro_n_bit_adder_full_correct` (`Cuccaro/CuccaroFull.lean`, **Verified**,
axiom-clean) proves the three positional invariants — the sum bit at `q_{2i+1}`
becomes `cᵢ ⊕ bᵢ ⊕ aᵢ`, the `a`-register is restored, and the carry-in is restored.

![modular multiplier x->7x mod 15](../../docs/diagrams/modmult_const_2_15_7.png)

Stacking controlled modular adds gives `modmult_const_gate 2 15 7` — the
108-gate `x ↦ 7·x mod 15` multiplier above. The accumulator obeys the
shift-and-accumulate recurrence `modmult_acc_spec` (`ModMult/Internal/Spec.lean`);
for `m=2` it steps `0 → 0 → (0 + 7·2 mod 15) = 14`. `modmult_const_gate_target_decode`
(`ModMult/Internal/PrefixInvariant/StateEq.lean`, **Verified**) proves the target
decodes to `(a·m) mod N`, and the full in-place multiplier `modmult_MCP_gate` is
promoted to the `MultiplyCircuitProperty` that `Shor` consumes as its oracle
(`modmult_correct`, `ModMult/ModMultCorrectness.lean`).

### More small examples

3. **Controlled modular adder.** The conditional building block the multiplier
   stacks `bits` times is the **Cuccaro-based**
   `sqir_style_controlledModAddConst_gate` (`ModularAdder/Cuccaro/Def.lean`),
   verified by `cuccaroControlledModAddConst_correct`
   (`ModularAdder/Cuccaro/Correctness.lean`): the target becomes `(x+c) mod N`
   exactly when the control bit is set, with the flag restored. The standalone
   Gidney-based `controlledModAddConstGate` (`ModularAdder/Gidney/Def.lean`,
   `controlledModAddConst_correct`) is the same textbook pipeline on the patched
   Gidney adder — both have worked, drawn examples in their folder READMEs.
4. **A numeric trace** of `cuccaro_n_bit_adder_full 3 0` on `a=2, b=3`: the MAJ chain
   computes the carries, the reverse UMA writes the sum register `2+3 = 5 = 101₂`
   (no overflow, top carry 0) and restores `a=2` — exactly the three
   `cuccaro_n_bit_adder_full_correct` invariants on concrete inputs.

## Essential proof techniques

- **Boolean basis-state action, not matrices.** Every gate is given a `Nat → Bool`
  action `Gate.applyNat`, with per-gate lemmas (`gate_{x,cx,ccx}_acts_on_basis`)
  glued by `gate_seq_acts_on_basis` (`Correctness.lean`);
  `uc_eval_toUCom_acts_on_basis` proves this Boolean semantics agrees with the
  matrix `uc_eval` on basis vectors. So arithmetic correctness reduces to symbolic
  Boolean identities — and a gate/T-count alone is *rejected* (CLAUDE.md): two
  circuits of equal T-count can compute different functions; only the action proves
  *what* is computed.
- **Induction on the carry chain.** The proof of the adder carries a three-band
  invariant (carry positions hold `carryᵢ ⊕ aᵢ`, sum positions `bᵢ ⊕ aᵢ`, plus the
  top carry) by induction on `n`, with *frame lemmas* isolating the support so
  outside positions are provably untouched and a *shift lemma*
  (`cuccaro_carry_after_MAJ0_shift`) advancing the carry as `q_start → q_start+2`;
  the reverse `UMA` chain then algebraically inverts each `MAJ` to deposit the sum.
- **A solvable recurrence for multiplication.** Because each step adds the
  *constant* `(a·2^k) mod N` (no cross-bit dependency), the accumulator recurrence
  closes by induction on the bit index (`modmult_acc_spec_eq_mul_mod`),
  evaluating to `(a·m) mod N` after all `bits` steps.
