# Modular adder — `(x + c) mod N`

There are **two** verified implementations of the modular add-constant, on two
different base ripple-carry adders. They compute the same value by the same
**textbook algorithm** and differ only in the base adder and in what consumes
them.

| | **Gidney** (`ModularAdder/Gidney/`) | **Cuccaro / SQIR** (spine in `ModularAdder/Cuccaro/`) |
|---|---|---|
| **Base adder** | `gidney_adder_full_faithful_no_measurement_patched` (`Arithmetic/RippleCarryAdder`) | `cuccaro_n_bit_adder_full` (`Arithmetic/Cuccaro`) |
| **Headline def** | `modAddConstGate`, `controlledModAddConstGate` | `sqir_style_modAddConst_clean_gate`, `sqir_style_controlledModAddConst_gate` |
| **Physical location** | `Arithmetic/ModularAdder/Gidney/` | `Arithmetic/Cuccaro/CuccaroSQIRDirtyFlag/` (kept with the Cuccaro adder; surfaced here) |
| **Proofs** | sorry/axiom-free | sorry/axiom-free |
| **Wired into Shor?** | **No — standalone** | **Yes — the live one** |

> Both are the same construction: **add `c`** (widened by one bit so the sum
> can't overflow) → **subtract `N`** → the high/borrow bit is the comparison
> flag `decide(x+c < N)` → **conditionally add `N` back** when it underflowed →
> **uncompute the flag**. The only difference is which adder does the adds.

## The shared algorithm, concretely

```
addConst c        : load c into the read register, run the base adder, unload  →  target += c
subConst N        : addConst (2^bits − N)                                       →  target −= N  (two's-complement)
conditionalAdd N  : same as addConst but the loaded constant is masked by a flag (no CCCX needed)
modAddConst N c   : addConst c (width bits+1) ; subConst N ; copy high bit → flag ;
                    conditionalAdd-back N ; uncompute flag                       →  target = (x+c) mod N
controlled…       : every add/sub is gated by an external control qubit         →  if control then (x+c) mod N else x
```

Both folders follow the **Def / Correctness / Resource spine** convention used by
`RippleCarryAdder/` and `Cuccaro/`:

| Concern | Gidney (`ModularAdder/Gidney/`) | Cuccaro (`ModularAdder/Cuccaro/`) |
|---|---|---|
| **Definition** | [`Gidney/Def.lean`](Gidney/Def.lean) | [`Cuccaro/Def.lean`](Cuccaro/Def.lean) |
| **Correctness** | [`Gidney/Correctness.lean`](Gidney/Correctness.lean) — `modAddConst_correct`, `controlledModAddConst_correct` | [`Cuccaro/Correctness.lean`](Cuccaro/Correctness.lean) — `cuccaroModAddConst_correct`, `cuccaroControlledModAddConst_correct` |
| **Resource** | [`Gidney/Resource.lean`](Gidney/Resource.lean) — qubit budget | [`Cuccaro/Resource.lean`](Cuccaro/Resource.lean) — qubit budget |

## Gidney implementation (`ModularAdder/Gidney/`)

Built on **your patched Gidney adder**. Spine: `Gidney/Def.lean` (all the
Gate-IR defs: `prepareConstRead`, `addConstGate`, `subConstGate`,
`prepareMaskedConstRead`, `conditionalAddConstGate`, `copyTargetHighBitToFlag`,
`modAddConstGate`, `controlledModAddConstGate`, and a full
`modMultConstGate`/`modMultInPlace` tower, + Boolean specs),
`Gidney/Correctness.lean`, `Gidney/Resource.lean`. The supporting proofs (read
only if auditing) live in `Gidney/PowerOfTwoCase.lean`,
`Gidney/ForwardFaithfulness.lean`, `Gidney/ControlledPipeline.lean`,
`Gidney/SwapSemantics.lean` (frame lemmas, clean bundles,
`controlledModAddConstGate_correct`, multiplier correctness, swap semantics).

It is **complete and verified** but currently **unused by Shor**: its only
out-of-folder reach is `MCPBridge.lean` (`modMultInPlaceShor_…`), which nothing
in `Shor/` consumes. `ModMult/` imports this folder only to borrow the
SWAP/layout primitives, not the Gidney modular adder.

## Cuccaro / SQIR implementation (`ModularAdder/Cuccaro/` → `Cuccaro/CuccaroSQIRDirtyFlag/`)

Built on the **Cuccaro** adder; "SQIR-style" means it matches SQIR `ModMult.v`'s
qubit layout (`q_start = 2`, `flagPos = 1`), not that it uses a SQIR base adder.
The `ModularAdder/Cuccaro/` spine (`Def`/`Correctness`/`Resource`) only
**surfaces** the family — the definitions and proofs stay under
`Cuccaro/CuccaroSQIRDirtyFlag/` (they belong with the Cuccaro adder and are
imported by `ModMult/`). This is the **live** one:

```
ModMult.modmult_step_gate  →  sqir_style_controlledModAddConst_gate
                           →  modmult_const_gate  →  modmult_MCP_gate  (verified multiplier, `modmult_correct`)
                           →  MCPBridge  →  VerifiedShor
```

The `ModularAdder/Cuccaro/` spine adds **no** definitions or proofs — it
re-exports the family (kept under `Arithmetic/Cuccaro/CuccaroSQIRDirtyFlag/`,
where it belongs with the Cuccaro adder and is consumed by `ModMult/`) so both
modular adders are discoverable from `ModularAdder/` under the same spine shape.

## Note on `Arithmetic/README.md`

`Arithmetic/README.md` currently headlines the Gidney `controlledModAddConstGate`
as *the* controlled modular adder, but the one actually feeding Shor is the
Cuccaro `sqir_style_controlledModAddConst_gate`. (Documentation inconsistency —
not fixed here to avoid touching the file mid-refactor.)
