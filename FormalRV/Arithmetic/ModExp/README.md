# Modular exponentiation (ModExp)

Modular exponentiation `x ↦ aˣ mod N` — Shor's order-finding oracle — built **on
top of the sealed `ModMult` module**. It is a controlled chain of modular
multipliers: iterate `i` multiplies by `a^(2ⁱ) mod N`, so the controlled-powers
composition over the exponent register computes `aˣ mod N`.

> **TL;DR** — `our_modmult_family bits N a ainv multBits` is the verified modexp
> oracle family (each iterate is a `modmult_MCP_gate` from `ModMult`). It is a
> `ModMulImpl` (the semantic core), which yields the end-to-end Shor
> success-probability bound `Shor_correct_with_verified_modexp`.

## Where everything lives (the spine)

| Concern | File | Headline |
|---|---|---|
| **Definition** | [`ModExpDef.lean`](ModExpDef.lean) | `our_modmult_family` (chain of `modmult_MCP_gate`) |
| **Correctness** | [`ModExpCorrectness.lean`](ModExpCorrectness.lean) | `our_modmult_family_ModMulImpl` (iterate `i` multiplies by `a^(2ⁱ) mod N`) + `Shor_correct_with_verified_modexp` |
| **Resource** | [`ModExpResource.lean`](ModExpResource.lean) | `tcount_shorModExpVerified` = **224·bits³** |
| **Example** | [`ModExpExample.lean`](ModExpExample.lean) | worked `our_modmult_family` instances |

## Built on ModMult (the modularized design)

ModExp uses only the **sealed** public interface
`import FormalRV.Arithmetic.ModMult` (giving `modmult_MCP_gate`, `modmult_tcount`)
— it never reaches into `ModMult/Internal/`. Each modexp iterate *is* a verified
modular multiplier; the `aˣ mod N` action is the QPE `controlled_powers`
composition of the family (the order-finding proof consumes `ModMulImpl`).

So the layering is: **Cuccaro adder → ModularAdder → ModMult → ModExp → Shor**,
each level using the sealed interface of the one below.

## Two terms (honest status)

- **Semantic** (`ModExpDef`/`ModExpCorrectness`): `our_modmult_family` + its
  `ModMulImpl` proof — this is what *computes `aˣ mod N`* and drives Shor.
- **Resource** (`ModExpResource`): the `Gate`-IR chain `shorModExpVerified`
  carries the **exact** T-count `224·bits³`. It is a *separate term* from the
  BaseUCom family above; bridging the two (a single object that is both
  semantically `aˣ mod N` and carries the Gate count) is a known open gap.
