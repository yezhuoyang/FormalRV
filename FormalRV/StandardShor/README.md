# `FormalRV.StandardShor` — the teaching baseline

**New here? Start with [`FormalRV/StandardShor.lean`](../StandardShor.lean).**

It is the **standard, textbook implementation of Shor's algorithm + surface-code
lattice surgery** — the version to understand *before* the advanced low-overhead
tricks the research papers layer on top (qLDPC / lifted-product / generalised-bicycle
codes, windowed Ekerå–Håstad, factory sharing, reaction-limited pipelining). It
**redefines nothing**: it curates and re-exports, under one namespace
`FormalRV.StandardShor`, the verified results of the standard pipeline.

> The order-finding success bound is **ported from the Coq [`SQIR`](https://github.com/inQWIRE/SQIR)
> project** — that attribution lives in the original `FormalRV.SQIRPort.*` names, which
> the `StandardShor` names alias.

## The four steps of "standard Shor on a surface code"

| Step | What is verified | `StandardShor` name |
|---|---|---|
| **1. The algorithm succeeds** | order finding succeeds with prob. `≥ κ/(log₂N)⁴` (κ = 4·e⁻²/π²), N-parametric | `orderFindingSucceeds`, `successProbabilityBound`, `successConstant` |
| **2. The circuit is correct** | a SQIR-faithful modular multiplier (built from the verified Cuccaro adder) implements the oracle | `verifiedModularMultiplier`, `cuccaroAdderCorrect` |
| **3. Gates = lattice surgery** | on the distance-3 surface code, a logical CNOT is a verified ZZ-merge + XX-merge; a Toffoli is a verified `|C̄CZ̄⟩` injection | `surfaceCnotVerifies`, `surfaceToffoliInjectionVerifies` |
| **4. End to end** | the Shor PPM program is physically realized as a surface-code surgery schedule that reduces the stabilizer state | `surfaceShorEndToEnd`, `surfaceFullStack` |

## Verify it yourself

```bash
lake build FormalRV.StandardShor      # every step type-checks
```

For the **system-scheduling + neutral-atom** view of this same surface-code pipeline,
see the worked example in [`Example/`](../../Example) (the 2-bit adder, end to end) and
[`Example/neutral_atom/`](../../Example/neutral_atom).

## How this relates to the research papers

`StandardShor` is the **surface-code baseline**. Each corpus paper trades it for lower
overhead — and [`FormalRV/Audit/`](../Audit) audits each one against its claim:

- **Gidney–Ekerå 2021** / **Gidney 2025** — still surface-code, but windowed arithmetic
  + factory farms + residue (CFS) arithmetic to cut qubits/time.
- **Cain–Xu 2026** / **Webster 2026 (Pinnacle)** — replace the surface code with
  high-rate **qLDPC** codes (lifted-product / generalised-bicycle) for order-of-magnitude
  fewer qubits.
- **Babbush 2026** — the same machinery applied to ECC-256 (non-RSA).

If you understand `StandardShor`, you have the scaffolding to read all of them: the
algorithm-success bound (Step 1) is **shared, N-parametric, and reused by every paper**.
