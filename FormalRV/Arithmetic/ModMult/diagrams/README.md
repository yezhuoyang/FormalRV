# ModMult — circuit diagrams

## Overview: `x ↦ (a·x) mod N` as shift-and-add of modular adders

![ModMult overview](modmult_modular.png)

The modular multiplier is built from **controlled modular ADDERs**. Reading left
to right (colour = role):

- 🔵 **encode** — move the input `x` into the internal register.
- 🟢 **3 green MODADDs** — add `a·2ʲ mod N` controlled by bit `xⱼ`; together they
  build `a·x` in the accumulator.
- 🟠 **SWAP** — move `a·x` into the `x` register.
- 🔴 **3 red MODADDs** — uncompute the old `x` to `0` (needs `a·a⁻¹ ≡ 1 mod N`).
- 🔵 **decode** — move the result back out.

Net: `x ↦ (a·x) mod N` in place, workspace restored. Each MODADD box is a
Cuccaro modular adder — see `modmult_step_zoom.png` for one expanded to gates,
and [`../README.md`](../README.md) for the full walkthrough.

## Zoom: one MODADD box at the gate level

![one MODADD, gate level](modmult_step_zoom.png)
