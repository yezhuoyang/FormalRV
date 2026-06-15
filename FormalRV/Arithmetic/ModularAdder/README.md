# Modular adder — `(x + c) mod N`

Two verified implementations of the modular add-constant, on two different base
ripple-carry adders. They compute the same value by the same **textbook
algorithm** (add `c` → subtract `N` → use the borrow/high bit as a comparison
flag → conditionally add `N` back → uncompute the flag) and differ only in the
base adder, the way they make room for the carry, and in what consumes them.

Each implementation has its own folder, spine (`Def`/`Correctness`/`Resource`),
and a **worked example with a rendered circuit diagram** — see the per-folder
READMEs:

| | [**Gidney**](Gidney/README.md) (`Gidney/`) | [**Cuccaro / SQIR**](Cuccaro/README.md) (`Cuccaro/`) |
|---|---|---|
| **Base adder** | patched Gidney adder (`Arithmetic/RippleCarryAdder`) | Cuccaro MAJ/UMA adder (`Arithmetic/Cuccaro`) |
| **Headline def** | `modAddConstGate`, `controlledModAddConstGate` | `sqir_style_modAddConst_clean_gate`, `sqir_style_controlledModAddConst_gate` |
| **Carry headroom** | widens the internal adder by one bit (`N ≤ 2^bits`) | dedicated flag qubit (`2N ≤ 2^bits`) |
| **Physical location** | `ModularAdder/Gidney/` | defs/proofs under `Cuccaro/CuccaroSQIRDirtyFlag/`, surfaced by `ModularAdder/Cuccaro/` |
| **Proofs** | sorry/axiom-free | sorry/axiom-free |
| **Wired into Shor?** | **No — standalone** | **Yes — the live one** |
| **Worked example** | `(x+1) mod 3` → [diagram](Gidney/README.md#worked-example-x--1-mod-3-with-x--1--modaddconstgate-2-3-1) | `(x+1) mod 3` → [diagram](Cuccaro/README.md#worked-example-x--1-mod-3-with-x--1--sqir_style_modaddconst_clean_gate-3-3-1) |

## Note on `Arithmetic/README.md`

`Arithmetic/README.md` currently headlines the Gidney `controlledModAddConstGate`
as *the* controlled modular adder, but the one actually feeding Shor is the
Cuccaro `sqir_style_controlledModAddConst_gate`. (Documentation inconsistency —
not fixed here to avoid touching the file mid-refactor.)
