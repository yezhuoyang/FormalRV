# FormalRV.Framework

The structural backbone of FormalRV's four-layer software stack for benchmarking fault-tolerant Shor's algorithm. Each layer (L4 QEC code -> L3 PPM/logical ops -> L2 arithmetic gadgets -> L1 algorithm) is given a Lean `structure` plus an inter-layer *contract* that propagates error bounds upward, and the three end-to-end error mechanisms are defined here. Most contracts are currently **interface freezes**: the signatures are stable so Phase B/C corpus instances can bind against them, but the deep proofs are stubbed.

## Layout
- `L4_QECCode.lean` — `QECCode` structure (parity-check matrices + `[[n,k,d]]`) and the subthreshold error ansatz `f_code`.
- `L3_PPM.lean` — `PPMGadget` and `LogicalGateSet` structures; cycle-cost projection `tau_s_cost`.
- `L2_Gadgets.lean` — re-export point binding the framework to the already-verified arithmetic gadgets (adder, unary lookup).
- `L1_Algorithm.lean` — `ShorAlgorithm` structure (N, q_A) and the top-level `rsa_correct` anchor.
- `Contracts.lean` — the inter-layer contract theorems (currently only L4->L3).
- `Errors.lean` — the three error-mechanism budget functions (logical / approximation / algorithmic).

## Key definitions
- `QECCode` (`L4_QECCode.lean`) — a qLDPC code as parity-check matrices `hx`/`hz` plus `(n,k,d)`.
- `f_code` (`L4_QECCode.lean`) — subthreshold logical-error ansatz; stub returns `p_g` unchanged.
- `PPMGadget` / `LogicalGateSet` (`L3_PPM.lean`) — Pauli-product-measurement gadget and a universal logical gate set over an L4 code.
- `ShorAlgorithm` (`L1_Algorithm.lean`) — parametric Shor + Ekera-Hastad instance (`N`, window `q_A`).
- `logical_error_budget`, `approximation_error`, `algorithmic_success_prob` (`Errors.lean`) — the three error-mechanism budgets (Nat placeholders).

## Key theorems
- `L4_to_L3_contract` (`Contracts.lean`) — per-cycle logical error rate is bounded by `f_code(p_g, d)` — **Arithmetic-only** (both sides reduce to the stub; proof is `Nat.le_refl`).
- `rsa_correct` (`L1_Algorithm.lean`) — top-of-stack algorithm-correctness anchor — **Scaffolded** (conclusion is currently `True`).
- `L2.gidney_adder_correct` (`L2_Gadgets.lean`) — re-export of the Gidney ripple-carry adder's parametric semantic-correctness theorem — **Verified** (proven in `Arithmetic/RippleCarryAdder.lean`).
- `L2.unary_lookup_iteration_correct` (`L2_Gadgets.lean`) — re-export of the single-iteration unary-lookup correctness theorem — **Verified** (proven in `Arithmetic/UnaryLookup.lean`).
- `Errors.lean` smoke checks — `algorithmic_success_prob` monotonicity (0->0, 1->50, 33->97) — **Arithmetic-only** (`rfl`).

## Status
The two L2 gadget contracts re-export genuinely **Verified** semantic-correctness theorems from elsewhere in the project. Everything native to this folder (the L1/L3/L4 structures, `f_code`, the error budgets, and the L4->L3 contract) is **Scaffolded**: the interfaces are frozen and build clean, but the definitions are Nat placeholders and the L3->L2 and L2->L1 contracts plus a non-trivial `rsa_correct` are still future ticks.
