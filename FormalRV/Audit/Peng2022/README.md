# Audit · peng-2022 — formally-verified Shor (SQIR/Coq) (arXiv:2204.07112)

**Headline:** a machine-checked end-to-end Shor; the **cross-cutting** order-finding success bound
`≥ κ/(log₂N)⁴` (κ = 4·e⁻²/π²), N-parametric, ported from SQIR's Coq proof — **every other paper's
algorithm layer reuses it.**

This paper is **algorithm-level only**: it has no QEC / system / PPM layers, so those rows are
honest ⬜ GAPs (not faked). [`Verifier.lean`](Verifier.lean) `#verify_clean`-ACCEPTS the success bound.

## Per-layer ledger  (✅ verify-clean · ⬜ GAP / abstract)

| Layer | File | Status |
|---|---|---|
| Hardware | [`Hardware.lean`](Hardware.lean) | ⬜ abstract (default placeholder; no hardware model) |
| System zones | [`SystemZones.lean`](SystemZones.lean) | ⬜ GAP — no zoned architecture (algorithm-level paper) |
| L1 algorithm | [`L1_Algorithm.lean`](L1_Algorithm.lean) | ✅ **THE cross-cutting bound** `Shor_correct_var`, `master_success_bound` |
| L2 arithmetic | [`L2_Arithmetic.lean`](L2_Arithmetic.lean) | ✅ SQIR-faithful modular multiplier realizes the oracle |
| L3 PPM | [`L3_PPM.lean`](L3_PPM.lean) | ⬜ GAP — no lattice-surgery / PPM layer |
| L4 code | [`L4_Code.lean`](L4_Code.lean) | ⬜ trivial (1,1,1) placeholder — the bound is code-agnostic |
| Verifier | [`Verifier.lean`](Verifier.lean) | ✅ algorithm success ≥ κ/(log₂N)⁴ (axiom-clean) |
| Codegen | [`Codegen.lean`](Codegen.lean) | emits the ACTUAL construction at each level via the general emitters (L1 = Peng's verified Shor circuit; L3/L4/system show the standard surface code other papers pair with this code-agnostic algorithm) |

## STILL UNSOLVED
- the ported QPE peak / continued-fractions semantics are the open frontier (the bound is clean at
  the level checked here; finishing the full quantum-state-semantics port remains);
- connecting Peng's gate-count bounds to the success theorem as a verified resource chain.
