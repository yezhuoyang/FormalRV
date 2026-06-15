# Audit · babbush-2026 — ECC-256 discrete log < 500k qubits, 18–23 min (arXiv:2603.28846)

**Headline:** ECC-256 in < 500,000 physical qubits, in 18–23 minutes — the first NON-RSA paper.

**Honest status:** parameter-tuple binding (it stress-tests that the L1 `ShorAlgorithm` interface is
modulus-agnostic) + a magic-state spacetime FLOOR (a `native_decide` numeric value, computed with
qianxu CCZ-factory parameters as a stand-in — see the Verifier row). The end-to-end obligation is OPEN.

## Per-layer ledger  (✅ verify-clean · ➗ arithmetic/native · ⬜ GAP/recorded)

| Layer | File | Status |
|---|---|---|
| Hardware | [`Hardware.lean`](Hardware.lean) | recorded (1e-3, 1 µs fast clock) |
| System zones | [`SystemZones.lean`](SystemZones.lean) | ⬜ GAP |
| L1 algorithm | [`L1_Algorithm.lean`](L1_Algorithm.lean) | ✅ shared bound (N-agnostic — confirms modulus-agnostic interface) |
| L2 arithmetic | [`L2_Arithmetic.lean`](L2_Arithmetic.lean) | ⬜ GAP — ECC-256 arithmetic not re-synthesised |
| L3 PPM | [`L3_PPM.lean`](L3_PPM.lean) | ⬜ GAP |
| L4 code | [`L4_Code.lean`](L4_Code.lean) | ⬜ recorded surface code [[425,1,14]] |
| Verifier | [`Verifier.lean`](Verifier.lean) | ➗ magic-state spacetime FLOOR (769,500 qubit·hours) — a `native_decide` numeric value computed with the **qianxu** CCZ factory (2565 qubits, 12000 µs) as a STAND-IN, not Babbush's own factory; a framework-generalization illustration, not a Babbush-specific instantiation of the lower-bound theorem. End-to-end OPEN |
| Codegen | [`Codegen.lean`](Codegen.lean) | emits the ACTUAL construction at each level via the general emitters (small reps; Babbush params noted in comments) |

## STILL UNSOLVED
- the L1 `rsa_correct` body (shared, pending the SQIR/Coq port — see Audit/Peng2022);
- ECC-256 modular-arithmetic synthesis; the parity matrices; the 18–23 min wall-clock (not circuit-verified).
