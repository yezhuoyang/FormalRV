# Audit · webster-2026 "The Pinnacle Architecture" — RSA-2048 < 100k qubits (arXiv:2602.11457)

**Headline:** RSA-2048 in < 100,000 physical qubits via generalised-bicycle (GB) qLDPC codes
(Processing Units + Magic Engines + Memory; Pauli-based computation).

**Honest status:** the GB-code-PARAMETER foundation is verified (a real [[72,12,6]] GB code, k DERIVED
from the matrices); the rest of the stack is the ROADMAP — its `Verifier.lean` end-to-end obligation
stays **open**, shown openly (no number is claimed as a proof).

## Per-layer ledger  (✅ verify-clean · ➗ arithmetic/native · ⬜ GAP/recorded)

| Layer | File | Status |
|---|---|---|
| Hardware | [`Hardware.lean`](Hardware.lean) | recorded (1e-3, 1 µs) |
| System zones | [`SystemZones.lean`](SystemZones.lean) | ⬜ GAP — Processing-Unit/Magic-Engine schedule on the roadmap |
| L1 algorithm | [`L1_Algorithm.lean`](L1_Algorithm.lean) | ✅ shared N-parametric success bound |
| L2 arithmetic | [`L2_Arithmetic.lean`](L2_Arithmetic.lean) | ⬜ GAP — GB-code arithmetic not assembled |
| L3 PPM | [`L3_PPM.lean`](L3_PPM.lean) | ⬜ GAP — GB measurement gadget (parallels cain-xu LP surgery) |
| L4 code | [`L4_Code.lean`](L4_Code.lean) | ➗ [[72,12,6]] GB k=12 DERIVED from matrices; ✅ RSA instance [[1620,16,24]] recorded |
| Verifier | [`Verifier.lean`](Verifier.lean) | end-to-end < 100k obligation OPEN (roadmap); ✅ on what is proven |

## STILL UNSOLVED (the Pinnacle roadmap)
- the RSA-scale GB [[1620,16,24]] parity matrices + k (homological formula, brute-rank-infeasible);
- the Processing-Unit logical-Pauli-measurement gadget on a GB code;
- the Magic Engine resource model (one |C̄CZ̄⟩ per cycle, supply ≥ demand);
- PBC compilation + the verified < 100,000-qubit resource bound.
