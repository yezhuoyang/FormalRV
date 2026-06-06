# Audit · webster-2026 "The Pinnacle Architecture" — RSA-2048 < 100k qubits (arXiv:2602.11457)

**Headline:** RSA-2048 in < 100,000 physical qubits via generalised-bicycle (GB) qLDPC codes
(Processing Units + Magic Engines + Memory; Pauli-based computation).

Every file lives in ONE flat namespace `FormalRV.Audit.Pinnacle`. [`Verifier.lean`](Verifier.lean)
runs `#verify_clean` on the ✅ theorems (a `sorry`/native axiom would fail the build).

**Honest status:** the GB-code-PARAMETER foundation is verified (a real [[72,12,6]] GB code, k DERIVED
from the constructed parity matrices); the rest of the stack is the ROADMAP — its `Verifier.lean`
end-to-end < 100k obligation stays **open**, shown openly (no number is claimed as a proof).

## Settings a reader should check match the paper
- physical error 1e-3; error-correction cycle 1 µs; reaction 10 µs (paper §III.D baseline)
- RSA-2048 GB code instance [[1620,16,24]] (n_cb = 1620, κ = 16, distance 24, syndrome rounds d+2 = 26)

## Per-layer ledger  (✅ verify-clean · ➗ arithmetic/native · ⬜ GAP/recorded)

| Layer | File | Status |
|---|---|---|
| Hardware | [`Hardware.lean`](Hardware.lean) | recorded (1e-3, 1 µs, 10 µs reaction) |
| System zones | [`SystemZones.lean`](SystemZones.lean) | ⬜ GAP — Processing-Unit/Magic-Engine schedule on the roadmap |
| L1 algorithm | [`L1_Algorithm.lean`](L1_Algorithm.lean) | ✅ shared N-parametric success bound |
| L2 arithmetic | [`L2_Arithmetic.lean`](L2_Arithmetic.lean) | ⬜ GAP — GB-code arithmetic not assembled |
| L3 PPM | [`L3_PPM.lean`](L3_PPM.lean) | ⬜ GAP — GB measurement gadget (parallels cain-xu LP surgery) |
| L4 code | [`L4_Code.lean`](L4_Code.lean) | ➗ REAL [[72,12,6]] GB code, k=12 DERIVED from constructed matrices; ✅ RSA instance [[1620,16,24]] recorded |
| Verifier | [`Verifier.lean`](Verifier.lean) | end-to-end < 100k obligation OPEN (roadmap); ✅ on what is proven |
| Codegen | [`Codegen.lean`](Codegen.lean) | emits the ACTUAL construction at each level; L4 emits Pinnacle's REAL `pinnacle_gb_72` (hx/hz/derivedK) |

## Our approach
The verified strength is the GB-code-parameter framework: a representative Pinnacle GB code
(`pinnacle_gb_72`, the [[72,12,6]] gross-code-family instance) is CONSTRUCTED via the shared
`bivariateBicycle`/`CSSCode` machinery, and its logical count `k = 12` is DERIVED from the parity
matrices (`k = n − rank H_X − rank H_Z` over GF(2)), not asserted. `Codegen.lean` emits this real
code's `hx`/`hz`/`derivedK`. The RSA-scale [[1620,16,24]] instance is recorded.

## STILL UNSOLVED (the Pinnacle roadmap)
- the RSA-scale GB [[1620,16,24]] parity matrices + k (GB homological formula, brute-rank-infeasible);
- the Processing-Unit logical-Pauli-measurement gadget on a GB code;
- the Magic Engine resource model (one |C̄CZ̄⟩ per cycle, supply ≥ demand);
- PBC compilation + the verified < 100,000-qubit resource bound (the headline figure stays OPEN).
