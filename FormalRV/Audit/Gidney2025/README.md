# Audit · gidney-2025 — RSA-2048, <1M qubits, <1 week (arXiv:2505.15917)

**Headline:** RSA-2048 in < 1,000,000 physical qubits, in < 1 week.

The most complete RSA **arithmetic** audit: the CFS residue-arithmetic engine is verified
**axiom-clean**; the one conjecture (Assumption 1) is stated, never asserted. The QUANTUM half is the
named GAP. [`Verifier.lean`](Verifier.lean) `#verify_clean`-ACCEPTS the CFS chain + the resource tally.

## Per-layer ledger  (✅ verify-clean · ➗ arithmetic · ⬜ GAP/recorded)

| Layer | File | Status |
|---|---|---|
| Hardware | [`Hardware.lean`](Hardware.lean) | recorded (1e-3, 1 µs; hot d=25, cold 430/logical) |
| System zones | [`SystemZones.lean`](SystemZones.lean) | ⬜ GAP — footprint checked as a tally, not a zoned schedule |
| L1 algorithm | [`L1_Algorithm.lean`](L1_Algorithm.lean) | ✅ shared N-parametric success bound |
| L2 arithmetic | [`L2_Arithmetic.lean`](L2_Arithmetic.lean) | ✅ **CFS engine axiom-clean** — exact RNS modexp, exact CRT reconstruction, bounded truncation |
| L3 PPM | [`L3_PPM.lean`](L3_PPM.lean) | ⬜ GAP — surface-code realization of the residue circuit not assembled |
| L4 code | [`L4_Code.lean`](L4_Code.lean) | ⬜ recorded hot surface code d=25 |
| Verifier | [`Verifier.lean`](Verifier.lean) | ✅ resource tally 897,864 < 10⁶ + ✅ Ekerå–Håstad recovery; ⬜ Assumption 1 |

## STILL UNSOLVED
- the QUANTUM half (QPE recovers the discrete log w.h.p.; the masked-state amplitude identity);
- the full Gate-IR assembly of all |P| residue registers;
- Assumption 1 itself (a findable prime set with ∏P ≥ N^m and Δ_N < 2^{-f}).
