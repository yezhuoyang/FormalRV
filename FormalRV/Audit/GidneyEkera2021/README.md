# Audit · gidney-ekera-2021 — 20M qubits, ~8 h (arXiv:1905.09749)

**Headline claim:** RSA-2048 in ~20,000,000 physical qubits, in ~8 hours.

Rigorous structure (semantic first, resource next); [`Verifier.lean`](Verifier.lean) runs
`#verify_clean` on the ✅ theorems (a `sorry`/native axiom would fail the build). The 8 h / 20 M are
demonstrated as **feasible ceilings** under the paper's own parameters — not asserted.

## Settings a reader should check match the paper
- distance d = 27; per-logical tile 2·(d+1)² = 1568; logical qubits = 6200 (Ekerå–Håstad windowed)
- total budget 20,000,000 (Computation 9.72 M + Factory 10.28 M); cycle 1 µs; Toffoli count 2.7×10⁹

## Per-layer ledger  (✅ verify-clean · ➗ arithmetic-only · ⬜ recorded/GAP)

| Layer | File | Status |
|---|---|---|
| Hardware | [`Hardware.lean`](Hardware.lean) | recorded (1e-3, 1 µs) |
| System zones | [`SystemZones.lean`](SystemZones.lean) | ✅ zones partition 20 M; ✅ schedule fits + over-budget REJECTED; ✅ decoder is a real constraint |
| L1 algorithm | [`L1_Algorithm.lean`](L1_Algorithm.lean) | ✅ shared N-parametric success bound |
| L2 arithmetic | [`L2_Arithmetic.lean`](L2_Arithmetic.lean) | ✅ shared verified Cuccaro adder (`cuccaro_n_bit_adder_full_correct` — a sorry-free framework theorem; `#check`-ed here via an alias, not re-`#verify_clean`-gated in this folder) |
| L3 PPM | [`L3_PPM.lean`](L3_PPM.lean) | ✅ shared verified surface-code surgery, one logical PPM (`surface_shor_ppm_physically_realized` — a sorry-free framework theorem; `#check`-ed here via an alias, not re-`#verify_clean`-gated in this folder) |
| L4 code | [`L4_Code.lean`](L4_Code.lean) | ⬜ recorded rotated surface code d=27 (parity matrices not constructed) |
| Verifier | [`Verifier.lean`](Verifier.lean) | ➗ CAPSTONE (axiom-free, but a `by decide` arithmetic conjunction — a RESOURCE reproduction, not a closed semantic theorem): 19.44 M ≤ 20 M; 8 h sits 2–3× UNDER the verified time ceiling. The numbers flow through the genuinely-verified `∀ model` area-law, but the capstone itself is a numeric comparison |
| Codegen | [`Codegen.lean`](Codegen.lean) | emits the ACTUAL construction at each level via the general emitters (small reps; GE2021 params noted in comments) |

## Our approach
A finite zoned architecture machine-checks the reported 20 M as a real budget (over-budget schedules
are rejected); a verified surface-code area/time law (proven `∀ model`) reproduces the headline:
qubits 19.44 M = 6200 · 2·1568 ≤ 20 M, time ceiling ~20.25 h (naive sequential). The capstone
`gidney_ekera_2021_reproduced` is **axiom-free** — but it is a `by decide` arithmetic conjunction
(19.44 M ≤ 20 M, residual ≤ 600 k, the time-window brackets), so it is a RESOURCE reproduction
(arithmetic-tier ➗), not a closed semantic theorem. The numbers it compares are computed through
the genuinely-verified `∀ model` area-law; the comparison itself is numeric.

## GAP we determined / STILL UNSOLVED
- the ~2.5× TIME gap (8 h vs the 20.25 h sequential ceiling) = **reaction-limited pipelining** of the
  2.7×10⁹-Toffoli critical path — the schedule layer permits it, the paper claims it, but full
  RSA-scale pipelining is not verified;
- the ~3% (≤600 k) qubit residual is the magic factory's detailed wiring (arithmetic-verified as a
  formula, layout not spelled out);
- the L4 surface-code parity matrices are not constructed (standard code, recorded tuple); end-to-end
  Hilbert-space closure is delimited per the source headers.
