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
| L2 arithmetic | [`L2_Arithmetic.lean`](L2_Arithmetic.lean) | ✅ shared verified Cuccaro adder |
| L3 PPM | [`L3_PPM.lean`](L3_PPM.lean) | ✅ shared verified surface-code surgery (one logical PPM) |
| L4 code | [`L4_Code.lean`](L4_Code.lean) | ⬜ recorded rotated surface code d=27 (parity matrices not constructed) |
| Verifier | [`Verifier.lean`](Verifier.lean) | ✅ CAPSTONE (axiom-free): 19.44 M ≤ 20 M; 8 h sits 2–3× UNDER the verified time ceiling |
| Workload assembly | [`WorkloadAssembly.lean`](WorkloadAssembly.lean) | ✅ literal = paper formula = realized circuit, BY THEOREM (axiom-free): `2,622,824,448` = `WindowedCostModel.toffoliCount 2048 3072 11`; circuit `modExpAt` realizes `2,578,993,152` with the gap exactly `43,831,296` = +1 rounding + runway folding; `n_toff = 2.7×10⁹` is a sound ceiling on all three; per-lookup row `5205 + 1 = 5206`; value-semantics witness; honest-gap ledger |
| Codegen | [`Codegen.lean`](Codegen.lean) | emits the ACTUAL construction at each level via the general emitters (small reps; GE2021 params noted in comments) |

## Our approach
A finite zoned architecture machine-checks the reported 20 M as a real budget (over-budget schedules
are rejected); a verified surface-code area/time law (proven `∀ model`) reproduces the headline:
qubits 19.44 M = 6200 · 2·1568 ≤ 20 M, time ceiling ~20.25 h (naive sequential). The capstone
`gidney_ekera_2021_reproduced` is **axiom-free**.

## Where each headline number comes from TODAY (honest sourcing)

| Number | Lives at | Status |
|---|---|---|
| **20,000,000 qubits** | `ge2021_reported_qubits` (`System/NaiveUpperBound.lean`) | paper LITERAL; checked against the **verified area formula** `ge2021_naive.qubits = 19,443,200 = 6200·(2·1568) ≤ 20 M` (`ge2021_qubits_derived`, `ge2021_qubits_reproduce_reported`, [`Verifier.lean`](Verifier.lean)) |
| **8 hours** | `ge2021_reported_time_us_tenths = 288×10⁹` tenths-µs (`System/NaiveUpperBound.lean`) | paper LITERAL; shown 2–3× UNDER the **verified** naive-sequential ceiling `2.7×10⁹ · 27 · 1 µs ≈ 20.25 h` (`ge2021_time_ceiling`, `ge2021_time_gap_2_to_3x`) — the factor is pipelining, the GAP below |
| **2.7×10⁹ Toffolis** | `ge2021_work.n_toff` (`System/NaiveUpperBound.lean`) | paper LITERAL as input to the zone/time layers; independently, the paper's own cost **FORMULA** is verified exactly at RSA-2048: `503808·5206 = 2,622,824,448` (`WindowedCostModel.toffoliCount_rsa2048`), and a composed **CIRCUIT** realizes `2,578,993,152` with the residual exactly named (+1 rounding + runway folding = 1.67%; `WindowedComposedCost.rsa2048_head_to_head`, `rsa2048_circuit_matches_model`) |
| **6200 logical qubits** | `ge2021_work.n_logical` (`System/NaiveUpperBound.lean`) | paper LITERAL (Tab. 1, Ekerå–Håstad windowed) |
| **d = 27, tile 2(d+1)² = 1568** | `ge2021_code` ([`L4_Code.lean`](L4_Code.lean)) | paper formula RECORDED; the distance-27 code itself is a real verified construction `[[1405, 1, 27]]` (`ge2021_distance_is_verified_code`, [`Verifier.lean`](Verifier.lean)), but the rotated-patch parity matrices are not constructed (L4 GAP) |

> **Landed:** [`WorkloadAssembly.lean`](WorkloadAssembly.lean) equates literal =
> formula = circuit count **by theorem** (all `#verify_clean`-gated):
> `audit_toffoli_literal_eq_cost_model` (Verifier literal = `WindowedCostModel`
> formula), `audit_magic_budget_eq` + `audit_data_qubit_literal_eq_derived`
> (system literals reconcile), `audit_toffoli_realized_by_circuit` (the
> value-correct `modExpAt` realizes `2,578,993,152`; gap exactly `43,831,296 =
> 503808·1 + 503808·86` = lookup rounding + runway folding),
> `audit_n_toff_upper_bounds_circuit` (`2.7×10⁹` dominates circuit, literal, and
> formula), `audit_per_lookup_add` (circuit `5205 + 1 =` paper `5206`),
> `audit_value_semantics_witness` (the counted lookup-add computes
> `acc += T[addr] mod 2^bits`), plus an HONEST-GAP LEDGER for what still has no
> verified circuit (runway additions, Ekerå–Håstad PE, pipelining ≈2.5×,
> whole-circuit width, the modexp-in-QPE weld).

## Import map for auditors — paper claim → which module to import

Master copy: the **auditor's routing table** in
[`FormalRV/Arithmetic/Windowed/README.md`](../../Arithmetic/Windowed/README.md)
(per-claim file + headline theorem). The GE2021-relevant rows:

| GE2021 claim | Import | Headline |
|---|---|---|
| Windowed multiply, value + per-window count (any adder, any `w`) | `FormalRV.Arithmetic.Windowed.WindowedCircuitCorrect` | `windowedMulCircuitOf_correct`, `tcount_windowedMulCircuitOf` |
| Babbush QROM read, Gray-code `2·(2^w−1)` Toffolis (the lookup term) | `FormalRV.Arithmetic.UnaryLookup.UnaryLookupGrayCode` | `grayLookupReadAt_selects_word`, exact gap `tcount_lookupReadAt_eq_w_mul_gray` |
| Measurement-based uncompute (1905.07682 App. C; the residual ×2) | `FormalRV.Shor.MeasuredLookupUncompute` / `MeasuredANDUncompute` / `PhaseLookupFixup`; value-correct measured lookup-add: `FormalRV.Shor.MeasUncomputeAt` | `measWordUncompute_perfect`, `babbushLookupAddAtValueSpecOn_holds` |
| The cheap `2^{w/2}` fixup | `FormalRV.Shor.SplitPhaseFixup` | `measWordUncompute_splitPhaseLookup` |
| Paper's exact ℚ cost formulas (l.712; `0.3 n³`) | `FormalRV.Arithmetic.Windowed.WindowedCostModel` | `toffoliCount_rsa2048`, `toffoliCount_le_paper` |
| Circuit-total ↔ paper-total bridge (gap exactly named) | `FormalRV.Shor.WindowedComposedCost` (structure: `FormalRV.Shor.WindowedComposed`) | `total_gap`, `rsa2048_head_to_head` |
| Cuccaro adder (l.593, `2n` per add) | `FormalRV.Arithmetic.Cuccaro.CuccaroFull` | `cuccaro_n_bit_adder_full_correct` |
| Exactly-modular windowed multiply (per-window mod N) | `FormalRV.Arithmetic.Windowed.WindowedModN` | `windowedModNMulCircuit_correct` |
| Order-finding success bound (L1) | `FormalRV.Shor.StandardShor` | `orderFindingSucceeds` |
| 20 M budget as a finite zoned machine; schedule fits; over-budget rejected | [`SystemZones.lean`](SystemZones.lean) (this folder) | see ledger above |
| The capstone reproduction | [`Verifier.lean`](Verifier.lean) (this folder) | `gidney_ekera_2021_reproduced` (axiom-free) |

## GAP we determined / STILL UNSOLVED
- the ~2.5× TIME gap (8 h vs the 20.25 h sequential ceiling) = **reaction-limited pipelining** of the
  2.7×10⁹-Toffoli critical path — the schedule layer permits it, the paper claims it, but full
  RSA-scale pipelining is not verified;
- the ~3% (≤600 k) qubit residual is the magic factory's detailed wiring (arithmetic-verified as a
  formula, layout not spelled out);
- the L4 surface-code parity matrices are not constructed (standard code, recorded tuple); end-to-end
  Hilbert-space closure is delimited per the source headers;
- the oblivious-carry-**runway** additions are accounted for in the cost FORMULA only (the composed
  circuit omits them — that omission is exactly the named `n·g_pad/g_sep` term in
  `WindowedComposedCost`), and the runway registers themselves are not built;
- the **Ekerå–Håstad**-specific phase estimation / post-processing is not formalized — L1 uses the
  shared N-parametric order-finding success bound with the EH window count (`q_A = 3072`) as input.
