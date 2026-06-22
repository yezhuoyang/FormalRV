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
- RSA-2048 GB code instance ⟦510,16,24⟧ (n = 510, k = 16, distance 24, syndrome rounds d+2 = 26; paper main.tex line 502). NOTE: 1620 is the **processing-block footprint** `n_pb = n_cb + 4n_g + 4n_b = 1020 + 396 + 204`, NOT the code's `n` — recorded separately as `pinnacle_n_pb`.

## Per-layer ledger  (✅ verify-clean · ➗ arithmetic/native · ⬜ GAP/recorded)

| Layer | File | Status |
|---|---|---|
| Hardware | [`Hardware.lean`](Hardware.lean) | recorded (1e-3, 1 µs, 10 µs reaction) |
| System zones | [`SystemZones.lean`](SystemZones.lean) | ⬜ GAP — Processing-Unit/Magic-Engine schedule on the roadmap |
| L1 algorithm | [`L1_Algorithm.lean`](L1_Algorithm.lean) | ✅ `pinnacle_dlog_recovery_succeeds` — the EKERÅ–HÅSTAD single-run dlog-recovery bound the factoring actually uses (CORRECTED from the prior vanilla-order-finding #check, the wrong algorithm for EH-RNS) |
| L2 arithmetic | [`L2_Arithmetic.lean`](L2_Arithmetic.lean) · [`L2_ArithmeticFaithful.lean`](L2_ArithmeticFaithful.lean) · [`ParallelReduction.lean`](ParallelReduction.lean) | ✅ reuses the verified Gidney2025 CFS residue engine; ✅ faithful per-gadget Toffoli (`pinnacle_addition_toffoli`=+1, `pinnacle_lookup_toffoli`=+w, honest our-side over-counts); ✅ Eq.20 parallel reduction (`parallelReduction_eq_serial`) + the per-register truncated accumulator is EXACTLY the serial one (`parApprAcc_eq_serial`) so its deviation bound transfers verbatim |
| **End-to-end QPE** | [`EndToEndQPE.lean`](EndToEndQPE.lean) | ✅ `pinnacle_modexp_endToEnd` — ONE composed `residueFold` object: computes `g^e mod N` (circuit-derived) → dlog → factors, + a true bound on the carried Ekerå witness (success seam), + the assembled RNS-modexp Toffoli count on the SAME gate, + the Eq.20 identity |
| **Factoring closure** | [`FactoringClosure.lean`](FactoringClosure.lean) | ✅ **`pinnacle_eh_rns_shor_succeeds` — THE FAITHFUL EKERÅ–HÅSTAD / RNS CIRCUIT FACTORS N** (Pinnacle's ACTUAL algorithm, NOT vanilla order-finding): (I) EH frequency-measurement success ≥ 1/8 on the GATE-BUILT QFT-measured state (inverse-QFT via real `uc_eval` + Born projection; the EH measurement law `ehProb = Born prob` is PROVEN — `prob_partial_meas_eq_ehCircuitMeasProb` — not the carried `EkeraDLPSuccess` witness) ∧ (II) the RNS `residueFold` CRT-computes `g^e mod N` ∧ (III) dlog link ∧ (IV) factor recovery. Residual = the entangling-ORACLE bridge (`twoRegOracleState` = `residueFold` ∘ prep) + Assumption 1 — NO quantum measurement-law gap |
| **Resource check** | [`ResourceCheck.lean`](ResourceCheck.lean) | ✅ every Table V row satisfies the stated conventions (`2·LC=3·T`, `T=4·Toffoli`); `υ`/`Λ`-serial assembled correctly — Table V is INTERNALLY CONSISTENT (no column-relation arithmetic mistake) |
| **PPM end-to-end** | [`PPMEndToEnd.lean`](PPMEndToEnd.lean) | ✅ `pinnacle_modexp_ppm_realized` — the RNS `residueFold` modexp Gate LOWERED to a magic-aware PPM program (Pauli-product measurements + one factory-DISTILLED `\|T⟩` per Toffoli) RUNS and its CRT-reconstructed measured output = `g^e mod N`; distilled-T demand = Toffoli count. Carried: the `teleportCCXRel` Clifford+T + physical distillation contracts (`TFactoryContract`) |
| L3 PPM | [`L3_PPM.lean`](L3_PPM.lean) | ✅ (PPM level) `gb_logical_computation_preserves_code` — any logical Pauli-product computation preserves the real [[72,12,6]] GB code (scale-free induction, axiom-clean); ➗ GB single-PPM/commutation facts (native_decide at 72q); ⬜ the Webster generalised-lattice-surgery gadget is below-PPM (QEC-compilation, deferred) |
| L4 code | [`L4_Code.lean`](L4_Code.lean) | ➗ REAL [[72,12,6]] GB code, k=12 DERIVED from constructed matrices; ✅ RSA code instance ⟦510,16,24⟧ recorded (n_pb=1620 separate) |
| Verifier | [`Verifier.lean`](Verifier.lean) | end-to-end < 100k obligation OPEN (roadmap); ✅ verify-clean gates on all of the above |
| Codegen | [`Codegen.lean`](Codegen.lean) | emits the ACTUAL construction at each level; L4 emits Pinnacle's REAL `pinnacle_gb_72` (hx/hz/derivedK) |

## Our approach
The verified strength is the GB-code-parameter framework: a representative Pinnacle GB code
(`pinnacle_gb_72`, the [[72,12,6]] gross-code-family instance) is CONSTRUCTED via the shared
`bivariateBicycle`/`CSSCode` machinery, and its logical count `k = 12` is DERIVED from the parity
matrices (`k = n − rank H_X − rank H_Z` over GF(2)), not asserted. `Codegen.lean` emits this real
code's `hx`/`hz`/`derivedK`. The RSA-scale ⟦510,16,24⟧ code instance is recorded (with `n_pb=1620`
recorded separately as the processing-block footprint, not the code's `n`).

## Logical-algorithm correctness — CLOSED on Pinnacle's ACTUAL (Ekerå–Håstad / RNS) algorithm
`pinnacle_eh_rns_shor_succeeds` (axiom-clean) is the FAITHFUL end-to-end: Pinnacle = Gidney 2025 =
Ekerå–Håstad short discrete log + Chevignard RNS one-shot modexp (NOT vanilla order-finding — there is
no `mult-by-a^(2^i)` ladder and no continued-fraction recovery; an earlier vanilla "closure" was a
different algorithm and was REMOVED). The hard QFT measurement law is now a PROVEN THEOREM
(`prob_partial_meas_eq_ehCircuitMeasProb`: the EH measurement probability `ehProb` = the gate-built
Born probability of the verified two-register inverse-QFT), so the EH per-run success `≥ 1/8` lands as
a `prob_partial_meas` bound on the genuine gate-built measured state — no carried `EkeraDLPSuccess`
witness. Conjoined with the verified RNS `residueFold` modexp (`g^e mod N`), the dlog link, and factor
recovery. The ONLY residuals are CLASSICAL/structural: the entangling-ORACLE bridge (realizing the
abstracted `twoRegOracleState` as `residueFold` ∘ input-prep — no quantum measurement-law content) and
the paper's own `SmallPrimeRNSModulusExists` (Assumption 1).

## STILL UNSOLVED (the Pinnacle roadmap — BELOW the logical-algorithm layer)
- the RSA-scale GB ⟦510,16,24⟧ parity matrices + k (GB homological formula, brute-rank-infeasible);
- the Processing-Unit logical-Pauli-measurement gadget on a GB code (the QEC-compilation surgery gadget);
- the Magic Engine resource model (one |C̄CZ̄⟩ per cycle, supply ≥ demand);
- PBC compilation + the verified < 100,000-qubit PHYSICAL resource bound (the headline figure stays OPEN).
