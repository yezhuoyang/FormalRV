# CFS-paper audit — Gidney 2025 & Pinnacle, against the verified CFS formalization

This is the audit of the two papers whose logical core is the CFS (Chevignard–Fouque–Schrottenloher)
residue-arithmetic factoring algorithm, against the now-largely-complete Lean formalization in
`FormalRV/Shor/CFS/` and the existing audit modules `FormalRV/Audit/{Gidney2025,Pinnacle}/`.

- **Gidney 2025** — arXiv:2505.15917, "How to factor 2048-bit RSA integers with less than a million
  noisy qubits" (`Library/2505.15917/`). Headline: **897,864 physical qubits** (< 1M), **1,537 logical**,
  **6.5×10⁹ Toffoli**, **4.96 days**, |P|≈640 22-bit primes, E(shots)≈9.2.
- **Pinnacle** — arXiv:2602.11457 (`Library/2602.11457/`). Headline: **< 100,000 physical qubits** (~10×
  fewer), GB-qLDPC **[[1620,16,24]]** code, Gidney's CFS arithmetic + **parallel reduction**.

## 1. What the formalization PROVES (the verified backing)

Every row is a `#verify_clean`/axiom-clean theorem (`[propext, Classical.choice, Quot.sound]` only),
on real objects.

| Paper claim | Proven theorem | File |
|---|---|---|
| Residue circuit computes `g^e mod N` (exact CRT, no wraparound) | `residueFold_crt_correct` (T7) | `CFS/ResidueCRT.lean` |
| RNS faithful (residue vector ⇒ value mod ∏P) | `rns_faithful` | `CFS/ResidueNumberSystem.lean` |
| Exact CRT reconstruction (constructed basis, no assumed units) | `reconstruction_explicit` | `CFS/CRTBasis.lean` |
| Truncation deviation `Δ_N/N ≤ |P|·ℓ·2^{-f}` | `modDev_truncAcc_normalized` | `CFS/TruncatedAccumulation.lean` |
| **Toffoli count** `= numP·(m·numWin·(16w·2^w+16·bits))` | `residueFold_toffoli` | `CFS/ResidueFold.lean` |
| Masked-state overlap `(W−d)/W` (computed, not assumed) | `masked_amplitude_identity` (T6) | `CFS/MaskedAmplitude.lean` |
| Squared infidelity `≤ 2·(ε/S)` (honest factor-2 vs paper's ε/S) | `masked_infidelity_sq_le` (T6) | `CFS/MaskedAmplitude.lean` |
| QFT/QPE peak law `≥ 4/(π²r)` (on the real orbit state) | `cfs_qft_peak_law_concrete` (T5) | `CFS/QPEPeakLaw.lean` |
| Ekerå-2023 dlog-recovery success bound | `EkeraDLPSuccess.success_ge` (T1) | `CFS/EkeraSuccess.lean` |
| Ekerå–Håstad factor recovery from `d=p+q−2` | `ekera_hastad_recovery` | `CFS/EkeraHastad.lean` |
| **End-to-end semantic correctness (quantum half PROVEN)** | `cfs_shor_semantic_correctness_concrete` | `CFS/SemanticClosure.lean` |
| Pinnacle: parallel tree-reduction = serial sum (Eq.20) | `parallelReduction_eq_serial` | `Audit/Pinnacle/ParallelReduction.lean` |
| Pinnacle: parallel-reduced deviation still bounded | `parallelReduction_modDev` | `Audit/Pinnacle/ParallelReduction.lean` |

### The semantic-correctness closure (the headline result)

`cfs_shor_semantic_correctness_concrete` composes, on shared `g,N,e,d,p,q`:
1. **Quantum period-finding succeeds** — `probability_of_success ≥ κ/(log₂N)⁴` via the FULLY-CONCRETE,
   axiom-clean `Shor_correct_verified_no_modmult_axioms` (verified oracle, **no quantum hypothesis, no
   `h_orbit_exists`, no `ModMulImpl` carried**). The "control-stub Phase-4 gap" was stale: the framework
   now proves the QPE circuit semantics (`qpe_on_eigenstate_correct`, `QPE_MMI_correct` is a theorem).
2. **The CFS residue circuit computes `g^e mod N`** (T7) — the efficient modexp implementation.
3. **The dlog link** `g^d ≡ g^{N−1} (mod N)` and **factor recovery**.

## 2. The existing audit modules (machine-checked, axiom-clean)

| Module | Headline theorem | Status |
|---|---|---|
| `Audit/Gidney2025/Verifier.lean` | `gidney2025_resource_reproduced` (897,864 < 1,000,000 ∧ logical = 1280+131+126) | ✅ `#verify_clean` |
| `Audit/Gidney2025/Verifier.lean` | `gidney2025_physical_tally` (1280·430 + 131·1352 + 7·18·1352 = 897,864) | ✅ `decide` |
| `Audit/Gidney2025/Verifier.lean` | `ekera_hastad_recovery` (factors from d) | ✅ `#verify_clean` |
| `Audit/Pinnacle/Verifier.lean` | `pinnacle_rsa_code_recorded` ([[1620,16,24]] recorded) | ✅ axioms `[]` |
| `Audit/Pinnacle/L4_Code.lean` | `pinnacle_gb_72_k_derived` (GB [[72,12,6]] k=12 DERIVED from matrices) | ✅ `native_decide` |
| `Audit/Pinnacle/L1_Algorithm.lean` | cites `StandardShor.orderFindingSucceeds` (= proven `Shor_correct_var`) | ✅ |

Both audits cite `StandardShor.orderFindingSucceeds` — the SAME now-proven standard-Shor success
(`probability_of_success ≥ κ/(log₂N)⁴` from `BasicSetting + ModMulImpl + well-typed`) that backs the CFS
closure. So the algorithmic-correctness leg of both papers rests on proven machinery.

## 3. Audit verdict — agreement vs. gap, per paper

### Gidney 2025 — **AGREES on everything checkable; honest about its gaps**

- ✅ **Algorithm correctness**: the residue modexp = `g^e mod N` (T7) and quantum period-finding succeeds
  (semantic closure) — the paper's §2 algorithm is verified correct.
- ✅ / ⚠️ **Toffoli FORMULA — but for the SIMPLE form, not the headline form**: `residueFold_toffoli` is the
  EXACT walk of the SIMPLE controlled-MULTIPLY residue circuit (`m·numWin·(16w·2^w+16·bits)`), which is the
  form the paper explicitly **replaces** with the optimized dlog-ADDITION form (`len(p)` multiplications, not
  `m`). So it is NOT the §2 *optimized* per-register cost the paper headlines. The headline **6.5×10⁹** is a
  grid-scan *optimization output* (a `def`, not a theorem); it is independently reproduced to ~6% by
  `ToffoliReproduction.lean` walking *distinct* value-correct dlog-addition gadgets (`gidneyAdderMeasured`,
  `gidneyModAddFixup`, `unaryQROMAt`) — these are bridged to the verified `residueFold` only at the VALUE
  level (`dlog_reduction_eq_residueAccumulate`), NOT at the circuit level. (Honest gaps flagged in
  `RESOURCE_AUDIT.md` and `Verifier.lean`.)
- ✅ **Resource tally**: 897,864 < 1M and the 1,537 logical reconciliation are machine-checked (`decide`).
- ✅ **Deviation / masking / success**: the deviation bound, masked infidelity (with the honest factor-2),
  and the Ekerå success bound are all proven.
- ⬜ **CARRIED**: `Assumption 1` (the prime-set conjecture — stated as a `Prop`, never asserted; the paper
  itself gives only numerical evidence). The cold-storage yoked-code cost (430/logical), the L3 surface
  surgery, and the runtime survival model are placeholders/unverified (honestly recorded, not faked).

### Pinnacle — **algorithm + code-parameter framework verified; <100k bound OPENLY OPEN**

- ✅ **Algorithm = Gidney's CFS + parallelization**: `parallelReduction_eq_serial` proves the parallel
  binary-tree reduction (Eq.20) equals the serial accumulator — so Pinnacle inherits ALL the CFS
  correctness (it is the SAME residue arithmetic, reordered) plus the verified parallel reduction.
- ✅ **GB code parameters DERIVED**: the representative [[72,12,6]] GB code has `k=12` *derived from the
  constructed parity matrices* (`native_decide`), not hardcoded; the RSA-scale [[1620,16,24]] is recorded.
- ⬜ **The `<100k` resource bound is shown OPEN** in `Verifier.lean` (not faked): the RSA-instance rank
  derivation (1620 columns), the L3 GB measurement gadget, and the processing-unit/magic-engine zoned
  schedule are roadmap. Honest discipline: the bound is never asserted without proof.

## 4. The two genuinely-open items (shared by both papers)

1. **`Assumption 1`** — a number-theoretic conjecture (∃ ℓ-bit prime set with `∏P ≥ N^m` and tiny
   modular deviation). Undischargeable from the papers (numerical evidence only). Stays a carried `Prop`,
   never an axiom. Made load-bearing in `cfs_capstone_under_assumption1`.
2. **The residue-oracle `ModMulImpl` encoding bridge** — connecting the CFS residue circuit, *as the QPE
   oracle*, to the basis-action spec. This is a CLASSICAL per-prime basis-action correspondence (no
   quantum content). The closure sidesteps it via function-level composition (the verified oracle carries
   the proven period-finding; `residueFold` carries the proven efficient arithmetic — both compute the
   same `g^· mod N`). Closing it would unify them into a single circuit.

**Bottom line:** both papers' *logical algorithm* (the CFS residue arithmetic + Ekerå–Håstad period
finding) is now formally verified end-to-end — exact arithmetic, deviation, masking, QPE peak law,
dlog recovery, and the quantum period-finding success (fully proven, axiom-clean) — with only
`Assumption 1` (a genuine conjecture) and the classical residue-oracle encoding bridge remaining. The
resource tallies are machine-checked where the papers give formulas; grid-scan optima and the physical
code/runtime models are honestly recorded as the engineering layer below the algorithm.
