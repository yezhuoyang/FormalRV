# CFS Shor — proof-dependency notes (source papers → repo gaps → formalization targets)

Notes taken from the four source papers before closing the CFS end-to-end gaps. Canonical algorithm =
**CFS** (Chevignard–Fouque–Schrottenloher, IACR ePrint **2024/222**, paywalled — see `Library/eprint_2024_222/README.md`);
working spec proxy = **Gidney 2025 §2** (`Library/2505.15917/`, the streamlined CFS exposition). Supporting
papers in `Library/`: Ekerå–Håstad 2017 (`1702.00249`), Ekerå 2023 (`2309.01754`), May–Schlieper 2019 (`1905.10074`).

## End-to-end algorithm skeleton (stage → spec → paper → repo anchor)

| Stage | Spec | Paper (eq/§) | Repo anchor | Status |
|---|---|---|---|---|
| 0. EH input prep / RSA→short-DLP | `g`∈Z_N\*, `h=g^{N-1}`, `d=p+q-2`; exponent reg ~`n/2+n/s` qubits (vs Shor 2n) | Gidney §2 L822-851; EH 1702 §4.7 | `ekera_hastad_exponent`, `ekera_hastad_recovery` | ✅ classical |
| 1. Controlled residue mult / prime `pⱼ` | `V_{pⱼ}=∏_{k<m} Mₖ^{eₖ} mod pⱼ`, `Mₖ=g^{2^k} mod N` | Gidney M_k L243, V_p L885 | `residueGate_verified`, `residueGate_unitary_computes_residue` | ✅ single-register (semantic+resource+unitary) |
| 1b. Fermat dlog compression | controlled SUM `S_p=∑Dₖeₖ`, `V_p=g_p^{S_p mod(p-1)} mod p` | Gidney L879-925 | `dlog_reduction`, `pow_mod_sub_one` | ✅ |
| 2. Exact CRT reconstruction | `(∑ⱼ rⱼuⱼ) mod L mod N = g^e mod N`, `L≥N^m` | Gidney eq:comp_v L287, eq:bound-L L256 | `reconstruction`, `residue_modexp_via_crt`, `crtBasis_delta` | ✅ |
| 3. Truncated reconstruction + deviation | `Δ_N(V-(Ṽ≪t)) ≤ |P|·ℓ·2^{-f}` | Gidney eq:modevbound L403 | `modDev_truncAcc_normalized`, `modDev_chain` | ✅ (algebra); Assumption1 carried |
| 4. Approximate periodicity | `Δ_N(f̃(x+yP)-f̃(x)) ≤ 2ε` | Gidney L438-439 | `approx_periodic`, `modexp_periodic` | ✅ classical |
| 5. Mask + measure + QFT (quantum core) | infidelity `1-|⟨ψ₁|ψ̃₁⟩|² ≤ ε/S`; QFT peaks | Gidney eq:max-infidelity L504, QFT L575 | T6: `masked_amplitude_identity` …; T5: `cfs_qft_peak_law_concrete`, `residueOracleFamily(_wellTyped)`, `residueShorFinalState_peak_law` | ✅ amplitude identity (T6, real states) + ✅ QFT peak law (T5, proven on concrete orbit state; reused on residue circuit, only the orbit-form bridge carried) |
| 6. Per-shot success | `P_deviant ≤ S+ε/S`, min at `S=√ε ⇒ ≤2√ε`; OR Ekerå 2023 tight | Gidney L808-814; Ekerå 2023 Thm 1 | `cfs_success_minimization` (T3); `EkeraDLPSuccess.success_ge` (T1) | ◑ mask route ✅ + lattice route ✅ (Lem1/Lem2 carried) |
| 7. EH post-processing | `s+1` shots; lattice recovery of `d`; factors from quadratic | EH 1702 Thm 11; Ekerå 2023 Thm 1/2 | `ekera_hastad_recovery`, `eh_good_vector_within_radius`, `goodProb_ge_eighth` | ◑ recovery+geometry+1/8 ✅; whp CARRIED |
| 8. End-to-end capstone | compose 2+3+4+5/6+7 under Assumption1 | Gidney §2 whole; E(shots) L1124 | `cfs_correctness_capstone`, `cfs_capstone_under_assumption1` (T8) | ✅ composed (T7 arith + EH exponent + T1 success + EH recovery; Assumption1 load-bearing) |

## Carried hypotheses → discharge sources

- **`cfs_dlog_recovered_whp`** (the quantum shots recover `d` w.h.p.; documented `EkeraHastad.lean:19`, currently only `≥1/8`)
  - **PRIMARY: Ekerå 2023 (2309.01754) Theorem 1** (`thm:main`): single run yielding `(j,k)` recovers `d` via lattice
    enumeration with prob `≥ max(0, 1-1/2^τ-1/(2·2^{2τ})-1/(6·2^{3τ})) · max(0, 1-2^{Δ-2(t-1)-τ})`. Factor 1 = Lemma 1
    (`lemma:bound-tau-good-pair`, trigamma/Nemes bound); factor 2 = Lemma 2 (t-balanced lattice). **Cor 1** drives →1;
    **Table 1** witnesses: `(τ,t)=(34,2) ⇒ ≥1-10^{-10}` at `≤2^{22.1}` ops. **Thm 2** = Gaudry–Schost variant.
  - FLOOR: EH 1702 **Thm 11** (Lemma 4 count `≥2^{ℓ+m-1}` × Lemma 7 per-pair `≥2^{-m-ℓ-2}` ⇒ `1/8`). Repo carries the
    deep Fourier facts (Lemma 7) as `EHShortDLPSuccess.*_obl`; only the 1/8 arithmetic + lattice geometry are proven.
- **Output-compression robustness** — May–Schlieper (1905.10074) **Main Thm**: `E_h[p_h(y)]=(1-2^{-t})·p(y)` ∀y≠0 under the
  cancellation criterion; `main_theorem_period`: success ρ invariant, ×`1/(1-2^{-t})` measurements, `q+t` qubits. **CAVEAT
  (their explicit open problem):** all Shor/EH results are ORACLE-BASED — they do NOT construct `h∘f` without computing full
  `a^x mod N`. So the qubit-count headline is conditional on an oracle the repo also only assumes.
- **`Assumption1`** — Gidney §2 Assumption 1 (L346): ∃ ℓ-bit pairwise-coprime prime set `P`, `∏P=L≥N^m`, `Δ_N(L)<2^{-f}`.
  **Undischargeable** from any of the four papers (numerical evidence only: 25000 22-bit primes for RSA-2048, `Δ<2^{-32}`).
  Stays a `Prop` hypothesis on the capstone.

## Ordered formalization targets

1. **T3 `cfs_success_minimization`** (Gidney L808/814) — `P_deviant ≤ S+ε/S`, AM-GM min at `S=√ε ⇒ ≤2√ε`. *Elementary real inequality — EASY.*
2. **T7 `cfs_residue_fold`** (Gidney §2) — the `|P|`-register fold of `residueGate_verified`: a **base-PARAMETRIC** residue
   gate + frame/disjointness (runway-adder template), assembling the per-prime residues to feed `reconstruction`.
   *Engineering, LOAD-BEARING (central seam) — MEDIUM/HARD; base-parametric gate is the unlock.*
3. **T6 `masked_amplitude_identity`** (Gidney eq:max-infidelity L504) — ✅ **DONE** (`CFS/MaskedAmplitude.lean`, 7 thms
   axiom-clean). Concrete window states `maskedIdeal`/`maskedApprox : Fin D → ℂ` (real vectors), overlap COMPUTED
   (`winFin_inter_card`, NO `hov` hypothesis), `masked_amplitude_identity` (`⟨ψ₁|ψ̃₁⟩ = (W−d)/W`), unit-vector proof
   (`maskedState_normalized`), deficit bound `masked_fidelity_ge` (`(W−d)/W ≥ 1−ε/S`, paper L499-500), and the honest
   squared form `masked_infidelity_sq_le` (`1−|⟨⟩|² ≤ 2·(ε/S)`; the paper's boxed `ε/S` is the linear deficit — the
   squared infidelity rigorously carries a benign factor ≤2, flagged not faked). Window model verbatim-faithful to
   L490-499. **REMAINS = T5**: the circuit that PREPARES these specific window states (the QFT peak law).
4. **T1 `EkeraDLPSuccess.success_ge`** (Ekerå 2023 Thm 1) — ✅ **DONE** (`CFS/EkeraSuccess.lean`, 5 thms axiom-clean).
   The two-factor combination `successProb ≥ factor1·factor2` proven as a real Finset calc (`ekera_twoFactor_lower_bound`);
   `ekeraGoodFactor`/`ekeraBalancedFactor` transcribed VERBATIM from thm:main (lines 1106-1128); amplification
   `ekeraGoodFactor_ge` (factor1 ≥ 1−3/2^τ → 1); non-vacuity machine-proven (`ekera_contract_inhabited`); composed with
   concrete `ekera_hastad_recovery` (`ekera_success_to_factors`). **CARRIED** (the honest, `EHShortDLPSuccess`-style half):
   Lemma 1 (trigamma good-pair) + Lemma 2 (t-balanced) as named structure-field obligations `good_obl`/`balanced_obl` —
   both are facts about the (j,k) MEASUREMENT DISTRIBUTION, closeable ONLY by T5 (the QFT peak law). The trigamma rational
   Nemes bound itself is NOT separately proven (it is the *content* of the carried Lemma-1 obligation, not re-derived).
5. **T4 `compression_robust_prob_scaling`** (May–Schlieper Main Thm) + `period_success_invariance`. *MEDIUM/HARD.*
6. **T5 `qft_peak_law`** (Gidney eq:beta_k L615/L726) — ✅ **DONE** (`CFS/QPEPeakLaw.lean`, 4 thms axiom-clean) by REUSE.
   The analytic core is ALREADY proven in-repo (`Framework.qpe_prob_peak_bound`, the 437-line Dirichlet bound;
   `QPE_MMI_correct_from_orbit`, peak `≥4/(π²r)` from orbit form + orthonormal β). T5 = `cfs_qft_peak_law_concrete`
   (the peak law on a CONCRETE ideal orbit state w/ basis-vector eigenstates, `basisVec_orthonormal` proven, ZERO
   hyps) + `residueOracleFamily(_wellTyped)` (the real QPE oracle wrapper on the residue circuit, proven well-typed)
   + `residueShorFinalState_peak_law` (peak law on the REAL `Shor_final_state … residueOracleFamily`: well-typedness
   discharged, peak law INHERITED, only the structural `h_orbit_exists` orbit-form bridge carried). The bridge is the
   framework-`control`-stub-blocked Phase-4 gap that standard Shor ALSO carries — never the peak law itself.
7. **T8 `cfs_correctness_capstone`** (Gidney §2) — ✅ **DONE** (`CFS/Capstone.lean`, 2 thms axiom-clean). The end-to-end
   composition: `cfs_correctness_capstone` = 4-way conjunction (T7 `residueFold_crt_correct` arith ∧ `ekera_hastad_exponent`
   dlog=p+q-2 ∧ T1 `EkeraDLPSuccess.success_ge` ∧ `ekera_hastad_recovery` factors), threaded through the concrete circuit
   and shared g,N,e,d,p,q. `cfs_capstone_under_assumption1` makes `Assumption1` LOAD-BEARING (derives `hL`/`hco`/`1<P`
   from the conjecture's prime set; only the per-prime size+multiplier contract carried). Carried: Assumption1, the
   EkeraDLPSuccess witness (Lemma1/2), order condition — none the conclusion.
8. **T9 `cfs_rsa_reduction`** (EH 1702 §4.7) — `N=pq`, `x=g^{(N-1)/2}`, `d=(p+q-2)/2`; factors from the quadratic. *Mostly present (`ekera_recover_actual`).*

## ★ SEMANTIC CORRECTNESS CLOSED (`CFS/SemanticClosure.lean`) — the "control-stub" caution below is STALE

The framework NOW PROVES the QPE circuit semantics (the docstrings calling it a "Phase-4 / control-stub gap" were
stale): `SQIRPort.qpe_on_eigenstate_correct` (unconditional QPE-on-eigenstate), `CosetOrbitEngine.qpe_var_lsb_on_eigenfamily_initial`
(eigenfamily → orbit form), `QPEModmultEigenstate.*` (modmult eigenstate spectrum for ANY ModMulImpl), and
**`PostQFTCompletion.QPE_MMI_correct` is a THEOREM** (peak `≥4/(π²r)` from `BasicSetting+ModMulImpl+well-typed`,
`h_orbit_exists` constructed internally). `VerifiedShor.Shor_correct_verified_no_modmult_axioms` is the FULLY-CONCRETE
axiom-clean Shor success (no `ModMulImpl`, no quantum hypothesis). So:
- `residueShorFinalState_peak_law_closed` — CFS peak law carrying ONLY `ModMulImpl` (`h_orbit_exists` DISCHARGED).
- `cfs_shor_semantic_correctness` — quantum success PROVEN via `Shor_correct_var`.
- **`cfs_shor_semantic_correctness_concrete`** — strongest: quantum half = `Shor_correct_verified_no_modmult_axioms`
  (NO quantum hyp) ∧ T7 residue modexp ∧ dlog link ∧ EH recovery. **The quantum correctness of CFS Shor is FULLY CLOSED.**
Remaining: `Assumption1` (conjecture) + the classical residue-oracle `ModMulImpl` encoding bridge (sidestepped by
function-level composition). See `PAPER_AUDIT.md` for the Gidney2025 + Pinnacle audit against these proven results.

## Cautions (load-bearing — read before building)

- **THE FOLD (T7) is the central un-bridged seam.** `residueGate_verified` is single-register; without a base-parametric gate +
  disjointness frame, the `|P|≈640` registers cannot be assembled and `reconstruction`'s `∑ⱼ over Fin |P|` has nothing to consume.
- **CONVENTION COLLISION on `d`:** three coexisting conventions — `d=p+q-2` (CFS/`x=g^{N-1}`), `d=(p+q-2)/2` (1702/`x=g^{(N-1)/2}`),
  `d=p+q` (8-hours audit/`x=g^{N+1}`). All exact but `m` and the recovery quadratic differ. Do **not** cross-wire.
- **UNADDRESSED SEAM:** Ekerå 2023 bounds an *exact* short-DLP circuit's success; it does **not** cover Gidney's ε-deviated/masked
  pipeline. Composing the Stage-3/4 ε-deviation into Ekerå's exact-DLP bound is a genuine research seam neither paper closes.
- **What the papers do NOT give:** Ekerå 2023 ≠ the circuit, the QFT peak law, or the amplitude identity. 1702 Lemma 7 (the per-pair
  Fourier fact) is deep and currently carried as an axiom. May–Schlieper compression is oracle-based (no `h∘f` construction).
- **Assumption1 is a conjecture** — stays carried; do not formalize Gidney's `O(2^f·poly)` findability.
- **Resource ≠ correctness:** the §2 `6.5×10⁹` Toffoli / runtime headline is a grid-scan output, NEVER a theorem conclusion
  (`Verifier.lean:47`). The capstone certifies CORRECTNESS only; the tally is the separate `gidney2025_resource_reproduced`.

## Two distinct success routes (pick ONE for the capstone, document which)
- **Mask route** (Gidney): `S=√ε ⇒ P_deviant ≤ 2√ε` (T3) — uses the masking accumulator; weaker, simpler.
- **Lattice route** (Ekerå 2023 Thm 1, T1) — tighter, pushable to `1-10^{-10}`, no mask tradeoff. Upgrading from the repo's
  current `≥1/8` (T2) to T1 materially changes the shot count `E(shots)=(s+1)/(1-P_deviant)/0.99`.
