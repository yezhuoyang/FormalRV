# Narrowing the Ekerå / Ekerå–Håstad obligations (for literature research)

## ★ PROGRESS 2026-06-22 — three components CLOSED axiom-clean

| Step | Status | File | Headline |
|---|---|---|---|
| **C2** (Nemes trigamma bound) | ✅ DONE | `CFS/TrigammaBound.lean` | `nemes_trigamma_bound : ψ'(x) ≤ 1/x + 1/(2x²) + 1/(6x³)` for **all** x>0 (tight constants), via an exact elementary telescoping identity `H(y)−H(y+1)−1/y² = 1/(6y³(y+1)³)` — NO Euler–Maclaurin needed. Plus `ekeraGoodFactor_trigamma` (the exact bracket at 2^τ). |
| **D** (EH count lemma) | ✅ DONE (κ=0 / d-odd RSA case) | `Audit/Gidney2025/EkeraCombinatorics.lean` | `eh_good_pair_iff` (j good ⟺ \|{dj}_{2^m}\|≤2^{m-2}, **all d**) + `count_good_pairs_lower_bound : 2^{ℓ+m-1} ≤ #good-j` (d odd). General 0<d (κ=v₂(d)>0) scoped out (needs 2-adic fiber count). |
| **STEP A** (2-reg peak law) | ✅ analytic core DONE; 1 bridge remains | `CFS/ShortDLPPeakLaw.lean` | `qpe_prob_2d_factorizes` (2-reg prob = product of two 1-reg probs) + `qpe_prob_2d_peak_bound ≥ (4/π²)²` (REUSES the proven 1-reg `qpe_prob_peak_bound` twice) + `short_dlp_prob_bound_of_phase_bounds ≥ 2^{-(m+ℓ+2)}` (Lemma 7 floor, GIVEN the two phase bounds). |

### Update 2 (same day) — more landed, plus an over-reach caught and removed

Additionally CLOSED, axiom-clean:
- **D general case** — `EkeraCombinatorics.count_good_pairs_lower_bound_general`: ≥ 2^{ℓ+m−1} good
  outcomes for ALL `0<d<2^m` (the 2-adic-fibre count; hypotheses are exactly the paper's, no oddness).
- **The 2-register orbit eigenstate** — `ShortDLPOrbit.short_dlp_orbit_joint_eigen`: the joint
  short-DLP eigenstate (Kronecker product of two `fourierEigenstate`s) is a joint eigenstate with the
  product phase, by reusing the proven 1-register `fourierEigenstate_eigen_lsb` once per register.
- **C2 → good-factor connector** — `EkeraGoodFactorBound.ekeraGoodFactor_le_clamped_trigamma`:
  `ekeraGoodFactor τ ≤ max 0 (1 − ψ'(2^τ))` (both clamped — the un-clamped form is false at τ=0).

**Over-reach caught and REMOVED (honesty).**  A build attempt tried to close the residue-to-phase
bridge by DEFINING the per-register "true phase" `ehPhaseM m d j` as a function of the *outcome* `j`
(`= (j + {dj}/2^{m-1})/2^m`), so the phase discrepancy is small *by construction*.  That is circular:
a real QPE eigenphase is fixed by `d`, not chosen per outcome; the resulting `short_dlp_measurement_dist`
is not a normalised Born distribution (it would assign ~peak probability to every outcome), so the
derived "EH ≥ 1/8 **unconditional**" and the structure inhabitations (`measProb`/`condGood` set to
whatever satisfies the obligation) were VACUOUS — no better than the pre-existing `ekeraTrivialSuccess`.
Those files (`ShortDLPSuccess.lean` + the bridge/unconditional parts of `ShortDLPOrbit.lean`) were
deleted.  The obligations are **NOT** discharged.

**The genuine remaining gap (still open, NOT faked):** the FAITHFUL residue-to-phase bridge — that
a good pair's joint residue puts the run near the FIXED eigenphase determined by `d` — together with
the paper's ACTUAL Lemma 7 (a single sum over `b` with one phase angle + Cauchy-Schwarz over the `T_e`
machinery, which does NOT reduce to the factorised two-1-register-peak idealisation that
`ShortDLPPeakLaw` models), and Ekerå Lemma 1/2 as facts about the REAL measurement distribution.  Only
then can `EkeraDLPSuccess` / `EHShortDLPSuccess` be inhabited with the real distribution to genuinely
discharge `good_obl` / `balanced_obl` / `good_prob_obl`.  All the pieces AROUND it (C2, D, the
factorised peak bound, the orbit eigenstate, the good-factor connector) are now in place.

---
## Original narrowing (below) — superseded for C2/D/STEP-A-core by the progress table above


Status after the 2026-06-22 attempt. Two carried hypotheses were targeted:

| Obligation | File / field | Paper source |
|---|---|---|
| `good_prob_obl` | `EkeraHastad.EHShortDLPSuccess.good_prob_obl` | EH 1702.00249 **Lemma 7** |
| `good_obl` | `EkeraSuccess.EkeraDLPSuccess.good_obl` | Ekerå 2023 (2309.01754) **Lemma 1** |
| `balanced_obl` | `EkeraSuccess.EkeraDLPSuccess.balanced_obl` | Ekerå 2023 **Lemma 2** |

**Result: none are provable in the current state, and the reason is a single shared blocker.**
All three are predicates on the abstract structure fields `measProb : ℕ → ℝ` and `condGood : ℕ → ℝ`.
Those fields are *not* the actual measurement distribution — they are placeholders. There is literally
nothing to prove until they are replaced by the genuine short-discrete-log two-register QPE output
law. So the obligations reduce to one construction + three downstream facts.

## The one irreducible blocker — STEP A (the short-DLP measurement distribution)

Construct, as a concrete object, the post-measurement probability
`measProb (j,k) = |⟨j,k| (QFT⊗QFT) · U_{short-DLP} |ψ⟩|²`
for the **two-register** short-DLP circuit (oracle `x ↦ g^x` with the `y = g^{N+1}` shift), the
two-dimensional analogue of order finding.

This is the *exact* analogue of the order-finding gap the repo already isolates:
- the repo PROVES the 1-register peak law `qpe_prob ≥ 4/π²` (`Framework.qpe_prob_peak_bound`,
  437-line Dirichlet-kernel bound, axiom-clean) and `QPE_MMI_correct_from_orbit`;
- the ONLY thing carried for order finding is the structural `h_orbit_exists` (the oracle's
  orbit-state eigendecomposition), see `CFS.QPEPeakLaw.residueShorFinalState_peak_law`.

STEP A is the two-register version of `h_orbit_exists` + the 2-D Dirichlet kernel. **This is the
research target with the most leverage** — it unblocks all three obligations.

## Downstream of STEP A (each then becomes a concrete, citable computation)

- **STEP B — `good_prob_obl` (EH Lemma 7):** per-good-pair amplitude `≥ 2^{-(m+ℓ+2)}`. A 2-D
  Dirichlet-kernel lower bound; should generalize the proven 1-D `qpe_prob_peak_bound`.
  *Lit:* Ekerå–Håstad PQCrypto 2017; Ekerå ePrint **2017/1122 App. A.2.1**.

- **STEP D — `balanced_obl` (Ekerå 2023 Lemma 2):** the `t`-balanced set carries measure
  `≥ 1 − 2^{Δ−2(t−1)−τ}`. Pure lattice-geometry counting of which measured `j` give a `t`-balanced
  `L^τ(j)` — does NOT need new analysis, only STEP A's distribution + a counting bound.
  *Lit:* Ekerå 2023 (2309.01754) `lemma:bound-t-balanced-Lj`.

- **STEP C — `good_obl` (Ekerå 2023 Lemma 1):** `condGood j ≥ ekeraGoodFactor τ`. Splits into:
  - **C1** (needs STEP A): `P((j,k) τ-good | j) = 1 − S(j,τ)` for an explicit finite sum `S`, and
    `S(j,τ) ≤ ψ'(2^τ)` (trigamma). Fourier identity on the conditional distribution.
  - **C2 — the one STANDALONE, self-contained sub-lemma** (the Nemes trigamma bound, already baked
    into `ekeraGoodFactor`'s definition): for `x ≥ 1`,
    `ψ'(x) ≤ 1/x + 1/(2x²) + 1/(6x³)`, where `ψ'(x) = ∑_{n≥0} 1/(x+n)²`.
    **Mathlib has NO polygamma/trigamma** (only `Real.Gamma`), so this requires defining `ψ'` as the
    series and proving the Nemes bound by integral/Euler–Maclaurin comparison. It is independent of
    STEP A and could be formalized on its own.
    *Lit:* Nemes, "Generalization of the bounds on the psi/polygamma functions" (2014); Ekerå 2023
    Claim `bound-trigamma`.

## What IS already proven (so the obligations are the only gap)

`EkeraSuccess` / `EkeraHastad` already prove, axiom-clean, everything *around* the obligations:
the two-factor combination `success_ge` (logical core of Thm 1), `ekeraGoodFactor_ge`
(`≥ 1 − 3/2^τ` amplification), the deterministic factor recovery (`ekera_recover`,
`ekera_factor`), and the lattice-radius geometry (`eh_good_vector_within_radius`). Only the
distribution-level STEP A and its consequences (B/C1/D) + the standalone analytic C2 remain.

## Recommended research order

1. **C2** (Nemes trigamma bound) — fully standalone, no quantum content; good warm-up.
2. **STEP A** (two-register short-DLP distribution) — highest leverage; mirror the order-finding
   `qpe_prob_peak_bound` / `h_orbit_exists` architecture in `CFS.QPEPeakLaw`.
3. **B, D, C1** — mechanical once A is in hand.
