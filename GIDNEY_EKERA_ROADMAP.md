# Roadmap — verifying Gidney–Ekerå "8 hours / 20M qubits" end-to-end

Goal: is FormalRV general enough to verify the **semantic correctness** (the
algorithm succeeds with the claimed probability) of Gidney & Ekerå,
*"How to factor 2048-bit RSA integers in 8 hours…"* — and if not, what does it
take?  (Resource-estimate verification — the qubit/time numbers from the Python
cost model — is a *separate* axis, noted at the end.)

## Where our framework is — and is not — general enough

Our headline is `Shor_correct_verified_no_modmult_axioms`
(`FormalRV/Shor/Main.lean`), kernel-clean `[propext, Classical.choice,
Quot.sound]`.  It proves, for **order-finding** Shor:

    probability_of_success a r N m n anc family ≥ κ / (log₂ N)^4

The proof (`Shor_correct_var_conditional`, `Shor/Part4.lean:83`) factors into
two layers — and this layering is the key to generalization:

| Layer | What it proves | Generality |
|---|---|---|
| **QPE peak** (`h_QPE_MMI_correct`) | the phase estimate concentrates at `s_closest(k/r)` with prob `≥ 4/(π² r)`, for any `ModMulImpl a N n anc family` | **semi-general** — about phase estimation over a modular-mult oracle family; parameterised over `a,r,N,m,n,anc` |
| **post-processing** (`r_found`, `s_closest`, `ContinuedFraction`, coprimality count, totient bound) | continued-fractions recovers `r`; coprime-residue count gives `κ/(log₂N)^4` | **order-finding-specific** |

Pluggable boundary that *is* general: the **arithmetic oracle**
(`VerifiedModMulFamily` / `ModMulImpl`) — any circuit realising
`MultiplyCircuitProperty (a^(2^i)) N` plugs in (this is how our SQIR and
windowed multipliers attach).

So we are general **at the oracle boundary** but **specialised at the algorithm
level**: order-finding, single exponent register, **exact** modular
multiplication, ideal QFT, continued-fraction post-processing.

## The four things Gidney–Ekerå needs that we don't have

From `main.tex` (deep-read): the paper's algorithm differs from textbook
order-finding in four independent ways.

### Gap 1 — Ekerå–Håstad short-DLP encoding (the "different Shor")
`main.tex:468–501`.  Factor `N=pq` via a **short discrete log** `d = log_g(g^{N+1}) = p+q`
(then `p,q` are roots of `p²−dp+N=0`).  Quantum part: **two** exponent registers
`e₁` (2m), `e₂` (m), `m≈0.5n`, period-finding on `f(e₁,e₂)=g^{e₁} y^{−e₂}`,
total exponent `n_e=1.5n`.  Classical post-processing is **lattice-based**
(Ekerå 2017, ≥99%, single run, does **not** need `r`).
- Reuses: the QPE-peak layer (extended to two registers).
- New: two-register phase estimation; the **lattice post-processing success
  theorem** (research-level — realistically *axiomatised*, citing Ekerå 2017,
  exactly as we once axiomatised `f_modmult_*` then discharged it).

### Gap 2 — Zalka coset representation (approximate arithmetic)
`main.tex:535–548`.  Represent `k mod N` as a periodic superposition
`√(2^{−c_pad}) Σ_j |jN+k⟩`; a **non-modular** adder then does *approximate*
modular addition, error `~2^{−c_pad}`.
- Our oracle contract is **exact** (`MultiplyCircuitProperty` = exact equality).
- New: an **`ApproximateModMulImpl`** contract with operator-norm / trace-distance
  error bounds, and a theorem that the success probability degrades gracefully
  (Gidney 2019 "approximate encoded permutations").  This is a *new verification
  mode* — moving from exact `Gate.applyNat` equality to bounded-error analysis.

### Gap 3 — two-level windowed arithmetic (`c_mul`, `c_exp`) + QROM
`main.tex:549–601`.  `c_mul` fuses additions into one **lookup addition** (QROM
table of `2^{c_mul}` values); `c_exp` fuses multiplications by folding exponent
bits into the lookup addresses.  We have **windowSize = 2** (`windowed2…`), and
even that uses an explicit 3-case CCX cascade, **not** a real QROM lookup.
- New: parametric window size; a **verified QROM lookup-addition + measurement
  uncomputation** primitive; the `c_exp` oracle structure (multiplicand looked
  up from exponent bits — a *different* oracle than fixed `a^(2^i)`).
- Note: for **semantic correctness** this is "build an oracle that meets the
  (approximate) contract"; the windowing *speedup* is a cost concern.

### Gap 4 — semiclassical (Griffiths–Niu) QFT + recycling
`main.tex:528–534`.  Benign: the paper analyses success **assuming an ideal QFT**,
so our ideal-QFT analysis stands.  Optional: a unitary-equivalence theorem.

## Phased plan

Difficulty: SMALL/MEDIUM = framework scaffolding we can fully prove; LARGE =
research-level math, realistically *axiomatised as a named contract* (then
optionally discharged later).

- **Phase A — encoding-agnostic Shor (keystone). ✅ FOUNDATION LANDED**
  (`FormalRV/Shor/EncodingAgnostic.lean`, kernel-clean, additive — headline
  untouched).  Extracted the concentration argument as the reusable peak-sum
  lower bound `success_ge_card_mul`; bundled it into the pluggable
  `ShorPostProcessing` contract (+ `.bound`); and showed order-finding fits via
  `probability_of_success_ge_peaks` (its headline quantity is `≥ |peaks|·p` for
  any accepted, concentrated peak set).  Ekerå–Håstad now gets the same bound
  from the same keystone with its own acceptance/peaks.  Remaining (later):
  optionally rewire the existing `Shor_correct_var_conditional` to call the
  keystone instead of inlining Steps 1–2.
- **Phase B — Ekerå–Håstad short-DLP. ✅ PER-RUN CONTRACT LANDED**
  (`FormalRV/Shor/EkeraHastad.lean`, kernel-clean; read verbatim from 1702.00249).
  - *Classical reduction* (§1): `ekera_recover`/`ekera_recover_actual` (recover
    `p,q` from `d` via the quadratic `p,q=(d+1)±√((d+1)²−N)`), `ekera_congruence`,
    `ekera_short_dl_eq`, `ekera_factor`.
  - *Lattice recovery* (§2): `EHGoodPair` (good-pair def, l.525) +
    `eh_good_vector_within_radius` — the geometric correctness (the good vector
    with last component `d` lies within radius `√(s/4+1)·2^m`, l.675), PROVEN.
  - *Per-run success* (§3): `EHShortDLPSuccess` contract bundling the two
    genuinely-quantum named obligations (Lemma 7 per-pair prob `≥2^{-m-ℓ-2}` +
    the count lemma `≥2^{ℓ+m-1}` good `j`); `EHShortDLPSuccess.goodProb_ge`
    derives per-run good-pair prob `≥ #good·p` **via the Phase-A keystone**
    `success_ge_card_mul`; `goodProb_ge_eighth` gives the paper's `≥ 1/8`.
  - Architectural payoff verified: the SAME keystone yields EH's
    `2^{ℓ+m-1}·2^{-m-ℓ-2}=1/8` and order-finding's `φ(r)·4/(π²r)`.
  - Remaining (optional refinement): discharge Lemma 7 / the count lemma from the
    quantum-Fourier analysis, or import the refined ≥99% bound from 2017/1122.
- **Phase C — approximate/coset oracle contract. ✅ LANDED**
  (`FormalRV/Shor/Approx/*.lean`, kernel-clean, wired into the default build).
  Read verbatim from Gidney 2019 (1905.08488) + Zalka 2006 + the 8-hours coset
  section.  Gidney's metric is COMBINATORIAL (`Dev = max_g |Deviated_g|/|C|`), not
  a norm — so the provable core split cleanly from the cited quantum facts:
  - *Graceful-degradation bridge* (`GracefulDegradation.lean`):
    `prob_partial_meas_diff_le_two_dist` — for a basis-vector outcome,
    `|P(s|φ) − P(s|ψ)| ≤ 2·‖φ−ψ‖₂` (the Born prob is `‖Pₛφ‖²`; proof = projector
    nonincreasing + `||a|²−|b|²| ≤ |a−b|(|a|+|b|)` + Cauchy–Schwarz).  PROVED.
  - *Success stability* (`SuccessStable.lean`): `probability_of_success_stable`
    (`|Δsuccess| ≤ 2^m·2δ`) and the headline `shor_success_approx`
    (`success_f ≥ B − 2^m·2δ`).  PROVED.
  - *Contract* (`CosetContract.lean`): `ApproxCosetShor` + `.shorCorrect`
    (`≥ idealBound − 2^m·4√totalDev`) + `.shorCorrect_exact` (`totalDev=0` ⇒ no
    degradation, recovering the exact path).  PROVED.
  - *Deviation algebra* (`Deviation.lean`): `Dev`/`DevBound` (Def 2.1–2.4),
    `DevBound_comp` (**Thm 2.10 subadditivity**, proved via finite union/injection),
    `DevBound_compList` (k ops ⇒ `≤ k·ε`, the accumulation), `DevBound_id`.  PROVED.
  - Two NAMED OBLIGATIONS (cited, the only quantum facts): `TraceDistanceFromDeviation`
    (Gidney Thm 2.6, `Dev ≤ ε ⇒ distance ≤ 2√ε`) and `CosetAdderDeviationBound`
    (Thm 3.3, per-add `Dev ≤ 2^{-pad}`).
- **Phase D — windowed arithmetic generalisation. 🔶 ARITHMETIC CORE LANDED**
  (`FormalRV/Shor/WindowedArith.lean`, kernel-clean, wired into the build).  Read
  verbatim from Gidney 1905.07682 + the 8-hours `c_mul`/`c_exp` section.
  - *Proved (parametric in window size `w`, generalising the hard-wired `w=2`):*
    `windowed_expansion` (base-`2^w` digit expansion), `windowed_mul`
    (`k·x = Σⱼ (k·windowⱼ(x))·2^{jw}`), **`windowed_modProductAdd`** (the windowed
    modular product-add `(Σⱼ tableValueⱼ) % N = (a·y) % N`, with `tableValue`
    matching the repo's entry = paper l.408), the circuit-aligned fold
    `windowedLookupFold` + `windowedLookupFold_modProductAdd`, and `address_concat`
    (the `c_exp` exponent⊕factor address split — same lookup, wider address).
  - *Arbitrary `c_mul` AND `c_exp`:* the window size `w` is a free `Nat` throughout.
    `windowed_modProductAdd` (set `w := c_mul`, additive) and **`windowed_exp_modProduct`**
    (set `w := c_exp`, MULTIPLICATIVE: `(∏ᵢ g^{windowᵢ(e)·2^{i·c_exp}} mod N) mod N =
    g^e mod N`) cover both windowing levels for any window size; `address_concat`
    gives the two-level `c_exp⊕c_mul` address split.
  - *Faithful `lookupAddGate`* (`WindowedLookupAdd.lean`): DEFINED as `read ; add ; read`
    (Gidney l.276) REUSING the exact existing proven components — the table read is
    `BQAlgo.unary_lookup_multi_iteration` (babbush2018 QROM, `unary_lookup_iteration_correct`)
    and the add is `BQAlgo.cuccaro_n_bit_adder_full` (`cuccaro_n_bit_adder_full_correct`).
    `lookupAddGate_tcount` proven (`= 2·read + 14·adderLen`).  Per-step value-correctness =
    composition of those two cited theorems + read-involution uncompute; multi-window value
    identity = the proven `windowedLookupFold_modProductAdd`.  (Remaining: the layout
    plumbing wiring the lookup word register to the adder addend — index alignment only.)
  - *FULL LOGICAL CIRCUIT, any window size* (`WindowedCircuit.lean`):
    `windowedMulCircuit w bits a numWin` — a concrete `Gate`-IR circuit that, on the
    integer `y` ENCODED in logical qubits (`encodeReg`), computes `acc += a·y` by
    folding per-window `read·add·unread` (proven QROM `unary_lookup_multi_iteration` +
    proven Cuccaro adder).  Executed on encoded integers at `w=1` and `w=2`
    (`WindowedCircuitExec`, `native_decide`).
  - *Resource count + PAPER COMPARISON* (kernel-clean): `windowedMulCircuit_toffoli`
    `= numWin·(4·w·2^w + 2·bits)` Toffolis.  Paper (1905.09749 §abstract, main.tex:78):
    `0.3 n³ + 0.0005 n³ lg n` Toffolis, `3n + 0.002 n lg n` logical qubits.  Our
    per-product-add `4n·2^w + 2n²/w` (`bits=n, numWin=n/w`) is the *no-optimization
    upper bound*; the gap to the paper's `O(n²/lg n)`/mult (→ `O(n³)` total) is EXACTLY
    the Gray-code (`×w`) + measurement-uncompute (`×2`) optimizations, which the repo
    defers to — and the **PPM layer** supplies.  Same `Θ` scaling.
  - *PPM HAND-OFF* (`WindowedPPM.lean`, kernel-clean): `windowedMulCircuit_magicDemand`
    — `shorMagicDemand (windowedMulCircuit …) = numWin·(4·w·2^w + 2·bits)`: compiling
    the circuit through the PPM magic-state compiler demands EXACTLY the verified
    Toffoli count of magic states (via the proven `shorMagicDemand_eq_ccxCount`).  The
    logical `Gate` plugs straight into the magic-factory / lattice-surgery layer.
  - *INTERFACE to the Shor headline*: `windowedLookupFold_eq_modmul` shows the circuit's
    value is `a·x mod N` = the `MultiplyCircuitProperty a N` spec; the `Gate` lifts to
    `uc_eval`/`ModMulImpl` via the existing `Gate→BaseUCom` adapter (same path the `w=2`
    `WindowedShorConnection` already uses to reach the verified Shor success bound).
  - *Capstone* (`WindowedCapstone.lean`): `windowedMultiplier_verified` bundles
    value-correctness + Toffoli count + PPM magic demand in one theorem, ∀ `(w,bits,a,numWin,N,x)`.
  - *Named obligations:* `WindowedExpCorrect` (the full exponentiation composition —
    Gidney l.502 states it is *empirically tested, not proven*); measurement-based
    uncompute is value-identity (provable) + a phase obligation (out of scope for the
    Boolean layer, cites berry2019/low2018); and the circuit-level
    `MultiplyCircuitProperty` for `windowedMulCircuit` (the value is proven; remaining =
    layout-index alignment + the in-place/encode wrapper, mirroring `WindowedShorConnection`).
- **Phase E — semiclassical QFT equivalence.**  Optional.  SMALL.
- **EH lattice post-processing + coset error bound** — the two research-level
  results; axiomatise as named contracts (cite Ekerå 2017 / Gidney 2019),
  discharge later if desired.

Dependencies: A is the keystone (unblocks plugging any encoding).  B feeds A's EH
instantiation.  C is orthogonal (oracle-contract generalisation).  D builds the
concrete oracle meeting C.  E benign.

## Honest bottom line
- **Oracle-level**: already general (pluggable).
- **Algorithm-level**: specialised to order-finding; EH needs Phases A+B + the
  (axiomatised) lattice success theorem.
- **Arithmetic-level**: coset (C) and windowing (D) are the bulk of the
  *new circuit verification*.
- Full end-to-end is a multi-phase effort; the heaviest math (lattice
  post-processing, coset approximation) is research-level and best entered as
  named contracts, with the framework providing verified scaffolding around them
  — the same pattern that took our windowed multiplier from `h_tw`/`h_unload`
  obligations to the unconditional headline.

## GAP-CLOSURE (a) parametric width + (b) measurement-uncompute
- **(a) DONE — parametric structural qubit count** (`FormalRV/Shor/WindowedWidth.lean`,
  kernel-clean): `width_windowedMulCircuit` proves `width (windowedMulCircuit w bits a numWin)
  = 2·w + 2·bits + numWin·w + 2` for ALL `w,bits,numWin ≥ 1`, by bounding `maxIdx` of every
  component (Cuccaro `maxIdx_cuccaro_full`, unary lookup `maxIdx_lookupReadAt_le`, copies)
  from their `Gate` definitions.  Generalizes the per-instance `decide` facts to all `n`;
  the `numWin·w` (data) + `2·bits` (acc+addend, incl. padding) are read off the structure.
- **(b) PARTIAL — measurement-uncompute** (`FormalRV/Shor/MeasUncompute.lean`, kernel-clean):
  added a non-breaking measurement-augmented IR `EGate = base Gate | mz | seq` (the top-level
  design; `mz q` = measure-reset, the computational effect of measurement-based uncompute).
  `measLookupAdd` = read·add·MEASURE-clear; `measUncompute_saves_a_read` proves its Toffoli
  count is `2·w·2^w + 2·bits`, HALF the double-read `lookupAddAt` (`4·w·2^w + 2·bits`) — the
  `4w·2^w → 2w·2^w` reduction read off the `EGate` structure.  `measLookupAdd_acc_eq` proves
  it computes the SAME accumulator as the proven unitary read+adder (measurement clears the
  temp without disturbing the accumulator); the phase-fixup is a named obligation (Berry 2019).
  Pushed further: `measUnaryRead` measures (not unitarily uncomputes) the per-iteration AND
  cascade, so the READ drops to `w·2^w` (`tcount_measUnaryRead`); `optLookupAdd` = that read ·
  add · measure-clear has Toffoli count `w·2^w + 2·bits` (`toffoli_optLookupAdd`).
- **(b) DONE — babbush2018 QROM, NO black box** (`MeasUncompute.lean`, kernel-clean; read from
  the now-in-library arXiv:1805.03662 §III.A unary iteration / §III.C QROM).  `unaryQROM` is the
  babbush unary-iteration QROM built directly as an `EGate`: at each node ONE `CCX` (AND),
  REUSED for both index halves via a `CX` flip, recurse, measure-uncompute — the `T(d)=2T(d−1)+1`
  recursion giving **exactly `2^w − 1` Toffolis** (`toffoli_unaryQROM`, proven structurally) with
  `w` ancillas, independent of word width.  `MeasUncomputeExec` `native_decide`-verifies it reads
  `T[a]` for ALL `w=2` addresses and two tables (semantically correct, not just the right count).
  `babbushLookupAdd` = unary read · Cuccaro add · measure-clear has Toffoli count
  **`(2^w − 1) + 2·bits`** (`toffoli_babbushLookupAdd`) — matching Gidney–Ekerå's `2^{c_mul+c_exp}`
  lookup.  The Gray-code/amortization factor is now a first-class emittable circuit, no citation
  black box; the structural lookup-add cost is the paper's `≈ 2^w + 2·bits`.

## AUDIT: structural (circuit-derived) vs paper-formula (arithmetic only)
A self-audit (does each reported count come from the verified `Gate`, or is it a formula?):
- **Circuit-DERIVED (proven by `tcount`/`maxIdx` recursion on the actual `Gate`)** —
  `WindowedCircuit`: `windowedMulCircuit_toffoli` (per multiply-add), `composedModExp_toffoli`
  (full `numMults`-mult skeleton), `windowedMulCircuit_toffoli_padded` (the `lg n` Toffoli
  term = adder over `g_pad` padding qubits), `width`/`width_…_padding` (qubit count from the
  Gate; padding adds `2·pad` qubits, kernel `decide`); `WindowedPPM.windowedMulCircuit_magicDemand`
  (magic = structural Toffoli).  These ARE provable from the semantically-correct circuit.
- **Paper-FORMULA arithmetic (NOT circuit-derived, now flagged in-file)** — `WindowedCostModel.*`
  (`toffoliCount`, `measurementDepth`, `totalDeviation`, `workRegisterQubits`) reproduce the
  paper's §"cost estimate" equations and prove they reduce to `0.3 n³ + …`.  Honestly: the
  structural circuit above is the UNOPTIMIZED construction (`≈6 n³` at `w=lg n`); the paper's
  `0.3 n³` needs Gray-code + meas-uncompute (`4·w·2^w→2^w`) + oblivious runways, NOT yet built
  as `Gate`s.  The cost model checks the paper's optimized formula is self-consistent; it does
  not assert that formula is a verified circuit's `tcount`.  Closing this fully = building the
  optimized circuit and counting it structurally (large, future work).

## Resource-estimate verification — ✅ HEADLINE NUMBERS VERIFIED
`FormalRV/Shor/WindowedCostModel.lean` (kernel-clean) formalizes the paper's EXACT
abstract-circuit cost formulas (main.tex:685–731) over ℚ and verifies the abstract's
reported figures (main.tex:78):
- **Toffoli count**: `toffoliCount = LookupAdditionCount · perLookupToffoli`, params
  `g_exp=g_mul=5, g_sep=1024, g_pad=3 lg n+10, n_e=1.5n`.  `toffoliCount_closed`:
  exact `= 123/512·n³ + 369/1048576·n³ lg n + …`.  `toffoli_coeffs_le_paper`: the exact
  leading coeffs `123/512 ≈ 0.2402` and `369/1048576 ≈ 0.000352` are `≤` the paper's
  reported `0.3` and `0.0005` (their `0.3 n³` is a rounded-up "approximate upper bound",
  l.731 — they round `LookupAdditionCount 0.08·n·n_e → 0.1`).  `toffoliCount_le_paper`
  (n≥2100) and **`toffoliCount_rsa2048`**: at `n=2048` the exact model gives
  `2 622 824 448` Toffolis `≤` paper's `≈2.624·10⁹` (agree to 0.05%).
- **Measurement depth**: `measurementDepth_le_paper` — exact `≈371 n² + 0.72 n² lg n`
  `≤` reported `500 n² + n² lg n`.
- **Logical qubits**: `workRegisterQubits_eq` — leading `3n` (three n-qubit registers;
  exponent recycled via semiclassical QFT).  The `+0.002 n lg n` coset/runway padding is
  cited (the paper gives no closed-form equation for it).

Honesty: typo flagged at main.tex:712 (`2^{g_exp+g_pad}` → `2^{g_exp+g_mul}`, per l.594).
Remaining: the circuit-level link is APPROXIMATE — `windowedMulCircuit` does *non-modular*
adds, made ≈modular by the coset rep, so it connects through Phase C's `ApproxCosetShor`
(degraded success), not the exact `MultiplyCircuitProperty` (which is the exact-modular path).

## Expected-TIME cost + the fidelity→repetition factor (`FormalRV/Shor/WindowedTimeCost.lean`)
Per-shot resource counts (Toffolis, depth) are NOT the wall-clock cost: total expected
time `= per-shot-time × shots`, and `shots ≈ 1/P_success`.  Kernel-clean:
- *Faithful degradation* (fixing the earlier `2^m` looseness): `success_diff_le_measL1`
  (`|Δsuccess| ≤ Σ_x|Δprob_x|`, PROVED — success is a subset-sum of the measurement
  distribution) + `ApproxCosetShorTight.shorCorrect` (`success ≥ idealBound − 4√totalDev`,
  via Gidney Thm 2.6 operational trace-distance obligation — NO `2^m`).
- *Time model*: `totalExpectedTime perShot p = perShot/p`; `time_inflates_under_degradation`
  (lower `p` ⇒ more time); `neglected_time_factor` (`perShot ≤ perShot/p`, the `1/p` that
  per-shot counts omit); `confidence_of_shots` (`(1−p)^k ≤ ε` for `1−ε` confidence).
- *Logical-error compounding* (the sharp form): `successWithLogicalError P p_L k = P·(1−p_L)^k`,
  `logicalError_inflates_time` — the SAME operation count `k` (Toffoli count) that sets the
  per-shot time ALSO suppresses success by `(1−p_L)^k`, so it inflates total time TWICE;
  per-shot-only estimates capture only the first.  This is the effect prior estimates may
  neglect (user's observation).
- *Coset deviation*: `cosetTotalDev numAdds c_pad = numAdds·2^{−c_pad}` (Thm 3.3 + 2.10
  accumulation), `cosetTotalDev_antitone` (padding shrinks it → approximation penalty → 0,
  so the dominant repetition cost is the logical-error factor).
- *Probability-theory foundation*: `expectedShots_eq_tailsum` — `expectedShots = 1/p` is
  DERIVED as the `Geometric(p)` mean via the tail-sum `E[T]=∑_{k≥0}P(T>k)=∑(1−p)^k=1/p`
  (`tsum_geometric_of_lt_one`), not posited.  `probExceeds p k = (1−p)^k`.
- *Exact `10⁻⁷` (faithful fix)*: `WindowedCostModel.totalDeviation` uses the paper's actual
  per-add deviation `n/(g_sep·2^{g_pad})` (main.tex:741); `totalDeviation_eq_const` proves it
  is the CONSTANT `41/536870912 ≈ 7.64·10⁻⁸` (the `n²·n_e` cancel), `totalDeviation_le` ⇒
  `≤ 10⁻⁷` — verifying main.tex:753 exactly.  This is WHY the resource counts carry the
  `+lg n` terms: `g_pad ∝ lg n` keeps the deviation (hence the shot count) `n`-independent —
  the per-shot `lg n` overhead is the price of constant fidelity.
- *Gaps audit (honest)*: the paper is careful — it explicitly accounts for "repeated
  attempts" (l.76) and bounds the approximation error (l.758).  Genuine findings: (i) typo
  main.tex:712 (`2^{g_exp+g_pad}`→`2^{g_exp+g_mul}`); (ii) the constant-deviation engineering
  (g_pad∝lg n) is easy to neglect — a fixed g_pad would blow up shots for large n; the
  general field pitfall of dropping the `1/P` shot factor is real but NOT made by this paper.
