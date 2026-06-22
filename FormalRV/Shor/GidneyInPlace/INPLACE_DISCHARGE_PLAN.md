# In-place coset multiplier — consolidated contract-discharge plan (G4+G5+G6+G7)

**Date:** 2026-06-18.  Supersedes the stale "ranked gap table" framing (which described the
**retired** `accYSwap ; mulFwd(N−aInv)` single-register variant and listed already-closed leaves
as open).  This plan is written against the **live faithful two-register construction**
`gidneyInPlaceWithSwap` and targets the one frozen frontier
`InPlaceCosetSpec.inplaceReducedLookupCosetMul_shift`.

---

## §0. Corrected state of the world (what is ACTUALLY green, axiom-clean)

All `[propext, Classical.choice, Quot.sound]`, no `sorry`/`native_decide`.

| Piece | Theorem | Status |
|---|---|---|
| **Arch-A** local deviation | `InPlaceCosetNormBound.gidneyTwoRegInPlace_coset_norm_bound` : `normSqDist (uc_eval(gidneyTwoRegInPlaceCosetMul)·cosetInputVec x 0) (cosetInputVec 0 ((k·x)%N)) ≤ 4·numWin/2^cm` | ✅ frozen-green |
| **Arch-B** off-bad exact shift | `InPlaceComposedAgree.gidneyInPlaceWithSwap_agree_off` : `∃B, ∀ i∉B, uc_eval(gidneyInPlaceWithSwap)·cosetInputVec x 0 = cosetInputVec ((k·x)%N) 0` (output back in a-block) | ✅ |
| **Arch-B** bad-set mass (D1–D4) | `InPlaceReverseCount.inplaceBadIn_bornWeight_le` : `bornWeightOn (cosetInputVec x 0) inplaceBadIn ≤ 2·numWin/2^cm` | ✅ (was RED in WIP — `inplaceBfwd_bornWeight_le` was unqualified; **fixed 2026-06-18**) |
| **Arch-B** bad-set mass CAPSTONE (D5) | `InPlaceComposedMassBound.inplaceBadSetB_evolved_bornWeight_le` : `bornWeightOn (uc_eval(gidneyInPlaceWithSwap)·cosetInputVec x 0) inplaceBadSetB ≤ 2·numWin/2^cm` | ✅ **new 2026-06-18** |

| **Arch-B** TARGET-mass leg | `InPlaceTargetMassLegClosed.inplaceBadSetB_target_bornWeight_le_closed` : `bornWeightOn (cosetInputVec ((k·x)%N) 0) inplaceBadSetB ≤ 2·numWin/2^cm` | ✅ **UNCONDITIONAL 2026-06-18** (T1+T2+T3) |
| **T1** normalization | `InPlaceCosetInputNorm.cosetInputVec_normalized` : `bornWeightOn (cosetInputVec x 0) univ = 1` | ✅ (eGid reindex · `betaB_normSq_total` · `cosetState_normalized`) |
| **T2** explicit-B agree | `InPlaceAgreeOffExplicit.gidneyInPlaceWithSwap_agree_off_explicit` : off the EXACT `inplaceBadSetB`, evolved = target (no `∃`) | ✅ (§6 body lifted) |

| **G3** deviation CAPSTONE | `InPlaceCosetDeviation.gidneyInPlaceWithSwap_coset_deviation` : `normSqDist (uc_eval(gidneyInPlaceWithSwap)·cosetInputVec x 0) (cosetInputVec ((k·x)%N) 0) ≤ 4·numWin/2^cm` | ✅ **SEALED 2026-06-18** (T2 agree + D5 + T3 via `normSqDist_le_of_agree_off`, no Arch-A shortcut) |

So **G1, G2, G3 are fully closed** on the two-register object — BOTH deviation-consumer masses (`hw₁` D5 evolved, `hw₂` T3 target) are supplied unconditionally, and the single contract-level deviation object `gidneyInPlaceWithSwap_coset_deviation` is sealed for the marginal route to consume.

⚠ **E0 CONSUMER AUDIT (2026-06-18) — correction of an earlier wrong claim.**  The deviation consumer
is `CosetBornWeight.normSqDist_le_of_agree_off`, whose signature **requires the bad mass on BOTH
states** (`hw₁` evolved AND `hw₂` target) — verified by signature, and matched by the proven
out-of-place template (`reducedLookupWindowedMul_embedAgreeOff_local` returns both masses) and the
`CosetAgreesOffWrap` bundle (`coset_born_le` + `ideal_born_le`).  My earlier "target leg not separately
needed" claim was **false for the deviation consumer**; D5 is only `hw₁`.  The target leg
(`hw₂`) is supplied by `InPlaceTargetMassLeg`, via mass conservation (target and evolved agree off `B`
+ equal totals ⇒ equal on-`B` mass ⇒ D5 transfers).  Both prerequisite facts are now DISCHARGED
(2026-06-18): `hagreeB` ← T2 `gidneyInPlaceWithSwap_agree_off_explicit` (the §6 body lifted, explicit-`B`,
no `∃`) and `hnorm` ← T1 `cosetInputVec_normalized` at residues `x` and `(k·x)%N` (both unit-norm).
The closed target leg is `InPlaceTargetMassLegClosed.inplaceBadSetB_target_bornWeight_le_closed`.
**Constant (E0 step 4):** both masses are `W = 2·numWin/2^cm` ⇒ `normSqDist ≤ 2·W =
4·numWin/2^cm` (matches the Arch-A scalar bound); `numWin` stays physical — no doubling at instantiation.

### The two gates (do not confuse)
- `gidneyTwoRegInPlaceCosetMul := Gate.seq pass1 (Gate.reverse pass2)` — output in **b**-block (no swap).  Used by Arch-A.
- `gidneyInPlaceWithSwap := Gate.seq gidneyTwoRegInPlaceCosetMul (swapAB)` — output back in **a**-block.  Used by Arch-B.  **This is the contract-facing gate** (input AND output read from the a-block).

---

## §1. The EXACT residual gap (two-register proven → single-register contract)

`inplaceReducedLookupCosetMul_shift n anc N cm a numWin g` (frozen, `InPlaceCosetSpec.lean:71`) wants
`g : BaseUCom (n+anc)` with, on the **single** work register `Fin(2^(n+anc))`:
- `∀z<N ∀i∉B, uc_eval g (cosetState (2^(n+anc)) N cm z) i 0 = cosetState (2^(n+anc)) N cm ((a·z)%N) i 0`,
- `∀z<N, bornWeightOn (cosetState (2^(n+anc)) N cm z) B ≤ numWin/2^cm`.

What we have proven is on `Fin(2^(cosetDim w bits))` and uses the **two-register** product state
`cosetInputVec w bits N cm x 0`.  The residual gap is exactly **three deltas**, none of which is new
arithmetic:

1. **Register-iso (G4).**  `Fin(2^(cosetDim w bits)) ≅ Fin(2^(bits + cosetAnc w bits))` with
   `n := bits`, `anc := cosetAnc w bits = 2+2w+2·bits`.  Nat core `bits + cosetAnc = cosetDim` is
   **already proven** (`InPlaceCosetGate.cosetWork_dim_eq`; `cosetDim = 2+2w+3·bits`).  Mechanical.

2. **State-encoding mismatch (G5 — the genuine pole).**  CONFIRMED factual difference:
   - `cosetState (2^(n+anc)) N cm z` is supported on `z + j·N < N + 2^cm·N` ⇒ as a full-register index
     it is `cosetState z` on the **a-block** ⊗ **|0⟩** on the b-block/scratch/ctrl.
   - `cosetInputVec z 0` is `cosetState z` (a) ⊗ **`cosetState 0`** (b, a runway *superposition*) ⊗
     |clean⟩ ⊗ |ctrl=1⟩.
   - They differ on the **b-block** (`|0⟩` vs `cosetState 0`) and on **ctrl**.  Reconciling this is G5.

3. **Constant (G6).**  Our bad mass is `2·numWin/2^cm`; the spec constant is `numWin/2^cm`.
   Discharge by instantiating the spec at `numWin := 2·numWin` (purely at the call site).  Trivial.

---

## §2. G5 — the central design decision (prototype FIRST, before any lemma work)

### ✅ PROBE RESULT (2026-06-18) — verdict: **Route B (marginal), Route C rejected, Route A costly**

The §2 probe is DONE.  Three facts, each grounded in a read of the live code (and one now a
**checked theorem**, `InPlaceContractInput.cosetState_support_lt_aBlock`):

1. **No relabel shortcut (G4-style move is impossible here).**  The contract input
   `cosetState (2^(n+anc)) N cm z` lives entirely in the a-block (support indices `< 2^n`,
   `cosetState_support_lt_aBlock`) ⇒ it is `cosetState z`⊗|0⟩_b, support card `2^cm`.  The proven
   `cosetInputVec z 0` has b = `cosetState 0` (a superposition), support card `(2^cm)²`.  Different
   cardinalities ⇒ no permutation/register-iso can bridge them.  G5 is genuinely a state-CHANGING
   step, not a relabel.
2. **No `prepB` gate exists to reuse.**  Coset preparation is modelled as the abstract isometry
   `E_phys`/`E_data` (`CosetEphys.lean`), and `CosetEmbeddedInit` literally defines the coset init as
   `E_phys (qpeInit)` — never a circuit.  So Route A's `prepB` would be a **fresh build** (a uniform
   `cm`-counter ×N into the b-block — real arithmetic, ~a small windowed-multiply, not "small").
3. **The downstream embedding is PINNED to the single-register `cosetState`.**
   `CosetEphys.cosetEmbedMat_eq_cosetState`: column `yp` of `cosetEmbedMat` IS `cosetState … yp`
   (b=|0⟩).  `ControlOracleLift` consumes exactly this fixed `cosetEmbedMat`.  Re-pointing it to the
   two-register input (**Route C**) would touch `E_phys` + `E_phys_marginal` + `ControlOracleLift` —
   **invasive, rejected.**

**Decision:** pursue **Route B (marginal)**.  The sound capstones already in the tree
(`coset_shor_succeeds_marginal`, `CosetMarginalShorBound`, `CosetMarginalRelabel.agree`) consume a
*marginal* relation, where the b-block (coset-0 ancilla, allocated-and-freed) is **traced out** — so
the `b=|0⟩` vs `b=coset-0` mismatch never has to be reconciled at the full-state level, and no `prepB`
build is needed.  Keep **Route A** documented as the fallback that would instead discharge the frozen
*full-state* contract verbatim (at the cost of the `prepB` arithmetic build).

The two route sketches below are retained for reference; the live plan is Route B (see §3 step 2′/4′).

### Route A — `|0⟩`-init wrapper (makes the contract literally true)
Define `g := prepB ; gidneyInPlaceWithSwap ; Gate.reverse prepB`, where `prepB : Gate` prepares the
b-block from `|0⟩` to `cosetState 0` (and sets ctrl).  Then:
- input `cosetState z` (b=|0⟩, ctrl=0) ──prepB──▶ `cosetInputVec z 0`,
- ──gidneyInPlaceWithSwap──▶ `cosetInputVec ((a·z)%N) 0` off `B` (G2),
- ──reverse prepB──▶ `cosetState ((a·z)%N)` (b back to |0⟩, ctrl cleared).

Obligations: (a) `prepB` correctness `uc_eval prepB · cosetState z = cosetInputVec z 0` (b-block prep +
ctrl set, a/scratch untouched); (b) `Gate.reverse prepB` clears b=coset0→|0⟩ on the *output* branch;
(c) bad set `B` transports through `prepB` unchanged in mass (`prepB` is a permutation ⇒
`normSqDist_perm_invariant` / `bornWeightOn` reindex — already a known move).
- **Risk:** `cosetState 0` is `uniformSuperposition` over `{0,N,…,(2^cm−1)N}`; is there a *clean small
  gate* `prepB` that produces it from `|0⟩`?  This is the one thing to settle on a tiny `#eval`/by-hand
  instance first.  If no clean `prepB` exists, fall back to Route B.

### Route B — marginal reframe (matches the already-sound capstone route)
Do **not** make `g` a literal single-register exact-off-B map.  Instead target the **marginal**
contract that the sound capstones (`coset_shor_succeeds_marginal`, `CosetMarginalShorBound`,
`CosetMarginalRelabel.agree`) actually consume: trace out the b-block (coset-0 ancilla) and prove the
**a-block marginal** is the coset shift.  The b-block never needs `|0⟩` init — it lives as coset-0
ancilla inside `anc`, exactly as the layout-resolution note (`GIDNEY_INPLACE_DESIGN §4.1 (iv)`)
already anticipated.
- **Risk:** lower (no prep gate), but the contract `inplaceReducedLookupCosetMul_shift` is stated on
  the *full* state, so Route B requires *either* relaxing the frozen spec to its marginal form *or*
  routing through G8 instead of feeding `inplaceReducedLookupCosetMul_shift` directly.  Decide this
  with the spec owner before building.

**Recommendation:** spend the first G5 session on the Route-A `prepB` feasibility probe.  If `prepB`
is clean, Route A discharges the frozen spec verbatim (best outcome).  If not, commit to Route B and
re-point the downstream glue at the marginal capstone.

---

## §3. Concrete lemma list + ordering

Ordering chosen so each step is independently kernel-clean and the riskiest probe is first.

0. **(probe, ½ session)** `prepB` feasibility on a tiny instance (`w=1,bits=…`); decide Route A vs B. *No commit.*
1. **G4 register-iso (mechanical, ~1 session).**
   - `inplaceWorkEquiv w bits : Fin (2^(cosetDim w bits)) ≃ Fin (2^(bits + cosetAnc w bits))` via
     `cosetWork_dim_eq` + `Fin.cast`/`finCongr`.
   - `inplaceWorkGate w bits … : BaseUCom (bits + cosetAnc w bits) := cosetWork_dim_eq ▸ Gate.toUCom (cosetDim w bits) (gidneyInPlaceWithSwap …)` and its `WellTyped`.
   - `cosetState`/`cosetInputVec` transport across the equiv (Born mass is reindex-invariant).
2. **G5 (the pole, Route A: ~3–5 sessions).**
   - `def prepB` + `prepB_correct` (b-block prep + ctrl); `prepB_wellTyped`.
   - `def g := prepB ; gidneyInPlaceWithSwap ; reverse prepB`; `g_wellTyped`.
   - `g_agree_off` : `∀z<N ∀i∉B', uc_eval g (cosetState z) i 0 = cosetState ((a·z)%N) i 0`
     (compose `prepB_correct`, `gidneyInPlaceWithSwap_agree_off`, reverse-prep clear).
   - `g_badmass` : `∀z<N, bornWeightOn (cosetState z) B' ≤ 2·numWin/2^cm`
     (transport `inplaceBadSetB_evolved_bornWeight_le` through the `prepB` permutation + the register equiv).
3. **G6 factor-2 (trivial, folded into the G5 instantiation).**
   - Instantiate `inplaceReducedLookupCosetMul_shift bits (cosetAnc w bits) N cm a (2*numWin) (inplaceWorkGate …)` with `B := B'`; the two bullets above are exactly its two conjuncts.
4. **G7 glue into `ControlOracleLift` (mechanical-but-large, ~3–6 sessions).**
   - `hwork` (good-set preservation off `badY`) ⟵ from `B'` (the off-`B'` support stays in the good set).
   - `hwork_int` (matrix intertwining `M_c ∘ cosetEmbedMat = cosetEmbedMat ∘ M_i` off `bad_step`) ⟵ the
     off-`B'` coset shift IS this identity column-by-column: `∑_yp workMat y yp · cosetEmbedMat yp z =
     uc_eval g (cosetState z) y = cosetState (az) y = ∑_yp cosetEmbedMat y yp · (idealShift)_{yp z}`.
     The work here is the index bookkeeping (`workMat`/`Fin.cast`/`jointIdx`/`shorDvd`) + the
     `B' ↔ badY ↔ bad_step` correspondence (all phase-independent).
   - Feed `controlled_shifted_oracle_hc_local` / `_hintertwine` → `embedAgreeOff_oracle_step` →
     `orbit_final_embedAgree` → `coset_route2_success_conditional` becomes **unconditional**.

### Route B (the chosen path) — concrete replacements for steps 2 & 4

The probe selected Route B, so steps 2 and 4 above are replaced by their marginal variants:

- **2′. G5 marginal (the pole, ~4–8 sessions).**  Do NOT build `prepB`.  Instead inhabit
  `CosetMarginalRelabel.agree` (the frontier `CosetMarginalShorBound §4` exposes) by lifting the proven
  `gidneyInPlaceWithSwap_agree_off` (off-`B` exact a-block coset shift) + `inplaceBadSetB_evolved_bornWeight_le`
  (D5 mass) through the **phase marginal** — the b-block (coset-0 ancilla) is traced out by
  `CosetEphys.E_phys_marginal` (already proven generic).  Key sub-obligations: (i) the a-block marginal of
  `uc_eval(gidneyInPlaceWithSwap)·cosetInputVec z 0` is `cosetState ((a·z)%N)` off the bad set; (ii) the
  traced b-ancilla returns to coset-0 (separability at the end) — from the swap structure
  (`gidneyInPlaceWithSwap = …;swapAB`, output in a, b cleared); (iii) the bad mass `≤ 2·numWin/2^cm`
  transfers to the marginal via `E_phys_marginal`'s Born-mass preservation.
- **4′. Glue (marginal, ~3–6 sessions).**  Feed the inhabited `CosetMarginalRelabel.agree` into the
  marginal capstone so `coset_shor_succeeds_marginal` becomes **unconditional** (instead of routing
  through `ControlOracleLift`'s full-state `hwork`/`hwork_int`, which Route A would use).

(Route A's steps 2/4 above remain the fallback for the frozen *full-state* contract if the marginal
capstone is ever deemed insufficient.)

---

## §3½. E1 / Route B — the marginal lift (roadmap, scouted 2026-06-18)

**Endpoint.**  Inhabit `CosetMarginalShorBound.CosetMarginalRelabel a r N m n anc f_coset f_ideal ε`
— whose `agree` field is at the **`Shor_final_state` level**: `∀ x y ∉ badY x,
Shor_final_state f_coset (jointIdx x y) = Shor_final_state f_ideal (jointIdx x (σ y))` (a
data-register **σ-relabel**, NOT the per-step shift) — then `coset_shor_succeeds_marginal` gives
`P_success(coset) ≥ P_ideal − 2ε` (or the `ε=0` exact endpoint).

**Machinery that already exists (no new infra):**
- `CosetMarginalShorBound.{prob_partial_meas_basis_dataPerm_offBad, prob_of_success_dataPerm_offBad}` — marginal-invariance off a data bad set ⇒ success transfer.
- `PhaseMarginalLift.{phaseMarginal, phaseMarginal_relabel_offBad}`, `PhaseMarginalEmbed.dataLocal_marginal_transfer_offBad`, `CosetEphys.E_phys_marginal` — Born-mass-preserving marginal trace of the data factor.
- `ApproxTransfer.prob_partial_meas_basis_sub_abs_le` — per-outcome marginal ≤ ∑_y |Δ normSq|; sum over x ⇒ ≤ `normSqDist`.
- **Register bridge (PROVEN):** `ControlStageBridge.workDim_eq : (2^m·2^n·2^anc)/2^m = 2^(n+anc)`, `InPlaceCosetGate.cosetWork_dim_eq : bits + cosetAnc w bits = cosetDim w bits` (n=bits, anc=cosetAnc), `qpeStage_oracle_jointIdx`, `ControlOracleLift.workMat` (already casts via `Fin.cast workDim_eq`).

**E1 bricks (ordered):**
1. ✅ **DONE** `InPlaceCosetMarginalStep1` — trace b (`normSqDist_branchOfE_decomp` at `aBase` ⇒ the sealed `≤ 4·numWin/2^cm` is a sum over b/scratch control of per-a-register `normSqDist`s) + the target's a-projection = `betaA·cosetState((k·x)%N)` (coset shift `z↦(k·z)%N`).
2. ✅ **DONE** `InPlaceCosetMarginalStep2` — register transport. `workReindex` = `Fin.cast (cosetWork_dim_eq)` (bijection) carries the sealed deviation into `Fin(2^(bits + cosetAnc w bits)) = Fin(2^(n+anc))` (n=bits residue, anc=cosetAnc holds the b-block + scratch), constant `4·numWin/2^cm` preserved (`normSqDist_workReindex` proves cast-invariance). Audit guard `bTrace_control_is_anc : cosetDim − bits = cosetAnc` — the b-trace control factor IS the ancilla register, so b is traced as `anc`, never discarded. (Pure register cast; the `workMat` SEMANTIC oracle-matrix identity is brick 3.)
3. **Orbit lift** — AUDITED 2026-06-18 (3-agent), and the plan CORRECTED:
   - **Route mismatch found:** `ControlOracleLift` feeds the **EmbedAgreeOff / embedding** route (`coset_route2_success_conditional`), NOT `CosetMarginalRelabel` (σ-relabel). The σ-relabel route has the phase-indexed-σ / inverse-QFT obstruction `EmbedOrbitCompose` was *built to avoid* (its docstring lines 8-10). So the marginal/`CosetMarginalRelabel` target is the WRONG endpoint — the embedding route is the sound, implemented one.
   - **Accumulation:** final ε = mass of `(range numIter).biUnion bad_delta` = Σ per-step ≤ `numIter·(per-oracle wrap mass)`, NOT the local `4·numWin/2^cm`. (`h_coset_wrap`/`h_embed_wrap` require ≤ ε on the accumulated biUnion.)
   - **b=|0⟩ obstruction** on the embedding route's `cosetEmbedMat` `hwork_int` ⇒ would need `prepB` for the faithful construction.
   - **OPTION (a) PROBED → PASS.** The Route-2 success engine (`CosetRoute2Consolidated.{ApproxCosetOrbitShift, coset_route2_success_conditional}` + `EmbedOrbitCompose`) is GENUINELY GENERIC over `E_phys` (plain parameter; `cosetEmbedMat` lives only in the replaceable `ControlOracleLift` bridge). So instantiate it with the **two-register embedding** `E₂ : z ↦ cosetInputVec z 0` (b-block = cosetState 0):
     - **A3 isometry PROVEN** (`InPlaceTwoRegEmbedProbe`, axiom-clean): columns unit-norm (T1 `cosetInputVec_normalized`) + orthogonal (`cosetInputVec_support_disjoint`, via `cosetWindow_disjoint`).
     - **A5 oracle PASS:** T2 `gidneyInPlaceWithSwap_agree_off_explicit` IS the work-level off-bad intertwining for E₂ — `uc_eval(gate)·cosetInputVec z 0 = cosetInputVec ((k·z)%N) 0` off bad — **NO prepB, NO b-mismatch** (E₂'s columns ARE the faithful b=coset0 states).
     - **A4 marginal:** `hmarg` for E₂ follows from A3 orthonormality by the SAME technique as `E_phys_marginal` (moderate plumbing).
     - Remaining (small-to-moderate, plumbing not math): hmarg/`E_phys_marginal` for E₂; re-prove the `ControlOracleLift` controlled-hintertwine bridge for E₂ (its proof uses only data-locality + the matrix identity, both of which E₂ has).
4. **Instantiate `ApproxCosetOrbitShift` with E₂** — feed T2 (via the E₂ controlled-lift) as `hstep`, A4 as `hmarg`, the `numIter`-accumulated D5/T3 masses as `h_*_wrap`; conclude via `coset_route2_success_conditional` (`P_coset ≥ P_ideal − 2ε`, ε = accumulated). (Endpoint corrected from `CosetMarginalRelabel` to the embedding route `coset_route2`.)

**⚠ SOUNDNESS caveats (flagged from the scout's optimistic skeleton):**
- The EVOLVED state's a-projection is NOT a clean `cosetState` — `branchOfE_…_passA` applies only to the static `cosetInputTwoReg`.  The evolved a-register is only *bounded* against the target by G3, never an equality.  Do not claim `uc_eval(gate)·… ` projects to a `cosetState`.
- `CosetMarginalRelabel.agree` is a **σ-relabel** at the final-state level, NOT the per-step `z↦(k·z)%N`.  The per-step shift feeds the orbit lift which *produces* the σ-relabel; they are different objects (the scout conflated them).
- `cosetEmbedMat` is pinned single-register; the b-block must enter via `anc`/the register transport (brick 2), not by changing the embedding.

## §4. The strategic point (why this plan changes the cadence)

Every prior session closed one *sub-lemma* (a D-series leaf).  Steps 1–4 above are **contract-level**
units: each closes a named obligation of the frozen spec, not a fragment of one.  The genuine
conceptual remainder is **only G5** (and only its `prepB`/marginal decision); G4 and G6 are mechanical,
and G7 is large-but-mechanical glue whose mathematical content (the off-bad coset shift) is already
proven.  Do the §2 probe first — it is the single fact that decides the whole downstream shape.

---

## §5. ⛔ EmbedAgreeOff / E₂ orbit route is BLOCKED — pivot to the hybrid ℓ²-telescoping route (2026-06-19)

**H0 — the documented blocker (do NOT patch with an `hBclosed` closure hypothesis).**
The E₂ embedding route of §3 (steps 3–4: instantiate `ApproxCosetOrbitShift` via `embedAgreeOff_oracle_step`)
is **not inhabitable non-vacuously**, proven by an 8-agent investigation + independent verification:

- `embedAgreeOff_oracle_step` (`EmbedOrbitCompose.lean:104-108`) discharges the per-step via
  `hc_local actual (D ideal)` at `badY := B` (the FIRST union slot).  So
  `ControlOracleLift.controlled_shifted_oracle_hc_local`'s `hwork` (good-set preservation,
  `ControlOracleLift.lean:43-44`) MUST hold at the **incoming accumulated `B`**, which
  `ApproxCosetOrbitShift.hstep` (`CosetRoute2Consolidated.lean:86-89`) quantifies **∀ B**.
- The controlled oracle **permutes** the data index `y` (`qpeStage_oracle_jointIdx` bit-TRUE branch =
  full `Σ_yp workMat(y,yp)·ψ`; `workMat(f_coset) = uc_eval(gidneyInPlaceWithSwap) = inplaceSigma`, a basis
  permutation).  Via `uc_eval_eq_permState`, **`hwork ⟺ σ(B) ⊆ B` (forward-closure)**.
- The physical bad set is **provably NOT σ-closed**:
  `inplaceBadSetB k x = (targetSupp \ σ(goodIn)) ∪ (σ(badIn) \ targetSupp)` (`InPlaceComposedAgree.lean:303-311`).
  Take `i = σ(p)`, `p ∈ badIn`, `σ(p) ∉ targetSupp`: then `i ∈ B` but `σ(i) = σ²(p)` is in no leg of `B`.
- Aggravated: one `σ_k` per step; accumulated `B` mixes all earlier `bad_delta` ⇒ needs cross-step closure
  under every `σ_j`.  **(R-restrict)** (σ-close the bad set) is vacuous: `CosetScalingAudit` (verified,
  kernel-clean) forces ε = Ω(1) for the σ-enlarged coarsening wrap mass.

Bricks 1–2 of F2 (`E2_hwork_int`, `controlled_shifted_oracle_hintertwine_E2`) remain CORRECT — they are the
*hintertwine* half; it is the `hc_local` half that cannot be discharged on this route.

**The new route — hybrid / telescoping ℓ²-deviation (H1–H5).**  Use the genuine **ℓ² distance**
`pmDist` (`Approx/GracefulDegradation.lean`), which IS unitary-invariant (so the inverse QFT is harmless —
no phase-indexed σ).  **Do NOT use `normSqDist`** (`ApproxTransfer.lean:116`): it is the **L1-Born** distance
`∑|‖s₁ᵢ‖²−‖s₂ᵢ‖²|`, only *permutation*-invariant, useless for telescoping through the QFT.

- **H1** generic telescoping: `pmDist (U_T∘…∘U_1 Φ_0) Φ_T ≤ ∑_j pmDist (U_j Φ_{j-1}) Φ_j`
  (induction + `pmDist_triangle` + `pmDist` unitary-invariance).  No bad sets, no `hwork`, no EmbedAgreeOff.
- **H2 — ALREADY DONE:** `prob_partial_meas_diff_le_two_dist` (`GracefulDegradation.lean:84`):
  on `pmNorm ≤ 1` states, `|P(s|φ) − P(s|ψ)| ≤ 2·pmDist φ ψ`.  ℓ², constant 2.
- **H3** local controlled-step bound in `pmDist` (NOT G3's `normSqDist`): L2 analogue of
  `normSqDist_le_of_agree_off` — `pmDist²(s₁,s₂) = ∑_{i∈B} normSq(s₁ᵢ−s₂ᵢ) ≤ 2(mass₁+mass₂) ≤ 4W`
  (via `|a−b|² ≤ 2(|a|²+|b|²)`), fed by T2 amplitude agreement + D5/T3 masses `W = 2·numWin/2^cm` ⇒
  local `pmDist ≤ 2·√(2·numWin/2^cm)`.
- **H4** accumulate: `pmDist final ≤ numIter · 2√(2·numWin/2^cm)`.
- **H5** capstone `coset_route2_success_hybrid_norm_E2`: `P_actual ≥ P_ideal − 4·numIter·√(2·numWin/2^cm)`.
  Do NOT inhabit `ApproxCosetOrbitShift.hstep`.

**Consequence (honest):** the error term changes from the (unachievable) linear bad-mass
`numIter·2numWin/2^cm` to the sound square-root local-deviation `≈ 4·numIter·√(numWin/2^cm)`.  Weaker, but
sound and directly backed by what is proved (G3-style local deviation).  If the final Shor bound needs the
linear scaling, the fix is a genuinely stronger LOCAL theorem or a different probabilistic coupling — NOT
patching EmbedAgreeOff.
