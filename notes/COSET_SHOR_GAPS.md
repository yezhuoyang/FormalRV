# Coset-based Shor — proof-gap tracker (autoresearch loop)

**Mission:** discharge the remaining gaps to a kernel-clean, UNCONDITIONAL coset-Shor
semantic-correctness theorem. Faithful formalization, ZERO cheating (see the no-cheating
gate in the loop command + `memory/faithful-formalization-methodology.md`).

**Frozen anchors (NEVER edit to ease discharge):**
- `inplaceReducedLookupCosetMul_shift` — `FormalRV/Shor/CosetEigenstate/InPlaceCosetSpec.lean:71`
- Top capstones: `coset_route2_success_conditional` (CosetRoute2Consolidated.lean:111),
  `coset_shor_succeeds_marginal` / `coset_shor_succeeds_exact` (CosetMarginalShorBound.lean)

**SUCCESS =** a top success theorem holds with its frontier hypothesis DISCHARGED, and
`lean_verify` shows axioms ⊆ {propext, Classical.choice, Quot.sound}.

**No-cheating gate (every "DONE" must pass ALL):** no sorry/admit/native_decide/new
axiom/unsafe; `lean_verify` axioms ⊆ {propext,Classical.choice,Quot.sound}; diagnostics
clean; statement not weakened (non-vacuity checked with a concrete witness); proven on the
REAL frozen object; targeted `lake build` green; adversarial recheck passed; frozen
statements untouched.

---

## Gap status (critical-path order)

| # | Gap | Status | File(s) | Notes |
|---|-----|--------|---------|-------|
| G1 | Two-register in-place norm bound ≤ 4·numWin/2^cm | ✅ DONE | InPlaceCosetNormBound | `gidneyTwoRegInPlace_coset_norm_bound`, kernel-clean, frozen+audited |
| G2 | Structured agree-off (∃B, off-bad pointwise =) | ✅ DONE | InPlaceComposedAgree | `gidneyInPlaceWithSwap_agree_off` |
| G3a | Born-mass forward leg ≤ numWin/2^cm | ✅ DONE | InPlaceForwardCount | `inplaceBfwd_bornWeight_le` (D2.1) |
| G3b | Born-mass reverse leg (Brev\Bfwd) ≤ numWin/2^cm | ✅ DONE | InPlaceReverseCount | `inplaceBrevSdiff_bornWeight_le` (D3) |
| **G3c** | **Born-mass UNION: bornWeightOn (cosetInputVec x 0) inplaceBadIn ≤ 2·numWin/2^cm** | 🟡 **NEXT (D4)** | new InPlaceUnionMass or ReverseCount | via `inplaceBadIn_eq_union` + `bornWeightOn_union_le` + G3a + G3b |
| G3d | Target-mass leg: bornWeightOn (cosetInputVec ((k·x)%N) 0) inplaceBadSetB ≤ 2·numWin/2^cm | 🔴 OPEN | (symmetric to G3a–c) | needed by `normSqDist_le_of_agree_off` hw₂ |
| G4 | Register iso Fin(2^cosetDim) ≅ Fin(2^(n+anc)) | 🔴 OPEN | InPlaceCosetGate §5 obl. (a) | PLAN-ONLY first iteration |
| G5 | Two-reg→single-reg reduction + lift cosetInputTwoReg → cosetState through uc_eval | 🔴 OPEN (longest pole) | InPlaceCosetGate §5 obl. (c) | PLAN-ONLY first iteration |
| G6 | Factor-2 reconciliation (numWin := 2·numWin) | 🔴 OPEN (mechanical) | contract instantiation | fold into G5 |
| G7 | GLUE: contract → ControlOracleLift → discharge ApproxCosetOrbitShift | 🔴 OPEN | ControlOracleLift, lemma-5 glue | scaffold built, not fed |
| G8 | Marginal `agree` lift through the QPE orbit | 🔴 OPEN | CosetMarginalShorBound §4 | frontier is sound/satisfiable, not inhabited |

## Blockers
(none yet)

## Iteration log
(appended per iteration)
