# FormalRV Refactor Plan

> Synthesized from a 20-agent read-only analysis (16 per-unit surveys + a cross-cut pass), a
> real full-build timing run (461/8798 modules recompiled), and targeted spot-verification of the
> highest-leverage claims. PLAN ONLY — no `.lean` file has been edited, moved, or deleted, and no
> build was run while producing this document.

## Hard constraints (apply to EVERY action below)

1. **Headlines stay kernel-clean.** After each step, the changed module's headline theorems must keep
   `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`. Zero `sorry`. Zero new custom axioms.
2. **Proven re-export-shim split pattern only.** Heavy `X.lean` → `X/` submodules that re-declare the
   **same namespace + same `open`s** + a thin import-only `X.lean` shim. Importers must remain byte-for-byte
   unchanged. This pattern is already used across the repo (Adder, ObliviousRunwayAdder, ModExpAt*).
3. **Never delete re-export shims or intentional codegen/`#eval` emitters.** Only true `*/Example.lean`
   and `*Demo.lean` *pure demos* (0 real decls, off the default build path, not imported) are deletion
   candidates — and only after confirming no live import (several flagged "safe" files are in fact imported;
   see §3).
4. **Single-threaded execution, one build at a time.** Concurrent `lake build`s crash the machine.
   `LEAN_NUM_THREADS=2`. Verify kernel-clean after each step. Kill stuck builds with PowerShell
   `Stop-Process`, never `taskkill /F`.

## Reconciliation notes (where the data disagreed)

- **native_decide count.** The cross-cut agent claimed "977 occurrences across 197 files." A direct
  spot-check of the working tree finds **~342 real `native_decide` tactic occurrences across ~325 files**
  (the 977 figure counted comment/docstring mentions, of which there are many — every "no native_decide"
  banner). **Trust the per-unit real-code counts**, which sum to ~340 (table in §2). GidneyInPlace, the
  Arithmetic adder units, and the PauliRotation/NumberTheory/Resource/Codegen/Verifier unit genuinely have
  **0** real `native_decide`; the apparent hits there are all docstrings.
- **`CircuitSizingStub.lean` is NOT safe to delete as-is.** The survey said "not imported by shim." Verified
  false: it is imported by `FormalRV/Shor/VerifiedShor/CanonicalBitWidth.lean` **and**
  `FormalRV/Shor/VerifiedShor.lean`. It has 0 real decls (only stale duplicate `open`s). → confirm-then-delete,
  and remove the two `import` lines as part of the same step.
- **`MeasUncomputeExec.lean` is NOT safe to delete.** The survey said "delete if no cross-unit import."
  Verified it IS imported by `WindowedComposed.lean`, `VerifiedWorkloadBridge.lean`, and
  `WindowedEmitDemo.lean`. → keep the file; only its 5 `native_decide` demo `example`s are in scope (and they
  are not headline-load-bearing). Do not delete.
- "NO ACTION" findings (intentional parallel proof legs, intentional precondition patterns, intentional
  parametric variants) are dropped from the action lists below and only noted where a reviewer might otherwise
  re-flag them.

---

## 0. Executive summary — top ~12 actions ranked by (impact / effort / risk)

Goals legend: **G1** faster compile · **G2** reusable/reviewable/short files · **G3** dedup · **G4** remove
unused · **G5** factor redundant proofs · **G6** remove native_decide.

| # | Action | Goal(s) | Impact | Effort | Risk |
|---|--------|---------|--------|--------|------|
| 1 | **Tame the 91s outlier `Arithmetic/UnaryLookup/UnaryLookupIterationCorrectness.lean`**: split into `Core` + `DecideExamples`, move all 20 `native_decide` examples out, fix the 2 large ones via the existing `tcount_unary_lookup_multi_iteration` closed-form lemma | G1,G2,G6 | **Very high** (single biggest build cost, 3.5× next) | Med | Low |
| 2 | Split `UnaryLookupGateDerivations.lean` (1277 L) → `Core` + `ConcreteSmoke` (43 decide examples) | G1,G2 | High | Low | Low |
| 3 | Remove `native_decide` from the **System/** unit (~161 real, mostly small finite-schedule `decide`/`omega`) | G6,G1 | High (largest single native_decide cluster) | Med | Low–Med |
| 4 | Delete the **confirmed-pure** demo files (4 Arithmetic `*Example.lean` + 3 ModularAdder `Example.lean` + 3 Gidney21 `*Demo.lean`); confirm-then-delete the rest | G4,G2 | Med | Low | Low |
| 5 | Split `Core/UnitarySem.lean` (1877 L) → Foundations/KroneckerOps/GateMatrices | G1,G2 | High (Core bottleneck, deep dependency fan-in) | Med | Med |
| 6 | Remove `native_decide` from **QEC/LatticeSurgery** fixed-size gadget specs (~110 of 240, low-risk → `decide`/structural `simp`) | G6 | High (largest QEC cluster) | Med–High | Low–Med |
| 7 | Factor `fin2`/`fin_cases` matrix-entry boilerplate into shared `Core/PauliMatrixLaws.lean` (132 instances; 42 in UnitarySem alone) | G5,G1,G2 | High | Med | Med |
| 8 | Split `WindowedShorConnection.lean` (1392 L) → Interface/Windowed/Instances (used by 10+ files) | G1,G2 | Med–High | Med | Low |
| 9 | Split `Arithmetic/Windowed/WindowedModN.lean` (1494 L, 21s) → per-§ submodules | G1,G2 | High | Med | Low |
| 10 | Dedup high-severity cross-cut clusters: `tcount_unary_lookup_*`, `tcount_foldl_seq_const`, `relabelGate` lemmas, `mul_pow_mod_one`, masked-read T-count | G3,G2 | Med | Low–Med | Low |
| 11 | Decouple imports: `FormalRV.Audit.lean` + per-paper shims so an audit no longer pulls all 17 top-level folders (one audit currently drags 8798 modules transitively) | G1,G2 | High (build fan-out) | Med | Med |
| 12 | Split the two PPM monoliths `CircuitFragmentClassifierAndCompiler.lean` (1488 L) + `SurgeryGadgetLoweringAndQECInstance.lean` (1445 L); isolate the 1 remaining hard PPM `native_decide` | G1,G2,G6 | Med–High | Med–High | Med (the 1 trace `native_decide` is genuinely hard) |

**Headline totals:** ~342 real `native_decide` to remove; of those **~6 are Hard** (1 PPM toy-trace match at
high risk; 2 large UnaryLookup multi-iteration counts; 2 Pinnacle L3_PPM 72-qubit code facts; ~1 Gidney21
class). **~10 files to delete** (pure demos) + **2 confirm-then-delete-with-import-removal**. **~50+ oversized
files to split** (>700 lines; ~30 are >1000). **Biggest structural moves:** (a) flatten the Audit import graph
so papers don't transitively pull the whole library; (b) group the 61 loose `Shor/` files into
Core/Multipliers/Windowed/Measured subfolders behind shims; (c) reorganize `QEC/LatticeSurgery` into
WidthScaling/ + CliffordFrame/ + Codegen/ + Demo/ subfolders.

---

## 1. Compilation speed

### 1a. The 91s outlier — `FormalRV/Arithmetic/UnaryLookup/UnaryLookupIterationCorrectness.lean`

**Confirmed**: 1276 lines, **20 real `native_decide`** tactic uses (verified by grep). It is the single biggest
build cost in the repo at 91s — 3.5× the next module (26s).

**Why it is slow.** `native_decide` compiles the goal to native code and runs it; each invocation pays a
compiler + runtime startup cost, and two of them run genuinely large computations:
- line 1243: `tcount (unary_lookup_multi_iteration 6 (List.replicate 64 ([],[]))) = 5376` — a 2^6 × … expansion;
- line 1274: the RSA-2048 instantiation, also hitting a 64-iteration count.
The other 17 are tiny finite Bool-function checks (`iter_triggers`, `effective_addr`, `address_and`, all on
`n_addr = 3`) at lines 691–939, but each still triggers a native-codegen round-trip. None of the 20 are
headline-load-bearing — they are auditor smoke tests; **grep confirms no other file references them.**

**Concrete fix (combines G1 + G6 + G2):**
1. Split via the re-export shim into `UnaryLookupIterationCorrectness/Core.lean` (the 29 parametric semantic
   theorems, fast, no `native_decide`) and `UnaryLookupIterationCorrectness/DecideExamples.lean` (the 23
   example blocks). Shim `UnaryLookupIterationCorrectness.lean` re-exports both.
2. In `DecideExamples.lean`, replace the **17 small** `native_decide` with `by decide` (kernel-cheap on
   `n_addr=3` Bool functions).
3. For the **2 large** ones (5376 / RSA-2048): rewrite using the already-proven closed-form
   `tcount_unary_lookup_multi_iteration` lemma (`rw [tcount_unary_lookup_multi_iteration]; norm_num`/`decide`)
   instead of brute native evaluation. This is the structural-lemma path, not native compute.
4. Heavy downstream users (e.g. `WindowedComposed`, anything counting T) then import only `Core`.

**Expected savings:** this is the dominant recompile cost; moving the native examples out of the default proof
path and replacing brute-force counts with the closed-form lemma should take this module from ~91s toward the
20s band (most of the 91s is the native examples, not the parametric proofs). The single highest-ROI action in
the repo.

### 1b. The 20–26s cluster — split the oversized files that dominate it

The recompiled-module timings line up almost 1:1 with oversized files. Splitting each (re-export shim) lets the
submodules compile in parallel on a future multi-core run and, more importantly here (single-threaded), shrinks
the *incremental* recompile when you touch one section. Highest-value, ordered by (build time × size):

| Module (build s) | File (lines) | Split target |
|---|---|---|
| 21 | `Arithmetic/Windowed/WindowedModN.lean` (1494) | per-§ (Helpers/CompareConst/RegCompareXor/CondSub/Reduction/LookupAddStep/StepInvariant/StepFold/Correctness/ToffoliCount) |
| 22 | `Arithmetic/ModularAdder/Gidney/GidneyModAddReg` + Cuccaro `CuccaroDirtyFlagStageCorrectness.lean` (1418) | 4 submodules by Tick range |
| 26/20 | `Shor/GidneyInPlace/Capstone/RunwayPrep{Done,Full,Core}.lean` (660/633/787) | Prep/ subfolder per §-section |
| 23 | `Shor/MeasuredWindowedModN.lean` (842) | Setup + ProofTheoremBlock |
| 22 | `Shor/GidneyInPlace/Deviation/Proof/E2ResidueEmbed.lean` (890) | 5 Embed/* submodules per § |
| 22 | `Audit/GidneyEkera2021/ModExpAt{SameObjectWeld,ReductionWeld}.lean` | Reduction/ subfolder |
| 21 | `Shor/VerifiedShor/WindowedCaseUnifiedStateEq.lean` (1587) | Core (case-2) + Case1Noop |
| 21 | `Shor/GidneyRunwayMul`, `Shor/MeasuredBabbushRead`, `Shor/EGateToUnitaryBridge` | 2 submodules each (Setup/Proof) |
| 20 | `Shor/WindowedComposedAt`, `VerifiedShor/ModExpWelded`, `GidneyTCount` | 2 submodules each |
| 20 | `Audit/GidneyEkera2021/{ModExpAtReductionDirect(1084),ModExpAtUnmul(820),InPlaceMulData(At)}` | per-§ subfolders |

### 1c. Expensive-tactic files (independent of size)

The redundant-proof patterns in §5 are also the compile-time hogs:
- **`Core/UnitarySem.lean`** — 42 `ext … <;> fin_cases i <;> fin_cases j <;> simp` matrix-entry expansions.
  Factoring into `matrix_ext_fin2` / `PauliMatrixLaws` (see §5) cuts both lines and elaboration time.
- **System/** schedule checks — `native_decide` on finite `List SysCall`; switching to `decide`/`omega`
  removes the native-codegen round-trip entirely (§2, §3 of the System unit estimate 20–40% on System rebuilds).
- **QEC/LatticeSurgery** — 240 `native_decide`; converting the fixed-size gadget specs to `decide`/structural
  `simp` removes native round-trips (§2).

### 1d. Oversized-file splits that ALSO cut build time

Splitting helps incremental builds most where the file is both large AND on a hot dependency path:
`Core/UnitarySem.lean` (1877, fan-in to all of Core/QFT/QPE/Shor), `QPE/PhaseKickback.lean` (1642),
`QFT/IQFTCircuitCorrectness.lean` (1311), `Core/PadAction/PadAction{Composite,GateEntry}.lean` (1285/1256),
`Shor/WindowedShorConnection.lean` (1392, 10+ importers), `Arithmetic/Windowed/WindowedModN.lean` (1494).
The two LP basis-import data files (§6) are large but **not** worth splitting (data, not proofs).

---

## 2. native_decide removal (ALL)

Total real tactic occurrences ≈ **342** across ~325 files (verified working-tree count; the cross-cut "977"
double-counts docstrings). Grouped by per-unit real counts (the reliable signal):

| File / cluster | count | removal approach | risk |
|---|---|---|---|
| **EASY — replace with `decide`/`omega`** ||||
| `System/Invariants/SystemInvariantStrengthening.lean` | 36 | `decide` (small finite schedules) | low |
| `System/Compile/PPMContractInstances.lean` | 37 | `decide`; fallback `rfl` on precomputed Bool | low |
| `System/Compile/SurgeryGadgetToSysCalls.lean` | 18 | `decide`; let-bind expanded schedule then `decide` | low–med |
| `System/Compile/CompressedSchedule.lean` | 18 | `decide`; fallback `@[simp]` precompute + `rfl` | med |
| `System/Artifacts/CompressedRepeat/AdderRegressions.lean` | 30 | split conjuncts `<;> decide` | med |
| `System/Compile/QECScheduleToSystem.lean` | 8 | `decide` | low |
| `System/Params/HardwareCatalog.lean` | 13 | `decide`/`omega` | low |
| `System/Examples/AdderSystem.lean` | 12 | `decide`; precompute `rfl` lemmas | low |
| `System/Checkers/SystemChecker.lean` | 9 | `decide` | low |
| `System/Bounds/{ScheduleLowerBound,ScheduleAdvance,HardwareSensitivity,NaiveSchedule}` | 5+6+4+1 | `omega` (pure Nat arithmetic) | low |
| `System/Magic/{MagicStateReadiness,MagicScheduleComplete}` | 6+2 | `omega` | low |
| `System/Compose/VerifiedWorkloadBridge.lean` | 6 | `omega` | low |
| `System/DeviceLane/RoutingResourceModel`, `System/Artifacts/LayeredArtifactCore` | 3+3 | `decide` | low |
| `Arithmetic/UnaryLookup/UnaryLookupIterationCorrectness.lean` (17 small) | 17 | `decide` after moving to `DecideExamples` | low |
| `Shor/MeasUncomputeExec.lean` (in-place; file stays — it IS imported) | 5 | `decide` (tiny 3-qubit QROM) | low |
| `Shor/WindowedShorPPMFactoryE2E.lean` | 1 | `decide`; fallback `factoryRequestSchedule_concrete` `rfl` lemma | med |
| `Audit/CainXu2026/L4_Code.lean` | 2 | `decide` (144-elt list, trivial) | low |
| **MEDIUM — structural / precompute** ||||
| `QEC/LatticeSurgery` fixed-size gadget specs (`GenuineMixedY` 23, `BasisChangeComposition` 17, `Routing` 16, `GenuineRotation` 12, `WidthScalingXMerge` 9, `WidthScalingYMeasure` 6, `WidthScalingYChain` 6, `EndToEndCert` 7, `CrossLayerHetero` 7, `ProgramAssembly` 6, …) | ~110 | precompute each property as a `@[simp]`/structural lemma, then `simp`/`rfl`; for width-symbolic certs apply the per-column locality technique already proven in WidthScaling | low–med |
| `QEC/LatticeSurgery/WidthScalingStep2b.lean` | 14 | per-layer structural lemmas at seam k∈{2,3} (this is Step2b's explicit goal) | low |
| `QEC/LatticeSurgery/MixedMergeGen.lean` | 17 | named helper def + structural proof; only risky if many `(s,h,N)` tuples | med |
| `QEC/Gidney21/ColorEnforcing.lean` | 11 | consolidate into 1 partition lemma (`gadgetKinds_faithful_partition` + one proof) — see §5 | low |
| `Arithmetic/UnaryLookup/UnaryLookupIterationCorrectness.lean` (2 large) | 2 | rewrite via `tcount_unary_lookup_multi_iteration` closed form | med |
| `Audit/GidneyEkera2021/{SystemZones(6),Verifier(5)}` | 11 | arithmetic-only; try `decide`/`omega`; or relocate to off-default `*Arithmetic.lean` and keep the honest ➗ label | low |
| **HARD — big-computation / genuine residue** ||||
| `PPM/Compiler/SurgeryGadgetLoweringAndQECInstance.lean:1414` (toy trace-match) | 1 | factor the `SurgeryGadgetTrace` match into smaller decidable lemmas; `decide` will likely time out otherwise. **Only PPM native_decide.** | high |
| `Audit/Pinnacle/L3_PPM.lean` (72-qubit `numLogicals` + `valid`) | 2 | structural code facts; keep honest ➗ label OR move to off-default `L3_PPMDerived.lean` (mirrors `CainXu2026.CodeKDerived`) | med |
| `Audit/CainXu2026/CodeKDerived.lean` (GF(2) rank on 248/4350-qubit codes) | 2 | **KEEP** — already off the default build path; genuine expensive arithmetic residue, intentionally gated | low (accept) |
| `QEC/Gidney21/GadgetToLaS.lean` (LaSCorrectFull surface certs) | 23 | the per-unit agent argues KEEP (kernel-clean, unavoidable surface enumeration, <100ms each). **Decision: treat as Hard/accept** unless G6 is absolute — re-proving needs ~500 hand lemmas with no correctness gain | accept/high |
| Remaining `QEC/LogicalLayout` "bridge certificate" `native_decide` (Bridge 6, Threader 3, Compiler 4, StimDriver 3, FrameComplete 4, CompileReport 2), `QEC/Instances` 3, `QEC/Circuit/SyndromeExtraction` 1 | ~26 | these are the documented "prove-once-reuse-parametrically" certificate design and large-code residues; convert to `decide` where the code is small, otherwise keep honest-labeled | low–med |

**Honest read on G6 (remove ALL):** the easy + medium buckets (~230) are genuinely removable. The hard bucket
(~6 distinct sites + the GadgetToLaS/GE2021-surface and large-code-rank families) are either (a) genuine
big-computation facts where `decide` will time out the kernel, or (b) the QEC certificate design that is
deliberately `native_decide`. For (a)/(b), the achievable "kernel-clean" interpretation is: relocate them to
explicitly off-default `*Derived.lean` targets (so the default build is native_decide-free) and keep them
honestly labeled, rather than fabricating fragile structural proofs. Flag this trade-off for the user before
spending effort on GadgetToLaS.

---

## 3. Dead & unused code

### 3a. Delete now (verified pure demos — 0 real decls, off default build, not imported)

Spot-verified that these match the "true demo" criteria. Delete the file (rm, not relabel):

- `FormalRV/Arithmetic/ModMult/ModMultExample.lean` (1 def gadget + #eval/QASM emit; core lives in `ModMultResource.lean`)
- `FormalRV/Arithmetic/Windowed/Example.lean` (0 theorem/def, only `report` helper + #eval)
- `FormalRV/Arithmetic/ModExp/ModExpExample.lean` (worked-instance demos; core in `ModExpCorrectness.lean`)
- `FormalRV/Arithmetic/ModularAdder/Cuccaro/Example.lean` (only #check + #eval)
- `FormalRV/Arithmetic/ModularAdder/Gidney/Example.lean` (only #check + #eval)
- `FormalRV/Arithmetic/ModularAdder/GidneySubtractFixup/Example.lean` (only #check/example/#eval)
- `FormalRV/QEC/Gidney21/CuccaroAdderDemo.lean` (audit-checklist demo; grep-confirmed not imported)
- `FormalRV/QEC/Gidney21/ModMultDemo.lean` (ditto)
- `FormalRV/QEC/Gidney21/ShorBlockDemo.lean` (ditto)

Before each rm, run `grep -rln "<ModuleName>"` to reconfirm zero importers (the criterion that already holds).

### 3b. Confirm-then-delete (delete requires also removing live imports)

- **`FormalRV/Shor/VerifiedShor/CircuitSizingStub.lean`** — 0 real decls (only stale duplicate `open`s).
  **It IS imported** by `CanonicalBitWidth.lean` and `VerifiedShor.lean` (survey claim of "not imported by
  shim" is wrong). Delete the file AND remove those two `import FormalRV.Shor.VerifiedShor.CircuitSizingStub`
  lines, then rebuild `VerifiedShor` to confirm nothing relied on its `open`s.
- `FormalRV/Arithmetic/Windowed/WindowedCircuitExec.lean` — 1 def + 3 `native_decide` examples, "off the
  routine build." Confirm no importer, then delete (its parametric core is in `WindowedCircuitCorrect.lean`).
- `FormalRV/Audit/Xu2024/Verifier.lean` — 8 lines, 1 bare `example` (cycle-time ratio), 0 verified decls.
  Confirm role (CI sanity vs orphan); if orphan, delete or fold the constant into the parent shim.
- `FormalRV/Shor/QEC/LatticeSurgery/SurgeryDemo{CNOT,Merge,Steane,Surface}.lean` — concrete small-case
  verification demos (15/18/11/14 decls). Not referenced by the verified pipeline per the unit survey. Confirm,
  then either delete or move to `QEC/LatticeSurgery/Demo/`. (These DO contain real `theorem`s, so they are
  "demo verification," not strictly 0-decl; prefer move-to-Demo over delete to preserve the regression value.)

### 3c. Standalone `example`/`#eval` blocks inside otherwise-real files

- `Shor/PhaseLookupFixup.lean` lines ~625–647 (2 smoke-check `example`s) — delete the blocks, keep the §7 header.
- `Shor/SplitPhaseFixup.lean` §8 (~935–977) — inspect; delete if `example`-only.
- `UnaryLookup/UnaryLookupIterationCorrectness.lean` lines 828/871/875/883/888 — 5 `decide`/`native_decide`
  witnesses fully subsumed by the parametric `effective_addr_testBit` / `iter_triggers` theorems; move to
  `DecideExamples` (do not keep in `Core`).
- `Core/QEC/LatticeSurgery/SurgeryCorrect.lean` lines 622 & 1168 — 2 `example` proof sketches; delete if diagnostic-only.

### 3d. KEEP (explicitly NOT dead — do not touch)

Intentional codegen/`#eval` emitters and worked examples that carry real theorems:
`QFT/IQFTExample.lean`, `QPE/QPEExample.lean` (headline `iqft_emitted_unitary_eq_IQFT_matrix` chain),
`Phaseup/Example.lean`, `MeasuredAdder/Example.lean`, `RippleCarryAdder/RippleCarryAdderExample.lean`
(verify QASM-pipeline use first), `Codegen/{WindowedEmitDemo,SysCallEmitDemo}.lean`,
`Resource/Examples.lean`, `PauliRotation/Examples.lean`, `System/Examples/{AdderSystem,CostModelWeightDemo,
ParallelismVerification}.lean`, and **`Shor/MeasUncomputeExec.lean`** (it IS imported by 3 files — keep file,
only soften its 5 `native_decide` to `decide`). All `*/Codegen.lean`, `PPMToQASM.lean`, and the dozens of
PPM/Shor/Arithmetic re-export shims are load-bearing — never delete.

### 3e. Unused-decl candidates (low-confidence — VERIFY references before deleting)

The cross-cut "unused" pass used `grep -rw`, which misses `open`/projection/`@[simp]` uses. Treat ALL as
"verify-then-delete," not safe deletes:
- **High-confidence-but-verify (gate algebra identities, defined-only):** in
  `Core/PadAction/PadActionComposite.lean` (`SDAG_S_eq_id`, `SDAG_Z_eq_S`, `S_SDAG_eq_id`, `S_Z_eq_SDAG`,
  `X_X_X_eq_X`, `Y_Y_Y_eq_Y`, `Z_Z_Z_eq_Z`, `exp_neg_pi4_pow_four`), `PadActionGateEntry.lean`
  (`T_S_eq_S_T`, `T_SDAG_eq_SDAG_T`, `TDAG_S_eq_S_TDAG`, `TDAG_SDAG_eq_SDAG_TDAG`),
  `CCXToffoliComplete.lean` (`H_H_eq_one`, `Z_Z_eq_one`, `H_H_H_H_H_eq_H`, `S_S_S_S_S_eq_S`),
  `Arithmetic/Correctness.lean` (`gate_ccx_acts_on_basis_symm`, `gate_cx_cx_id_on_basis`,
  `gate_x_x_id_on_basis`), `Cuccaro/Cuccaro.lean` (`gcount_assoc_right_iter`, `tcount_assoc_right_iter`).
  These read like "documentation/regression" gate-law lemmas. **Caveat: may be intentional public API / sanity
  lemmas.** Decision rule: delete only those with literally one reference (the definition) AND not `@[simp]`
  AND not re-exported; otherwise keep. Low total LOC; low priority vs §1.
- **Medium-confidence:** `flipBit_ne`, `ne_iff_eq_flipBit` (PadActionGateEntry) — trivial helpers; verify.
- `LP20BasisFullCert.lean` flagged "0 external refs" — **do NOT delete**; it is the thin kernel-verification
  cert shim for generated data (§6). Its job is to be the `decide` proof, not to be imported.

---

## 4. Duplicate code → canonical home + dedup action

### 4a. High-severity genuine duplicates (act)

| Cluster | Canonical home | Action |
|---|---|---|
| `tcount_unary_lookup_iteration`, `tcount_unary_lookup_multi_iteration` (defined in both `UnaryLookup/UnaryLookupGateDerivations.lean` and `Arithmetic/Windowed/WindowedCircuit.lean`) | `UnaryLookup/UnaryLookupGateDerivations.lean` | move/keep canonical there, `import` + re-export from WindowedCircuit (and any Shor user) |
| `tcount_foldl_seq_const` (`Arithmetic/Windowed/WindowedCircuit.lean` & `Shor/WindowedComposed.lean`) | `Arithmetic/Windowed/WindowedCircuit.lean` | re-export from `Shor/WindowedComposed.lean` |
| `tcount_relabelGate`, `wellTyped_relabelGate_src` (`Audit/GidneyEkera2021/DivModNAt.lean` & `InPlaceMulDataAt.lean`) | new `Audit/GidneyEkera2021/RelabelGateShared.lean` | extract once, import in both |
| `tcount_sqir_prepareMaskedConstRead` (`Arithmetic/ModMult/Internal/ToffoliCount.lean` & `Audit/Gidney2025/EkeraHastadOracleGate.lean`) | `ModMult/Internal/ToffoliCount.lean` (more general) | instantiate in the audit file; unify param names |
| `mul_pow_mod_one` (`ModExp/ModExpCorrectness.lean` & `Windowed/WindowedExpInPlaceQ.lean`) | `ModExp/ModExpCorrectness.lean` | import in WindowedExpInPlaceQ |

### 4b. Medium-severity (act, low risk — name collisions / small lemma copies)

- `runAnc_clean_of_scratchClean'` (RunwayPrepFull & RunwayPrepSubBlock) → new
  `Shor/GidneyInPlace/Capstone/RunwayPrepShared.lean`.
- `perm_cast_apply` (E2RunwaySynthRunwayGate & RunwayPrepCore) → new
  `Shor/GidneyInPlace/Capstone/RunwayUtilities.lean`.
- `extendBool_inplaceAccInput` (InPlaceComposedBranch & InPlaceStepAction) → new
  `Shor/GidneyInPlace/InPlace/Proof/InPlaceInputShared.lean` (use the more general InPlaceStepAction signature).
- `wellTyped_mono` (RunwayAdderFunctional/WellTyped & E2RunwayDivider) — narrow versions; rename the
  E2RunwayDivider one `wellTyped_mono_gidneyInPlace` to stop shadowing (or hoist a general one to Core).
- `aReg`/`bReg` name collision (`ProductAddLayout.lean` Nat-valued vs `E2RunwaySynthRunwayGate`/`RunwayPrepFull`
  List-valued) — rename the Nat versions `aRegIdx`/`bRegIdx` to remove the shadow.

### 4c. The parallel "E2*Canonical vs E2*" variants — KEEP BOTH, extract shared utilities

`Deviation/Proof/E2ResidueEmbed.lean` (890 L) vs `Capstone/E2ResidueEmbedCanonical.lean` (333 L) are
**intentional proof variants** (Route A general vs Route B′ canonical with weakened `hf_residue` →
`hf_res_can` + `hf_res_pres` for constructible implementations). This is the deliberate "weaken ∀k to ∀k<m"
bridge already recorded in project memory. **Do not merge.** Instead: extract the shared utility lemmas
(`E2residueData_marginal`, `qpeStageMap_qftinv_indep`, `qstate_ext_jointIdx`) into a shared import consumed by
both, and add a header comment documenting the dual-route relationship.

### 4d. The `Audit/GidneyEkera2021/ModExpAt*` variants (8 files) — KEEP, but reorganize

`FullOutput, LayoutAdapterInstance, ReductionBound, ReductionDirect, ReductionWeld, ResidueInstance,
SameObjectWeld, Unmul` form a deliberate proof cascade with distinct reduction routes; project memory shows
each closes a real seam (ReductionDirect = direct discharge, Unmul = UnmulSpecRfree discharge, etc.). They are
**not duplicative** of each other. Recommendation: regroup under `Audit/GidneyEkera2021/ModExpAt/` (§6) and add
a one-paragraph header in the parent shim mapping each file to its route, so a reviewer can tell which are live
vs which (if any) are superseded. Only after that map exists should anyone propose removing a route — and only
if it has zero downstream importers.

---

## 5. Redundant proofs → shared lemmas

| Pattern | ~#sites | Proposed shared lemma (name + sketch) | Where it lives |
|---|---|---|---|
| `ext i j <;> fin_cases i <;> fin_cases j <;> simp` matrix-entry equality | **132** (42 in UnitarySem, 24 PadActionGateEntry, 13 PadActionComposite, 23 across Core/CliffordTRotations/GateDecompositions/UnitaryOps) | `matrix_ext_fin2 (M N : Matrix (Fin 2) (Fin 2) ℂ) (h : ∀ i j, M i j = N i j) : M = N` + per-pair specializations (`σx_mul_σz`, …) wrapping the `fin_cases` automation | new `Core/PauliMatrixLaws.lean` |
| `pad_u` basis-entry triple-equality + `by_cases` block | 10+ (PadActionGateEntry 112–217, 364–399) | `pad_u_basis_match_three_way … : pad_u dim n M … = if (rH=cH ∧ rM=cM ∧ rL=cL) then M rM cM else 0` (entry formula + triple-eq iff in one) | `Core/PadAction/PadActionDefinitions.lean` |
| basis-state lift via `funbool_to_nat`/`padEquiv` | 6+ (PhaseKickback, Gate/Spec/UCEvalBridge) | `basis_f_to_vec_via_equiv (dim) (i) : ∃ φ, i.val = funbool_to_nat dim (extendBool dim φ) ∧ basis_vector … = f_to_vec …` | `Shor/GidneyInPlace/Gate/Spec/UCEvalBridge.lean` (BasisEquivLaws section) |
| permutation `cast`/`Fin.val` injectivity in embedding proofs | 35+ files (Embedding/Deviation/Ideal) | `fin_equiv_val_injective (e : Fin (2^n) ≃ T) : Injective (fun x => (e x).val)` + `permState_injective_on_support` | new `Shor/GidneyInPlace/Embedding/Def/PermEmbedLaws.lean` |
| `uc_eval` bridge: basis agreement → linearity → isometry | 5+ (UCEvalBridge, PhaseKickback, ControlledGates) | `uc_eval_bridge_abstract (U) (basis_action : ∀ i, U·bv i = bv (σ i)) (σ : Perm) : ∀ s, U·s = permState σ.symm s` | new `Shor/GidneyInPlace/Gate/Spec/UCEvalLiftingLaws.lean` |
| `List.countP` invariant lift + range split (PauliRotation) | 10+ (CommBridge 82–222) | `list_countP_invariant_lift (h_eq : ∀ a∈l, p a = q a) : l.countP p = l.countP q` + `countP_range_bounded_index` | `PauliRotation/Semantics/CommBridge.lean` (ListCountPLaws section) |
| `Fin 2` case exhaustion for Pauli projections (`proj0_apply`, `σx_apply`, …) | 10+ (PauliRotation/Semantics + Core/PadAction) | `@[simp] proj0_apply_dec (i j) : proj0 i j = decide (i=0 ∧ j=0)` + Decidable wrappers | `Core/PadAction/PadActionGateEntry.lean` (Fin2DecidableLaws) |
| WidthScaling per-layer `funcCubeOK`, parity-k1, all-or-none (QEC) | 5 files (zMerge/xMerge/yIdle/yMeasure/Hetero) | `perLayerFuncCubeOK_template`, `parity_k1_zero_when_NO_JK_seam`, `allOrNone_k1_const_when_seam` | new `QEC/LatticeSurgery/WidthScaling/GenericLayers.lean` |
| Phase-fold collapse / seam equalities / idle gadget (QEC) | SurgeryCorrect + Weld + Step2b + Hetero + YChain | `foldl_phase_neutral`; shared `SeamEqualities.lean`; shared `IdleGadget.lean` | `QEC/LatticeSurgery/SurgeryCorrect/PhaseAlgebra.lean`, `WidthScaling/{SeamEqualities,IdleGadget}.lean` |
| GE2021 placed-gate `applyNat`/`frame`/`tcount`/`wellTyped` + state-witness s1–s5 | ~6 ModExpAt/InPlace files | `applyNat_on_disjoint_bands`, `wellTyped_relabel_frame`, `Gate.tcount_seq_fold`, `StateWitness.prove_state_evolution` | new `Audit/GidneyEkera2021/Utilities/{PlacedGateLemmas,CopyBand,StateWitness,Tcount}.lean` |
| Gidney21 gadget-faithful checks | 11 (ColorEnforcing) | `gadgetKinds_faithful_partition` + one batch proof (also removes 10 native_decide — see §2) | `QEC/Gidney21/ColorEnforcing.lean` |
| `arithmetic_simp` set + `omega_simp` macro | 59+ files | named `@[simp]` set + tactic macro for the `simp only […]; omega` idiom | new `Framework/TacticHelpers.lean` |

**Explicitly NOT to "dedup"** (intentional, would hurt clarity): the two InPlace deviation legs
(forward/reverse), the `cases a<;>cases b<;>cases c<;>rfl` 8-case carry idiom, the per-step frame lemmas in
RippleCarry (touched positions differ), the `sortedStrict ∧ width ≤ n` precondition pattern in PauliRotation,
the 17-line `open` boilerplate (Lean hygiene requires each file to stand alone — at most extract a documented
prelude, not a shared `open`), and the gadget-specific `LaSCorrectFull` surface certs.

---

## 6. Structure & naming

### 6a. Folder/file reorganizations (each behind re-export shims; importers unchanged)

- **`Shor/` (61 loose files).** Group into `Shor/Core/` (Main, PostQFT, MainAlgorithm, VerifiedShor),
  `Shor/Multipliers/` (Gidney*, ~20), `Shor/Windowed/` (Windowed*, ~16), `Shor/Measured/` (Meas*/Measured*, ~15);
  keep existing subfolders (Approx/, CFS/, GidneyInPlace/, OrderFinding/, PPM/, Resource/). Add `Shor/Core.lean`,
  `Shor/Multipliers.lean`, `Shor/Windowed.lean`, `Shor/Measured.lean` shims; shrink `Shor.lean` from ~95 lines /
  46 explicit imports to ~20 by importing the shims. (Highest-value structural move after the Audit decoupling.)
- **Missing aggregator shims.** Create `Shor/OrderFinding.lean` and `Shor/RunwayWindowed.lean` (both folders
  have submodules but no umbrella, breaking the Approx/PostQFT pattern; StandardShor currently imports
  submodules directly).
- **`QEC/LatticeSurgery/`.** Reorganize into `WidthScaling/` (Base → Step1 → Step2 → Step2b → Variants/{XMerge,
  YChain,YMeasure,Hetero}), `CliffordFrame/` (Rotation, MixedMerge, MixedMergeGen, YMeasure),
  `Codegen/` (SceneExport, StimEmit, ScheduleEmit — emission, not verified), `Demo/` (the 4 SurgeryDemo*).
- **`QEC/Gidney21/`.** Split `GadgetToLaS.lean` (1009) into a ~350-line surface-convention anchor +
  `Gadgets/{MixedMerge,Rotations,Readouts}.lean`. Move the 3 demo files to `Audits/` (or delete per §3a).
  Rename `Common.lean` → `Catalog.lean` (it is a module catalog, exports 0 decls).
- **`QEC/` root.** Move infrastructure (BasisCodec, CodeBuilders, BlockAddressing, Addressing, CodeDimension,
  CSSCode, GF2*) into `QEC/Infrastructure/`; instances (Instances, SmallCodeValidity, QECCodeInstances,
  LPInstancesValid) into `QEC/Instances/`.
- **`Audit/GidneyEkera2021/`.** Create `ModExpAt/`, `InPlace/`, `Utilities/` subfolders (§4d, §5). Consolidate
  the four tiny layer files into one `Layers.lean` with `L1/L2/L3/L4` sections (each currently 7–43 lines of
  shim+docs).
- **`Core/`.** Split the four giants (UnitarySem, UnitaryOps, PadActionComposite, PadActionGateEntry) per §1d;
  add docstrings to `Semantics.lean`/`DensitySem.lean`/`NDSem.lean` clarifying scope vs UnitarySem; rename or
  merge `IQFTDefinitions.lean` ("Def" vs "Definitions" ambiguity).
- **`PPM/Magic/`, `PPM/Rules/`, `PPM/Semantics/`.** Subfolder by concern (Interface/Teleport/Factory;
  GateLevel/PPMLevel/Synthesis/ZXCalculus; Core/Bridges/Operational). Lower priority — clarity only.
- **`System/`.** Move `CompressedRepeat/`→`Artifacts/Repeat/`, `LayeredArtifact*`→`Artifacts/Layered/`; split
  `Examples/` into `Working/` (AdderSystem, CostModelWeightDemo) vs `Demos/`. Clarify Bounds/ vs Invariants/
  via README/docstrings.

### 6b. The LP*BasisImport "data vs code" question

`Codes/LiftedProduct/LP20BasisImport.lean` (2488) and `LP16BasisImport.lean` (1528) are the two largest files
but are **generated hex-encoded GF(2)-solver output, NOT code** — do not split (splitting corrupts the in-kernel
`bitsToVec` codec / `LogicalBasis.valid` cert). Their thin `*BasisFullCert.lean` (~22 lines, one `decide`) is
the proof shim. Action: add a `Codes/GENERATED_DATA.md` (and a one-line header banner) documenting they are
regenerated by `scripts/find_logicals.py` and must not be hand-edited; if build time ever dominates, the only
legitimate move is a binary blob + codec (out of scope now). **Keep the `*FullCert.lean` files** even though
grep shows "0 importers" — being the standalone cert IS their purpose.

### 6c. Import coupling — why one audit pulls 8798 modules

The cross-cut coupling pass found the root cause: `FormalRV.Audit` (and transitively `FormalRV.lean`) imports
all 17 top-level folders, so importing one paper drags Core + QFT + QPE + NumberTheory + Resource + Codegen +
PPM (77) + QEC (159) + System (55), regardless of need. Concrete decoupling (highest structural ROI, do in
Phase E with care):
1. **`FormalRV.Audit.lean` → thin shim** importing only Framework + Shor + Qualtran + Verifier; push
   paper-specific heavy imports (System for GE2021, NumberTheory for Xu2024) into each paper's own `.lean`.
2. **`GidneyEkera2021.lean` → thin shim** importing only the 8 layer files + EndToEnd + Verifier +
   WorkloadAssembly; **drop `GidneyEkera2021.Codegen`** from it (move that #eval-only file to an `Example/`
   route — it pulls Codegen + PPM + QEC + SurgeryDemoSurface purely for demos).
3. **`System.lean` → core shim + focused sub-umbrellas** (`System.HardwareBudget` = Params+Decoder+Magic;
   `System.Core.Reexports` = Architecture+CodedLayout). Then `SystemZones`/`Verifier` import the focused
   umbrella, cutting transitive count from 55 to ~10–12.
4. Break the **Shor → System → Invariants** cycle: `WindowedShorPPMFactoryE2E` imports the heavy
   `System.Invariants.ScheduleInvariantsExplicit`; extract a Lean-only signature shim it can import instead.
5. **Flatten `Framework.L2_Gadgets`/`L3_PPM`** (L2 importing L3 is an inverted, low-value indirection); fold
   the two re-export `abbrev`s into `L1_Algorithm` and delete the middle layers, or document the 4-layer
   contract in `Framework/README.md`.
6. Consider moving the whole `Codegen/` folder to `Example/Codegen/` and dropping it from `FormalRV.lean`
   (it is #eval emitters, removes a 236-file transitive pull for audit-only users). Lower priority; verify no
   theorem depends on a Codegen decl first.

### 6d. God-modules / over-importing aggregators

- `FormalRV.lean` imports 17 folders wholesale — fine as the everything-umbrella, but should NOT be on the
  transitive path of a single-paper audit (see 6c).
- `PPM/Compiler/CircuitFragmentClassifierAndCompiler.lean` (1488, 17 §) and
  `SurgeryGadgetLoweringAndQECInstance.lean` (1445) are the PPM god-modules — split per §1/§12.

---

## 7. Sequenced execution roadmap

> Run one `lake build <module>` at a time, single-threaded (`LEAN_NUM_THREADS=2`). After every step:
> `#print axioms <headline>` must show ⊆ {propext, Classical.choice, Quot.sound}, and the module's
> diagnostics must be sorry-free. Rollback = `git checkout -- <touched paths>` (each step is a small,
> self-contained git commit so rollback is a single revert).

### Phase A — delete safe dead/demo code  *(LOW risk)*
Order: (1) the 9 verified pure demos in §3a (grep-confirm zero importers immediately before each rm);
(2) confirm-then-delete in §3b — `CircuitSizingStub.lean` **with** removal of its 2 imports, then
`WindowedCircuitExec.lean`, `Xu2024/Verifier.lean`; (3) the inline `example`/`#eval` blocks in §3c.
**Checkpoint:** build each touched parent module + its umbrella; `#print axioms` on the umbrella's headline.
**Rollback:** revert the commit; demos carry no proof dependencies so blast radius is nil.

### Phase B — remove native_decide  *(LOW→MED risk)*
Order by risk bucket from §2: (B1) all System/ Easy `decide`/`omega` (~150) — biggest, safest cluster, do
file-by-file; (B2) UnaryLookup small 17 + MeasUncomputeExec 5 + misc Easy; (B3) QEC fixed-size gadget specs to
`decide`/structural simp (~110) + ColorEnforcing partition lemma; (B4) the 2 large UnaryLookup counts via the
closed-form lemma + WidthScalingStep2b structural; (B5) decide the Hard set (PPM trace, Pinnacle L3,
GadgetToLaS) — for these, prefer relocate-to-off-default + honest label over fragile rewrites, and **get user
sign-off** before investing in GadgetToLaS. **Checkpoint after EACH file:** rebuild + `#print axioms`
(`decide` keeps axioms clean; confirm `Lean.ofReduceBool` disappears where you removed native_decide).
**Rollback:** per-file commits; if `decide` times out, revert that one file and reclassify to MED/Hard.

### Phase C — dedup + factor redundant proofs  *(MED risk)*
Order: (C1) §4a high-severity duplicates (move to canonical + re-export) — pure relocation, low risk;
(C2) §4b name-collision renames; (C3) the §5 shared lemmas, starting with `matrix_ext_fin2`/`PauliMatrixLaws`
(also a compile-time win) then the GE2021 `Utilities/*`, then WidthScaling `GenericLayers`/`IdleGadget`/
`SeamEqualities`, then the permutation/uc_eval lifting laws; (C4) extract shared E2Residue utilities (keep both
variant files). **Checkpoint:** after each extraction, rebuild every consumer named in the cluster +
`#print axioms` on their headlines (a refactored lemma must not introduce an axiom). **Rollback:** each shared
lemma is one commit; if a consumer breaks, revert and leave the duplicate in place.

### Phase D — file-splits  *(LOW→MED risk; mechanical but voluminous)*
Order by impact (§1): (D1) the 91s outlier UnaryLookupIterationCorrectness (overlaps Phase B — do its split
first to host the moved examples); (D2) UnaryLookupGateDerivations; (D3) Core/UnitarySem then the PadAction
giants and PhaseKickback/IQFTCircuitCorrectness; (D4) WindowedShorConnection, WindowedModN, the Cuccaro/Gidney
ModularAdder 1400-line files, the GidneyInPlace Capstone/Deviation giants; (D5) PPM
CircuitFragmentClassifier + SurgeryGadgetLowering; (D6) remaining >700-line files. Each split = create `X/`
submodules (same namespace + opens, verbatim bodies) + thin import-only `X.lean` shim. **Checkpoint:** build
the shim (proves submodules + re-export compile) and one downstream importer; `#print axioms` on the headline
that lived in the original file. **Rollback:** delete the `X/` folder, restore original `X.lean` from git
(importers never changed, so rollback is local).

### Phase E — structure/naming  *(HIGH risk — broad import surface)*
Order: (E1) create missing aggregator shims (OrderFinding, RunwayWindowed) — additive, low risk;
(E2) folder reorganizations behind shims (Shor/ grouping, QEC/LatticeSurgery, Gidney21, GidneyEkera2021,
QEC root) one folder at a time; (E3) the import-decoupling in §6c (Audit shim, System sub-umbrellas, break the
Shor→System cycle, flatten Framework L2/L3, optionally relocate Codegen). E3 is the highest-risk because it
changes what transitively compiles. **Checkpoint:** after EACH folder/shim change, run a FULL `lake build`
(single-threaded) — this is the only phase where a partial build can hide a broken transitive import — and
re-`#print axioms` the top-level audit headlines. **Rollback:** revert the folder's commit; because every move
is shim-backed, importers are unchanged and rollback restores the prior layout cleanly.

**Risk summary:** A LOW · B LOW→MED · C MED · D LOW→MED · E HIGH. Do A→B→C→D→E; never overlap builds.

---

## Appendix — per-unit findings index

- **Shor/GidneyInPlace** (122 files): split E2RunwaySynthSwap (1143), E2RunwayDivider (993), E2ResidueEmbed
  (890), RunwayPrep{Core,Full,Done}; reorganize Capstone into Synth/ + Prep/. **0 real native_decide** (all
  docstring banners). Register-helper "duplication" is intentional re-export — NO ACTION.
- **Shor/VerifiedShor + CFS** (54): split WindowedCaseUnifiedStateEq (1587), WindowedLoaderBitExtraction
  (1516), ToyWindow2Case3StateEquality (1499), ToyWindow2CaseNoOpHelper (1492), WindowedSwapLoaderWithDataClear
  (1466), WindowedMultiplyAddSpecification (1430); extract ToyWindow2/ArithmeticBase; delete CircuitSizingStub
  (confirm-then-delete + remove 2 imports); add VerifiedShor docstring.
- **Shor/MainAlgorithm+OrderFinding+PostQFT+Approx+RunwayWindowed** (50): split OrderFinding/Eigenstate (1138)
  into 6; split RunwayMulCorrect (793) into 4; create missing OrderFinding.lean + RunwayWindowed.lean shims.
  No dead code / native_decide / duplication found.
- **Shor/loose+PPM+Resource+StandardShor** (67): split WindowedShorConnection (1392), SplitPhaseFixup (977),
  WindowedModNShor (863), MeasuredWindowedModN (842), +6 more; remove 6 native_decide (MeasUncomputeExec 5,
  WindowedShorPPMFactoryE2E 1); group the 61 loose files into Shims/Verified/Measured/Windowed; extract
  FramePreservation / MeasUncomputePattern / GrayWalkCore.
- **Arithmetic/RippleCarry+Adder+ObliviousRunway** (33): split Adder/Gidney.lean (709) → GidneyShift + shim;
  monitor PropagationInvariantBackbone (605) / ReverseFramesAndHeadline (545); **native_decide count = 0**
  (docstrings only); frame duplication is intentional. Verify RippleCarryAdderExample QASM use before deleting.
- **Arithmetic/ModMult+Windowed+ModExp** (46): split WindowedModN (1494, 12 §), WindowedExpInPlaceQ (1227),
  WindowedExpStep (933); delete ModMultExample, Windowed/Example, WindowedCircuitExec, ModExpExample (4 demos);
  rename ModMult/Internal → Core; defer the compareConst/condSub/regCompare general-state extraction.
- **Arithmetic/ModularAdder + Cuccaro** (30): split CuccaroCleanModularAddCorrectness (1424),
  CuccaroDirtyFlagStageCorrectness (1418), CuccaroControlledModularAddCorrectness (1206), Gidney/
  ControlledPipeline (1433), ForwardFaithfulness (1432), PowerOfTwoCase (1419) by Tick range; delete 3
  Example.lean demos; extract compareConst_frame_theorem + cuccaro_input_F bundle; **native_decide = 0**.
- **Arithmetic/UnaryLookup+Phaseup+MeasuredAdder+loose** (15): **the 91s file** — split
  UnaryLookupIterationCorrectness (1180, 20 native_decide) into Core + DecideExamples and remove all 20;
  split UnaryLookupGateDerivations (1277, 43 decide examples) into Core + ConcreteSmoke; split MeasuredAdderDef
  (737); Phaseup/MeasuredAdder Example.lean native_decide are docstring-only.
- **QEC/LatticeSurgery** (54): **240 native_decide** — largest cluster; ~110 low-risk fixed-gadget →
  decide/simp, WidthScalingStep2b 14 structural, MixedMergeGen 17 med. Split SurgeryCorrect (1173) +
  6 WidthScaling files; reorganize into WidthScaling/ + CliffordFrame/ + Codegen/ + Demo/; extract
  GenericLayers/SeamEqualities/IdleGadget/PhaseAlgebra; move/clarify 4 SurgeryDemo* files.
- **QEC/Gidney21+Codes** (53): the two LP basis-import data files (2488/1528) are GENERATED — do not split,
  document. Split GadgetToLaS (1009) into anchor + Gadgets/. Delete 3 *Demo.lean. Consolidate ColorEnforcing 11
  native_decide → 1 partition lemma. GadgetToLaS 23 native_decide = accept/Hard (surface certs). Rename
  Common.lean → Catalog.lean.
- **QEC/LogicalLayout+Circuit+Cultivation+Time+loose** (52): split CircuitSemantics (535), PhysicalCompile
  (420); the LogicalLayout Bridge/Threader/Compiler/StimDriver native_decide (~22) are the intentional
  "prove-once-reuse" certificate design — convert where small, else keep honest-labeled; extract
  blockBuilder_length; reorganize QEC/ root (Infrastructure/ + Instances/). Cultivation/ is exemplary — leave.
- **Audit (all 105 files)** (105): split ModExpAtReductionDirect (1084), ModExpAtUnmul (820),
  Gidney2025/ToffoliReproduction (770), +4 more into per-§ subfolders; **88 native_decide** mostly
  arithmetic-only/honest — relocate SystemZones/Verifier (11) + Pinnacle L3_PPM (2) to off-default targets,
  keep CodeKDerived (2) as-is; extract CopyBand + PlacedGateLemmas + StateWitness; keep the 8 ModExpAt routes,
  add a route map.
- **PPM/all** (77): split CircuitFragmentClassifierAndCompiler (1488), SurgeryGadgetLoweringAndQECInstance
  (1445), Syntax/Core (1420), Semantics/LogicalState (1222), Magic/CircuitToPPMMagicFactory (983),
  EnrichedPPMStateAndIntegration (878); **only 1 native_decide** (line 1414 trace-match, HARD); consolidate
  Pauli smoke-tests into Syntax/Examples; extract PauliCommutativity + StabilizerGroup; many shims (keep all).
- **System/all** (55, 17497 lines): **~161 native_decide** (mostly small finite schedules) → decide/omega for
  a projected 20–40% System rebuild speedup; split FreshnessSoundness (1231), SystemInvariantStrengthening
  (1067), SurgeryGadgetToSysCalls (1165), Core/Architecture (1026), Params/HardwareCatalog (761); extract
  CheckBundleHelpers + wallclock_derived_is_correct; clarify Bounds vs Invariants, Working vs Demo examples.
- **Core+Framework+QFT+QPE** (50): split UnitarySem (1877), UnitaryOps (1112), PadActionComposite (1285),
  PadActionGateEntry (1256), PhaseKickback (1642), IQFTCircuitCorrectness (1311); **0 native_decide**; extract
  ComplexPhase + SpecialAngles + PauliMatrixLaws (132 fin_cases sites); rename IQFTDefinitions; the unused gate
  identities (§3e) live here — verify before deleting.
- **PauliRotation+NumberTheory+Resource+Codegen+Verifier+Qualtran** (37): **0 native_decide anywhere** (fully
  compliant); split only DeviceProgramParse (458) into Parse + Backend; SchedulerK/ToPPM/Induction fine as-is;
  precondition pattern is shallow (not real duplication); Verifier/Qualtran structure is clean. Lowest-debt unit.
