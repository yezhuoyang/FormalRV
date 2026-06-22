# FormalRV.QEC — the QEC layer (demand side)

**Charter (John, 2026-06-10).**  The QEC layer creates and verifies the
syntactic object needed for fault-tolerant Shor **assuming infinitely many
qubits**.  Every qubit here is a *virtual qubit* (a bare `Nat`); allocation is
free; there is no placement, routing, hardware mapping, wallclock time, or
system call.  The layer's outputs are *demand-side obligations* — virtual-qubit
counts (including every syndrome / surgery ancilla), gate counts, and logical-
cycle durations — and the `FormalRV.System` layer answers the supply-side
question: *can a finite machine run this demand in a given time?*

Import discipline (enforced by `scripts/check_layering.py`): no file under
`FormalRV/QEC/` imports `FormalRV.System.*`, `FormalRV.Shor.*`, or
`FormalRV.Audit.*`.

## The four pillars

1. **Low-level syntactic objects** (`Circuit/PhysCircuit.lean`,
   `Circuit/SyndromeExtraction.lean`).  A physical-operation IR
   (`prep`/`cx`/`meas` over virtual qubits) in which syndrome-extraction
   circuits are Lean objects: `CheckBlock` (prep ancilla → CNOT fan → measure),
   `Round`, and the compiler `extractionBlocks` from any CSS code's check
   matrices — including a surgery gadget's *merged* code
   (`SurgeryGadget.extractionRound` / `.extractionCircuit`, `tau_s` rounds).
   `toStim` serializes the IR to exactly what the legacy `StimEmit` emitter
   produced (pinned by `steane_extraction_stim_eq`), so emitted Stim is now a
   view of the verified object.  Syndrome ancillas, surgery ancillas, and
   (future) teleportation ancillas are explicit indices in the syntax tree —
   the overhead the top layer neglects is *in the object*.

2. **Independent resource verification** (`Resource/QECCircuitCount.lean`
   counters + `Circuit/ExtractionCount.lean` theorems).  Honest tree-walk
   counters (`widthC`, `cxCountC`, `measCountC`, `prepCountC`, `opCountC`)
   import only the IR.  Parametric count theorems close the audit gap
   "counts are defined on gadget fields with no theorem linking them to the
   emitted circuit":
   `widthC = surgeryPhysQubits g`, `cxCountC = surgeryCNOTs g`,
   `measCountC = surgeryMeasPerRound g` (per round) and `= surgeryTotalMeas g`
   (over `tau_s` rounds), plus `native_decide`-on-the-object corpus
   cross-checks (surface3: 28 qubits / 45 CNOTs / 14 measurements) and the
   `rfl` pins tying `Time/LogicalCycle` footprints to the counted widths.

3. **Low-level semantics** (`Circuit/CircuitSemantics.lean`).  Heisenberg
   interpretation of the IR (`conjOps`; per check block definitionally the
   `PPM/CliffordConj` gadgets).  **Headline:**
   `extractionRound_measures_code` — the compiled extraction round of *any*
   well-shaped CSS code measures exactly `c.toStabilizers`, parametrically
   (generalizing the [[4,2,2]] `decide` demo of `GateSyndromeWorkedExample`).
   For surgery gadgets, `extraction_implements_merge` shows running the
   compiled circuit's measured observables through the Gottesman update *is*
   the `SurgeryCorrect.measureChecks` merge — composing with
   `surgery_implements_logical_measurement(_Z)` (eigenvalue readout +
   non-disturbance) and `LogicalMeasurementGeneral` up to PPM sequences on
   logical qubits.  Gottesman–Knill faithfulness of the symplectic picture is
   the standing cited residue.

4. **Logical-cycle time** (`Time/LogicalCycle.lean`).  A cycle-valued schedule
   algebra (`op | seq | par | rep`): one logical cycle = one syndrome round; a
   surgery PPM costs `tau_s` cycles; `seq` adds, `par` takes max (well-formed
   only on disjoint virtual-qubit ranges — decidable), `rep` scales.
   Expresses *parallel PPM* and *parallel syndrome extraction* vs sequential,
   with the space/time tradeoff explicit (`widthDemand`).  Bridge:
   `seqGadgets_duration` = the legacy sequential `scheduleTotalRounds`.
   No microseconds anywhere.

## Per-family end-to-end test cases (`Codes/`)

`Codes/{Surface, HypergraphProduct, BivariateBicycle, LiftedProduct}/` run the
IDENTICAL pipeline on a concrete member of each family — validity → COMPUTED
logical operators → a verified logical-X̄ surgery built by the generic
`canonicalXSurgery` (`LatticeSurgery/XSurgeryBuilder.lean`) on the computed
logical → compiled-circuit semantics → independent counts via the parametric
theorems → cycle schedules.  Kernel-`decide` throughout, except the declared
surface d=5 validity pins in `SurfaceFamily.lean` (`native_decide`).
See `Codes/README.md` for the table (surface3 28/45/14, hgp73 53/105/25,
bbSmall 39/77/20 — independently matching the Audit layer's 39 — and
lpTiny 30/40/14).

## Code mathematics (pre-existing, now joined by general codes)

* GF(2) toolkit: `LDPCMatrix`, `GF2Linear`, `GF2Linearity`, `GF2Rank`
  (`BoolVec`/`BoolMat`, `vec_xor`, `row_combination`, `hcat`/`vcat`,
  `is_qldpc`, rank/rowspace).
* `CSSCode` (+ `syndrome_circuit_implements_code`), `CodeDimension`,
  logical operators (`Logical`, `LogicalFinder`, `LogicalValidity`,
  `LogicalGenuine`, `LogicalMeasurementGeneral`, `Addressing`).
* Code families (`FrontendAlgebraic`, `Instances`): surface (= HGP of
  repetition), hypergraph product, bivariate bicycle, lifted product, with
  the real corpus (surface3/5, bb18, lp16/20/24); `QECCodeInstances` holds the
  flat `(n,k,d)` Framework containers.
* **NEW** `StabilizerCode` — arbitrary (non-CSS) stabilizer codes over phased
  Pauli checks, with the [[5,1,3]] perfect code as the genuinely-non-CSS
  instance (`code513_valid` by kernel `decide`, `code513_not_css`).
* **NEW** `CodeBuilders` — generic `CSSCode.directSum` (block-diagonal
  two-patch code) and `CSSCode.dual`, with parametric validity preservation
  (`directSum_css_condition`, `dual_css_condition`) and matrix-level pins to
  the previously hand-rolled `surface3x2_qec` / `surface3x2_dual`.

## LatticeSurgery/ (moved here 2026-06-10)

Lattice surgery is QEC content and now lives under the QEC layer:
syntax (`LDPCSurgery.SurgeryGadget` + decidable `verify_surgery_gadget`),
semantics (`SurgeryReadout`/`SurgeryCorrect`: code-general, axiom-free
eigenvalue readout (R) + non-disturbance (N); `SurgeryReduction` /
`SurgerySchedule`: operational reduction), magic injection
(`MagicInjectionSurgery`: teleportCCX as three merges), the verified corpus
(`SurgeryDemo{Surface,Merge,CNOT,Steane}` — load-bearing despite the names),
resource counts (`SurfaceShorResourceCount` Parts A/B), schedule capstone
(`SurfaceShorFullStack`), and the emitters (`StimEmit`, `ScheduleEmit`).

**Moved OUT to `FormalRV/System/`** (supply side — SysCalls, µs wallclock,
hardware): `LatticeSurgeryPPMContract`, `SurgeryGadgetToSysCalls`,
`SurfaceSystemCompile`, `SurfaceShorFullSchedule`.
**Moved to `FormalRV/Shor/PPM/`**: `SurfaceShorPPMEndToEnd` (conjoins
Shor-level results — belongs above both layers).

## Honest residues (tracked)

* **Transitive System reach**: `MagicInjectionSurgery` imports
  `PPM.CircuitToPPMToffoliMagic`, and parts of `PPM/` still import
  `FormalRV.System` (e.g. `PPM.PauliOps`); the *direct*-import boundary is
  enforced, the PPM-side cleanup is future work.
* **Namespace debt**: many moved files keep `FormalRV.Framework.*` /
  `FormalRV.LatticeSurgery.*` namespaces (≠ paths).  Identifiers were kept
  stable on purpose; a namespace unification is a separate mechanical pass.
* `SurfaceShorResourceCount` Part C (Hardware-parametric Shor-scale estimate)
  still lives here and imports `Framework.CostModel`; splitting it to the
  estimate layer is pending.
* Parallel-slot semantic interchange (par ≡ any sequential order at the
  stabilizer level) awaits the parametric commutation-preservation laws that
  `PPMOperational` lists as open; `par` currently has duration/footprint
  accounting + decidable well-formedness.
* General-Pauli (non-CSS) extraction blocks need basis-change gates in the IR;
  the compiler covers the CSS fragment (which is what surgery uses).
* The IR has no measurement-OUTCOME semantics yet, so the `signs` argument of
  the (R) readout identity (`extraction_measures_readout`) is not bound to
  the circuit's measurement records; full-round Heisenberg interchange across
  blocks (which holds exactly under the merged CSS condition) is likewise
  unformalized — the per-block segmentation is documented in
  `Circuit/CircuitSemantics.lean`.
* The row-length hypotheses of `widthC_extractionRound` /
  `extractionRound_measures_merged` are discharged per-instance; deriving
  them once from `SurgeryGadget.dimensions_consistent` is pending.
* Parametric Stim string-equality of `toStim` vs the legacy emitter is pinned
  instance-level (Steane) — the parametric string identity is plumbing-only.
* Pre-existing residues unchanged: LP `css_condition` at scale
  (`LPCssCondition` programme), code distance never formalized, merged-code
  distance as implementer-supplied input, `decide`-pinned GF(2) rank.

`sorry`/`axiom` count in this folder: **zero** (`native_decide` where the
corpus already used it; new corpus checks use kernel `decide` except the
28-qubit counter evaluations and the Stim string pin).
