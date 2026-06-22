# FormalRV.QEC.Codes — per-family END-TO-END test cases

**Charter (John, 2026-06-10).**  These folders exist to *justify the QEC-layer
design with concrete codes and concrete logical circuits carrying proofs* —
not abstractions.  Each family folder runs the SAME pipeline on a real code:

1. **Code** — built by the family constructor (`FrontendAlgebraic`), validity
   (`well_shaped`, `css_condition`) by kernel `decide`, embedded as a valid
   `StabilizerCode`.
2. **Logical operators, COMPUTED** — `LogicalFinder.logicalX/logicalZ`
   (GF(2) kernel mod rowspace), count = `k`, genuineness certified.
3. **A logical operation with proof** — the canonical X̄-measurement surgery
   gadget (`canonicalXSurgery`, the generic form of the hand-rolled demos)
   built on the *computed* logical support, passing the full decidable
   verifier `verify_surgery_gadget`.
4. **The compiled physical circuit** — the gadget's merged-code syndrome-
   extraction circuit as a syntactic `PhysCircuit` object
   (`SurgeryGadget.extractionRound`), with SEMANTICS
   (`extractionRound_measures_merged`: the circuit measures exactly the
   merged stabilizers) and composed (R)/(N)
   (`extraction_measures_readout` / `extraction_preserves_commuting`).
5. **Independent resource counts** — the tree-walk counters on the circuit
   object, tied to closed figures through the PARAMETRIC count theorems
   (`widthC_extractionRound` etc.), not by per-instance evaluation alone.
6. **Logical-cycle schedules** — parallel vs sequential composition of the
   family's operations with explicit cycle/width demand.

Each folder has TWO files:

* **`<X>Family.lean` — the ARBITRARY-parameter generator.**  `code …` is
  total in the family parameters (`Surface.code d` for any distance;
  `HGP.code h1 h2 …` for any seed matrices; `BB.code l m a b` for any block
  sizes/polynomials; `LP.code l A rA nA` for any lift/seed) and exposes the
  review/use artifacts at every parameter: `checkMatrixX/Z`, `stabilizers`
  (the detailed phased-Pauli generator list), the compiled `extractionRound`,
  and its `extractionStim` text.  The compiled-circuit SEMANTICS theorem
  `family_extraction_measures` holds at EVERY parameter, conditional only on
  the decidable `well_shaped` check (closed parametrically for LP via
  `liftedProduct_well_shaped`; per-instance `decide` elsewhere — the
  ∀-parameter CSS programmes are tracked work).  Each family discharges the
  hypothesis at TWO different parameter choices (e.g. surface d = 3 and 5,
  HGP(Hamming,rep3) and HGP(rep3,rep4), BB 3×3 and 4×2, LP l=3 and l=5).

* **`<X>Chain.lean` — the fixed-instance deep chain** (logical operators
  computed, verified X̄-surgery, composed (R)/(N), counts, cycle schedules):

| Family | Chain instance | k (computed) | X̄-surgery (phys qubits, CNOTs/round, meas/round) |
|---|---|---|---|
| Surface | `surface3` [[13,1,3]] | 1 | 28 / 45 / 14 |
| Hypergraph product | `hgp73` = HGP(Hamming[7,4], rep 3) [[27,4,·]] | 4 | 53 / 105 / 25 |
| Bivariate bicycle | `bbSmall` [[18,2,·]] | 2 | 39 / 77 / 20 |
| Lifted product | `lpTiny` [[15,3,·]] | 3 | 30 / 40 / 14 |

Cross-check: the BB gadget's 39 physical qubits independently reproduces the
Audit layer's `lpGadget_footprint = 39` (`Audit/CainXu2026/SystemZones.lean`),
derived there from the hand-built `bb_x_surgery`.

Distances are asserted inputs (paper-cited or believed), consumed only by the
`3·τ_s ≥ 2d` cycle bound — the standing distance residue.  The large-scale
corpus (surface d≥5, bb18 [[248,10,18]], lp16/20/24) stays in
`QEC/Instances.lean` with its documented `native_decide`/css residues.
