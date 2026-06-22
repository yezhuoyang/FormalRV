# Resource — the separate, independent resource-counting system

A resource count must be an **honest tree-walk over a syntactic object** and
nothing else. Everything in this folder imports **only the circuit IRs**
(`Core.Gate`, `Core.QuantumGate`, and the QEC physical-circuit leaf IR
`QEC.Circuit.PhysCircuit` — the exact allowlist is enforced by
`scripts/check_layering.py` R3) — never the gadget constructors, never the
correctness proofs. Because the counters live in their own world, a resource
theorem `countT (gadget n) = 14·n` **cannot fudge the count**: the number is
forced by the syntax tree, and a skeptic can `#eval` the counter on a constructed
circuit to check it *without reading any proof*.

## The verification shape this enforces

Every verified resource claim carries a **triple**:

1. a concrete **syntactic object** (or a generator that builds it),
2. a proof it is **semantically correct** against the spec, and
3. a proof that **these counters, applied to that same object, equal the closed form**.

No formula like `3n` is ever asserted without a real object behind it. Item (3) —
the per-gadget count theorem — lives *with its gadget* (e.g.
`Arithmetic/Cuccaro/CuccaroAdderResource.lean`, `QFT/IQFTResource.lean`); this
folder owns the **counters** they use.

## Time and Space

Resources come in two kinds, and the folder counts both:

- **Time** — gate counts (`countT`, `countCNOT`, `gateCount`/`gateCountU`) and
  sequential `depth`. How long the circuit runs.
- **Space** — the qubit count / register width (`width`/`widthU`). How many
  qubits the circuit needs.

## Contents

| File | Time counters | Space counter | IR |
|---|---|---|---|
| `GateCount.lean` | `countT`, `countCNOT`, `countToffoli`, `countX`, `gateCount`, `depth` | `width` | reversible `Gate` (I/X/CX/CCX) |
| `UComCount.lean` | `gateCountU`, `cnotCountU`, `oneQCountU` | `widthU` | unitary `BaseUCom` (H/Rz/CNOT/SWAP…) |
| `QECCircuitCount.lean` | `cxCountC`, `measCountC`, `prepCountC`, `opCountC` | `widthC` | QEC physical circuit `PhysCircuit` (prep/CX/meas; syndrome+surgery ancillas explicit) |
| `Interface.lean` | `HasResourceCount` typeclass: `cnot`, `gates` (time), `qubits` (space) | | unifies the IRs |

`GateCount` bridges to the legacy `Gate.tcount`/`gcount` (`countT_eq_tcount`,
etc.), so the existing arithmetic resource theorems are already statements about
these canonical counters. `UComCount` **closes a real gap**: before it,
`BaseUCom` (the QFT/QPE IR) had *no* gate counter — its "resource" was only an
`IsCliffordT` predicate and a real-valued error budget, neither of which is a
count.

## Third-party testability (the whole point)

A skeptic who distrusts the proofs constructs the object and runs the counter:

```lean
#eval countT (cuccaro_n_bit_adder_full 5 0)      -- 70   (= 14 × 5, no proof read)
#eval countToffoli (cuccaro_n_bit_adder_full 5 0)
```

and the anchored theorem ties that walk to the closed form on the SAME object:

```lean
example (n : Nat) : countT (cuccaro_n_bit_adder_full n 0) = 14 * n := by
  rw [countT_eq_tcount]; exact cuccaro_adder_tcount n 0
```

See `Examples.lean` (off the default build path) for the worked triple.

## Migration status (this folder is being grown)

**Done:**
- The canonical `Gate` and `BaseUCom` counters + the unified Time/Space interface.
- `UComCombinators.lean` — count laws for the core combinators: `SWAP` (3 CNOT),
  `CCX` (9 + 6), `controlled_R` (4 + 2), the general `control` law
  (`1q ↦ 4·1q + 9·CNOT`, `CNOT ↦ 2·1q + 6·CNOT`), `npar` (sums), `npar_H`.
- **QFT/QPE closed forms, fully closed** (`QFT/IQFTCount.lean`,
  `QPE/QPECount.lean`): `cnotCountU (IQFT n) = 3·⌊n/2⌋ + n·(n−1)`,
  `widthU (IQFT n) = n` (no hidden ancilla), and QPE's count decomposed over a
  black-box oracle — proven by induction over the circuits' own loop recursions,
  bundled with semantic correctness (`iqft_verified_with_resources`,
  `qpe_verified_with_resources`). Cross-checked by `#eval`-counting the emitted
  QASM text (n = 0..8) with no proofs.

- **QEC extraction-circuit counts, theorem-tied** (`QECCircuitCount.lean` +
  `QEC/Circuit/ExtractionCount.lean`): the legacy lattice-surgery gadget-field
  counters (`surgeryPhysQubits`/`surgeryCNOTs`/`surgeryMeasPerRound`/
  `surgeryTotalMeas`) are now proven equal to these tree-walk counters on the
  compiled syndrome-extraction circuit object.

**Next (tracked in the resource-architecture audit):**
- Re-home the PPM measurement/magic-T counters (`ppmProgramResourceSummary`,
  `numMeas`) and the system `CostModel` under this folder behind the
  `HasResourceCount`-style interface.
- Retire/fence the few asserted figures (Gidney 7n measurement-uncompute; the
  paper-sourced top-level Toffoli count) so every number has an object behind it.
