# FormalRV.PPM

The Pauli-product-measurement (PPM) layer of FormalRV. It builds the Pauli
algebra from first principles, the Gottesman stabilizer-update semantics of a
single PPM, a compiler lowering the arithmetic `Gate` IR into PPM programs, an
honest magic-state-factory / Gidney measurement-AND model, and a matrix-level
stabilizer-PVM / logical-state model. The layer sits *above* the QEC/backend
SysCall layer and *below* the logical-circuit arithmetic correctness layer; it
deliberately does not model decoders, code distance, or fault tolerance.

## Layout
- `PauliSemantics.lean` — first-principle decidable Pauli algebra (`Pauli`, `Phase`, multiplication, commutation) over n-qubit strings.
- `PPM.lean` / `PauliOps.lean` — `PauliString` group ops, symplectic form, commutation lemmas; logical-operator declarations + syntactic measurement verifier.
- `PPMOperational.lean` — `StabilizerState` + the Gottesman PPM update (`apply_PPM_pos/neg`) with post-condition theorems.
- `LogicalState.lean` — `Pauli.toMatrix`/`PauliString.toMatrix`, stabilizer projector idempotence/orthogonality/resolution, pointwise-commutation ⇒ matrix-commutation.
- `CircuitToPPMInterface/Part1..7.lean` (+ umbrella `.lean`) — the arithmetic `Gate → PPMProgram` compiler and semantic-model interface.
- `CircuitToPPMSemanticBridge.lean` — refines compiled PPM runs to `Gate.applyNat` Boolean correctness; transfers decoder postconditions down.
- `CircuitToPPMObservationBridge.lean` — honest computational-basis reference model closing the ICX-fragment refinement with no external assumption.
- `CircuitToPPMMagicFactory.lean` / `FactoryHierarchy.lean` — abstract T-factory contracts, magic tokens, atomic-factory vs 8T-to-CCZ specs.
- `CircuitToPPMToffoliMagic.lean` — extended IR with a `teleportCCX` magic primitive (success-branch contract for Toffoli).
- `CircuitToPPMFactoryProvision.lean` — provisioning + executability: a provisioned magic pool lets the compiled program run to completion.
- `GidneyAND.lean` — Gidney measurement-based logical-AND (forward CCX, measurement-uncompute reverse).
- `LayeredPPMQECInterface.lean` / `GE2021PPMSysInv.lean` — layering interface to the backend; a concrete 16-SysCall PPM block with derived resource numbers.

## Key definitions
- `Pauli`, `Phase`, `Pauli.mul` (`PauliSemantics.lean`, `PPM.lean`) — single-qubit Pauli group with `{±1,±i}` phase tracking.
- `PauliString` + `commutes` (`PPM.lean`) — n-qubit Paulis; commute iff anticommuting positions are even.
- `StabilizerState`, `apply_PPM_pos/neg` (`PPMOperational.lean`) — stabilizer generators and the Gottesman measurement update.
- `Pauli.toMatrix` / `PauliString.toMatrix` (`LogicalState.lean`) — complex-matrix interpretation via Kronecker product.
- `PPMCommand`/`PPMProgram` and the `Gate → PPMProgram` compiler (`CircuitToPPMInterface/`) — the lowering target.
- `TFactoryContract`, `MagicToken`, `MagicPPMCommand.teleportCCX` (`...MagicFactory.lean`, `...ToffoliMagic.lean`) — factory + Toffoli-teleportation interfaces.
- `GidneyAND_forward`, `GidneyAND_reverse` (`GidneyAND.lean`) — the measurement-AND construction.

## Key theorems
- `PPM_preserves_validity_*`, `PPM_Z*_on_*` (`PPMOperational.lean`) — Gottesman update preserves generator commutation / gives stated outcome on concrete states — **Verified** (concrete instances, `decide`).
- `PauliString.toMatrix_projector_resolution`, `..._orthogonality`, `..._mul_self` (`LogicalState.lean`) — stabilizer ±1 projectors resolve identity, are orthogonal, and `P²=I` at matrix level — **Verified**.
- `PauliString.toMatrix_comm_of_pointwise` (`LogicalState.lean`) — pointwise Pauli commutation implies matrix commutation — **Verified**.
- `magicCompile_executable` / `compileToMagicPPM_run_observe` (`...FactoryProvision.lean`) — a sufficiently provisioned pool yields a successful run that observes `Gate.applyNat g` — **Verified** (modulo the `teleportCCX` contract).
- `shor_arithmetic_applyNat_correctness_transfers_to_PPM` (`...SemanticBridge.lean`) — `Gate.applyNat` arithmetic postconditions transfer to the compiled PPM run — **Verified** for the ICX fragment; **Axiom** for CCX (exposed as `MagicInjectionObligations.CCX_ok` / `teleportCCXRel` contract, not proved).
- `GidneyAND_reverse_tcount_eq_zero`, `tcount_GidneyAND_forward = 7` (`GidneyAND.lean`) — measurement reverse costs 0 Toffolis; forward costs 7 T — **Arithmetic-only** (no measurement-semantics equivalence proof yet).

## Status
The Pauli algebra, the Gottesman PPM update on concrete states, and the matrix-level stabilizer-projector / commutation facts are **Verified** and `sorry`-free. The circuit-to-PPM compiler is **Verified** semantically for the ICX (Clifford-X/CX) fragment; Toffoli/CCZ magic injection is **Scaffolded** behind an explicitly named contract (`teleportCCXRel` / `CCX_ok`) that is assumed, not proved. Physical distillation, gate-teleportation circuits, the Gidney-AND measurement equivalence, QEC, and decoders are out of scope and remain unmodelled.

## PPM visualization gallery

Every PPM diagram in this README is rendered (Qiskit / matplotlib) from a program
**emitted by the verified Lean** — in the Litinski lattice-surgery style: qubit wires,
joint Pauli measurements as colour-coded box columns (`Z` green) joined by a bar,
magic-T injections purple, deferred `X`-frames dashed, and a classical record lane of
blue `mₖ` outcome bits.

| Diagram | Shows |
|---|---|
| [`ppm_rules`](../../docs/diagrams/ppm_rules.png) | the two rewrite rules — commuting measurements reorder; measuring an anticommuting Pauli replaces the stabilizer (Gottesman) |
| [`ppm_cx`](../../docs/diagrams/ppm_cx.png) | `CX` → joint `ZZ` measurement + `X`-frame, with outcome bit `m₀` on the record lane |
| [`ppm_ccx`](../../docs/diagrams/ppm_ccx.png) | `CCX` → magic-T inject + joint `ZZZ` + `X`-frame |
| [`ppm_seq`](../../docs/diagrams/ppm_seq.png) | `seq` → programs concatenate; records `m₀, m₁` |
| [`ppm_adder3`](../../docs/diagrams/ppm_adder3.png) | full PPM program of the verified 3-bit Cuccaro adder — 42 commands, 6 magic-T |
| [`ppm_modmult`](../../docs/diagrams/ppm_modmult.png) | full PPM program of `x ↦ 7x mod 15` — 248 commands, 32 magic-T, folded |

Reproduce: `lake env lean --run scripts/EmitPPMQASM.lean` (T/CCZ gadgets) ·
`lake env lean --run scripts/EmitAdderPPM.lean` (adder + multiplier PPM programs) ·
`python PyCircuits/draw_ppm.py` (all PPM diagrams above).

## Worked example — the T gate by magic-state teleportation

![T-gadget teleportation](../../docs/diagrams/t_gadget.png)

Emitted as OpenQASM 3 (`tGadgetQASM`): prepare `|T⟩ = T·H|0⟩` on the ancilla,
`CX` data→ancilla, `Z`-measure the ancilla, and apply `S` to the data **iff the
outcome is 1** (the red feed-forward box). `t_gadget_with_feedback`
(`TGadgetTeleport.lean:60`, **Verified**, axiom-clean) proves that after the
classically-controlled correction the data register holds `T|ψ⟩` for *both*
outcomes — the byproduct differs only by the Born amplitude and the ancilla label.
The companion CCZ gadget (`ccz_gadget.png`) is emitted and numerically cross-checked
against a Qiskit density-matrix simulation (`PyCircuits/ppm_qasm_verification.py`).

## Worked example — compiling Clifford+T to PPM (and how we prove it)

The PPM layer turns a reversible `Gate` circuit into a stream of **Pauli-product
measurements** — the operations a qLDPC / surface code performs natively via lattice
surgery. `compileArithmeticGateToPPM` (`CircuitToPPMInterface/Part2.lean:159`) does it
gate-by-gate:

```lean
def compileArithmeticGateToPPM : Gate → PPMProgram
  | .I         => []
  | .X q       => [.applyFrameUpdate [q]]                              -- deferred Pauli frame
  | .CX c t    => [.measurePauliKind .Z [c, t], .applyFrameUpdate [t]] -- joint ZZ measurement
  | .CCX a b t => [.useMagicT t, .measurePauliKind .Z [a, b, t], .applyFrameUpdate [t]]
  | .seq g₁ g₂ => compileArithmeticGateToPPM g₁ ++ compileArithmeticGateToPPM g₂
```

Drawn in the Litinski PPM calculus (qubit wires; each measurement a column of Pauli
boxes joined by a bar, `Z` green; magic-T injection purple; deferred X-frames dashed):

<p align="center"><img src="../../docs/diagrams/ppm_cx.png" width="430" alt="CNOT compiled to PPM">&nbsp;<img src="../../docs/diagrams/ppm_ccx.png" width="520" alt="Toffoli compiled to PPM"></p>

The blue `mₖ` boxes on the classical lane `c` are the **measurement record**: each
joint Pauli measurement lands one outcome bit, and the deferred `X`-frames are exactly
the Pauli corrections those recorded bits control. A `seq` simply concatenates the
programs ([`ppm_seq.png`](../../docs/diagrams/ppm_seq.png)).

**Scaling to a full gadget.** Running the *same* compiler on the verified 3-bit
Cuccaro adder (`cuccaro_n_bit_adder_full 3 0`, emitted from Lean by
`scripts/EmitAdderPPM.lean`) gives a **complete 42-command PPM program with 6
magic-T injections** — and the forward-MAJ → reverse-UMA structure of the adder is
visible as the climb-then-descend of the joint measurements:

<p align="center"><img src="../../docs/diagrams/ppm_adder3.png" width="980" alt="3-bit Cuccaro adder compiled to a full PPM program"></p>

And the modular multiplier `x ↦ 7x mod 15` (`sqir_modmult_const_gate 2 15 7`) compiles
to a **248-command PPM program with 32 magic-T injections** (its 32 Toffolis), folded
into rows:

<p align="center"><img src="../../docs/diagrams/ppm_modmult.png" width="960" alt="modular multiplier compiled to a full PPM program"></p>

Regenerate everything with `lake env lean --run scripts/EmitAdderPPM.lean` then
`python PyCircuits/draw_ppm.py`.

**How we prove it — a three-layer refinement** (each layer isolates one source of
complexity, so the non-Clifford obligation is explicit, not buried):

1. **Structural compilation** — `compileArithmeticGateToPPM_sound_from_primitives`
   (`Part2.lean:327`, **Verified**) reduces correctness to five per-gate obligations
   by induction on the `Gate` IR; the `seq` case uses `PPMProgramRel_append`
   (program concatenation mirrors semantic composition).
2. **ICX semantic model** — for the Clifford `{I, X, CX}` fragment,
   `compileICXGateToPPM_sound_from_cxMacro` (`Part2.lean:1367`, **Verified**) proves
   the compiled commands match the Gottesman measurement + Pauli-frame transitions on
   a `LogicalPPMState` (stabilizer · frame · magic-counter).
3. **Transfer to Boolean output** —
   `shor_arithmetic_ICX_correctness_transfers_to_PPM_no_reflect_hyp`
   (`CircuitToPPMSemanticBridge.lean:534`, **Verified**) carries `Gate.applyNat`
   decoder-level correctness through to the observed PPM output bits.

**Honest scope:** the `CCX`/Toffoli `useMagicT` command is *resource accounting* (one
T token); its semantic magic-injection correctness is the explicitly-**assumed**
`MagicInjectionObligations.CCX_ok` / `teleportCCXRel` contract — Scaffolded, not
proved. `magicCompile_executable_ICX` (`CircuitToPPMFactoryProvision.lean:214`) proves
only that a pool of ≥ `shorMagicDemand g` certified T-tokens lets the compiled program
*run to completion*.

### PPM rewrite rules (the calculus)

PPM circuits are simplified by two rules, both backed by FormalRV's Pauli algebra
and Gottesman update — drawn here in the same lattice-surgery style:

<p align="center"><img src="../../docs/diagrams/ppm_rules.png" width="900" alt="PPM rewrite rules"></p>

- **(a) Commuting measurements reorder.** `commutes p q` (`PPM.lean:109`) is `true`
  iff the two Pauli products share an *even* number of anticommuting sites (e.g.
  `Z⊗Z` and `X⊗X`); `commutes_self` / `commutes_I_*` are the base lemmas. Commuting
  PPMs swap freely.
- **(b) Measuring an anticommuting Pauli replaces the stabilizer.** `apply_PPM_pos` /
  `apply_PPM_neg` (`PPMOperational.lean:104`) are the Gottesman update: a measured `P`
  anticommuting with a generator replaces it (measuring `Z` on `|+⟩` turns stabilizer
  `X` into `Z`, `PPM_Z_on_plus_pos`), and the generator set stays commuting
  (`PPM_preserves_validity_plus_Z`).

These are the FormalRV-verified core of the Litinski PPM calculus — the
Pauli-commutation and measurement-update rules — checked by `decide` on concrete
states (a full π/8-rotation-pushing calculus is not formalised).

### More small examples

2. **CCZ teleportation gadget** (`ccz_gadget.qasm`, diagram
   [`ccz_gadget.png`](../../docs/diagrams/ccz_gadget.png)) — prepare `|CCZ⟩` on three
   ancillas, a transversal CNOT chain, three Z-measurements, then the `CZ`/`Z`
   feed-forward corrections. `ccz_teleport_outcome_000` (`CCZGadgetTeleport.lean:127`,
   **Verified**) proves the `|000⟩` branch lands `CCZ|ψ⟩` at amplitude `1/(2√2)`; the
   full feed-forward gadget is emitted and cross-checked by Qiskit simulation (the
   other 7 outcome branches are not state-vector-proved — honest scope).
3. **A Gottesman PPM update** — measuring `Z` on `|+⟩`: `PPM_preserves_validity_plus_Z`
   (`PPMOperational.lean:189`, **Verified** by `decide`) shows `apply_PPM_pos` keeps
   the stabilizer-generator set commuting through the measurement. This is the
   stabilizer-frame bookkeeping behind every logical measurement.

## Essential proof techniques

- **Outcome-by-outcome state vectors.** For each measurement result `b` the proof
  computes the projected post-measurement state, its Born amplitude, and the Clifford
  correction that erases the branch dependence — `t_teleport_outcome_0/1` discharge
  the two T-gadget branches by `fin_cases` over `Fin 4` and ring algebra. For CCZ,
  `cnotChain_mul_apply` turns the transversal CNOT chain into an index *permutation*,
  so the 6-qubit `|000⟩`-outcome branch is handled by Kronecker decomposition rather
  than a `Fin 64` case split.
- **Stabilizer PVM as algebra.** The `±1` Pauli projectors `(1±P)/2` are proven
  idempotent, orthogonal, and resolving identity purely by ring normalisation (using
  `P²=I`), and pointwise Pauli commutation is lifted to matrix commutation by list
  induction (`toMatrix_comm_of_pointwise`) — the algebraic backbone of the Gottesman
  measurement update.

Honest scope: the T gadget and the CCZ `|000⟩` branch are state-vector **Verified**;
the other 7 CCZ branches and the full Toffoli magic injection (`teleportCCXRel` /
`CCX_ok`) are an explicitly *assumed* contract, and distillation/decoders are out of
scope.
