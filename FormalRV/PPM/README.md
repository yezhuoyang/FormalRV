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
