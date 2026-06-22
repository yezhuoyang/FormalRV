# `FormalRV/PauliRotation` — the Pauli-rotation IR

The standard (Litinski, *A Game of Surface Codes*) layer between the logical
circuit IRs and PPM measurement programs.  Circuits compile to
`±{π, π/2, π/4, π/8}` Pauli-product rotations `e^{−iθP}`; commuting rotations
group into **parallel layers** (depth = layer count); layers lower to PPM
teleport blocks with magic-state counts transferred exactly.

## Folder map — syntax / semantics / compiler / correctness

```
PauliRotation/
├── Syntax.lean        THE IR.  Rot {neg, angle, axis}, RotLayer, RotProg,
│                      the decidable commutation test commF (acCount parity),
│                      well-formedness.  Imports nothing semantic.
├── Semantics/         THE MEANING.
│   ├── Core.lean        rotOf θ M = cos θ•1 − i sin θ•M (exact for M²=1) and
│   │                    its algebra (merge/cancel/commute/π-phases);
│   │                    axisMat via the function-indexed Kronecker opsMat;
│   │                    Rot/RotLayer/RotProg denotations.
│   ├── CommBridge.lean  commF P Q = true → the MATRICES commute
│   │                    (axisMat_comm_of_commF, exchange lemma Rot.denote_swap).
│   ├── BasisAction.lean entrywise axisMat actions (Z = parity diagonal,
│   │                    X = bit flip, Y = bit flip with ±i).
│   └── PauliPhase.lean  THE PHASE-TRACKED PRODUCT: axisMat P · axisMat Q
│                        = i^(phaseF P Q) • axisMat (mulF P Q) — the engine
│                        of verified Clifford pushing.
├── Compiler/          THE COMPILERS (all verified).
│   ├── GateDictionary.lean  Clifford+T → rotations (T/S/H/CNOT/CCZ rows as
│   │                        syntax trees; structural counts by decide).
│   ├── GateBridge.lean      gateRots : Gate-IR → flat rotation sequence
│   │                        (counts, boundedness, T-count = Gate.tcount).
│   ├── CircuitCompile.lean  circuit-level compile = schedule ∘ naive.
│   ├── QFTLadder.lean       the banded inverse-QFT / QPE rotation programs.
│   ├── Scheduler.lean       greedy ASAP parallelizer; scheduleList_denote
│   │                        (exact), counts on the nose, depth ≤ length.
│   ├── SchedulerK.lean      THE HARDWARE-BOUNDED COMPILER (≤ K rotations
│   │                        per layer): exact denotation, validity
│   │                        (layersLE), counts, the universal lower bound
│   │                        N ≤ K·depth, and VERIFIED OPTIMALITY
│   │                        depth = ⌈N/K⌉ for pairwise-commuting sequences.
│   ├── Rules.lean           adjacent rewrite rules (drop-π with exact
│   │                        phase, cancel, merge: T² = S …).
│   ├── PushRules.lean       VERIFIED CLIFFORD PUSHING: delay ±π/4 past an
│   │                        anticommuting rotation (axis ↦ mulF, sign in
│   │                        neg — Rot.pushedBy); ±π/2 push; swap.
│   ├── Optimizer.lean       THE CERTIFICATE CHECKER: untrusted optimizers
│   │                        emit RuleApp traces; applyTrace replays them;
│   │                        applyTrace_sound = exact preservation; capstones
│   │                        optimized_schedule(K)_applyNat.
│   └── ToPPM/               THE LOWERING to PPM measurement programs:
│       │                    π/8 ↦ |T⟩-teleport block (selective
│       │                    destruction), π/4 ↦ |Y⟩-block, π/2 ↦ frame.
│       ├── Lowering.lean      lowerRot/lowerFlat + branch semantics
│       │                      stmtDenote/progDenote; countMagicT = countPi8.
│       ├── TensorHigh.lean / BlockIdentities.lean / Embed.lean
│       │                      the ancilla-split calculus.
│       ├── TBlock.lean / TBlockNeg.lean / SBlock.lean
│       │                      the proven teleport-block branch identities.
│       ├── RotStep.lean       per-rotation step theorems (20 branches).
│       ├── Induction.lean     THE PRESERVATION THEOREM lowerFlat_denote:
│       │                      lowering preserves seqDenote on EVERY branch.
│       ├── GadgetLowering.lean  lowerGate_denote + lowerShorQPE_denote.
│       ├── LoweredInstances.lean 24 gadget instances + shor15Lowered.
│       ├── CCZBlock.lean      the 1-CCZ teleport machinery (tensorTriple,
│       │                      twisted destructions, quadratic corrections).
│       ├── CCZLane.lean       cczBlock emitter, isCCZRots recognizer
│       │                      (sound + complete), ccz_route_tradeoff —
│       │                      THE VERIFIED 8T-vs-1CCZ ECONOMICS.
│       └── CCZBlockBranch.lean  FENCED: the 64-branch CCZ semantic theorem
│                                (statement = the Qiskit-validated closed
│                                form; 4096-leaf proof compiles out-of-tree).
├── Correctness/       THE PROOFS that compiled programs ARE the gates.
│   ├── SingleQubitRows.lean  the 2×2 dictionary rows (T/S/Z/X/H) with
│   │                         explicit global phases.
│   ├── CircuitIdentities.lean rot_quarter_push (the Litinski push rule at
│   │                         matrix level), the braid/Hadamard identity.
│   ├── GateRows.lean / CCZRow.lean / CCXRow.lean  the n-qubit rows vs
│   │                         Gate.applyNat (X, CX, CCZ diagonal, CCX).
│   ├── QFTRows.lean          the CS† row.
│   ├── Assembly.lean         gateRots_denote_applyNat + the capstone
│   │                         gateRotSchedule_applyNat (compile → schedule
│   │                         → denote = gphase · applyMat).
│   └── ShorEndToEnd.lean     the COMPLETE Shor/QPE circuit composed:
│                             shorQPE_rots_denote, shor15_schedule_denote
│                             (743 rotations, kernel-checked).
├── Gadgets.lean + Gadgets/   per-arithmetic-gadget compilations
│                             (Cuccaro/Gidney/modadd/modmult/modexp/QROM/
│                             windowed) + SemanticInstances.lean (23 _applyNat
│                             theorems by decide).
└── Examples.lean             kernel-checked parallelism/count anchors.
```

## The verified pipeline

```
Gate-IR ──gateRots──▶ rotations ──[optimize: applyTrace certificates]──▶
        ──scheduleList / scheduleListK──▶ parallel layers ──lowerFlat──▶ PPM
```

Every arrow has a semantic-preservation theorem; counts are exact at every
stage (`tcount = countPi8 = countMagicT`); the end-to-end capstones are
`gateRotSchedule_applyNat` (per gadget), `optimized_scheduleK_applyNat`
(any certified optimizer + hardware bound K), `lowerGate_denote` /
`lowerShorQPE_denote` (to PPM, every measurement branch), and
`shor15Lowered` (the complete Shor-15 circuit as a PPM program).

The whole folder is sorry-free and axiom-clean
(`propext, Classical.choice, Quot.sound`); side conditions discharge by
`decide` on concrete gadgets.

## Status / fenced gaps (do NOT cite as verified)

1. **General ASAP depth-optimality** — `scheduleList_depth_le` (≤ length) is
   proven, and `scheduleListK_depth_eq`/`scheduleListK_optimal` close the
   ⌈N/K⌉ sandwich for PAIRWISE-COMMUTING sequences; depth-optimality for
   general anticommutation DAGs remains open (NP-hard with the K-bound;
   per-instance depths are kernel-computable).
2. **Readout absorption** — the rotation IR has no measurement statement
   yet, so "trailing Cliffords are absorbed into readout for free"
   (Litinski's endgame) has no formal footing; rotations are currently
   lowered uniformly.
3. **`CCZBlockBranch.lean`** — the 64-branch CCZ-block semantic theorem is
   stated exactly as Qiskit-validated (all 64 branches, Born sum 1) but its
   Lean proof is a 4096-leaf elaboration kept outside the umbrella.
4. **QFT at four angles** — only (π/4)·ℤ-lattice rotations are exact; the
   full QFT is expressible up to ε via the banded decomposition
   (`aqft2Rots`); the per-rotation error calculus over `RotProg.denote` is
   the named follow-up.
5. **Per-gadget symbolic `opsOK`** — concrete sizes discharge by `decide`;
   symbolic-width lemmas remain open.
