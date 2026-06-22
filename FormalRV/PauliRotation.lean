/-
  FormalRV.PauliRotation — umbrella.

  The Pauli-rotation IR: the standard (Litinski) layer between the logical
  circuit IRs and PPM programs.  Circuits compile to ±{π, π/2, π/4, π/8}
  Pauli-product rotations, commuting rotations group into PARALLEL layers
  (depth = layer count), and the layers lower to PPM.

  Folder map (see `PauliRotation/README.md`):
    Syntax.lean    — THE IR: `Rot`/`RotLayer`/`RotProg`, `commF`, wf
    Semantics/     — THE MEANING: `rotOf` algebra, `axisMat`, denotations,
                     the commutation bridge, basis actions, the
                     phase-tracked Pauli product
    Compiler/      — THE COMPILERS: gate dictionary, schedulers (greedy +
                     hardware-K-bounded), rewrite rules, Clifford pushing,
                     the certificate-checked optimizer; `ToPPM/` lowers
                     rotations to PPM measurement programs
    Correctness/   — THE PROOFS that compiled programs equal the gate
                     unitaries (dictionary rows → assembly → Shor)
    Gadgets/       — per-arithmetic-gadget instances
-/
import FormalRV.PauliRotation.Syntax
import FormalRV.PauliRotation.Semantics.Core
import FormalRV.PauliRotation.Semantics.CommBridge
import FormalRV.PauliRotation.Semantics.BasisAction
import FormalRV.PauliRotation.Semantics.PauliPhase
import FormalRV.PauliRotation.Compiler.GateDictionary
import FormalRV.PauliRotation.Compiler.GateBridge
import FormalRV.PauliRotation.Compiler.CircuitCompile
import FormalRV.PauliRotation.Compiler.QFTLadder
import FormalRV.PauliRotation.Compiler.Scheduler
import FormalRV.PauliRotation.Compiler.SchedulerK
import FormalRV.PauliRotation.Compiler.Rules
import FormalRV.PauliRotation.Compiler.PushRules
import FormalRV.PauliRotation.Compiler.Optimizer
import FormalRV.PauliRotation.Correctness.SingleQubitRows
import FormalRV.PauliRotation.Correctness.CircuitIdentities
import FormalRV.PauliRotation.Correctness.GateRows
import FormalRV.PauliRotation.Correctness.CCZRow
import FormalRV.PauliRotation.Correctness.CCXRow
import FormalRV.PauliRotation.Correctness.QFTRows
import FormalRV.PauliRotation.Correctness.Assembly
import FormalRV.PauliRotation.Correctness.ShorEndToEnd
import FormalRV.PauliRotation.Gadgets
import FormalRV.PauliRotation.Gadgets.SemanticInstances
import FormalRV.PauliRotation.Compiler.ToPPM.TensorHigh
import FormalRV.PauliRotation.Compiler.ToPPM.BlockIdentities
import FormalRV.PauliRotation.Compiler.ToPPM.TBlock
import FormalRV.PauliRotation.Compiler.ToPPM.SBlock
import FormalRV.PauliRotation.Compiler.ToPPM.Lowering
import FormalRV.PauliRotation.Compiler.ToPPM.Embed
import FormalRV.PauliRotation.Compiler.ToPPM.TBlockNeg
import FormalRV.PauliRotation.Compiler.ToPPM.RotStep
import FormalRV.PauliRotation.Compiler.ToPPM.Induction
import FormalRV.PauliRotation.Compiler.ToPPM.GadgetLowering
import FormalRV.PauliRotation.Compiler.ToPPM.LoweredInstances
import FormalRV.PauliRotation.Compiler.ToPPM.CCZBlock
import FormalRV.PauliRotation.Compiler.ToPPM.CCZLane
import FormalRV.PauliRotation.Examples
