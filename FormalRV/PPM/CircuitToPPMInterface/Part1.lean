import FormalRV.PPM.LayeredPPMQECInterface
import FormalRV.Core.QuantumGate
import FormalRV.PPM.PPMOperational
import FormalRV.PPM.FactoryHierarchy

open FormalRV.Framework
open FormalRV.Framework.Architecture
open FormalRV.Framework.LayeredArtifactInterface
open FormalRV.Framework.SystemInvariantStrengthening
open FormalRV.Framework.LayeredPPMQECInterface
open FormalRV.Framework.Factory
open FormalRV.Framework.SurgeryGadgetToSysCalls
open FormalRV.Framework.LDPC
open FormalRV.Framework.AdderSystem
open FormalRV.Framework.CompressedRepeatSoundness

/-
  FormalRV.Framework.CircuitToPPMInterface — the first
  high-level-circuit → PPM lowering interface for the
  ARITHMETIC fragment of FT-Shor.

  ## Scope

  This file defines a structural lowering from the existing
  arithmetic-only Gate IR (`FormalRV.Framework.Gate`,
  constructors `I | X | CX | CCX | seq`) into a logical-layer
  PPM program (`PPMCommand` / `PPMProgram`).  It targets the
  arithmetic subcircuits of Shor (modular-exponentiation,
  modular-multiplication, modular-addition, Cuccaro adders,
  Gidney 2018 adders, etc.) — NOT the QPE phase-rotation
  fragment, which generally requires either exact-Clifford+T
  decomposition or approximate synthesis before it can enter
  this PPM path.

  ## Layering (recap)

      Logical Shor / arithmetic correctness
          ↓ (Clifford+T / Toffoli-CNOT-X arithmetic fragment, THIS FILE)
      PPM / lattice-surgery logical-measurement layer
          ↓
      QEC gadget implementation
          ↓
      Backend compressed SysCall schedule
          ↓
      System resource/invariant certificate

  The arithmetic fragment lives ABOVE the PPM layer.  The PPM
  layer lives ABOVE the SysCall/System layer.  Do not collapse
  PPM into physical SysCall schedules.

  ## What is and is NOT proved in this tick

  Proved structurally:
  * Empty `Gate.I` compiles to `[]`.
  * `Gate.seq g₁ g₂` compiles to the append of the compiled
    halves.

  NOT proved:
  * Semantic equivalence between the source `Gate` and the
    compiled `PPMProgram`.  The user must supply a separate
    semantic proof; the interface records the obligation as a
    `Prop` slot.

  Existing definitions REUSED:
  * `FormalRV.Framework.Gate` — the arithmetic Gate IR.
  * `FormalRV.Framework.Architecture.PauliKind` — I/X/Y/Z.
  * `FormalRV.Framework.LayeredPPMQECInterface.PPMSpec`,
    `QECGadgetSpec`, `LogicalQubitId`, `PauliKind` re-export.

  Existing definitions deferred:
  * `BaseUCom dim` (`QuantumGate.lean`) — QPE-capable IR with
    real-angle R primitives.  Real-angle equality is not
    decidable, so the BaseUCom-side classifier here only tags
    structural kinds (CNOT vs R), not specific Clifford+T
    rewrites.  Real lowering of BaseUCom (decompose to Gate)
    is a future tick.
  * `PPMOperational.StabilizerState` and Gottesman PPM
    updates — these formalise PPM operational semantics; they
    will be consumed by the future `semantic_obligation`
    refinement.
-/




