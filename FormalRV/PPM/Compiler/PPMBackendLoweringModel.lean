import FormalRV.PPM.QECBridge.LayeredPPMQECInterface
import FormalRV.Core.QuantumGate
import FormalRV.PPM.Semantics.PPMOperational
import FormalRV.PPM.QECBridge.FactoryHierarchy
import FormalRV.PPM.Compiler.EnrichedPPMStateAndIntegration

namespace FormalRV.Framework.CircuitToPPMInterface
namespace PPMProgramResourceSummary
open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.LayeredArtifactInterface
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.Framework.LayeredPPMQECInterface
open FormalRV.Framework.Factory
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.Framework.LDPC
open FormalRV.System.AdderSystem
open FormalRV.System.CompressedRepeatSoundness


/-- Zero summary — identity for `add`. -/
def zero : PPMProgramResourceSummary :=
  ⟨0, 0, 0, 0⟩

/-- Fieldwise addition. -/
def add (a b : PPMProgramResourceSummary) : PPMProgramResourceSummary :=
  ⟨ a.commandCount + b.commandCount
  , a.measureCount + b.measureCount
  , a.frameUpdates + b.frameUpdates
  , a.magicTCount  + b.magicTCount ⟩

end PPMProgramResourceSummary
end FormalRV.Framework.CircuitToPPMInterface
