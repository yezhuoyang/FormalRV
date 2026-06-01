import FormalRV.PPM.LayeredPPMQECInterface
import FormalRV.Core.QuantumGate
import FormalRV.PPM.PPMOperational
import FormalRV.PPM.FactoryHierarchy
import FormalRV.PPM.CircuitToPPMInterface.Part3

namespace FormalRV.Framework.CircuitToPPMInterface
namespace PPMProgramResourceSummary
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
