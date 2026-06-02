import FormalRV.PPM.CircuitToPPMFactoryProvision
import FormalRV.PPM.CircuitToPPMInterface
import FormalRV.PPM.CircuitToPPMMagicFactory
import FormalRV.PPM.CircuitToPPMObservationBridge
import FormalRV.PPM.CircuitToPPMSemanticBridge
import FormalRV.PPM.CircuitToPPMToffoliMagic
import FormalRV.PPM.EightTToCCZScheme
import FormalRV.PPM.FactoryHierarchy
import FormalRV.PPM.GE2021PPMSysInv
import FormalRV.PPM.GidneyAND
import FormalRV.PPM.LayeredPPMQECInterface
import FormalRV.PPM.LogicalState
import FormalRV.PPM.MagicStateTeleport
import FormalRV.PPM.PPM
import FormalRV.PPM.PPMOperational
import FormalRV.PPM.PPMUpdateInvariants
import FormalRV.PPM.PauliOps
import FormalRV.PPM.PauliSemantics
import FormalRV.PPM.ToffoliFromCCZ
import FormalRV.PPM.ToffoliScheme
import FormalRV.PPM.ToffoliSchemeDischarge

/-!
# FormalRV.PPM

Pauli-product measurement: Pauli algebra, the Gottesman update, circuit-to-PPM compilation, magic-state factories.

This umbrella imports every module under `PPM/`.
-/
