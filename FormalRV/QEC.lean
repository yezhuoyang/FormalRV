import FormalRV.QEC.LDPCMatrix
import FormalRV.QEC.GF2Linear
import FormalRV.QEC.GF2Linearity
import FormalRV.QEC.GF2Rank
import FormalRV.QEC.CSSCode
import FormalRV.QEC.CodeDimension
import FormalRV.QEC.FrontendAlgebraic
import FormalRV.QEC.StabilizerScheduleVerify
import FormalRV.QEC.Logical
import FormalRV.QEC.LogicalFinder
import FormalRV.QEC.LogicalGenuine
import FormalRV.QEC.LogicalMeasurementGeneral
import FormalRV.QEC.LPCssCondition
import FormalRV.QEC.LogicalValidity
import FormalRV.QEC.QECCodeInstances
import FormalRV.QEC.Instances
import FormalRV.QEC.LPInstancesValid
import FormalRV.QEC.Addressing
import FormalRV.QEC.GateSyndromeWorkedExample
import FormalRV.QEC.SmallCodeValidity
import FormalRV.QEC.StabilizerCode
import FormalRV.QEC.CodeBuilders
import FormalRV.QEC.BlockAddressing
import FormalRV.QEC.LogicalLayout.GlobalIndex
import FormalRV.QEC.LogicalLayout.Labeling
import FormalRV.QEC.LogicalLayout.Notation
import FormalRV.QEC.LogicalLayout.PhysicalCompile
import FormalRV.QEC.LogicalLayout.MagicMerge
import FormalRV.QEC.LogicalLayout.StimDriver
import FormalRV.QEC.LogicalLayout.Geometry
import FormalRV.QEC.LogicalLayout.FixedBoard
import FormalRV.QEC.LogicalLayout.DerivedRoutingBridge
import FormalRV.QEC.LatticeSurgery.LaSre
import FormalRV.QEC.LatticeSurgery.MajorityGate
import FormalRV.QEC.LatticeSurgery.MajorityGateLaS
import FormalRV.QEC.LatticeSurgery.CNOTFromLaSsynth
import FormalRV.QEC.LatticeSurgery.CZFromLaSsynth
import FormalRV.QEC.LatticeSurgery.HFromLaSsynth
import FormalRV.QEC.LatticeSurgery.SFromLaSsynth
import FormalRV.QEC.LatticeSurgery.Weld
import FormalRV.QEC.LatticeSurgery.MixedMergeWeld
import FormalRV.QEC.LatticeSurgery.FaithfulMixedMerge
import FormalRV.QEC.LatticeSurgery.ConjugationWeld
import FormalRV.QEC.LatticeSurgery.ProgramAssembly
import FormalRV.QEC.LatticeSurgery.WeldComposition
import FormalRV.QEC.LatticeSurgery.ChainComposition
import FormalRV.QEC.LatticeSurgery.Pad
import FormalRV.QEC.LatticeSurgery.Routing
import FormalRV.QEC.LatticeSurgery.RoutedMerge
import FormalRV.QEC.LatticeSurgery.RoutedSchedule
import FormalRV.QEC.LatticeSurgery.RoutedParallel
import FormalRV.QEC.LatticeSurgery.CliffordFrame
import FormalRV.QEC.LatticeSurgery.MixedMergeGen
import FormalRV.QEC.LatticeSurgery.Dispatch
import FormalRV.QEC.LatticeSurgery.WidthScaling
import FormalRV.QEC.LatticeSurgery.WidthScalingStep2
import FormalRV.QEC.LatticeSurgery.WidthScalingStep2b
import FormalRV.QEC.LatticeSurgery.WidthScalingXMerge
import FormalRV.QEC.LatticeSurgery.WidthScalingHetero
import FormalRV.QEC.LatticeSurgery.WidthScalingHeteroPorts
import FormalRV.QEC.LatticeSurgery.WidthScalingResources
import FormalRV.QEC.LatticeSurgery.GenuineRotation
import FormalRV.QEC.LatticeSurgery.GenuineMixedY
import FormalRV.QEC.LatticeSurgery.BasisChangeComposition
import FormalRV.QEC.LatticeSurgery.WidthScalingYMeasure
import FormalRV.QEC.LatticeSurgery.WidthScalingYChain
import FormalRV.QEC.LatticeSurgery.CrossLayerHetero
import FormalRV.QEC.LatticeSurgery.PauliFrame
import FormalRV.QEC.LatticeSurgery.EndToEndCert
import FormalRV.QEC.LogicalLayout.Threader
import FormalRV.QEC.LogicalLayout.FrameTracker
import FormalRV.QEC.LogicalLayout.Compiler
import FormalRV.QEC.LogicalLayout.Bridge
import FormalRV.QEC.LogicalLayout.CompileReport
import FormalRV.QEC.LogicalLayout.FrameComplete
import FormalRV.QEC.Gidney21.ShorBlockDemo
import FormalRV.QEC.Gidney21.CuccaroAdderDemo
import FormalRV.QEC.Gidney21.ModMultDemo
import FormalRV.QEC.LogicalLayout.PlacedGadgetRouting
import FormalRV.QEC.Gidney21.ComposedSemantic
import FormalRV.QEC.Gidney21.BasisFrame
import FormalRV.QEC.Gidney21.ColorEnforcing
import FormalRV.QEC.Gidney21
import FormalRV.QEC.LogicalLayout.Examples
import FormalRV.QEC.LatticeSurgery.LDPCSurgery
import FormalRV.QEC.LatticeSurgery.SurgeryReadout
import FormalRV.QEC.LatticeSurgery.SurgeryCorrect
import FormalRV.QEC.LatticeSurgery.SurgeryReduction
import FormalRV.QEC.LatticeSurgery.SurgerySchedule
import FormalRV.QEC.LatticeSurgery.MagicInjectionSurgery
import FormalRV.QEC.LatticeSurgery.SurgeryDemoSurface
import FormalRV.QEC.LatticeSurgery.SurgeryDemoMerge
import FormalRV.QEC.LatticeSurgery.SurgeryDemoCNOT
import FormalRV.QEC.LatticeSurgery.SurgeryDemoSteane
import FormalRV.QEC.LatticeSurgery.SurfaceShorResourceCount
import FormalRV.QEC.LatticeSurgery.StimEmit
import FormalRV.QEC.LatticeSurgery.ScheduleEmit
import FormalRV.QEC.LatticeSurgery.LaSsynthImport
import FormalRV.QEC.Circuit.PhysCircuit
import FormalRV.QEC.Circuit.SyndromeExtraction
import FormalRV.QEC.Circuit.ExtractionCount
import FormalRV.QEC.Circuit.CircuitSemantics
import FormalRV.QEC.Time.LogicalCycle
import FormalRV.QEC.LatticeSurgery.XSurgeryBuilder
import FormalRV.QEC.LatticeSurgery.ZSurgeryBuilder
import FormalRV.QEC.Codes.Surface.SurfaceChain
import FormalRV.QEC.Codes.Surface.SurfaceFamily
import FormalRV.QEC.Codes.Surface.RotatedSurface
import FormalRV.QEC.Codes.Surface.RotatedLogical
import FormalRV.QEC.Codes.HypergraphProduct.HGPChain
import FormalRV.QEC.Codes.HypergraphProduct.HGPFamily
import FormalRV.QEC.Codes.BivariateBicycle.BBChain
import FormalRV.QEC.Codes.BivariateBicycle.BBFamily
import FormalRV.QEC.Codes.LiftedProduct.LPChain
import FormalRV.QEC.Codes.LiftedProduct.LPFamily
import FormalRV.QEC.Codes.LiftedProduct.LPTinyBasisImport
import FormalRV.QEC.Codes.LiftedProduct.LPTinyBasisFullCert
import FormalRV.QEC.Codes.LiftedProduct.LP16Indexing

/-!
# FormalRV.QEC

The QEC layer: the *demand side* of fault-tolerant Shor, assuming infinitely many
**virtual qubits** (no hardware mapping, no system calls — those live in
`FormalRV.System`, the supply side that answers whether a finite machine can run
this in a given time).

Contents:
* GF(2) toolkit + code mathematics (CSS codes, code families surface/HGP/BB/LP,
  logical operators, code dimension).
* `LatticeSurgery/` — lattice-surgery gadgets over arbitrary CSS codes: syntax
  (`SurgeryGadget`), decidable structural verification, stabilizer semantics
  (the gadget implements the target logical Pauli measurement), schedules,
  resource counts (incl. per-check syndrome ancillas), and Stim emitters.

This umbrella imports every module under `QEC/`.
-/
