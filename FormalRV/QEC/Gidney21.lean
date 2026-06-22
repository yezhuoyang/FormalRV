/-
  FormalRV.QEC.Gidney21 — umbrella.

  Per-gadget physical compilation + verification for Gidney–Ekerå 2021, at
  level-2 surface-code distance d = 27.  Each gadget file carries the EXACT
  PPM object the PauliRotation layer verified (its `LoweredOK` instance)
  through the physical compiler (`compilePPM`), and exposes, for that one
  gadget: semantic correctness (`*_compiled : GadgetCompiledOK`) and
  resource counts walked from the monolithic physical circuit
  (`*_measCount`, `*_qubits`).  See `Common.lean` for the shared recipe.
-/
import FormalRV.QEC.Gidney21.Compiler.Board
import FormalRV.QEC.Gidney21.Compiler.Lower
import FormalRV.QEC.Gidney21.Resource
import FormalRV.QEC.Gidney21.Accounting
import FormalRV.QEC.Gidney21.SurgerySemantics
import FormalRV.QEC.Gidney21.AlgorithmCorrectness
import FormalRV.QEC.Gidney21.RotatedMerge
import FormalRV.QEC.Gidney21.GadgetSchedule
import FormalRV.QEC.Gidney21.GadgetScheduleDispatch
import FormalRV.QEC.Gidney21.MixedMerge
import FormalRV.QEC.Gidney21.YMerge
import FormalRV.QEC.Gidney21.AdaptiveDispatch
import FormalRV.QEC.Gidney21.SplitDetach
import FormalRV.QEC.Gidney21.QuadraticFrame
import FormalRV.QEC.Gidney21.YFromT
import FormalRV.QEC.Gidney21.YByEdgeTracking
import FormalRV.QEC.Gidney21.EndToEnd
import FormalRV.QEC.Gidney21.ResourceTable
import FormalRV.QEC.Gidney21.Correctness
import FormalRV.QEC.Gidney21.Common
import FormalRV.QEC.Gidney21.CuccaroAdder
import FormalRV.QEC.Gidney21.ModMult
import FormalRV.QEC.Gidney21.ModExp
import FormalRV.QEC.Gidney21.Windowed
import FormalRV.QEC.Gidney21.ScheduleFlowSoundness
import FormalRV.QEC.Gidney21.GadgetToLaS
import FormalRV.QEC.Gidney21.FoldPPMProg
import FormalRV.QEC.Gidney21.FoldPPMProgScale
