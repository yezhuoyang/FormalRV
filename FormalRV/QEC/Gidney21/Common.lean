/-
  FormalRV.QEC.Gidney21.Common — convenience re-export.

  The Gidney21 audit is MODULARIZED into compilation vs proof:

      Compiler/Board.lean   — qubit layout (one d=27 patch per logical qubit)
      Compiler/Lower.lean    — THE COMPILER: PPM object → physical object
      Resource.lean          — resource counts, walked from the circuit
      Correctness.lean       — semantic correctness (PPM + syndrome extraction)

  Each `Gidney21/<Gadget>.lean` imports this and instantiates the generic
  recipe at one specific gadget, citing its existing `LoweredOK` proof.
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
import FormalRV.QEC.Gidney21.Correctness
