/-
  FormalRV.QEC.Gidney21.ShorBlockDemo
  -----------------------------------
  **★ A REAL Shor arithmetic block compiles ENTIRELY to verified lattice
  surgery. ★**

  `cczBlock` (from `PauliRotation.Compiler.ToPPM.CCZLane`) is the genuine
  CCZ-state-teleport PPM program — the Toffoli at the heart of Shor's modular
  adders, Qiskit-validated branch-exact on all 64 branches.  We route ITS
  measurements (NOT a hand-written example) through the verified-gadget dispatch
  and prove the WHOLE block is covered: every measured Pauli product — the
  weight-2 `ZZ` joins, the weight-1 `X` readouts, the weight-2 mixed `XZ`/`ZX`
  branches, and the weight-3 mixed `XZZ`/`ZXZ`/`ZZX` branches — routes to a
  SINGLE verified lattice-surgery gadget, with NOTHING left uncovered.
-/
import FormalRV.QEC.Gidney21.GadgetToLaS
import FormalRV.PauliRotation.Compiler.ToPPM.CCZLane

namespace FormalRV.QEC.Gidney21

open FormalRV.PPM.Prog

/-- A concrete CCZ block: data qubits 0,1,2; ancillas 3,4,5; outcome slots 6.. -/
def shorCCZ : FormalRV.PPM.Prog.PPMProg := FormalRV.PauliRotation.cczBlock 0 1 2 3 6

/-- The gadget list the REAL CCZ block compiles to — 15 verified gadgets. -/
theorem shorCCZ_gadgets :
    progGadgets shorCCZ =
      [.zMerge, .zMerge, .zMerge,
       .mX1, .mxzMerge, .mxzMerge, .mxzz3,
       .mX1, .mxzMerge, .mzxMerge, .mzxz3,
       .mX1, .mzxMerge, .mzxMerge, .mzzx3] := by native_decide

/-- **Every measurement of the real CCZ block is COVERED** — nothing left out. -/
theorem shorCCZ_fully_covered : uncoveredMeasurements shorCCZ = [] := by native_decide

/-- **★ THE REAL SHOR CCZ BLOCK ROUTES ENTIRELY TO VERIFIED LATTICE SURGERY ★.**
Every measured Pauli product of the genuine Toffoli/CCZ teleport — across all
weights and X/Z patterns its adaptive branches produce — routes to a single
verified-LaS gadget, and the coverage is COMPLETE.  A real Shor arithmetic
gadget, end to end, on the verified-gadget pipeline (not a toy example). -/
theorem shorCCZ_routes_to_verified :
    (∀ k ∈ progGadgets shorCCZ, ScheduleImplementsSpec (gadgetFor k) = true)
      ∧ uncoveredMeasurements shorCCZ = [] :=
  fully_covered_program_routes_to_verified shorCCZ shorCCZ_fully_covered

end FormalRV.QEC.Gidney21
