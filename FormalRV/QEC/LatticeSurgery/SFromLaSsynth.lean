/-
  FormalRV.QEC.LatticeSurgery.SFromLaSsynth
  -----------------------------------------
  **The S (phase) gate — LaSsynth-synthesized, imported verbatim,
  re-verified in Lean.**

  S maps X̄→Ȳ, Z̄→Z̄ — a non-Clifford-boundary operation realized with
  Y-CUBES (Y-basis init/measure: the surface-code S-gadget).  The OUTPUT
  port carries Ȳ, so BOTH its blue(Z) and red(X) correlation pieces are
  present (`portBlue Y = portRed Y = true`).  Spec stabilizers `XY` / `ZZ`,
  z3-synthesized (3 Y-cubes), re-checked by `LaSCorrectFull`.
-/
import FormalRV.QEC.LatticeSurgery.LaSre

namespace FormalRV.QEC.LaSre

def sgI  : List (Nat × Nat × Nat) := [(0,0,1), (0,1,1), (0,1,2)]
def sgJ  : List (Nat × Nat × Nat) := []
def sgK  : List (Nat × Nat × Nat) := [(0,0,0), (0,0,1), (0,0,2), (0,1,1), (1,0,1), (1,1,1)]
def sgCI : List (Nat × Nat × Nat) := [(0,0,1), (0,0,2), (0,1,0), (0,1,1)]
def sgCJ : List (Nat × Nat × Nat) := []
def sgY  : List (Nat × Nat × Nat) := [(0,1,0), (1,0,2), (1,1,0)]

/-- The LaSsynth-synthesized S-gate pipe diagram (with 3 Y-cubes). -/
def sLaS : LaSre :=
  { maxI := 2, maxJ := 2, maxK := 3
    YCube  := fun i j k => sgY.contains (i, j, k)
    ExistI := fun i j k => sgI.contains (i, j, k)
    ExistJ := fun i j k => sgJ.contains (i, j, k)
    ExistK := fun i j k => sgK.contains (i, j, k)
    ColorI := fun i j k => sgCI.contains (i, j, k)
    ColorJ := fun i j k => sgCJ.contains (i, j, k) }

theorem sLaS_valid : sLaS.valid = true := by native_decide

def sgIJ : List (Nat × Nat × Nat × Nat) := [(0,0,0,1), (1,0,1,0), (1,0,1,1), (1,0,1,2)]
def sgIK : List (Nat × Nat × Nat × Nat) := [(0,0,0,1)]
def sgJK : List (Nat × Nat × Nat × Nat) := []
def sgJI : List (Nat × Nat × Nat × Nat) := []
def sgKI : List (Nat × Nat × Nat × Nat) := [(0,0,0,0), (0,0,0,1), (0,0,0,2), (0,1,0,0), (0,1,0,1), (1,0,1,0), (1,1,1,0)]
def sgKJ : List (Nat × Nat × Nat × Nat) := [(0,0,0,1), (0,0,0,2), (0,1,0,1), (1,0,0,0), (1,0,0,1), (1,0,0,2), (1,0,1,0), (1,0,1,1), (1,1,1,0), (1,1,1,1)]

def sSurf : Surf :=
  { IJ := fun s i j k => sgIJ.contains (s,i,j,k)
    IK := fun s i j k => sgIK.contains (s,i,j,k)
    JK := fun s i j k => sgJK.contains (s,i,j,k)
    JI := fun s i j k => sgJI.contains (s,i,j,k)
    KI := fun s i j k => sgKI.contains (s,i,j,k)
    KJ := fun s i j k => sgKJ.contains (s,i,j,k) }

/-- Both ports z_basis=J: blue=KJ(5), red=KI(4). -/
def sPorts : List Port := [⟨0, 0, 0, 5, 4⟩, ⟨0, 0, 2, 5, 4⟩]

def sFlows : List (List Pauli) :=
  let x := Pauli.X; let z := Pauli.Z; let y := Pauli.Y
  [ [x,y], [z,z] ]

def sPaulis (s p : Nat) : Pauli := (sFlows.getD s []).getD p Pauli.I

/-- **★ THE S (PHASE) GATE IS FULLY-VERIFIED LATTICE SURGERY ★** — the
synthesized Y-cube diagram passes the COMPLETE `LaSCorrectFull` for both
flows X̄→Ȳ and Z̄→Z̄, including the Y-OUTPUT port (both blue+red present) and
the Y-cube both-or-none functionality. -/
theorem sLaS_fully_correct :
    LaSCorrectFull sLaS sSurf sPorts sPaulis 2 = true := by native_decide

theorem sLaS_report_empty :
    LaSReport sLaS sSurf sPorts sPaulis 2 = [] := by native_decide

end FormalRV.QEC.LaSre
