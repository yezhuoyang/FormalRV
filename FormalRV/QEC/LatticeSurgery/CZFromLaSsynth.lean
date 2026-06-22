/-
  FormalRV.QEC.LatticeSurgery.CZFromLaSsynth
  ------------------------------------------
  **The CZ gate (a MIXED-basis multi-merge) — LaSsynth-synthesized,
  imported verbatim, and re-verified in Lean.**

  CZ couples X to Z (X̄₁ → X̄₁Z̄₂), the canonical MIXED-basis two-qubit
  operation a PPM multi-Pauli measurement needs.  Synthesized with z3 on
  the spec stabilizers `X.XZ / Z.Z. / .XZX / .Z.Z` (port order
  c1in,c2in,c1out,c2out), imported verbatim, re-checked by `LaSCorrectFull`.
-/
import FormalRV.QEC.LatticeSurgery.LaSre

namespace FormalRV.QEC.LaSre

def czI  : List (Nat × Nat × Nat) := [(0,0,3), (0,1,1), (0,1,3), (0,1,4)]
def czJ  : List (Nat × Nat × Nat) := [(0,0,2)]
def czK  : List (Nat × Nat × Nat) := [(0,0,0), (0,0,1), (0,0,2), (0,0,3), (0,1,0), (0,1,1), (0,1,3), (0,1,4), (1,0,0), (1,0,1), (1,0,2), (1,0,3), (1,0,4), (1,1,0), (1,1,1), (1,1,2), (1,1,3)]
def czCI : List (Nat × Nat × Nat) := [(0,0,4), (0,1,4)]
def czCJ : List (Nat × Nat × Nat) := [(0,0,1), (0,0,2), (0,0,3), (1,0,1), (1,0,2)]
def czY  : List (Nat × Nat × Nat) := [(0,0,0), (0,0,1), (0,0,4), (1,1,0)]

/-- The LaSsynth-synthesized CZ pipe diagram (2×2×5). -/
def czLaS : LaSre :=
  { maxI := 2, maxJ := 2, maxK := 5
    YCube  := fun i j k => czY.contains (i, j, k)
    ExistI := fun i j k => czI.contains (i, j, k)
    ExistJ := fun i j k => czJ.contains (i, j, k)
    ExistK := fun i j k => czK.contains (i, j, k)
    ColorI := fun i j k => czCI.contains (i, j, k)
    ColorJ := fun i j k => czCJ.contains (i, j, k) }

theorem czLaS_valid : czLaS.valid = true := by native_decide

def czIJ : List (Nat × Nat × Nat × Nat) := [(0,0,0,1), (0,0,0,4), (0,0,1,1), (0,0,1,3), (1,0,0,4), (2,0,0,3), (2,0,0,4), (2,0,1,1), (3,0,0,4), (3,0,1,1), (3,0,1,4)]
def czIK : List (Nat × Nat × Nat × Nat) := [(0,0,0,3), (0,0,0,4), (0,0,1,2), (1,0,0,1), (2,0,1,1), (2,0,1,2), (2,0,1,3), (2,0,1,4), (3,0,1,2)]
def czJK : List (Nat × Nat × Nat × Nat) := [(0,0,0,1), (0,0,0,2), (0,1,0,2), (1,0,0,1), (1,1,0,1), (2,0,0,2), (2,0,0,3), (2,1,0,2), (3,0,0,1)]
def czJI : List (Nat × Nat × Nat × Nat) := [(0,0,0,1), (0,0,0,3), (0,1,0,2), (1,0,0,1), (1,1,0,1), (1,1,0,2), (2,0,0,2), (2,0,0,3), (3,0,0,1), (3,0,0,3)]
def czKI : List (Nat × Nat × Nat × Nat) := [(0,0,0,1), (0,0,0,2), (0,0,0,3), (0,0,1,2), (0,1,0,0), (0,1,0,1), (0,1,0,2), (0,1,0,3), (0,1,0,4), (1,0,0,4), (2,0,0,0), (2,0,0,1), (2,0,0,4), (2,0,1,0), (2,0,1,1), (2,0,1,3), (2,0,1,4), (2,1,1,0), (2,1,1,1), (2,1,1,2), (2,1,1,3), (2,1,1,4), (3,0,1,2)]
def czKJ : List (Nat × Nat × Nat × Nat) := [(0,0,0,1), (0,0,0,2), (0,0,0,3), (0,0,1,1), (0,0,1,2), (0,0,1,3), (0,0,1,4), (0,1,1,1), (0,1,1,2), (1,0,0,4), (1,1,0,0), (1,1,0,1), (1,1,0,2), (1,1,0,3), (1,1,0,4), (2,0,0,0), (2,0,0,1), (2,0,0,2), (2,0,0,4), (2,0,1,1), (2,0,1,2), (2,1,0,3), (2,1,0,4), (2,1,1,0), (2,1,1,4), (3,0,1,0), (3,0,1,4), (3,1,1,1), (3,1,1,2), (3,1,1,3)]

def czSurf : Surf :=
  { IJ := fun s i j k => czIJ.contains (s,i,j,k)
    IK := fun s i j k => czIK.contains (s,i,j,k)
    JK := fun s i j k => czJK.contains (s,i,j,k)
    JI := fun s i j k => czJI.contains (s,i,j,k)
    KI := fun s i j k => czKI.contains (s,i,j,k)
    KJ := fun s i j k => czKJ.contains (s,i,j,k) }

def czPorts : List Port := [⟨1, 0, 0, 5, 4⟩, ⟨0, 1, 0, 5, 4⟩, ⟨1, 0, 4, 5, 4⟩, ⟨0, 1, 4, 5, 4⟩]

def czFlows : List (List Pauli) :=
  let x := Pauli.X; let z := Pauli.Z; let o := Pauli.I
  [ [x,o,x,z], [z,o,z,o], [o,x,z,x], [o,z,o,z] ]

def czPaulis (s p : Nat) : Pauli := (czFlows.getD s []).getD p Pauli.I

/-- **★ THE CZ GATE (MIXED-BASIS MULTI-MERGE) IS FULLY-VERIFIED LATTICE
SURGERY ★** — the synthesized diagram passes the COMPLETE `LaSCorrectFull`
for all four CZ flows (X̄₁→X̄₁Z̄₂ etc.): validity + interior functionality +
the mixed-basis port boundary. -/
theorem czLaS_fully_correct :
    LaSCorrectFull czLaS czSurf czPorts czPaulis 4 = true := by native_decide

theorem czLaS_report_empty :
    LaSReport czLaS czSurf czPorts czPaulis 4 = [] := by native_decide

end FormalRV.QEC.LaSre
