/-
  FormalRV.QEC.LatticeSurgery.HFromLaSsynth
  -----------------------------------------
  **The Hadamard gate (a surface-code PATCH ROTATION) — LaSsynth-
  synthesized, imported verbatim, re-verified in Lean.**

  H swaps X̄↔Z̄, realized as a patch rotation that SWAPS the X and Z
  boundaries — so the OUTPUT port's blue/red planes are FLIPPED relative to
  the input (z_basis_direction J at the input, I at the output).  Spec
  stabilizers `XZ` (X̄→Z̄) and `ZX` (Z̄→X̄); z3-synthesized, re-checked by
  `LaSCorrectFull`.
-/
import FormalRV.QEC.LatticeSurgery.LaSre

namespace FormalRV.QEC.LaSre

def hI  : List (Nat × Nat × Nat) := [(0,0,1), (0,1,0), (0,1,2)]
def hJ  : List (Nat × Nat × Nat) := [(1,0,0), (1,0,2)]
def hK  : List (Nat × Nat × Nat) := [(0,0,0), (0,0,1), (0,0,2), (0,1,0), (0,1,1), (1,0,0), (1,0,1)]
def hCI : List (Nat × Nat × Nat) := [(0,0,1), (0,1,0)]
def hCJ : List (Nat × Nat × Nat) := [(0,0,2), (1,0,1), (1,0,2)]
def hY  : List (Nat × Nat × Nat) := []

/-- The LaSsynth-synthesized Hadamard pipe diagram. -/
def hLaS : LaSre :=
  { maxI := 2, maxJ := 2, maxK := 3
    YCube  := fun i j k => hY.contains (i, j, k)
    ExistI := fun i j k => hI.contains (i, j, k)
    ExistJ := fun i j k => hJ.contains (i, j, k)
    ExistK := fun i j k => hK.contains (i, j, k)
    ColorI := fun i j k => hCI.contains (i, j, k)
    ColorJ := fun i j k => hCJ.contains (i, j, k) }

theorem hLaS_valid : hLaS.valid = true := by native_decide

def hIJ : List (Nat × Nat × Nat × Nat) := [(0,0,1,0), (0,0,1,2), (1,0,1,1)]
def hIK : List (Nat × Nat × Nat × Nat) := [(0,0,0,1), (0,0,1,0), (0,0,1,2), (1,0,1,0), (1,0,1,2)]
def hJK : List (Nat × Nat × Nat × Nat) := [(0,1,0,0), (0,1,0,2), (1,1,0,0), (1,1,0,2)]
def hJI : List (Nat × Nat × Nat × Nat) := [(0,1,0,0), (0,1,0,2)]
def hKI : List (Nat × Nat × Nat × Nat) := [(0,0,0,0), (0,0,0,1), (0,0,0,2), (0,0,1,0), (0,0,1,1), (0,1,0,0), (0,1,0,1), (1,0,1,0), (1,0,1,1), (1,0,1,2), (1,1,1,0)]
def hKJ : List (Nat × Nat × Nat × Nat) := [(0,0,1,0), (0,0,1,1), (0,1,0,0), (0,1,0,1), (1,0,0,0), (1,0,0,1), (1,0,0,2), (1,0,1,2), (1,1,0,0), (1,1,0,1)]

def hSurf : Surf :=
  { IJ := fun s i j k => hIJ.contains (s,i,j,k)
    IK := fun s i j k => hIK.contains (s,i,j,k)
    JK := fun s i j k => hJK.contains (s,i,j,k)
    JI := fun s i j k => hJI.contains (s,i,j,k)
    KI := fun s i j k => hKI.contains (s,i,j,k)
    KJ := fun s i j k => hKJ.contains (s,i,j,k) }

/-- Input port (z_basis J): blue=KJ(5), red=KI(4).  OUTPUT port (z_basis I,
the rotated patch): blue=KI(4), red=KJ(5) — the boundary swap H performs. -/
def hPorts : List Port := [⟨0, 0, 0, 5, 4⟩, ⟨0, 0, 2, 4, 5⟩]

def hFlows : List (List Pauli) :=
  let x := Pauli.X; let z := Pauli.Z
  [ [x,z], [z,x] ]

def hPaulis (s p : Nat) : Pauli := (hFlows.getD s []).getD p Pauli.I

/-- **★ THE HADAMARD GATE IS FULLY-VERIFIED LATTICE SURGERY ★** — the
synthesized patch-rotation diagram passes the COMPLETE `LaSCorrectFull` for
both flows X̄→Z̄ and Z̄→X̄, with the FLIPPED output-port boundary the rotation
produces. -/
theorem hLaS_fully_correct :
    LaSCorrectFull hLaS hSurf hPorts hPaulis 2 = true := by native_decide

theorem hLaS_report_empty :
    LaSReport hLaS hSurf hPorts hPaulis 2 = [] := by native_decide

end FormalRV.QEC.LaSre
