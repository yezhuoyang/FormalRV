/-
  FormalRV.QEC.LatticeSurgery.CNOTFromLaSsynth
  --------------------------------------------
  **The CNOT lattice-surgery subroutine, SYNTHESIZED by LaSsynth and imported
  VERBATIM — a fully-verified MULTI-MERGE composition.**

  The single-merge gadgets (`GadgetToLaS`) cover single-basis joint
  measurements; a CNOT is a genuine MULTI-MERGE composition (a helper patch
  that I-merges with the control and J-merges with the target).  Its
  correlation surfaces span BOTH seams and must be solved together — the
  LaSsynth SAT problem.

  We ran LaSsynth (`docs/demo.ipynb` CNOT spec, `2x2x3`, ports
  `(c_in,t_in,c_out,t_out)`, stabilizers `Z.Z. / .ZZZ / X.XX / .X.X`, z3
  backend) and imported its output `cnot.lasre.json` VERBATIM: the pipe diagram
  (one I-pipe, one J-pipe, the worldlines, two inert Y-cubes) AND the four
  synthesized correlation surfaces.  LaSsynth's own Stim-ZX check already
  verified the stabilizers; here we INDEPENDENTLY re-verify the COMPLETE
  `LaSCorrectFull` in Lean — structural validity + interior functionality
  (even-parity, all-or-none, Y-both-or-none) + the port boundary matching the
  CNOT spec — and reject corruptions.

  (z_basis_direction `J` ⇒ the blue/`Z` piece is `KJ` and the red/`X` piece is
  `KI` at the ports, the I↔J flip from the `K`-z-basis memory convention.)
-/
import FormalRV.QEC.LatticeSurgery.LaSre

namespace FormalRV.QEC.LaSre

/-! ## §1. The synthesized CNOT pipe diagram (verbatim from cnot.lasre.json). -/

def cnI  : List (Nat × Nat × Nat) := [(0,0,1)]
def cnJ  : List (Nat × Nat × Nat) := [(0,0,2)]
def cnK  : List (Nat × Nat × Nat) := [(0,0,1), (0,1,0), (0,1,1), (0,1,2), (1,0,0), (1,0,1), (1,0,2)]
def cnCI : List (Nat × Nat × Nat) := [(0,0,1), (0,1,1), (0,1,2)]
def cnCJ : List (Nat × Nat × Nat) := [(0,0,2)]
def cnY  : List (Nat × Nat × Nat) := [(1,1,0), (1,1,2)]

/-- **The LaSsynth-synthesized CNOT pipe diagram** (2×2×3): control worldline
`(1,0,·)`, target `(0,1,·)`, a helper patch `(0,0)` that I-merges with the
control at `k=1` and J-merges with the target at `k=2`, plus two inert Y-cubes. -/
def cnotSynthLaS : LaSre :=
  { maxI := 2, maxJ := 2, maxK := 3
    YCube  := fun i j k => cnY.contains (i, j, k)
    ExistI := fun i j k => cnI.contains (i, j, k)
    ExistJ := fun i j k => cnJ.contains (i, j, k)
    ExistK := fun i j k => cnK.contains (i, j, k)
    ColorI := fun i j k => cnCI.contains (i, j, k)
    ColorJ := fun i j k => cnCJ.contains (i, j, k) }

/-- The CNOT diagram is STRUCTURALLY VALID (no 3D corner; the two Y-cubes carry
only — vacuously — K, no I/J). -/
theorem cnotSynth_valid : cnotSynthLaS.valid = true := by native_decide

/-! ## §2. The four synthesized correlation surfaces (verbatim). -/

def ccIJ : List (Nat × Nat × Nat × Nat) := [(0,0,1,1), (0,0,1,2), (1,0,0,1), (1,0,1,2), (2,0,0,2), (2,0,1,1), (3,0,1,2)]
def ccIK : List (Nat × Nat × Nat × Nat) := [(0,0,0,2), (0,0,1,2), (1,0,1,1), (1,0,1,2), (2,0,0,1), (2,0,0,2), (2,0,1,1), (3,0,1,1)]
def ccJK : List (Nat × Nat × Nat × Nat) := [(0,1,0,1), (1,0,0,2), (1,1,0,2), (2,1,0,2), (3,1,0,1), (3,1,0,2)]
def ccJI : List (Nat × Nat × Nat × Nat) := [(0,1,0,1), (0,1,0,2), (2,0,0,2)]
def ccKI : List (Nat × Nat × Nat × Nat) := [(0,0,0,0), (0,1,1,0), (0,1,1,1), (0,1,1,2), (1,0,0,0), (1,0,0,2), (1,1,1,0), (1,1,1,1), (1,1,1,2), (2,0,0,1), (2,0,0,2), (2,0,1,2), (2,1,0,0), (2,1,0,1), (2,1,0,2), (3,0,1,0), (3,0,1,1), (3,0,1,2), (3,1,1,0), (3,1,1,1), (3,1,1,2)]
def ccKJ : List (Nat × Nat × Nat × Nat) := [(0,0,0,0), (0,1,0,0), (0,1,0,1), (0,1,0,2), (0,1,1,0), (0,1,1,1), (0,1,1,2), (1,0,0,0), (1,0,0,1), (1,0,0,2), (1,0,1,0), (1,0,1,1), (1,0,1,2), (1,1,0,1), (1,1,0,2), (1,1,1,0), (1,1,1,1), (1,1,1,2), (2,0,0,2), (3,1,1,0), (3,1,1,1), (3,1,1,2)]

/-- The four synthesized correlation surfaces (one per CNOT stabilizer flow). -/
def cnotSynthSurf : Surf :=
  { IJ := fun s i j k => ccIJ.contains (s,i,j,k)
    IK := fun s i j k => ccIK.contains (s,i,j,k)
    JK := fun s i j k => ccJK.contains (s,i,j,k)
    JI := fun s i j k => ccJI.contains (s,i,j,k)
    KI := fun s i j k => ccKI.contains (s,i,j,k)
    KJ := fun s i j k => ccKJ.contains (s,i,j,k) }

/-! ## §3. Ports and the CNOT spec, and the COMPLETE correctness. -/

/-- The four K-pipe ports `(c_in, t_in, c_out, t_out)`.  `z_basis_direction = J`
⇒ blue(`Z`)=`KJ` (selector 5), red(`X`)=`KI` (selector 4). -/
def cnotPorts : List Port :=
  [⟨1, 0, 0, 5, 4⟩, ⟨0, 1, 0, 5, 4⟩, ⟨1, 0, 2, 5, 4⟩, ⟨0, 1, 2, 5, 4⟩]

/-- The four CNOT stabilizer flows (port order `c_in, t_in, c_out, t_out`):
`Z.Z.` (Z̄_c→Z̄_c), `.ZZZ` (Z̄_t→Z̄_cZ̄_t), `X.XX` (X̄_c→X̄_cX̄_t), `.X.X`
(X̄_t→X̄_t) — the CNOT Heisenberg table. -/
def cnotFlows : List (List Pauli) :=
  let x := Pauli.X; let z := Pauli.Z; let o := Pauli.I
  [ [z,o,z,o], [o,z,z,z], [x,o,x,x], [o,x,o,x] ]

def cnotPaulis (s p : Nat) : Pauli := (cnotFlows.getD s []).getD p Pauli.I

/-- **★ THE CNOT COMPILES TO FULLY-VERIFIED LATTICE SURGERY ★.**  The LaSsynth-
synthesized multi-merge composition passes the COMPLETE `LaSCorrectFull` in
Lean for all four CNOT stabilizer flows: structural validity + interior
functionality (even-parity b, all-or-none c, Y-both-or-none d) across BOTH
merge seams + the port boundary matching the CNOT Heisenberg table.  So the
composed surgery provably realizes a CNOT — an INDEPENDENT re-verification of
LaSsynth's Stim-ZX check, inside the same checker that caught the majority-gate
bug. -/
theorem cnotSynth_fully_correct :
    LaSCorrectFull cnotSynthLaS cnotSynthSurf cnotPorts cnotPaulis 4 = true := by
  native_decide

/-- The localized report is EMPTY (⇔ fully correct). -/
theorem cnotSynth_report_empty :
    LaSReport cnotSynthLaS cnotSynthSurf cnotPorts cnotPaulis 4 = [] := by native_decide

/-! ## §4. TEETH — corruptions of the composed CNOT are rejected. -/

/-- (Corruption: wrong CNOT direction) specifying the IDENTITY flows
(`Z̄_c→Z̄_c, Z̄_t→Z̄_t, X̄_c→X̄_c, X̄_t→X̄_t` — i.e. no cross-propagation) does NOT
match the synthesized surgery: the checker REJECTS, because the diagram really
implements the CROSS-coupling of a CNOT, not the identity. -/
def identityFlows : List (List Pauli) :=
  let x := Pauli.X; let z := Pauli.Z; let o := Pauli.I
  [ [z,o,z,o], [o,z,o,z], [x,o,x,o], [o,x,o,x] ]

def identityPaulis (s p : Nat) : Pauli := (identityFlows.getD s []).getD p Pauli.I

theorem cnot_not_identity :
    LaSCorrectFull cnotSynthLaS cnotSynthSurf cnotPorts identityPaulis 4 = false := by
  native_decide

/-- (Corruption: flipped surface piece) flipping one correlation piece breaks
the interior parity — REJECTED. -/
def cnotSynthSurf_flip : Surf :=
  { cnotSynthSurf with
    KJ := fun s i j k => ccKJ.contains (s,i,j,k) != (s == 0 && i == 1 && j == 0 && k == 0) }

theorem cnot_flip_rejected :
    LaSCorrectFull cnotSynthLaS cnotSynthSurf_flip cnotPorts cnotPaulis 4 = false := by
  native_decide

end FormalRV.QEC.LaSre
