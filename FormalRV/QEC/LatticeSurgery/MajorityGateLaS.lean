/-
  FormalRV.QEC.LatticeSurgery.MajorityGateLaS
  -------------------------------------------
  The LaSsynth-synthesized majority-gate LaS, read VERBATIM from LaSsynth's
  output `results/majority_gate.lasre.json`: a 4x4x5 spacetime pipe diagram
  (13 I-, 21 J-, 18 K-pipes) AND its 9 correlation surfaces (the stabilizer
  flows that make it a majority gate).

  We prove BOTH levels for this REAL design:
    * `majorityLaS_valid`   -- STRUCTURAL well-formedness (rules c,d);
    * `majorityLaS_correct` -- FULL stabilizer-flow FUNCTIONALITY: the
      correlation surfaces pass the whole-grid functionality check for all 9
      flows (even-parity + Y-both-or-none), so the diagram realizes a majority
      gate, not merely a legal-looking pile of pipes.
  Several deliberately corrupted copies are REJECTED at each level.
  (Gidney's original buggy design lives only in the binary `maj.skp`.)
-/
import FormalRV.QEC.LatticeSurgery.LaSre
import FormalRV.QEC.LatticeSurgery.MajorityGate

namespace FormalRV.QEC.LaSre

/-! ## §1. Structure (verbatim from the .lasre.json). -/

def mgI : List (Nat × Nat × Nat) := [(0,1,0), (0,1,1), (1,1,0), (1,2,1), (1,2,2), (1,3,4), (2,1,4), (2,2,2), (2,2,3), (2,2,4), (2,3,0), (3,1,0), (3,1,1)]
def mgJ : List (Nat × Nat × Nat) := [(1,1,0), (1,1,2), (1,1,3), (1,2,0), (1,2,3), (1,3,2), (1,3,3), (1,3,4), (2,0,1), (2,1,0), (2,1,1), (2,1,2), (2,2,0), (2,2,1), (2,2,3), (2,2,4), (2,3,1), (3,1,0), (3,1,3), (3,2,3), (3,2,4)]
def mgK : List (Nat × Nat × Nat) := [(1,1,1), (1,1,2), (1,2,0), (1,3,0), (1,3,1), (2,1,2), (2,1,3), (2,3,1), (2,3,2), (3,1,1), (3,1,2), (3,1,3), (3,2,0), (3,2,1), (3,3,0), (3,3,1), (3,3,2), (3,3,3)]
def mgCI : List (Nat × Nat × Nat) := [(0,1,0), (0,1,1), (1,1,0), (2,2,3), (2,3,0), (3,1,0), (3,1,1)]
def mgCJ : List (Nat × Nat × Nat) := [(1,1,2), (1,1,3), (1,2,3), (1,3,2), (1,3,3), (1,3,4), (2,0,1), (2,1,1), (2,1,2), (2,2,1), (2,2,4), (2,3,1), (3,2,4)]

/-- **The LaSsynth majority-gate pipe diagram** (4x4x5). -/
def majorityLaS : LaSre :=
  { maxI := 4, maxJ := 4, maxK := 5,
    YCube  := fun _ _ _ => false,
    ExistI := fun i j k => mgI.contains (i, j, k),
    ExistJ := fun i j k => mgJ.contains (i, j, k),
    ExistK := fun i j k => mgK.contains (i, j, k),
    ColorI := fun i j k => mgCI.contains (i, j, k),
    ColorJ := fun i j k => mgCJ.contains (i, j, k) }

/-- **STRUCTURAL validity** of the real design (the weaker claim). -/
theorem majorityLaS_valid : majorityLaS.valid = true := by native_decide

theorem majorityLaS_pipe_counts :
    mgI.length = 13 ∧ mgJ.length = 21 ∧ mgK.length = 18 := by decide

/-! ## §2. The 9 correlation surfaces (verbatim) and FULL functionality. -/

def cIJ : List (Nat×Nat×Nat×Nat) := [(0,0,1,1), (0,2,1,4), (0,3,1,1), (1,1,2,1), (1,1,3,4), (1,2,2,4), (2,0,1,0), (2,0,1,1), (2,1,1,0), (2,2,1,4), (2,2,3,0), (2,3,1,1), (3,1,3,4), (3,2,2,4), (4,0,1,1), (4,3,1,0), (5,1,2,1), (5,1,2,2), (5,2,2,2), (5,2,2,3), (7,1,2,1), (7,2,2,3)]
def cIK : List (Nat×Nat×Nat×Nat) := [(0,1,2,2), (0,2,2,3), (1,1,1,0), (1,2,3,0), (2,1,2,1), (2,1,2,2), (2,1,3,4), (2,2,2,4), (3,0,1,0), (3,1,1,0), (3,2,3,0), (4,1,2,2), (4,2,2,2), (5,1,1,0), (5,2,1,4), (5,2,3,0), (5,3,1,0), (6,0,1,1), (7,1,1,0), (7,2,3,0), (7,3,1,1), (8,1,2,1)]
def cJK : List (Nat×Nat×Nat×Nat) := [(0,1,1,2), (0,1,1,3), (0,1,2,3), (0,1,3,3), (0,2,0,1), (0,2,1,1), (0,2,1,2), (0,2,2,1), (0,2,2,3), (0,2,3,1), (0,3,1,3), (1,1,1,0), (1,1,2,0), (1,1,3,2), (1,2,1,0), (1,2,2,0), (2,1,1,2), (2,1,1,3), (2,1,2,3), (2,1,3,3), (2,1,3,4), (2,2,0,1), (2,2,1,1), (2,2,1,2), (2,2,2,4), (2,3,1,3), (2,3,2,3), (2,3,2,4), (3,2,1,0), (3,2,2,0), (4,1,1,2), (4,1,1,3), (4,1,2,3), (4,1,3,3), (5,1,1,0), (5,1,2,0), (5,1,3,2), (5,2,1,0), (5,2,2,0), (5,3,1,0), (7,1,1,0), (7,1,2,0), (7,1,3,2), (7,2,1,0), (7,2,2,0), (8,2,0,1), (8,2,1,1)]
def cJI : List (Nat×Nat×Nat×Nat) := [(1,1,3,4), (1,2,0,1), (1,2,1,1), (1,2,2,1), (1,2,2,4), (1,2,3,1), (1,3,2,4), (2,1,1,0), (2,2,1,0), (2,2,2,0), (3,1,3,4), (3,2,2,4), (3,3,2,4), (4,3,1,0), (5,1,1,2), (5,1,1,3), (5,1,2,3), (5,1,3,3), (5,2,0,1), (5,2,1,1), (5,2,1,2), (5,2,2,1), (5,2,2,3), (5,3,1,3), (5,3,2,3), (6,1,1,3), (6,1,2,3), (6,1,3,3), (7,2,0,1), (7,2,1,1), (7,2,2,1), (7,2,2,3), (7,3,1,3), (7,3,2,3), (8,1,2,0), (8,1,3,2)]
def cKI : List (Nat×Nat×Nat×Nat) := [(1,3,3,0), (1,3,3,1), (1,3,3,2), (1,3,3,3), (2,1,2,0), (3,3,3,0), (3,3,3,1), (3,3,3,2), (3,3,3,3), (4,3,2,0), (4,3,2,1), (5,1,1,2), (5,2,1,2), (5,2,1,3), (5,2,3,1), (5,2,3,2), (5,3,1,3), (5,3,3,0), (5,3,3,1), (5,3,3,2), (6,1,1,1), (6,1,1,2), (7,2,3,1), (7,2,3,2), (7,3,1,1), (7,3,1,2), (7,3,3,0), (7,3,3,1), (7,3,3,2), (8,1,2,0), (8,1,3,0), (8,1,3,1)]
def cKJ : List (Nat×Nat×Nat×Nat) := [(0,1,1,1), (0,1,1,2), (0,2,1,2), (0,2,1,3), (0,2,3,1), (0,2,3,2), (0,3,1,1), (0,3,1,2), (0,3,1,3), (1,1,2,0), (1,1,3,0), (1,1,3,1), (2,1,1,1), (2,1,1,2), (2,2,1,2), (2,2,1,3), (2,3,1,1), (2,3,1,2), (2,3,1,3), (2,3,3,0), (2,3,3,1), (2,3,3,2), (2,3,3,3), (4,1,1,1), (4,1,1,2), (5,1,2,0), (5,1,3,0), (5,1,3,1), (5,3,2,0), (5,3,2,1), (7,1,2,0), (7,1,3,0), (7,1,3,1)]

/-- The synthesized correlation surfaces for all 9 stabilizer flows. -/
def majoritySurf : Surf :=
  { IJ := fun s i j k => cIJ.contains (s,i,j,k),
     IK := fun s i j k => cIK.contains (s,i,j,k),
     JK := fun s i j k => cJK.contains (s,i,j,k),
     JI := fun s i j k => cJI.contains (s,i,j,k),
     KI := fun s i j k => cKI.contains (s,i,j,k),
     KJ := fun s i j k => cKJ.contains (s,i,j,k) }

/-- **THE REAL MAJORITY GATE IS FULLY FUNCTIONALLY CORRECT** — its 9
correlation surfaces pass the whole-grid functionality check (even-parity at
every non-Y cube, for every stabilizer flow).  So the diagram provably
realizes the majority-gate stabilizer flows, not just a structurally legal
shape.  This is the STRONG claim (`LaSCorrect`), distinct from
`majorityLaS_valid`. -/
theorem majorityLaS_correct :
    LaSCorrect majorityLaS majoritySurf 9 = true := by native_decide

/-! ## §3. The verifiers have TEETH — corruptions are rejected. -/

/-- (Corruption 1: 3D corner) forcing an I-pipe at cube (1,2,0) — which has J
and K pipes — makes STRUCTURAL `valid` reject. -/
def majorityLaS_corner : LaSre :=
  { majorityLaS with
     ExistI := fun i j k => mgI.contains (i, j, k) || (i == 1 && j == 2 && k == 0) }
theorem corner_rejected : majorityLaS_corner.valid = false := by native_decide

/-- (Corruption 2: deleted pipe) removing the I-pipe at (0,1,0) breaks the
FUNCTIONALITY — the even-parity at an adjacent cube no longer holds, so
`LaSCorrect` rejects even though the structure may still pass validity. -/
def majorityLaS_delPipe : LaSre :=
  { majorityLaS with
     ExistI := fun i j k => mgI.contains (i, j, k) && !(i == 0 && j == 1 && k == 0) }
theorem delPipe_breaks_function :
    LaSCorrect majorityLaS_delPipe majoritySurf 9 = false := by native_decide

/-- (Corruption 3: flipped correlation surface) flipping ONE correlation piece
breaks the even-parity, so `LaSCorrect` rejects — the functionality check is
not vacuous in the surface either. -/
def majoritySurf_flip : Surf :=
  { majoritySurf with
     IJ := fun s i j k => cIJ.contains (s,i,j,k)
       != (s == 0 && i == 0 && j == 1 && k == 1) }
theorem flippedSurf_rejected :
    LaSCorrect majorityLaS majoritySurf_flip 9 = false := by native_decide

/-! ## §4. THE COMPLETE correctness — interior functionality + PORT BOUNDARY. -/

/-- The 9 ports: pipe cell + blue/red correlation selectors (computed from the
spec's port directions and z-basis, verified to hold on the real surfaces). -/
def majPorts : List Port :=
  [⟨2,3,1,3,2⟩, ⟨0,1,0,1,0⟩, ⟨1,3,4,3,2⟩, ⟨3,1,0,1,0⟩, ⟨0,1,1,1,0⟩,
   ⟨1,3,3,3,2⟩, ⟨3,1,1,1,0⟩, ⟨1,3,2,3,2⟩, ⟨2,0,1,3,2⟩]

/-- The Pauli of stabilizer `s` on port `p`, from the spec strings (`majFlows`). -/
def majPaulis (s p : Nat) : Pauli := (majFlows.getD s []).getD p Pauli.I

/-- **THE REAL MAJORITY GATE FULLY IMPLEMENTS ITS SPEC.**  `LaSCorrectFull` =
structural validity + the COMPLETE §4.4 functionality (even-parity b,
all-or-none c, Y-both-or-none d) + the PORT BOUNDARY (a) matching every
correlation surface to the spec's port Paulis, for all 9 stabilizer flows.
So the LaSsynth design provably implements a majority gate end-to-end — the
strong claim. -/
theorem majorityLaS_fully_correct :
    LaSCorrectFull majorityLaS majoritySurf majPorts majPaulis 9 = true := by
  native_decide

/-- (Corruption 4: wrong port connection) flipping the BLUE piece at port 0's
pipe cell breaks the port boundary, so `LaSCorrectFull` REJECTS it — the
spec-equality is genuinely enforced. -/
def majoritySurf_badPort : Surf :=
  { majoritySurf with
    JI := fun s i j k => cJI.contains (s,i,j,k)
      != (s == 0 && i == 2 && j == 3 && k == 1) }
theorem badPort_rejected :
    LaSCorrectFull majorityLaS majoritySurf_badPort majPorts majPaulis 9 = false := by
  native_decide

/-! ## §5. FAILURE LOCALIZATION on the real design. -/

/-- **The real majority gate has ZERO violations** — the localized report is
empty, equivalent to (and stronger than) `LaSCorrectFull = true`. -/
theorem majority_report_empty :
    LaSReport majorityLaS majoritySurf majPorts majPaulis 9 = [] := by native_decide

-- LOCALIZATION: a flipped correlation piece -> the EXACT failing
-- flow/cube/constraint (parity/orthogonal `Viol`s), not just `false`:
#eval LaSReport majorityLaS majoritySurf_flip majPorts majPaulis 9
-- a corrupted port -> the EXACT failing (flow, port) `Viol.port`:
#eval LaSReport majorityLaS majoritySurf_badPort majPorts majPaulis 9

end FormalRV.QEC.LaSre
