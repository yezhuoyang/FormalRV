/-
  FormalRV.PauliRotation.Syntax
  ─────────────────────────────
  THE PAULI-ROTATION IR (John's directive, 2026-06-10) — the standard
  Litinski layer between the logical circuit IRs and the PPM program IR:

      circuit  ──compile──▶  Pauli rotations e^{-iθP},  θ ∈ ±{π, π/2, π/4, π/8}
               ──reorganize / group commuting rotations into PARALLEL layers──
               ──lower──▶  PPM programs (`PPM/Syntax/Program.lean`)

  A program here is a list of LAYERS; a layer is a list of rotations whose
  axes pairwise commute, so they are executable in parallel — the program
  length IS the parallel logical depth.  The angle dictionary (full-angle
  Litinski convention `P_θ = e^{-iθP}`):

      θ = π    : global phase −1 (droppable)
      θ = π/2  : the Pauli `P` itself, up to phase −i  (frame level)
      θ = π/4  : Clifford level (S = Z_{π/4}; H, CNOT = products of ±π/4)
      θ = π/8  : T level (T = Z_{π/8}) — the only non-Clifford, hence
                 `countPi8` IS the T-count

  Signs are necessary: `T†`/`S†` rotations appear in the standard CCZ
  seven-rotation phase polynomial and in the CNOT/H decompositions, so each
  rotation carries `neg`.  NO ancilla / syndrome qubits exist at this layer —
  rotations act on logical data qubits only (ancillas appear only when
  lowering π/8 rotations to PPM measurements).

  This file is the LEAF of the layer: it imports ONLY the sparse Pauli
  product syntax (`PPM/Syntax/Program.lean`, itself zero-import), so the
  `Resource/` counters may walk this tree (honest-resource discipline).
  Semantics: `Semantics.lean`; optimization rules: `Rules.lean`.
-/
import FormalRV.PPM.Syntax.Program

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog

/-! ## §1. Rotation angles. -/

/-- A discrete rotation angle `θ ∈ {π, π/2, π/4, π/8}` (full-angle Litinski
convention `e^{-iθP}`): `pi` = global phase, `piHalf` = Pauli level,
`piQuarter` = Clifford level, `piEighth` = T level (non-Clifford). -/
inductive RAngle where
  | pi | piHalf | piQuarter | piEighth
  deriving Repr, DecidableEq

/-- The angle in units of π/8 (for merge arithmetic: `pi` = 8, …, `piEighth`
= 1). -/
def RAngle.eighths : RAngle → Nat
  | .pi => 8 | .piHalf => 4 | .piQuarter => 2 | .piEighth => 1

/-! ## §2. Rotations, layers, programs. -/

/-- One Pauli-product rotation `e^{∓iθ·axis}` (`neg = true` is the `+i`
direction, i.e. angle `−θ`: `T† = Z_{−π/8}`).  The axis is a sparse
canonical Pauli product on the LOGICAL data qubits — no ancillas at this
layer. -/
structure Rot where
  neg   : Bool
  angle : RAngle
  axis  : PauliProduct
  deriving Repr, DecidableEq

/-- A PARALLEL layer: rotations whose axes pairwise commute (enforced by
`RotLayer.wf`), hence simultaneously executable.  One layer = one unit of
parallel logical depth. -/
abbrev RotLayer := List Rot

/-- A Pauli-rotation program: a sequence of parallel layers. -/
abbrev RotProg := List RotLayer

/-! ## §3. Commutation of sparse Pauli products (decidable, structural).

Two Pauli products commute iff the number of qubits where BOTH act with
DIFFERENT kinds is even.  The check is a structural `countP`, so it kernel-
evaluates (`decide` works on concrete layers). -/

/-- Does `f`'s qubit appear in `Q` with a different (anticommuting) kind? -/
def overlapMismatch (Q : PauliProduct) (f : PFactor) : Bool :=
  match Q.find? (fun g => g.qubit == f.qubit) with
  | some g => g.kind != f.kind
  | none   => false

/-- The number of anticommuting overlap positions between two products. -/
def acCount (P Q : PauliProduct) : Nat := P.countP (overlapMismatch Q)

/-- **Commutation test**: `P` and `Q` commute iff the anticommuting overlap
count is even. -/
def commF (P Q : PauliProduct) : Bool := acCount P Q % 2 == 0

/-! ## §4. Well-formedness (decidable). -/

/-- A rotation is well-formed when its axis is canonical and nonempty.
(`pi` rotations are also well-formed — they are global phases, removable by
the optimizer, but the compiler is allowed to emit them.) -/
def Rot.wf (r : Rot) : Bool := sortedStrict r.axis && !r.axis.isEmpty

/-- All ordered pairs in the layer commute (suffices: commutation of the
underlying products is symmetric). -/
def layerComm : RotLayer → Bool
  | []     => true
  | r :: t => t.all (fun s => commF r.axis s.axis) && layerComm t

/-- **Layer well-formedness**: every rotation well-formed, all axes pairwise
commuting — the layer is executable in parallel. -/
def RotLayer.wf (L : RotLayer) : Bool := L.all Rot.wf && layerComm L

/-- **Program well-formedness**: every layer well-formed. -/
def RotProg.wf (p : RotProg) : Bool := p.all RotLayer.wf

/-! ## §5. Space dimensions (the honest SPACE readouts). -/

/-- Quantum width of a rotation: the qubits its axis touches. -/
def Rot.width (r : Rot) : Nat := r.axis.width

/-- Quantum width of a layer. -/
def RotLayer.width : RotLayer → Nat
  | []     => 0
  | r :: t => max r.width (RotLayer.width t)

/-- **Quantum width** of a program: the number of logical qubits it touches.
There are no ancillas at this layer, so this is the DATA width. -/
def RotProg.width : RotProg → Nat
  | []     => 0
  | L :: p => max L.width (RotProg.width p)

/-! ## §6. Structural laws. -/

/-- Appending parallel layers: the result is pairwise-commuting iff both
parts are and every cross pair commutes. -/
theorem layerComm_append (L M : RotLayer) :
    layerComm (L ++ M) = true ↔
      (layerComm L = true ∧ layerComm M = true ∧
        ∀ r ∈ L, ∀ s ∈ M, commF r.axis s.axis = true) := by
  induction L with
  | nil => simp [layerComm]
  | cons r t ih =>
      simp only [List.cons_append, layerComm, Bool.and_eq_true,
        List.all_append, List.all_eq_true, ih, List.mem_cons]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
        refine ⟨⟨h1, h3⟩, h4, ?_⟩
        rintro r' (rfl | hr) s hs
        · exact h2 s hs
        · exact h5 r' hr s hs
      · rintro ⟨⟨h1, h3⟩, h4, h5⟩
        exact ⟨⟨h1, fun s hs => h5 r (.inl rfl) s hs⟩, h3, h4,
          fun r' hr s hs => h5 r' (.inr hr) s hs⟩

theorem RotProg.wf_append (p q : RotProg) :
    RotProg.wf (p ++ q) = (RotProg.wf p && RotProg.wf q) := by
  simp [RotProg.wf, List.all_append]

theorem RotProg.width_append (p q : RotProg) :
    RotProg.width (p ++ q) = max (RotProg.width p) (RotProg.width q) := by
  induction p with
  | nil => simp [RotProg.width]
  | cons L t ih =>
      show max L.width (RotProg.width (t ++ q)) = _
      rw [ih]
      show max L.width (max (RotProg.width t) (RotProg.width q))
          = max (max L.width (RotProg.width t)) (RotProg.width q)
      omega

/-! ## §7. Smoke checks (kernel-decidable). -/

-- X[0]X[1] vs Z[1]Z[2]: one anticommuting overlap (qubit 1) — anticommute.
example : commF [⟨0, .x⟩, ⟨1, .x⟩] [⟨1, .z⟩, ⟨2, .z⟩] = false := by decide
-- X[0]X[1] vs Z[0]Z[1]: two anticommuting overlaps — commute.
example : commF [⟨0, .x⟩, ⟨1, .x⟩] [⟨0, .z⟩, ⟨1, .z⟩] = true := by decide
-- Disjoint supports always commute.
example : commF [⟨0, .x⟩] [⟨5, .z⟩] = true := by decide
-- Same axis commutes with itself.
example : commF [⟨0, .x⟩, ⟨3, .z⟩] [⟨0, .x⟩, ⟨3, .z⟩] = true := by decide

-- A parallel layer of two disjoint T-level rotations is well-formed …
example : RotLayer.wf
    [⟨false, .piEighth, [⟨0, .z⟩]⟩, ⟨false, .piEighth, [⟨1, .z⟩]⟩] = true := by
  decide
-- … and so is the XX‖ZZ overlapping-but-commuting pair.
example : RotLayer.wf
    [⟨false, .piQuarter, [⟨0, .x⟩, ⟨1, .x⟩]⟩,
     ⟨true,  .piQuarter, [⟨0, .z⟩, ⟨1, .z⟩]⟩] = true := by decide
-- An anticommuting pair is NOT a parallel layer.
example : RotLayer.wf
    [⟨false, .piEighth, [⟨0, .x⟩]⟩, ⟨false, .piEighth, [⟨0, .z⟩]⟩] = false := by
  decide

example : RotProg.width
    [[⟨false, .piEighth, [⟨0, .z⟩, ⟨4, .x⟩]⟩], [⟨true, .pi, [⟨2, .y⟩]⟩]] = 5 := by
  decide

end FormalRV.PauliRotation
