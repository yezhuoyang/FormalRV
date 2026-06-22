/-
  FormalRV.QEC.LatticeSurgery.PauliFrame
  --------------------------------------
  **★ THE CLASSICAL PAULI FRAME — composes a NON-COMMUTING measurement sequence
  on top of the per-round flow certificates. ★**

  The cross-layer boundary (`CrossLayerHetero`): the single-round flow model
  (`LaSCorrectFull`) certifies each measurement gadget and COMMUTING cross-layer
  composition, but the NON-commuting case — a qubit `Z`-measured then `X`-measured
  — is genuinely outside it (the `X̄` membrane anticommutes with the measured `Z̄`).
  That case is handled CLASSICALLY: a Pauli FRAME, tracked in GF(2), records the
  byproduct operators and corrects each later measurement's outcome by its
  symplectic (anticommutation) inner product with the frame.

  Here the frame is a GF(2) symplectic vector (`x`/`z` parts over `ZMod 2`); the
  key facts are the SYMMETRY and BILINEARITY of the symplectic form (so byproduct
  corrections compose linearly — the essence of frame tracking), and the explicit
  resolution of the `Z`-then-`X` non-commuting round that the flow model could not
  thread.  This is the layer ABOVE the geometric checker, not inside it.
-/
import Mathlib

namespace FormalRV.QEC.PauliFrame

open Finset

/-- A Pauli operator (mod phase) on the qubit line: GF(2) `X`-support and
`Z`-support.  `mul` is the group operation (`I,X,Y,Z` mod phase). -/
structure P2 where
  x : Nat → ZMod 2
  z : Nat → ZMod 2

/-- Pauli product (mod phase) = componentwise GF(2) sum. -/
def mul (p q : P2) : P2 := ⟨fun i => p.x i + q.x i, fun i => p.z i + q.z i⟩

/-- The identity Pauli. -/
def one : P2 := ⟨fun _ => 0, fun _ => 0⟩

/-- **The symplectic (anticommutation) inner product** over `n` qubits: `0` iff the
two Paulis COMMUTE, `1` iff they ANTICOMMUTE. -/
def symp (n : Nat) (p q : P2) : ZMod 2 :=
  ∑ i ∈ range n, (p.x i * q.z i + p.z i * q.x i)

/-! ## §1. The symplectic form is symmetric and BILINEAR (corrections add). -/

theorem symp_comm (n : Nat) (p q : P2) : symp n p q = symp n q p := by
  unfold symp; apply Finset.sum_congr rfl; intro i _; ring

/-- **★ BILINEARITY (left) ★** — the correction for a frame `mul a b` is the SUM of
the corrections for `a` and `b`.  This is why byproduct corrections COMPOSE
linearly in GF(2) — the algebraic heart of Pauli-frame tracking. -/
theorem symp_mul_left (n : Nat) (a b c : P2) :
    symp n (mul a b) c = symp n a c + symp n b c := by
  unfold symp mul
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

theorem symp_mul_right (n : Nat) (a b c : P2) :
    symp n a (mul b c) = symp n a b + symp n a c := by
  unfold symp mul
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

theorem symp_one_left (n : Nat) (p : P2) : symp n one p = 0 := by
  unfold symp one; simp

/-! ## §2. The frame-corrected outcome, and its linear composition. -/

/-- The reported outcome of measuring `meas` corrected for the frame: flip iff the
frame ANTICOMMUTES with the measured Pauli. -/
def corrected (n : Nat) (frame meas : P2) (raw : ZMod 2) : ZMod 2 := raw + symp n frame meas

/-- **★ FRAME CORRECTIONS COMPOSE ★** — accumulating two byproducts `F1,F2` into
the frame applies each one's correction in turn (`symp_mul_left`).  So a whole
sequence of byproducts collapses to one symplectic correction. -/
theorem corrected_mul (n : Nat) (F1 F2 meas : P2) (raw : ZMod 2) :
    corrected n (mul F1 F2) meas raw = corrected n F1 meas (corrected n F2 meas raw) := by
  unfold corrected
  rw [symp_mul_left]; ring

theorem corrected_one (n : Nat) (meas : P2) (raw : ZMod 2) :
    corrected n one meas raw = raw := by
  unfold corrected; rw [symp_one_left]; ring

/-! ## §3. The single-qubit Paulis, and the NON-COMMUTING resolution. -/

/-- `Z̄` on qubit `q`. -/
def Zq (q : Nat) : P2 := ⟨fun _ => 0, fun i => if i = q then 1 else 0⟩
/-- `X̄` on qubit `q`. -/
def Xq (q : Nat) : P2 := ⟨fun i => if i = q then 1 else 0, fun _ => 0⟩

/-- **★ `Z̄_q` AND `X̄_q` ANTICOMMUTE ★** — the exact obstruction that blocked the
flow model from threading an `X`-readout below a `Z`-merge on the same qubit. -/
theorem Z_X_anticommute (n q : Nat) (h : q < n) : symp n (Zq q) (Xq q) = 1 := by
  unfold symp Zq Xq
  rw [Finset.sum_eq_single q]
  · simp
  · intro b _ hb; simp [hb]
  · intro hq; simp at hq; omega

/-- ...but on DIFFERENT qubits they COMMUTE (so the flow model handled THAT case). -/
theorem Z_X_commute_diff (n q q' : Nat) (hne : q ≠ q') : symp n (Zq q) (Xq q') = 0 := by
  unfold symp Zq Xq
  apply Finset.sum_eq_zero
  intro i _
  by_cases h1 : i = q <;> by_cases h2 : i = q' <;> simp_all

/-- **★ THE NON-COMMUTING ROUND, RESOLVED CLASSICALLY ★** — measure `Z̄_q` (round 1,
producing a `Z`-byproduct in the frame), then `X̄_q` (round 2).  The flow model
could not thread this.  The classical frame DOES: the `X̄_q` outcome is FLIPPED by
the `Z`-byproduct (`+1`), exactly because `Z̄_q` and `X̄_q` anticommute.  So the
sequence composes — the correction the flow checker could not see is supplied
here. -/
theorem nonCommuting_round_resolved (n q : Nat) (h : q < n) (raw : ZMod 2) :
    corrected n (Zq q) (Xq q) raw = raw + 1 := by
  unfold corrected; rw [Z_X_anticommute n q h]

/-- ...and a byproduct on a DIFFERENT qubit leaves the `X̄_q` outcome UNCHANGED — the
frame only corrects where it genuinely anticommutes. -/
theorem commuting_round_no_correction (n q q' : Nat) (hne : q ≠ q') (raw : ZMod 2) :
    corrected n (Zq q') (Xq q) raw = raw := by
  unfold corrected
  rw [Z_X_commute_diff n q' q (fun h => hne h.symm)]; ring

/-! ## §4. A measurement SEQUENCE with frame tracking. -/

/-- Accumulate a list of byproduct Paulis into one frame (their product). -/
def frameOf : List P2 → P2
  | []      => one
  | f :: fs => mul f (frameOf fs)

/-- **★ A SEQUENCE OF BYPRODUCTS COLLAPSES TO ONE SYMPLECTIC CORRECTION ★** — the
correction a measurement `meas` receives from a whole list of accumulated
byproducts is the GF(2) SUM of each byproduct's anticommutation with `meas`.  So a
non-commuting measurement sequence of any length composes into one classical
correction per round — the Pauli-frame layer is linear and well-defined. -/
theorem symp_frameOf (n : Nat) (fs : List P2) (meas : P2) :
    symp n (frameOf fs) meas = (fs.map (fun f => symp n f meas)).foldr (· + ·) 0 := by
  induction fs with
  | nil => simp [frameOf, symp_one_left]
  | cons f fs ih => simp only [frameOf, List.map_cons, List.foldr_cons]; rw [symp_mul_left, ih]

end FormalRV.QEC.PauliFrame
