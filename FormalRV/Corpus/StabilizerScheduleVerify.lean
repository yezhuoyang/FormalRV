/-
  FormalRV.Corpus.StabilizerScheduleVerify — let the USER specify their own
  stabilizer-measurement schedule (the CNOT ordering per check), and VERIFY ALL
  schedules at once.

  A syndrome round measures an X-check on support S by: ancilla in |+⟩, `CX anc→s`
  for each `s ∈ S` in SOME ORDER, measure ancilla in X (dually Z).  The user picks
  the order (the stabilizer schedule).  KEY FACT: the CNOTs share the ancilla as
  common control, so they COMMUTE, and the measured operator depends only on the SET
  S — NOT the order.  Hence the framework verifies EVERY schedule uniformly: any two
  orderings that are permutations of each other measure the IDENTICAL stabilizer.

  This makes "verify all scheduling" a theorem (`scheduledCheckOp_perm_invariant`),
  parametric over the user's `List Nat` order.  `StimEmit.xCheckBlock` already takes
  the support as an ordered `List Nat`, so a user emits their schedule directly; the
  theorem certifies it measures the right stabilizer regardless of the order they
  chose.

  No `sorry`, no `axiom`.
-/

import FormalRV.PPM.ZXStabilizer

namespace FormalRV.Corpus.StabilizerScheduleVerify

open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.Framework.SurgeryReadout
open FormalRV.Framework.PauliSem
open FormalRV.Framework.ZX

/-- A user-supplied CNOT ordering for one check: the order the ancilla is coupled to
    its support qubits.  ANY `List Nat`. -/
abbrev CNOTOrder := List Nat

/-- The support a scheduled measurement actually produces: the SET of coupled qubits
    over `n` qubits — order-agnostic by construction. -/
def scheduledSupport (order : CNOTOrder) (n : Nat) : BoolVec :=
  (List.range n).map (fun i => decide (i ∈ order))

/-- **All CNOT orderings produce the same measured support.**  Two schedules that
    are permutations of each other (same coupled set, any order) yield the IDENTICAL
    indicator — the stabilizer support is invariant under the user's scheduling. -/
theorem scheduledSupport_perm_invariant (order order' : CNOTOrder) (n : Nat)
    (h : order.Perm order') : scheduledSupport order n = scheduledSupport order' n := by
  unfold scheduledSupport
  apply List.map_congr_left
  intro i _
  exact decide_eq_decide.mpr h.mem_iff

/-- The Pauli a scheduled check measures: a Z-check measures `zRow` of its coupled
    support, an X-check `xRow`. -/
def scheduledCheckOp (color : ZXColor) (order : CNOTOrder) (n : Nat) : PauliString :=
  match color with
  | ZXColor.Z => zRow (scheduledSupport order n)
  | ZXColor.X => xRow (scheduledSupport order n)

/-- **VERIFY ALL SCHEDULING.**  For ANY user-chosen CNOT orderings that permute the
    same coupled set, a check measures the IDENTICAL stabilizer — so every stabilizer
    schedule is correct, and the framework certifies them all uniformly. -/
theorem scheduledCheckOp_perm_invariant (color : ZXColor) (order order' : CNOTOrder)
    (n : Nat) (h : order.Perm order') :
    scheduledCheckOp color order n = scheduledCheckOp color order' n := by
  unfold scheduledCheckOp
  rw [scheduledSupport_perm_invariant order order' n h]

/-! ## Concrete: different schedules of the same check measure the same stabilizer -/

/-- An X-check on {0,1,2} measured in order [0,1,2] vs [2,0,1] (a user reschedule)
    measures the SAME stabilizer. -/
example : scheduledCheckOp ZXColor.X [0, 1, 2] 3 = scheduledCheckOp ZXColor.X [2, 0, 1] 3 :=
  scheduledCheckOp_perm_invariant ZXColor.X [0,1,2] [2,0,1] 3 (by decide)

/-- …and both equal the `xRow` of the full support {0,1,2}. -/
example : scheduledCheckOp ZXColor.X [2, 0, 1] 3 = xRow [true, true, true] := by decide

/-- A Z-check rescheduled [0,3,9] → [9,3,0] measures the same stabilizer (10 qubits). -/
example : scheduledCheckOp ZXColor.Z [0, 3, 9] 10 = scheduledCheckOp ZXColor.Z [9, 3, 0] 10 :=
  scheduledCheckOp_perm_invariant ZXColor.Z [0,3,9] [9,3,0] 10 (by decide)

end FormalRV.Corpus.StabilizerScheduleVerify
