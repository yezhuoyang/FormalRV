/-
  FormalRV.PauliRotation.Gadgets.CuccaroAdder
  ───────────────────────────────────────────
  THE CUCCARO–DKM RIPPLE-CARRY FAMILY, compiled to Pauli rotations through
  the verified pipeline (`GateBridge.lean`): the n-bit adder and its
  constant-arithmetic variants (add-const, sub-const, compare, the
  mod-reduce halves).

  Every gadget gets the uniform pair:
    • SYMBOLIC rotation T-count (all sizes/placements), by composing the
      generic `gateRotSchedule_countPi8 : countPi8 = Gate.tcount` with the
      family's existing anchored `tcount_*` theorem;
    • the optimizer-leg CORRECTNESS instance at a small concrete size
      (`gateRotSchedule_denote`, side conditions kernel-checked by `decide`).

  HONESTY: "correctness" = the parallel layers denote exactly the naive
  gate-by-gate rotation sequence; the dictionary leg (sequence = Gate
  unitary up to global phase) is the layer's known open item
  (`PauliRotation/README.md`).
-/
import FormalRV.PauliRotation.Compiler.GateBridge
import FormalRV.Arithmetic.Cuccaro.CuccaroAdderResource
import FormalRV.Arithmetic.Cuccaro.CuccaroVariantsResource

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource
open FormalRV.BQAlgo

/-! ## §1. The n-bit Cuccaro adder. -/

/-- The Cuccaro adder as a parallelized rotation program. -/
def cuccaroRot (bits q_start : Nat) : RotProg :=
  gateRotSchedule (cuccaro_n_bit_adder_full bits q_start)

/-- **Rotation T-count = `14·bits`**, all sizes and placements. -/
theorem cuccaroRot_countPi8 (bits q_start : Nat) :
    countPi8 (cuccaroRot bits q_start) = 14 * bits := by
  rw [cuccaroRot, gateRotSchedule_countPi8, cuccaro_adder_tcount]

/-- Correctness instance (4-bit adder on its own 9 qubits). -/
theorem cuccaroRot_denote_4 :
    RotProg.denote (width (cuccaro_n_bit_adder_full 4 0)) (cuccaroRot 4 0)
      = seqDenote _ (gateRots (cuccaro_n_bit_adder_full 4 0)) :=
  gateRotSchedule_denote _ _ (by decide) (Nat.le_refl _)

-- well-formed layers; 76 rotations parallelize into 20 layers (3.8×):
example : RotProg.wf (cuccaroRot 2 0) = true := by decide
example : (gateRots (cuccaro_n_bit_adder_full 2 0)).length = 76 := by decide
example : rotDepth (cuccaroRot 2 0) = 20 := by decide

/-! ## §2. Add-constant / subtract-constant. -/

/-- `target += c` as a parallelized rotation program. -/
def cuccaroAddConstRot (bits q_start c : Nat) : RotProg :=
  gateRotSchedule (cuccaro_addConstGate bits q_start c)

theorem cuccaroAddConstRot_countPi8 (bits q_start c : Nat) :
    countPi8 (cuccaroAddConstRot bits q_start c) = 14 * bits := by
  rw [cuccaroAddConstRot, gateRotSchedule_countPi8, tcount_cuccaro_addConstGate]

theorem cuccaroAddConstRot_denote_3 :
    RotProg.denote (width (cuccaro_addConstGate 3 0 5))
        (cuccaroAddConstRot 3 0 5)
      = seqDenote _ (gateRots (cuccaro_addConstGate 3 0 5)) :=
  gateRotSchedule_denote _ _ (by decide) (Nat.le_refl _)

/-- `target -= N` (two's-complement add) as a rotation program. -/
def cuccaroSubConstRot (bits q_start N : Nat) : RotProg :=
  gateRotSchedule (cuccaro_subConstGate bits q_start N)

theorem cuccaroSubConstRot_countPi8 (bits q_start N : Nat) :
    countPi8 (cuccaroSubConstRot bits q_start N) = 14 * bits := by
  rw [cuccaroSubConstRot, gateRotSchedule_countPi8, tcount_cuccaro_subConstGate]

/-! ## §3. Compare and the mod-reduce halves (forward-only / reverse-only). -/

/-- Constant comparison (forward MAJ chain only; flag at the top carry). -/
def cuccaroCompareRot (bits q_start N : Nat) : RotProg :=
  gateRotSchedule (cuccaro_compareConstForwardGate bits q_start N)

theorem cuccaroCompareRot_countPi8 (bits q_start N : Nat) :
    countPi8 (cuccaroCompareRot bits q_start N) = 7 * bits := by
  rw [cuccaroCompareRot, gateRotSchedule_countPi8,
      tcount_cuccaro_compareConstForwardGate]

/-- Forward-only subtract half (mod-reduce building block). -/
def cuccaroSubForwardRot (bits q_start N : Nat) : RotProg :=
  gateRotSchedule (cuccaro_subConstForwardOnlyGate bits q_start N)

theorem cuccaroSubForwardRot_countPi8 (bits q_start N : Nat) :
    countPi8 (cuccaroSubForwardRot bits q_start N) = 7 * bits := by
  rw [cuccaroSubForwardRot, gateRotSchedule_countPi8,
      tcount_cuccaro_subConstForwardOnlyGate]

/-- Reverse-only subtract half (mod-reduce building block). -/
def cuccaroSubReverseRot (bits q_start N : Nat) : RotProg :=
  gateRotSchedule (cuccaro_subConstReverseOnlyGate bits q_start N)

theorem cuccaroSubReverseRot_countPi8 (bits q_start N : Nat) :
    countPi8 (cuccaroSubReverseRot bits q_start N) = 7 * bits := by
  rw [cuccaroSubReverseRot, gateRotSchedule_countPi8,
      tcount_cuccaro_subConstReverseOnlyGate]

end FormalRV.PauliRotation
