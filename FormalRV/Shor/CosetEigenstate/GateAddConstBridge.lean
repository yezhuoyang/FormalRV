/-
  FormalRV.Shor.CosetEigenstate.GateAddConstBridge — the gate-connection layer: a
  classical gate whose VALUE permutation is `+c mod 2^bits` acts on `cosetState` as the
  abstract `wrapShiftState` / `shiftState`.
  ════════════════════════════════════════════════════════════════════════════

  The literal `cuccaro_addConstGate` adds `c` to the scratch register modulo `2^bits`
  (`cuccaro_addConstGate_target_decode : cuccaro_target_val (…) = (x+c) % 2^bits`).  In
  the value coordinatization, that gate's basis permutation IS the `+c mod 2^bits`
  permutation `addPerm`.  This file proves the bridge from the literal `uc_eval` action
  to the abstract `wrapShiftState` / `cosetState`-shift used by
  `CosetFoldWindowed.cosetState_windowedMul_embed_off`, via the already-proven
  `UCEvalBridge.uc_eval_eq_permState` (`uc_eval(toUCom g) = permState (gateToPerm g).symm`):

    * `addPerm dim c` — the `|i⟩ ↦ |(i+c) mod dim⟩` basis permutation.
    * `wrapShiftState_eq_permState` — `wrapShiftState c = permState (addPerm c).symm`
      (the wrapping add IS this permutation; Fin-arithmetic, de-risked via parallel
      verified attempts).
    * `uc_eval_eq_wrapShiftState` — for a classical gate with `gateToPerm g = addPerm c`,
      `uc_eval(toUCom g) · s = wrapShiftState c s` for EVERY state `s`.
    * `uc_eval_addConst_cosetState` — hence, under the per-window fit, the gate carries
      `cosetState N m k` to `cosetState N m (k+c)` (= `shiftState`, exactly the abstract
      step the windowed fold uses).

  ⚠ INSTANTIATION (flagged).  The hypothesis `gateToPerm g = addPerm (2^dim) c` is the
  VALUE-action condition — true of `cuccaro_addConstGate` only on its STRUCTURED layout
  (target register = the value, carry/read ancilla clean), via
  `cuccaro_addConstGate_target_decode`.  Discharging it for the literal interleaved
  cuccaro register requires the layout adapter (value-register ↔ cuccaro target decode);
  that layout-threading is the remaining circuit obligation.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.UCEvalBridge

namespace FormalRV.Shor.CosetEigenstate.GateAddConstBridge

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.CosetEigenstate.ApproxOp
  (wrapShiftState permState cosetState wrapShiftState_cosetState)
open FormalRV.Shor.CosetEigenstate.GatePerm (gateToPerm)
open FormalRV.Shor.CosetEigenstate.UCEvalBridge (uc_eval_eq_permState)

/-- A translation `+b` followed by its inverse `+(dim − b % dim)` (mod `dim`) is the
    identity on `i < dim`. -/
theorem add_sub_mod (dim b i : Nat) (hi : i < dim) :
    ((i + b) % dim + (dim - b % dim)) % dim = i := by
  have hpos : 0 < dim := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  have hbd : b % dim < dim := Nat.mod_lt _ hpos
  rw [Nat.mod_add_mod]
  have hdm := Nat.div_add_mod b dim
  have h1 : i + b + (dim - b % dim) = i + dim + dim * (b / dim) := by omega
  rw [h1, Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

/-- The inverse translation `+(dim − b % dim)` followed by `+b` (mod `dim`) is the
    identity on `i < dim`. -/
theorem sub_add_mod (dim b i : Nat) (hi : i < dim) :
    ((i + (dim - b % dim)) % dim + b) % dim = i := by
  have hpos : 0 < dim := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  have hbd : b % dim < dim := Nat.mod_lt _ hpos
  rw [Nat.mod_add_mod]
  have hdm := Nat.div_add_mod b dim
  have h1 : i + (dim - b % dim) + b = i + dim + dim * (b / dim) := by omega
  rw [h1, Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

/-- The `+c mod dim` basis permutation `|i⟩ ↦ |(i+c) mod dim⟩`.  Its `invFun` is the
    literal `+(dim − c)` translation `wrapShiftState` reads at (for `c < dim` the `toFun`
    shift reduces to `c`); valid for EVERY `c` (translation mod `dim` is a bijection). -/
def addPerm (dim c : Nat) : Equiv.Perm (Fin dim) where
  toFun i := ⟨((i : Nat) + (dim - (dim - c) % dim)) % dim,
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩
  invFun i := ⟨((i : Nat) + (dim - c)) % dim,
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩
  left_inv := fun i => Fin.ext (sub_add_mod dim (dim - c) i i.isLt)
  right_inv := fun i => Fin.ext (add_sub_mod dim (dim - c) i i.isLt)

/-- **The wrapping add IS the `addPerm` permutation.**  `wrapShiftState c = permState
    (addPerm c).symm` — the index `wrapShiftState` reads at is exactly `(addPerm c).symm`. -/
theorem wrapShiftState_eq_permState (dim c : Nat) (s : QState dim) :
    wrapShiftState dim c s = permState (addPerm dim c).symm s := by
  funext i z
  unfold wrapShiftState permState
  rw [Subsingleton.elim z 0]
  rfl

/-- **THE GATE → WRAPPING-ADD BRIDGE.**  For a classical gate `g` whose value
    permutation is `+c mod 2^dim` (`gateToPerm g = addPerm`), the literal SQIR action
    `uc_eval(toUCom g)` equals the abstract `wrapShiftState c` on EVERY state. -/
theorem uc_eval_eq_wrapShiftState (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g) (c : Nat)
    (hperm : gateToPerm g dim hwt = addPerm (2 ^ dim) c)
    (s : Matrix (Fin (2 ^ dim)) (Fin 1) ℂ) :
    Framework.uc_eval (Gate.toUCom dim g) * s = wrapShiftState (2 ^ dim) c s := by
  rw [uc_eval_eq_permState g dim hwt s, hperm, ← wrapShiftState_eq_permState]

/-- **THE GATE ACTS AS THE COSET SHIFT (off the fit).**  Under the per-window fit, the
    classical `+c` gate carries `cosetState N m k` to `cosetState N m (k+c)` — exactly
    the abstract `shiftState`/`addConst` step `cosetState_windowedMul_embed_off` folds. -/
theorem uc_eval_addConst_cosetState (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (c N m k : Nat) (hperm : gateToPerm g dim hwt = addPerm (2 ^ dim) c) (hN : 0 < N)
    (hfit : k + c + (2 ^ m - 1) * N < 2 ^ dim)
    (s : Matrix (Fin (2 ^ dim)) (Fin 1) ℂ) (hs : s = cosetState (2 ^ dim) N m k) :
    Framework.uc_eval (Gate.toUCom dim g) * s = cosetState (2 ^ dim) N m (k + c) := by
  rw [uc_eval_eq_wrapShiftState g dim hwt c hperm s, hs,
      wrapShiftState_cosetState (2 ^ dim) N m k c hN hfit]

end FormalRV.Shor.CosetEigenstate.GateAddConstBridge
