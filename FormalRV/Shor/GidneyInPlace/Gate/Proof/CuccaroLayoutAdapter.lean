/-
  FormalRV.Shor.GidneyInPlace.CuccaroLayoutAdapter — the cuccaro decode-level uc_eval
  adapter, and the honest statement of the subregister-layout requirement.
  ════════════════════════════════════════════════════════════════════════════

  `GateAddConstBridge.uc_eval_eq_wrapShiftState` proves: a classical gate whose GLOBAL
  value permutation is `+c mod 2^dim` acts as `wrapShiftState c`.  The literal
  `cuccaro_addConstGate` does NOT satisfy this globally — its register is INTERLEAVED
  (`cuccaro_input_F`: target bit `i` at `q_start+2i+1`, read bit `i` at `q_start+2i+2`,
  carry at `q_start`), so the cuccaro TARGET value (`cuccaro_target_val`, reading the
  odd positions) is NOT the contiguous global `funbool` value.  The gate adds `c` to the
  target SUBregister while preserving the carry/read ancilla.

  THIS FILE PROVES the decode-level lift of the cuccaro correctness to the quantum
  (`uc_eval`) level — the foundation a full subregister adapter rests on:

    `cuccaro_addConst_uc_eval_adapter` : on the structured input basis state
      `f_to_vec (cuccaro_input_F q_start false 0 x)` (target `= x`, carry `= 0`,
      read `= 0`), the LITERAL `uc_eval (toUCom cuccaro_addConstGate c)` produces the
      basis state of the `applyNat` output, whose TARGET decodes to `(x+c) % 2^bits`.

  ⚠ THE REMAINING SUBREGISTER OBLIGATION (honest, NOT hidden).  To feed
  `GateAddConstBridge.uc_eval_addConst_cosetState` (which needs the gate to act as
  `addPerm` / `wrapShiftState` on the value the `cosetState` lives on), one needs a
  SUBREGISTER framework: `cosetState` on the cuccaro TARGET subregister (the interleaved
  odd positions), with the gate acting as `addPerm_on_target ⊗ id_ancilla`.  Concretely:
    (i)  a `layoutEmbed` : target value `v` + clean ancilla ↦ global basis index,
    (ii) `uc_eval(cuccaro) = layoutEmbed.symm ∘ addPerm_target c ∘ layoutEmbed` on the
         clean subspace (target `+c mod 2^bits`, carry/read restored, frame preserved).
  The cuccaro decode theorems (`cuccaro_addConstGate_target_decode` for `+c`,
  `cuccaro_addConstGate_read_decode` for read-restore) supply the per-basis content; the
  missing piece is the tensor/relabel structure that makes the INTERLEAVED target a
  contiguous value register the `cosetState` machinery indexes.  An alternative is a
  LAYOUT-RELABELING (a SWAP network à la `reverse_register_swap`) to a contiguous target,
  after which `GateAddConstBridge` applies directly.  Either is the genuine remaining
  circuit obligation — it is NOT a one-line corollary of the decode-level adapter.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroAddConst
import FormalRV.Arithmetic.Correctness

namespace FormalRV.BQAlgo

open FormalRV.Framework

/-- **THE CUCCARO DECODE-LEVEL `uc_eval` ADAPTER.**  On the structured input basis state
    (target `= x`, carry/read clean), the LITERAL `uc_eval (toUCom cuccaro_addConstGate)`
    action equals the basis state of the `applyNat` output, whose TARGET register decodes
    to `(x + c) % 2^bits`.  The bit-level cuccaro correctness lifted to the quantum level
    — the foundation of the subregister layout adapter (see file header). -/
theorem cuccaro_addConst_uc_eval_adapter (bits q_start c x dim : Nat)
    (hdim : q_start + 2 * bits + 1 ≤ dim) (hc : c < 2 ^ bits) :
    uc_eval (Gate.toUCom dim (cuccaro_addConstGate bits q_start c))
        * f_to_vec dim (cuccaro_input_F q_start false 0 x)
      = f_to_vec dim (Gate.applyNat (cuccaro_addConstGate bits q_start c)
          (cuccaro_input_F q_start false 0 x))
    ∧ cuccaro_target_val bits q_start
        (Gate.applyNat (cuccaro_addConstGate bits q_start c) (cuccaro_input_F q_start false 0 x))
      = (x + c) % 2 ^ bits :=
  ⟨uc_eval_toUCom_acts_on_basis dim (cuccaro_addConstGate bits q_start c)
      (cuccaro_addConstGate_wellTyped bits q_start c dim hdim) (cuccaro_input_F q_start false 0 x),
   cuccaro_addConstGate_target_decode bits q_start c x hc⟩

end FormalRV.BQAlgo
