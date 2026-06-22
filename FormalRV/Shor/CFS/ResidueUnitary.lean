/-
  FormalRV.Shor.CFS.ResidueUnitary — the UNITARY (uc_eval) lift of the syntactic CFS residue circuit.

  `ResidueGate` gave the BOOLEAN basis action (`Gate.applyNat`) of the residue circuit.  This file
  lifts that to the UNITARY level — `uc_eval (Gate.toUCom dim …)` acting on the encoded basis state —
  by REUSING the SAME bridge the Standard-Shor success proof uses to connect a syntactic `Gate`
  sequence to its unitary semantics:

    * `uc_eval_toUCom_acts_on_basis` (Arithmetic/Correctness) — `uc_eval (Gate.toUCom dim g) · f_to_vec dim f
      = f_to_vec dim (Gate.applyNat g f)` for every well-typed `g` (the linearity lemma underneath
      `MultiplyCircuitProperty` / `ModMulImpl` in the textbook Shor pipeline);
    * `windowedModNMulGate_wellTyped` + `wellTyped_foldl_seq_range` (WindowedModNShor) — the residue
      chain (a `foldl` of well-typed in-place multiplies) is well-typed in any wide-enough dimension.

  Result: the residue circuit's UNITARY maps the clean encoded input basis state to the basis state
  whose result register holds the CFS residue `modexpProd g N m e mod pj` — the per-register oracle
  action at the `uc_eval` level, the same boundary the rest of the FormalRV Shor pipeline lives at.
  Kernel-clean.
-/
import FormalRV.Shor.CFS.ResidueGate
import FormalRV.Shor.WindowedModNShor
import FormalRV.Arithmetic.Correctness

namespace FormalRV.CFS

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open FormalRV.BQAlgo.WindowedModNShor

/-- The `n`-step in-place mod-`N` multiply chain is well-typed in any dimension wide enough to hold
    its register layout (the `foldl` of well-typed per-round multiplies). -/
theorem windowedModNMulInPlaceSeq_wellTyped (w bits N numWin : Nat) (as ainvs : Nat → Nat)
    (n dim : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) :
    Gate.WellTyped dim (windowedModNMulInPlaceSeq w bits N numWin as ainvs n) := by
  have h0 : 0 < dim := by omega
  exact wellTyped_foldl_seq_range
    (fun k => windowedModNMulInPlace w bits (as k) (ainvs k) N numWin) n dim h0
    (fun k _ => windowedModNMulGate_wellTyped w bits N numWin (as k) (ainvs k) dim hw hbits hdim)

/-- **The Gate → unitary lift for the residue chain.**  The unitary `uc_eval (Gate.toUCom dim …)`
    acts on every encoded basis state exactly as the Boolean circuit `Gate.applyNat` does — the same
    `uc_eval_toUCom_acts_on_basis` bridge the Standard-Shor `MultiplyCircuitProperty` pipeline uses. -/
theorem residueGate_uc_eval (w bits N numWin : Nat) (as ainvs : Nat → Nat) (n dim : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) (f : Nat → Bool) :
    uc_eval (Gate.toUCom dim (windowedModNMulInPlaceSeq w bits N numWin as ainvs n)) * f_to_vec dim f
      = f_to_vec dim (Gate.applyNat (windowedModNMulInPlaceSeq w bits N numWin as ainvs n) f) :=
  uc_eval_toUCom_acts_on_basis dim _
    (windowedModNMulInPlaceSeq_wellTyped w bits N numWin as ainvs n dim hw hbits hdim) f

/-- **THE UNITARY-LEVEL CFS RESIDUE COMPUTATION — one register.**  The residue circuit's UNITARY
    `uc_eval (Gate.toUCom dim residueGate)` maps the clean encoded input basis state to the basis
    state of its `Gate.applyNat` image, whose result register decodes to the CFS residue
    `modexpProd g N m e mod pj`.  Connects the actual gate SEQUENCE to its UNITARY SEMANTIC and the
    CFS residue spec — kernel-clean, all faces on the same syntactic circuit. -/
theorem residueGate_unitary_computes_residue (w bits numWin pj g N e m dim : Nat) (ainvs : Nat → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hpj1 : 1 < pj) (hpj2 : 2 * pj ≤ 2 ^ bits)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim)
    (hinv : ∀ k, k < m → ainvs k < pj ∧ residueConst g N pj e k * ainvs k % pj = 1) :
    uc_eval (Gate.toUCom dim
            (windowedModNMulInPlaceSeq w bits pj numWin (residueConst g N pj e) ainvs m))
          * f_to_vec dim (mulInputOf cuccaroAdder w bits numWin 1)
        = f_to_vec dim (Gate.applyNat
            (windowedModNMulInPlaceSeq w bits pj numWin (residueConst g N pj e) ainvs m)
            (mulInputOf cuccaroAdder w bits numWin 1))
    ∧ decodeReg (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits
        (Gate.applyNat (windowedModNMulInPlaceSeq w bits pj numWin (residueConst g N pj e) ainvs m)
          (mulInputOf cuccaroAdder w bits numWin 1))
        = modexpProd g N m e % pj :=
  ⟨residueGate_uc_eval w bits pj numWin (residueConst g N pj e) ainvs m dim hw hbits hdim _,
   (residueGate_verified w bits numWin pj g N e m ainvs hw hbits hpj1 hpj2 hinv).1⟩

end FormalRV.CFS
