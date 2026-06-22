/-
  FormalRV.Shor.CFS.ResidueGateAt — the BASE-PARAMETRIC residue circuit, verified at ANY base.

  `residueGate_verified` proves the residue circuit correct at base 0.  Placing |P| residue registers
  in one wide circuit needs the SAME gate at disjoint bases `b = j·width`.  Rather than re-derive the
  windowed multiplier's correctness generically in its layout parameters (a large re-proof), we REUSE
  base 0 via `GateShift`: `residueGateAt b = shiftGate b residueGate`, and TRANSPORT both faces:

    * SEMANTIC — `applyNat (shiftGate b g)` at a `+b`-shifted index equals `g` on the down-shifted
      register (`applyNat_shiftGate_at`); pushed through `decodeReg` (via `decodeReg_congr`), the
      base-`b` accumulator reads the same residue `modexpProd % pj` as base 0.
    * RESOURCE — relabeling preserves the count (`tcount_shiftGate`), so the Toffoli count is unchanged.

  This is the base-parametric unlock for the CFS |P|-register fold.  Kernel-clean.
-/
import FormalRV.Shor.CFS.ResidueGate
import FormalRV.Arithmetic.GateShift
import FormalRV.Arithmetic.Adder.ContiguousTransport

namespace FormalRV.CFS

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open FormalRV.Arithmetic (shiftGate applyNat_shiftGate_at tcount_shiftGate)

/-- The residue circuit placed at base `b` (its register block occupies qubits `[b, b+width)`). -/
def residueGateAt (b w bits numWin pj : Nat) (cs cinvs : Nat → Nat) (m : Nat) : Gate :=
  shiftGate b (windowedModNMulInPlaceSeq w bits pj numWin cs cinvs m)

/-- **The base-parametric residue gate, verified — semantic + resource at ANY base `b`.**  Given the
    register block at base `b` holds the clean encoded input (`hF`), the accumulator (read at the
    `+b`-shifted result indices) decodes to the CFS residue `modexpProd g N m e mod pj`, and the
    Toffoli count is the same `m·numWin·(16·w·2^w + 16·bits)` as at base 0.  Both transported from
    `residueGate_verified` through the `GateShift` relabeling. -/
theorem residueGateAt_verified (b w bits numWin pj g N e m : Nat) (ainvs : Nat → Nat) (F : Nat → Bool)
    (hw : 0 < w) (hbits : numWin * w = bits) (hpj1 : 1 < pj) (hpj2 : 2 * pj ≤ 2 ^ bits)
    (hinv : ∀ k, k < m → ainvs k < pj ∧ residueConst g N pj e k * ainvs k % pj = 1)
    (hF : ∀ j, F (j + b) = mulInputOf cuccaroAdder w bits numWin 1 j) :
    decodeReg (fun i => b + (1 + 2 * w + (2 * bits + 1) + i)) bits
        (Gate.applyNat (residueGateAt b w bits numWin pj (residueConst g N pj e) ainvs m) F)
        = modexpProd g N m e % pj
    ∧ toffoliCount (residueGateAt b w bits numWin pj (residueConst g N pj e) ainvs m)
        = m * numWin * (16 * w * 2 ^ w + 16 * bits) := by
  have hbase := residueGate_verified w bits numWin pj g N e m ainvs hw hbits hpj1 hpj2 hinv
  set G := windowedModNMulInPlaceSeq w bits pj numWin (residueConst g N pj e) ainvs m with hG
  have hkey : ∀ i, Gate.applyNat (shiftGate b G) F (b + (1 + 2 * w + (2 * bits + 1) + i))
      = Gate.applyNat G (fun j => F (j + b)) (1 + 2 * w + (2 * bits + 1) + i) := by
    intro i
    rw [Nat.add_comm b (1 + 2 * w + (2 * bits + 1) + i)]
    exact applyNat_shiftGate_at b G F (1 + 2 * w + (2 * bits + 1) + i)
  refine ⟨?_, ?_⟩
  · unfold residueGateAt
    rw [← hG, decodeReg_congr (fun i => b + (1 + 2 * w + (2 * bits + 1) + i))
          (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits
          (Gate.applyNat (shiftGate b G) F)
          (Gate.applyNat G (fun j => F (j + b)))
          (fun i _ => hkey i)]
    rw [show (fun j => F (j + b)) = mulInputOf cuccaroAdder w bits numWin 1 from funext hF]
    exact hbase.1
  · unfold residueGateAt
    rw [← hG, toffoliCount, tcount_shiftGate]
    exact hbase.2

end FormalRV.CFS
