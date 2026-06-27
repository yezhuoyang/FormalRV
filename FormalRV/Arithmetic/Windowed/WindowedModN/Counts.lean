/- WindowedModN — §12 exact Toffoli/T counts.
   Part of `WindowedModN` (the `WindowedModN.lean` shim re-exports all parts). -/
import FormalRV.Arithmetic.Windowed.WindowedModN.Fold

namespace FormalRV.Shor.WindowedCircuit
open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §12. Toffoli/T-counts (kernel-clean, exact).

Per window: four table reads (`4·14·w·2^w` T), one Cuccaro add (`14·bits`),
one constant compare (`14·bits`), one conditional subtract (`14·bits`), one
register-compare flag-uncompute (`14·bits`) — copies/prepares are T-free.
Versus the product-adder step (`28·w·2^w + 14·bits`), the per-window mod-N
reduction costs two extra table reads and three extra MAJ-chain passes. -/

private theorem tcount_targetComplement :
    ∀ (n q_start : Nat), tcount (targetComplement n q_start) = 0
  | 0, _ => rfl
  | n + 1, q_start => by
    show tcount (targetComplement n q_start) + tcount (Gate.X (q_start + 2 * n + 1)) = 0
    rw [tcount_targetComplement n q_start]
    rfl

private theorem tcount_majChain :
    ∀ (n q_start : Nat), tcount (cuccaro_maj_chain n q_start) = 7 * n
  | 0, _ => rfl
  | n + 1, q_start => by
    show tcount (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
        + tcount (cuccaro_maj_chain n (q_start + 2)) = 7 * (n + 1)
    rw [tcount_majChain n (q_start + 2)]
    show 7 + 7 * n = 7 * (n + 1)
    ring

private theorem tcount_majChainInv :
    ∀ (n q_start : Nat), tcount (cuccaro_maj_chain_inv n q_start) = 7 * n
  | 0, _ => rfl
  | n + 1, q_start => by
    show tcount (cuccaro_maj_chain_inv n (q_start + 2))
        + tcount (cuccaro_MAJ_inv q_start (q_start + 1) (q_start + 2)) = 7 * (n + 1)
    rw [tcount_majChainInv n (q_start + 2)]
    show 7 * n + 7 = 7 * (n + 1)
    ring

private theorem tcount_prep0 :
    ∀ (n q_start c : Nat), tcount (cuccaro_prepareConstRead n q_start c) = 0
  | 0, _, _ => rfl
  | n + 1, q_start, c => by
    show tcount (cuccaro_prepareConstRead n q_start c)
        + tcount (cond (c.testBit n) (Gate.X (q_start + 2 * n + 2)) Gate.I) = 0
    rw [tcount_prep0 n q_start c]
    cases c.testBit n <;> rfl

private theorem tcount_maskedPrep0 :
    ∀ (n q_start N flagPos : Nat),
      tcount (sqir_prepareMaskedConstRead n q_start N flagPos) = 0
  | 0, _, _, _ => rfl
  | n + 1, q_start, N, flagPos => by
    show tcount (sqir_prepareMaskedConstRead n q_start N flagPos)
        + tcount (cond (N.testBit n) (Gate.CX flagPos (q_start + 2 * n + 2)) Gate.I) = 0
    rw [tcount_maskedPrep0 n q_start N flagPos]
    cases N.testBit n <;> rfl

/-- The register-register comparator costs two MAJ-chain passes: `14·bits` T. -/
theorem tcount_regCompareXor (bits q_start flagPos : Nat) :
    tcount (regCompareXor bits q_start flagPos) = 14 * bits := by
  show tcount (targetComplement bits q_start)
      + (tcount (cuccaro_maj_chain bits q_start)
        + (tcount (Gate.CX (q_start + 2 * bits) flagPos)
          + (tcount (cuccaro_maj_chain_inv bits q_start)
            + tcount (targetComplement bits q_start)))) = 14 * bits
  rw [tcount_targetComplement, tcount_majChain, tcount_majChainInv]
  show 0 + (7 * bits + (0 + (7 * bits + 0))) = 14 * bits
  ring

private theorem tcount_compareConstC (bits q_start N flagPos : Nat) :
    tcount (sqir_style_compareConst_candidate bits q_start N flagPos) = 14 * bits := by
  show tcount (cuccaro_prepareConstRead bits q_start (2 ^ bits - N))
      + (tcount (cuccaro_maj_chain bits q_start)
        + (tcount (Gate.CX (q_start + 2 * bits) flagPos)
          + (tcount (cuccaro_maj_chain_inv bits q_start)
            + tcount (cuccaro_prepareConstRead bits q_start (2 ^ bits - N))))) = 14 * bits
  rw [tcount_prep0, tcount_majChain, tcount_majChainInv]
  show 0 + (7 * bits + (0 + (7 * bits + 0))) = 14 * bits
  ring

private theorem tcount_condSub (bits q_start N flagPos : Nat) :
    tcount (sqir_conditionalSubConstGate bits q_start N flagPos) = 14 * bits := by
  show tcount (sqir_prepareMaskedConstRead bits q_start (2 ^ bits - N) flagPos)
      + (tcount (cuccaro_n_bit_adder_full bits q_start)
        + tcount (sqir_prepareMaskedConstRead bits q_start (2 ^ bits - N) flagPos))
      = 14 * bits
  rw [tcount_maskedPrep0, tcount_cuccaro_n_bit_adder_full]
  ring

/-- The mod-N reduction (compare + conditional subtract): `28·bits` T. -/
theorem tcount_modNReduceFlag (bits q_start N flagPos : Nat) :
    tcount (modNReduceFlag bits q_start N flagPos) = 28 * bits := by
  show tcount (sqir_style_compareConst_candidate bits q_start N flagPos)
      + tcount (sqir_conditionalSubConstGate bits q_start N flagPos) = 28 * bits
  rw [tcount_compareConstC, tcount_condSub]
  ring

/-- One mod-N lookup-add: `56·w·2^w + 56·bits` T (four table reads, one add,
    one compare, one conditional subtract, one register-compare). -/
theorem tcount_modNLookupAddStep (w bits N : Nat) (T : Nat → Nat)
    (q_start flagPos : Nat) :
    tcount (modNLookupAddStep w bits N T q_start flagPos)
      = 56 * w * 2 ^ w + 56 * bits := by
  show tcount (lookupReadAt w (addendIdx q_start) bits T)
      + (tcount (cuccaro_n_bit_adder_full bits q_start)
        + (tcount (lookupReadAt w (addendIdx q_start) bits T)
          + (tcount (modNReduceFlag bits q_start N flagPos)
            + (tcount (lookupReadAt w (addendIdx q_start) bits T)
              + (tcount (regCompareXor bits q_start flagPos)
                + tcount (lookupReadAt w (addendIdx q_start) bits T))))))
      = 56 * w * 2 ^ w + 56 * bits
  rw [tcount_lookupReadAt, tcount_cuccaro_n_bit_adder_full, tcount_modNReduceFlag,
      tcount_regCompareXor]
  ring

/-- One mod-N window step: copies are T-free, so `56·w·2^w + 56·bits` T. -/
theorem tcount_windowedModNStep (w bits a N q_start yBase flagPos j : Nat) :
    tcount (windowedModNStep w bits a N q_start yBase flagPos j)
      = 56 * w * 2 ^ w + 56 * bits := by
  show tcount (copyWindow w yBase j)
      + (tcount (modNLookupAddStep w bits N (WindowedArith.tableValue a N w j)
          q_start flagPos)
        + tcount (copyWindow w yBase j)) = 56 * w * 2 ^ w + 56 * bits
  rw [tcount_copyWindow, tcount_modNLookupAddStep]
  ring

/-- **Closed-form T-count of the per-window mod-N windowed multiplier**:
    `numWin · (56·w·2^w + 56·bits)`. -/
theorem tcount_windowedModNMulCircuit (w bits a N numWin : Nat) :
    tcount (windowedModNMulCircuit w bits a N numWin)
      = numWin * (56 * w * 2 ^ w + 56 * bits) := by
  rw [windowedModNMulCircuit, windowedModNMul,
      tcount_foldl_seq_const
        (fun j => windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) j)
        (56 * w * 2 ^ w + 56 * bits)
        (fun j => tcount_windowedModNStep w bits a N (1 + 2 * w)
          (1 + 2 * w + (2 * bits + 1)) (1 + 2 * w + (2 * bits + 1) + numWin * w) j)]
  simp [tcount, List.length_range]


end FormalRV.Shor.WindowedCircuit
