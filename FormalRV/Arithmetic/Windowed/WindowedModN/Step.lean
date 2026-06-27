/- WindowedModN — §7 per-window mod-N lookup-add step + full circuit.
   Part of `WindowedModN` (the `WindowedModN.lean` shim re-exports all parts). -/
import FormalRV.Arithmetic.Windowed.WindowedModN.Reduction

namespace FormalRV.Shor.WindowedCircuit
open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §7. The per-window mod-N lookup-add step and the full circuit.

Layout (Cuccaro, exactly the product-adder multiplier's layout plus one flag):
`ctrl = 0`; address bits `1,3,…,2w−1`; AND-ancillas `2,4,…,2w`;
Cuccaro block at `q_start = 1+2w` (carry-in, then interleaved acc/addend up
to `q_start + 2·bits`); `y`-register at `yBase = q_start + 2·bits + 1`;
the comparison flag at `flagPos = yBase + numWin·w` (one fresh qubit above
the `y`-register — clean in `mulInputOf`). -/

/-- One mod-N lookup-ADD: `acc ← (acc + T[v]) mod N` for the table row
    selected by the address register (Gidney l.296 with per-window
    reduction).  The Cuccaro comparator borrows the addend register for its
    two's-complement constant, so the QROM word is cleared before the
    reduction and re-read for the flag-uncompute register-compare. -/
def modNLookupAddStep (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat) : Gate :=
  Gate.seq (lookupReadAt w (addendIdx q_start) bits T)
    (Gate.seq (cuccaro_n_bit_adder_full bits q_start)
      (Gate.seq (lookupReadAt w (addendIdx q_start) bits T)
        (Gate.seq (modNReduceFlag bits q_start N flagPos)
          (Gate.seq (lookupReadAt w (addendIdx q_start) bits T)
            (Gate.seq (regCompareXor bits q_start flagPos)
              (lookupReadAt w (addendIdx q_start) bits T))))))

/-- One mod-N window step: copy window `j` into the address register,
    mod-N lookup-add the entry `T_j[v] = a·(2^w)^j·v mod N`, uncopy. -/
def windowedModNStep (w bits a N q_start yBase flagPos j : Nat) : Gate :=
  Gate.seq (copyWindow w yBase j)
    (Gate.seq (modNLookupAddStep w bits N (WindowedArith.tableValue a N w j)
                q_start flagPos)
      (copyWindow w yBase j))

/-- The per-window mod-N windowed multiplier: a fold of mod-N window steps. -/
def windowedModNMul (w bits a N q_start yBase flagPos numWin : Nat) : Gate :=
  (List.range numWin).foldl
    (fun g j => Gate.seq g (windowedModNStep w bits a N q_start yBase flagPos j))
    Gate.I

/-- **The full per-window mod-N windowed-multiplier circuit** at the standard
    layout (flag above the `y`-register).  On `acc = 0` it leaves
    `(a·y) mod N` in the accumulator. -/
def windowedModNMulCircuit (w bits a N numWin : Nat) : Gate :=
  windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
    (1 + 2 * w + (2 * bits + 1) + numWin * w) numWin


end FormalRV.Shor.WindowedCircuit
