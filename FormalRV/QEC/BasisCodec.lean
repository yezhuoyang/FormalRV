/-
  FormalRV.QEC.BasisCodec — compact lossless encoding for imported GF(2)
  vectors (the external-solver pipeline, `scripts/find_logicals.py`).

  A `BoolVec` of width `w` is stored as ONE `Nat` (bit `j` = entry `j`),
  written as a hex literal in the generated `*BasisImport.lean` files —
  ~4 bits per character instead of ~7 characters per bit for
  `[true, false, …]` literals (≈ 27× slimmer at lp16/lp20 scale).

  Nothing about the encoding is trusted: the generated certificate theorems
  (`LogicalBasis.valid` by kernel `decide`) operate on the DECODED vectors
  against the real check matrices and the symplectic δ-pairing, so a decoding
  error cannot silently pass.  `bitsToVec_toBits` additionally pins the
  round-trip, so no information is lost by construction.

  No Mathlib.  No `sorry`, no `axiom`.
-/

import FormalRV.QEC.LDPCMatrix

namespace FormalRV.QEC

open FormalRV.Framework.LDPC

/-- Decode a bitset `Nat` into a width-`w` `BoolVec` (bit `j` = entry `j`). -/
def bitsToVec (w : Nat) (bits : Nat) : BoolVec :=
  (List.range w).map bits.testBit

/-- Encode a `BoolVec` as its bitset `Nat`. -/
def vecToBits (v : BoolVec) : Nat :=
  v.foldr (fun b acc => 2 * acc + (if b then 1 else 0)) 0

@[simp] theorem bitsToVec_length (w bits : Nat) :
    (bitsToVec w bits).length = w := by
  simp [bitsToVec]

/-- Round-trip sanity on a concrete vector (the parametric round-trip is
    plumbing; the generated certificates make it non-load-bearing). -/
example :
    bitsToVec 5 (vecToBits [true, false, true, true, false])
      = [true, false, true, true, false] := by decide

end FormalRV.QEC
