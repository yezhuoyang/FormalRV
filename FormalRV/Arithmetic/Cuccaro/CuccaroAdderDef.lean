/-
  FormalRV.Arithmetic.Cuccaro.CuccaroAdderDef
  ──────────────────────────────────────────
  THE definition of the Cuccaro–Draper–Kutin–Moulton n-bit ripple-carry
  adder, as concrete `Gate` data over the Framework IR. **Definitions only —
  no proofs.**

  THE adder is `cuccaro_n_bit_adder_full`: a forward MAJ chain followed by a
  REVERSE UMA chain, on `2*n + 1` qubits starting at `q_start`:
    • q_start + 0      : carry-in
    • q_start + 2i + 1 : bit i of b  (target register; becomes (a+b+c_in) mod 2^n)
    • q_start + 2i + 2 : bit i of a  (read register; preserved)

  Where to look next:
    • Semantic correctness : `CuccaroAdderCorrectness.lean`
    • Resources (T/Toffoli/qubits) : `CuccaroAdderResource.lean`
    • Supporting lemmas : `CuccaroFull.lean` / `CuccaroCorrectness.lean` / `CuccaroDecoded.lean`

  Refs: Cuccaro–Draper–Kutin–Moulton, arXiv:quant-ph/0410184; SQIR
  `ModMult.v`. The reverse-UMA ordering is the boundary correction validated
  by `scripts/check_cuccaro_adder.py` (exhaustive for n = 1..4).
-/
import FormalRV.Core.Gate

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Atomic gadgets -/

/-- Cuccaro MAJ gadget:  `MAJ a b c = CX c b ; CX c a ; CCX a b c`. -/
def cuccaro_MAJ (a b c : Nat) : Gate :=
  seq (CX c b) (seq (CX c a) (CCX a b c))

/-- Cuccaro UMA gadget:  `UMA a b c = CCX a b c ; CX c a ; CX a b`. -/
def cuccaro_UMA (a b c : Nat) : Gate :=
  seq (CCX a b c) (seq (CX c a) (CX a b))

/-! ## Ripple chains -/

/-- Forward chain of `n` MAJ gadgets on consecutive triples starting at
`q_start`, then `q_start + 2`, … (the Cuccaro ripple structure). -/
def cuccaro_maj_chain : Nat → Nat → Gate
  | 0,     _       => I
  | n + 1, q_start =>
      seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
          (cuccaro_maj_chain n (q_start + 2))

/-- Reverse UMA chain: `UMA_{n-1}, UMA_{n-2}, …, UMA_0` applied in
descending order on consecutive triples starting at `q_start`. -/
def cuccaro_uma_chain_reverse : Nat → Nat → Gate
  | 0,     _       => I
  | n + 1, q_start =>
      seq (cuccaro_uma_chain_reverse n (q_start + 2))
          (cuccaro_UMA q_start (q_start + 1) (q_start + 2))

/-! ## THE adder -/

/-- **THE n-bit Cuccaro adder** (boundary-corrected): forward MAJ chain
then REVERSE UMA chain, on `2*n + 1` qubits from `q_start`, computing
`target := (a + b + c_in) mod 2^n` in place.

Correctness: `cuccaro_n_bit_adder_full_target_decode` (CuccaroAdderCorrectness).
Resource: `tcount_cuccaro_n_bit_adder_full = 14 * n` (CuccaroAdderResource). -/
def cuccaro_n_bit_adder_full (n q_start : Nat) : Gate :=
  seq (cuccaro_maj_chain n q_start) (cuccaro_uma_chain_reverse n q_start)

end FormalRV.BQAlgo
