/-
  FormalRV.QFT.IQFTDef
  ────────────────────
  THE definition of the inverse Quantum Fourier Transform (IQFT), as a concrete
  `BaseUCom` unitary circuit, together with the ideal matrix it must reproduce.
  **Definitions only — no proofs.**

  THE circuit is `real_QFTinv_layer n` (also exposed as the framework's
  `BaseUCom.QFTinv n`): on `n` qubits it runs a bit-reversal SWAP cascade, then a
  countdown of phase ladders — for each target `t = n-1 … 0`, a chain of
  controlled phases `controlled_Rz j t (-π/2^(j-t))` (controls `j > t`) followed
  by `H t`.  THE ideal target is `IQFT_matrix n`, the matrix
  `(y,x) ↦ (1/√2ⁿ)·exp(-2πi·x·y/2ⁿ)`.

  (The forward `QFT` is a placeholder; the real, verified object in this folder
  is the INVERSE QFT — the measurement-basis transform of QPE / Shor.)

  Where to look next:
    • Circuit correctness (THE main theorem) : `IQFTCorrectness.lean`
    • Clifford+T compilation + error budget  : `IQFTResource.lean`
    • Worked example + QASM emission          : `IQFTExample.lean`
    • Supporting proofs                       : `IQFTCircuitCorrectness.lean`,
      `IQFTRecursiveArbitrary.lean` (and `IQFTDefinitions.lean` for the helper
      defs the proofs run on).

  Refs: Nielsen–Chuang §5.1 (QFT); Coppersmith (approximate/banded QFT). The
  circuit pieces also live, `{dim}`-polymorphic, in `Framework.QPE` /
  `Framework.BaseUCom` (`QFTinv n := real_QFTinv_layer n`, replacing the prior
  semantically-wrong `invert (npar_H n)` stub).
-/
import FormalRV.QFT.IQFTDefinitions

namespace FormalRV.SQIRPort

open FormalRV.Framework

/-! ## THE inverse-QFT circuit and its ideal target.

Both names below are the canonical, already-defined objects (re-surfaced here
so the spine has a single "Definition" entry point); `IQFT n` is a reducible
alias for the circuit the correctness theorem is stated about. -/

/-- **THE n-qubit inverse-QFT circuit** — bit-reversal SWAP cascade then the
phase-ladder countdown, on `n` qubits.  Reducible alias of the canonical
`real_QFTinv_layer n` (= framework `BaseUCom.QFTinv n`).

Correctness: `iqft_correct` (`IQFTCorrectness.lean`), i.e.
`uc_eval (IQFT n) = IQFT_matrix n`.  Compilation/resource: `IQFTResource.lean`.

(`IQFT_matrix n y x = (1/√2ⁿ)·exp(-2πi·x·y/2ⁿ)`, re-surfaced from
`IQFTDefinitions`, is the matrix-level target `IQFT n` must reproduce.) -/
@[reducible] noncomputable def IQFT (n : Nat) : BaseUCom n := real_QFTinv_layer n

/-- Smoke: the alias is definitionally the canonical circuit, and its ideal
target is `IQFT_matrix`. -/
example (n : Nat) : IQFT n = real_QFTinv_layer n := rfl

end FormalRV.SQIRPort
