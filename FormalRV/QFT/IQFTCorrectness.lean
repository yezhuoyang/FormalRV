/-
  FormalRV.QFT.IQFTCorrectness
  ────────────────────────────
  THE semantic-correctness theorem for the inverse QFT.

  Imports THE definition from `IQFTDef.lean`.  The single theorem to audit is
  `iqft_correct`: the real `BaseUCom` inverse-QFT circuit evaluates EXACTLY to
  the ideal `IQFT_matrix`, for every width `n ≥ 1`.  Its proof is delegated to
  the recursive column argument in `IQFTRecursiveArbitrary.lean` (base cases in
  `IQFTCircuitCorrectness.lean`).
-/
import FormalRV.QFT.IQFTDef
import FormalRV.QFT.IQFTRecursiveArbitrary

namespace FormalRV.SQIRPort

open FormalRV.Framework

/-- **Inverse QFT — circuit correctness (THE headline).**

For every `n ≥ 1`, the real inverse-QFT circuit evaluates to the ideal
inverse-QFT matrix:

  `uc_eval (IQFT n) = IQFT_matrix n`.

i.e. the bit-reversal-plus-phase-ladder circuit `real_QFTinv_layer n` is, as a
unitary, exactly `(y,x) ↦ (1/√2ⁿ)·exp(-2πi·x·y/2ⁿ)`.  Proved by induction on `n`
(column-by-column) — no approximation, no axiom. -/
theorem iqft_correct (n : Nat) (hn : 0 < n) :
    FormalRV.Framework.uc_eval (IQFT n) = IQFT_matrix n :=
  uc_eval_real_QFTinv_layer_eq_IQFT_matrix n hn

/-- **Inverse QFT — well-typed.** `IQFT n` uses only qubits `< n`. -/
theorem iqft_wellTyped (n : Nat) (hn : 0 < n) :
    UCom.WellTyped n (IQFT n) :=
  wellTyped_real_QFTinv_layer n hn

/-- **Inverse QFT — verified bundle (correctness AFTER well-typedness).** The
single circuit `IQFT n` is simultaneously `WellTyped` on `n` qubits and equal,
as a unitary, to the ideal `IQFT_matrix n`. -/
theorem iqft_correct_verified (n : Nat) (hn : 0 < n) :
    UCom.WellTyped n (IQFT n)
    ∧ FormalRV.Framework.uc_eval (IQFT n) = IQFT_matrix n :=
  ⟨iqft_wellTyped n hn, iqft_correct n hn⟩

/-- **Framework bridge.** The framework-level `BaseUCom.QFTinv m` (the object the
QPE / Shor pipeline plugs into its measurement basis) also evaluates to the
ideal `IQFT_matrix m`. -/
theorem QFTinv_correct (m : Nat) (hm : 0 < m) :
    FormalRV.Framework.uc_eval (FormalRV.Framework.BaseUCom.QFTinv m : BaseUCom m)
      = IQFT_matrix m :=
  uc_eval_QFTinv_eq_IQFT_matrix m hm

end FormalRV.SQIRPort
