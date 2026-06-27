/- PhaseKickback — Part6 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.QPE.PhaseKickback.FourierFormQPE

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-! ### Control-register factorization infrastructure

When the real QFTinv is implemented, it will be a `BaseUCom m`
acting only on the control register (qubits `0..m-1`). Its lift via
`map_qubits (fun q => q)` to `BaseUCom (m + anc)` must commute with
`kron_vec`. The two theorems below provide that infrastructure.

This infrastructure is also independently useful: any future
control-side circuit (QFT, bit reversal, classical post-processing)
will need exactly these factorization lemmas. -/

/-- **Control-register `pad_ctrl` (CNOT) factorization.** When both
the control qubit `a` and the target qubit `b` lie in the control
register (`a, b < m`), the CNOT factors through `kron_vec` and only
affects the control component `χ`. -/
theorem pad_ctrl_control_kron_vec_factors {m anc a b : Nat}
    (ha : a < m) (hb : b < m)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    pad_ctrl (m + anc) a b σx * kron_vec χ ψ
      = kron_vec (pad_ctrl m a b σx * χ) ψ := by
  unfold pad_ctrl
  rw [Matrix.add_mul]
  rw [pad_u_control_kron_vec_factors ha proj0 χ ψ]
  rw [Matrix.mul_assoc]
  rw [pad_u_control_kron_vec_factors hb σx χ ψ]
  rw [pad_u_control_kron_vec_factors ha proj1 _ ψ]
  rw [← kron_vec_add_left]
  rw [Matrix.add_mul, Matrix.mul_assoc]

/-- **Generic control-register circuit factorization.** Any well-typed
`BaseUCom m` circuit, lifted via `map_qubits (· + 0) = id` to
`BaseUCom (m + anc)`, factors through `kron_vec` and acts only on the
control component `χ`. Structural induction on the circuit; each gate
case dispatches to the corresponding control-side factorization lemma. -/
theorem uc_eval_control_register_circuit_kron_vec
    {m anc : Nat}
    (c : FormalRV.Framework.BaseUCom m)
    (h_wt : UCom.WellTyped m c)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => q) c : FormalRV.Framework.BaseUCom (m + anc))
      * kron_vec χ ψ
    = kron_vec (FormalRV.Framework.uc_eval c * χ) ψ := by
  induction c generalizing χ with
  | seq c₁ c₂ ih₁ ih₂ =>
      cases h_wt with
      | seq h_wt1 h_wt2 =>
        show FormalRV.Framework.uc_eval
              (map_qubits (fun q => q) c₂ : FormalRV.Framework.BaseUCom (m + anc))
              * FormalRV.Framework.uc_eval
                  (map_qubits (fun q => q) c₁ : FormalRV.Framework.BaseUCom (m + anc))
              * kron_vec χ ψ = _
        rw [Matrix.mul_assoc]
        rw [ih₁ h_wt1 χ]
        rw [ih₂ h_wt2 _]
        show kron_vec (FormalRV.Framework.uc_eval c₂ *
                       (FormalRV.Framework.uc_eval c₁ * χ)) ψ
              = kron_vec (FormalRV.Framework.uc_eval c₂ *
                          FormalRV.Framework.uc_eval c₁ * χ) ψ
        rw [Matrix.mul_assoc]
  | app1 u n =>
      cases h_wt with
      | app1 hn =>
        cases u with
        | R θ φ lam =>
          exact pad_u_control_kron_vec_factors hn (rotation θ φ lam) χ ψ
  | app2 u a b =>
      cases h_wt with
      | app2 ha hb _ =>
        cases u
        exact pad_ctrl_control_kron_vec_factors ha hb χ ψ
  | app3 u _ _ _ => cases u


end FormalRV.SQIRPort
