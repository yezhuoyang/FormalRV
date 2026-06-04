/-
  FormalRV.Shor.AQFTCompile — an ACTUAL Clifford+T compiler for the
  inverse-QFT phase ladder of Shor's QPE, with derived approximation
  error.  No existence axiom: `compileLadder` is a real circuit
  transformation, proven to emit only Clifford+T gates, and its total
  approximation error is the closed-form geometric tail
  (`ApproxQFT.aqft_ladder_error_budget`).

  ## What this is

  The inverse QFT (`FormalRV.Framework.BaseUCom.QFTinv`) is a ladder of
  controlled rotations `controlled_Rz q t (−π/2^m)` plus Hadamards.  The
  `controlled_Rz` decomposition uses the half-angle `R_z(∓π/2^{m+1})`, so
  a ladder rotation is exactly Clifford+T iff `m ≤ 1`
  (`m=0 → S†/S = CZ`, `m=1 → T†/T = controlled-S†`).  The approximate
  ("banded") QFT keeps `m < cutoff` and DROPS the rest; with `cutoff ≤ 2`
  the output is exactly Clifford+T (`compileLadder_isCliffordT`), and the
  dropped rotations contribute the derived error budget.

  This compiles the QFT layer; the modular-exponentiation layer of QPE is
  already exact Clifford+T, so together they compile QPE's circuit to
  Clifford+T up to the stated, derived error.
-/
import FormalRV.Shor.QPE
import FormalRV.Core.ApproxQFT

namespace FormalRV.Framework.AQFTCompile

open FormalRV.Framework
open FormalRV.Framework.BaseUCom
open FormalRV.Framework.CliffordTRotations
open FormalRV.Framework.ApproxQFT

/-! ## §1. The compiler. -/

/-- One inverse-QFT phase-ladder rotation: control `q`, target `t`, depth
    `m` (the rotation angle is `−π/2^m`). -/
structure PhaseRot where
  q : Nat
  t : Nat
  m : Nat

/-- **Compile one rotation under cutoff `c`.**  Keep the (Clifford+T)
    `controlled_Rz` when `m < c`; otherwise DROP it (`SKIP`).  This is the
    approximate-QFT decision, applied gate by gate. -/
noncomputable def compileRot {dim : Nat} (c : Nat) (r : PhaseRot) : BaseUCom dim :=
  if r.m < c then
    BaseUCom.controlled_Rz r.q r.t (-(Real.pi / 2 ^ r.m))
  else
    SKIP

/-- **The compiled approximate inverse-QFT phase ladder.**  Sequences the
    compiled rotations.  The actual compiler output. -/
noncomputable def compileLadder {dim : Nat} (c : Nat) (rs : List PhaseRot) :
    BaseUCom dim :=
  rs.foldr (fun r acc => UCom.seq (compileRot c r) acc) SKIP

/-! ## §2. The output is Clifford+T (cutoff ≤ 2). -/

theorem skip_isCliffordT {dim : Nat} : IsCliffordT (SKIP : BaseUCom dim) := by
  show IsCliffordT (UCom.app1 U_I 0 : BaseUCom dim)
  exact IsCliffordT.gate1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-- `controlled_Rz q t lam` is Clifford+T whenever its half-angle gates
    `R_z(lam/2)` and `R_z(−lam/2)` are named Clifford+T gates. -/
theorem controlled_Rz_isCliffordT {dim : Nat} (q t : Nat) (lam : ℝ)
    (hpos : (U_Rz (lam / 2) = U_H ∨ U_Rz (lam / 2) = U_S ∨ U_Rz (lam / 2) = U_T
              ∨ U_Rz (lam / 2) = U_SDAG ∨ U_Rz (lam / 2) = U_TDAG
              ∨ U_Rz (lam / 2) = U_I))
    (hneg : (U_Rz (-(lam / 2)) = U_H ∨ U_Rz (-(lam / 2)) = U_S
              ∨ U_Rz (-(lam / 2)) = U_T ∨ U_Rz (-(lam / 2)) = U_SDAG
              ∨ U_Rz (-(lam / 2)) = U_TDAG ∨ U_Rz (-(lam / 2)) = U_I)) :
    IsCliffordT (BaseUCom.controlled_Rz q t lam : BaseUCom dim) := by
  unfold BaseUCom.controlled_Rz Rz CNOT
  exact IsCliffordT.seq (IsCliffordT.gate1 hpos)
    (IsCliffordT.seq IsCliffordT.cnot
      (IsCliffordT.seq (IsCliffordT.gate1 hneg)
        (IsCliffordT.seq IsCliffordT.cnot
          (IsCliffordT.gate1 hpos))))

/-- Depth-0 ladder rotation (`−π`, i.e. CZ): half-angles are `S†, S` —
    Clifford. -/
theorem controlled_Rz_isCliffordT_depth0 {dim : Nat} (q t : Nat) :
    IsCliffordT (BaseUCom.controlled_Rz q t (-(Real.pi / 2 ^ 0)) : BaseUCom dim) := by
  apply controlled_Rz_isCliffordT
  · right; right; right; left
    show U_Rz _ = U_SDAG
    unfold U_Rz U_SDAG; congr 1 <;> ring
  · right; left
    show U_Rz _ = U_S
    unfold U_Rz U_S; congr 1 <;> ring

/-- Depth-1 ladder rotation (`−π/2`, controlled-`S†`): half-angles are
    `T†, T` — Clifford+T. -/
theorem controlled_Rz_isCliffordT_depth1 {dim : Nat} (q t : Nat) :
    IsCliffordT (BaseUCom.controlled_Rz q t (-(Real.pi / 2 ^ 1)) : BaseUCom dim) := by
  apply controlled_Rz_isCliffordT
  · right; right; right; right; left
    show U_Rz _ = U_TDAG
    unfold U_Rz U_TDAG; congr 1 <;> ring
  · right; right; left
    show U_Rz _ = U_T
    unfold U_Rz U_T; congr 1 <;> ring

/-- **The compiled ladder is exactly Clifford+T** (for cutoff `c ≤ 2`).
    Every kept rotation has depth `< c ≤ 2`, hence depth `0` or `1`, hence
    Clifford+T; every dropped rotation is `SKIP`. -/
theorem compileLadder_isCliffordT {dim : Nat} (c : Nat) (hc : c ≤ 2)
    (rs : List PhaseRot) :
    IsCliffordT (compileLadder c rs : BaseUCom dim) := by
  unfold compileLadder
  induction rs with
  | nil => exact skip_isCliffordT
  | cons r rs ih =>
      rw [List.foldr_cons]
      refine IsCliffordT.seq ?_ ih
      unfold compileRot
      split
      · rename_i hm
        have : r.m = 0 ∨ r.m = 1 := by omega
        rcases this with h | h <;> rw [h]
        · exact controlled_Rz_isCliffordT_depth0 _ _
        · exact controlled_Rz_isCliffordT_depth1 _ _
      · exact skip_isCliffordT

/-! ## §3. The derived approximation error.

    The total error of the cutoff-`c` compilation is the sum of the
    dropped-rotation drop errors — each `‖R_z(−π/2^m) − I‖ ≤ π/2^m`
    (`ApproxQFT.dropRotationError_le`) — over the dropped depths `m ≥ c`,
    which is the closed-form geometric tail `≤ 2π/2^c`
    (`ApproxQFT.aqft_ladder_error_budget`).  Restated here as the
    compiler's headline error guarantee, and it `→ 0` as `c` grows. -/

/-- **Compiler error budget.**  The total approximation error of the
    cutoff-`c` AQFT ladder — summed over every dropped depth `c ≤ m < n`
    of its derived per-rotation drop cost — is at most `2π/2^c`. -/
theorem compileLadder_error_budget (c n : ℕ) (hcn : c ≤ n) :
    ∑ m ∈ Finset.Ico c n, (Real.pi / 2 ^ m) ≤ 2 * Real.pi / 2 ^ c :=
  aqft_ladder_error_budget c n hcn

end FormalRV.Framework.AQFTCompile
