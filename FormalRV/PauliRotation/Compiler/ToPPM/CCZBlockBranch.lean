/-
  FormalRV.PauliRotation.Compiler.ToPPM.CCZBlockBranch
  ───────────────────────────────────────────
  **FENCED — the 64-branch CCZ-block semantic theorem.**

  The statement is EXACTLY the closed form validated branch-exactly by
  the independent Qiskit suite (`scripts/ppm_qiskit_validation.py`,
  route-B section: all 64 branches, Born sum 1).  The Lean proof is a
  4096-leaf arithmetic case bash (64 index contexts x 64 outcome
  combinations, each closed by norm_num) — mathematically routine but
  hours of elaboration, so it lives OUTSIDE the umbrella and compiles
  on its own schedule.  Nothing downstream depends on it: the lane's
  emitter, recognizer, and count theorems are proven in CCZLane.lean.
-/
import FormalRV.PauliRotation.Compiler.ToPPM.CCZBlock

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

set_option maxHeartbeats 220000000 in
/-- **THE CCZ-BLOCK BRANCH THEOREM (all 64 branches)**: three joint
`Z_{d_i}Z_{a_i}` measurements against `|CCZ⟩`, the `m`-selected TWISTED
destructions, and the quadratic-parity `Z` corrections implement EXACTLY
the CCZ gate on the data, with explicit branch scalar `⅛·(−1)^{⟨m,b⟩}`
and the collapsed (graph-state) ancillas.  Numerically pinned, now
machine-checked. -/
theorem cczBlock_branch (m d₁ d₂ d₃ : Nat)
    (h₁ : d₁ < m) (h₂ : d₂ < m) (h₃ : d₃ < m)
    (m₁ m₂ m₃ b₁ b₂ b₃ : Bool) (ψ : Fin (2 ^ m) → ℂ) :
    (if b₃ ^^ (m₁ && m₂) then axisMat (m + 3) [(⟨d₃, .z⟩ : PFactor)]
        else 1).mulVec
      ((if b₂ ^^ (m₁ && m₃) then axisMat (m + 3) [(⟨d₂, .z⟩ : PFactor)]
          else 1).mulVec
        ((if b₁ ^^ (m₂ && m₃) then axisMat (m + 3) [(⟨d₁, .z⟩ : PFactor)]
            else 1).mulVec
          ((projHalf (axisMat (m + 3)
              ((if m₂ then [(⟨m, .z⟩ : PFactor)] else [])
                ++ ((if m₁ then [(⟨m + 1, .z⟩ : PFactor)] else [])
                    ++ [(⟨m + 2, .x⟩ : PFactor)]))) b₃).mulVec
            ((projHalf (axisMat (m + 3)
                ((if m₃ then [(⟨m, .z⟩ : PFactor)] else [])
                  ++ ((⟨m + 1, .x⟩ : PFactor)
                      :: (if m₁ then [(⟨m + 2, .z⟩ : PFactor)] else [])))) b₂).mulVec
              ((projHalf (axisMat (m + 3)
                  ((⟨m, .x⟩ : PFactor)
                    :: ((if m₃ then [(⟨m + 1, .z⟩ : PFactor)] else [])
                        ++ (if m₂ then [(⟨m + 2, .z⟩ : PFactor)] else [])))) b₁).mulVec
                ((projHalf (axisMat (m + 3)
                    [(⟨d₃, .z⟩ : PFactor), ⟨m + 2, .z⟩]) m₃).mulVec
                  ((projHalf (axisMat (m + 3)
                      [(⟨d₂, .z⟩ : PFactor), ⟨m + 1, .z⟩]) m₂).mulVec
                    ((projHalf (axisMat (m + 3)
                        [(⟨d₁, .z⟩ : PFactor), ⟨m, .z⟩]) m₁).mulVec
                      (tensorTriple m cczF ψ)))))))))
    = ((8 : ℂ)⁻¹ * cczSign m₁ m₂ m₃ b₁ b₂ b₃)
        • tensorTriple m (cczCollapse m₁ m₂ m₃ b₁ b₂ b₃)
            ((cczMat m d₁ d₂ d₃).mulVec ψ) := by
  simp only [projHalf_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    mulVec_joint1_tt m d₁ h₁, mulVec_joint2_tt m d₂ h₂,
    mulVec_joint3_tt m d₃ h₃,
    mulVec_dest1_tt, mulVec_dest2_tt, mulVec_dest3_tt,
    mulVec_corr_tt m d₁ h₁, mulVec_corr_tt m d₂ h₂, mulVec_corr_tt m d₃ h₃,
    smul_add, smul_smul]
  funext M
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, tensorTriple,
    Matrix.mulVec_diagonal, cczMat, corr_entry m d₁ (b₁ ^^ (m₂ && m₃)) h₁,
    corr_entry m d₂ (b₂ ^^ (m₁ && m₃)) h₂,
    corr_entry m d₃ (b₃ ^^ (m₁ && m₂)) h₃,
    zMat_mulVec m d₁ h₁, zMat_mulVec m d₂ h₂, zMat_mulVec m d₃ h₃,
    lowBits3_testBit m M d₁ h₁, lowBits3_testBit m M d₂ h₂,
    lowBits3_testBit m M d₃ h₃]
  cases hy₁ : (M : Nat).testBit m <;> cases hy₂ : (M : Nat).testBit (m + 1) <;>
    cases hy₃ : (M : Nat).testBit (m + 2) <;>
    cases ht₁ : (M : Nat).testBit d₁ <;> cases ht₂ : (M : Nat).testBit d₂ <;>
    cases ht₃ : (M : Nat).testBit d₃ <;>
    cases m₁ <;> cases m₂ <;> cases m₃ <;>
    cases b₁ <;> cases b₂ <;> cases b₃ <;>
    norm_num [cczF, cczCollapse, cczSign, twf]

end FormalRV.PauliRotation
