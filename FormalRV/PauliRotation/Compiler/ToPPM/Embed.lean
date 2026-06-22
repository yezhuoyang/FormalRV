/-
  FormalRV.PauliRotation.Compiler.ToPPM.Embed
  ──────────────────────────────────
  **THE EMBEDDING LAYER**: a lowered block's statements act on the wires
  `< n`, so their action passes through a top split `ψ ⊗ (α,β)` at wire
  `n` untouched.  Iterating this is how block `i` of the lowered program
  acts on the joint state `ψ ⊗ anc_i ⊗ … ⊗ anc_k`: the outer ancillas are
  spectators.

    §1  vector linearity of the split,
    §2  the `Y_q` data-wire pass-through (completing Z/X/Y),
    §3  the KIND-FREE axis pass-through (`mulVec_axis_tensorHigh'`),
    §4  statement- and program-level pass-through (`stmtLow`,
        `stmtDenote_tensorHigh`, `progDenote_tensorHigh`).
-/
import FormalRV.PauliRotation.Compiler.ToPPM.Lowering

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-! ## §1. Vector linearity of the split. -/

theorem tensorHigh_vec_add (n : Nat) (α β : ℂ) (φ φ' : Fin (2 ^ n) → ℂ) :
    tensorHigh n α β (φ + φ')
      = tensorHigh n α β φ + tensorHigh n α β φ' := by
  funext m
  show (if (m : Nat).testBit n then β else α) * (φ + φ') (lowBits n m) = _
  show _ * (φ (lowBits n m) + φ' (lowBits n m))
      = (if (m : Nat).testBit n then β else α) * φ (lowBits n m)
        + (if (m : Nat).testBit n then β else α) * φ' (lowBits n m)
  ring

theorem tensorHigh_vec_smul (n : Nat) (α β c : ℂ) (φ : Fin (2 ^ n) → ℂ) :
    tensorHigh n α β (c • φ) = c • tensorHigh n α β φ := by
  funext m
  show (if (m : Nat).testBit n then β else α) * (c • φ) (lowBits n m) = _
  show _ * (c * φ (lowBits n m))
      = c * ((if (m : Nat).testBit n then β else α) * φ (lowBits n m))
  ring

/-! ## §2. `Y_q` at a data wire passes through. -/

theorem mulVec_yq_tensorHigh (n q : Nat) (hq : q < n) (α β : ℂ)
    (ψ : Fin (2 ^ n) → ℂ) :
    (axisMat (n + 1) [(⟨q, .y⟩ : PFactor)]).mulVec (tensorHigh n α β ψ)
      = tensorHigh n α β ((axisMat n [(⟨q, .y⟩ : PFactor)]).mulVec ψ) := by
  funext m
  rw [yMat_mulVec (n + 1) q (by omega)]
  show (if ((flipT (n + 1) q (by omega) m : Fin (2 ^ (n + 1))) : Nat).testBit q
        then -Complex.I else Complex.I)
      * tensorHigh n α β ψ (flipT (n + 1) q (by omega) m)
    = (if (m : Nat).testBit n then β else α)
        * ((axisMat n [(⟨q, .y⟩ : PFactor)]).mulVec ψ) (lowBits n m)
  rw [yMat_mulVec n q hq]
  show _ = (if (m : Nat).testBit n then β else α)
      * ((if ((flipT n q hq (lowBits n m) : Fin (2 ^ n)) : Nat).testBit q
          then -Complex.I else Complex.I)
        * ψ (flipT n q hq (lowBits n m)))
  show (if ((flipT (n + 1) q (by omega) m : Fin (2 ^ (n + 1))) : Nat).testBit q
        then -Complex.I else Complex.I)
      * ((if ((flipT (n + 1) q (by omega) m : Fin (2 ^ (n + 1))) : Nat).testBit n
          then β else α)
        * ψ (lowBits n (flipT (n + 1) q (by omega) m))) = _
  rw [lowBits_flip n q hq, flipT_val, flipT_val,
      testBit_xor_other (by omega : n ≠ q) (m : Nat),
      show (((lowBits n m : Fin (2 ^ n)) : Nat) ^^^ 2 ^ q).testBit q
          = (((m : Nat) ^^^ 2 ^ q)).testBit q from by
        rw [Nat.testBit_xor, Nat.testBit_xor]
        congr 1
        exact lowBits_testBit n m q hq]
  ring

/-! ## §3. The kind-free axis pass-through. -/

/-- ANY sorted axis on wires `< n` passes through the split (Z, X, and Y
factors alike). -/
theorem mulVec_axis_tensorHigh' (n : Nat) :
    ∀ (P : PauliProduct), sortedStrict P = true →
      PauliProduct.width P ≤ n →
      ∀ (α β : ℂ) (ψ : Fin (2 ^ n) → ℂ),
        (axisMat (n + 1) P).mulVec (tensorHigh n α β ψ)
          = tensorHigh n α β ((axisMat n P).mulVec ψ)
  | [], _, _, α, β, ψ => by
      show (axisMat (n + 1) []).mulVec _ = _
      rw [show axisMat (n + 1) [] = 1 from opsMat_one (n + 1),
          show axisMat n [] = 1 from opsMat_one n,
          Matrix.one_mulVec, Matrix.one_mulVec]
  | ⟨q, k⟩ :: P, hs, hw, α, β, ψ => by
      have hw' := hw
      simp only [PauliProduct.width] at hw'
      have hq : q < n := by omega
      have hwP : PauliProduct.width P ≤ n := by omega
      have hsP : sortedStrict P = true := sorted_cons_tail hs
      rw [axisMat_cons_split (n + 1) ⟨q, k⟩ P hs, ← Matrix.mulVec_mulVec,
          mulVec_axis_tensorHigh' n P hsP hwP α β ψ,
          axisMat_cons_split n ⟨q, k⟩ P hs, ← Matrix.mulVec_mulVec]
      cases k with
      | z => exact mulVec_zq_tensorHigh n q hq α β _
      | x => exact mulVec_xq_tensorHigh n q hq α β _
      | y => exact mulVec_yq_tensorHigh n q hq α β _

/-! ## §4. Statement- and program-level pass-through. -/

/-- A statement is LOW for width `n` when every product it can apply is
canonical and lives on wires `< n` (decidable). -/
def stmtLow (n : Nat) : PPMStmt → Bool
  | .measure _ P => sortedStrict P && decide (PauliProduct.width P ≤ n)
  | .measureSel _ _ Pt Pe =>
      sortedStrict Pt && decide (PauliProduct.width Pt ≤ n)
        && sortedStrict Pe && decide (PauliProduct.width Pe ≤ n)
  | .measureSel2 _ _ _ P00 P01 P10 P11 =>
      sortedStrict P00 && decide (PauliProduct.width P00 ≤ n)
        && sortedStrict P01 && decide (PauliProduct.width P01 ≤ n)
        && sortedStrict P10 && decide (PauliProduct.width P10 ≤ n)
        && sortedStrict P11 && decide (PauliProduct.width P11 ≤ n)
  | .frame P => sortedStrict P && decide (PauliProduct.width P ≤ n)
  | .correct _ thn els =>
      sortedStrict thn && decide (PauliProduct.width thn ≤ n)
        && sortedStrict els && decide (PauliProduct.width els ≤ n)
  | .correctQ _ thn els =>
      sortedStrict thn && decide (PauliProduct.width thn ≤ n)
        && sortedStrict els && decide (PauliProduct.width els ≤ n)
  | .useT _ => true
  | .useCCZ _ _ _ => true

/-- **A low statement acts through the split.** -/
theorem stmtDenote_tensorHigh (n : Nat) (outs : List Bool) (b : Bool)
    (st : PPMStmt) (hst : stmtLow n st = true) (α β : ℂ)
    (ψ : Fin (2 ^ n) → ℂ) :
    (stmtDenote (n + 1) outs b st).mulVec (tensorHigh n α β ψ)
      = tensorHigh n α β ((stmtDenote n outs b st).mulVec ψ) := by
  cases st with
  | measure dst P =>
      simp only [stmtLow, Bool.and_eq_true, decide_eq_true_eq] at hst
      simp only [stmtDenote]
      rw [projHalf_mulVec, projHalf_mulVec,
          mulVec_axis_tensorHigh' n P hst.1 hst.2 α β ψ,
          ← tensorHigh_vec_smul, ← tensorHigh_vec_add, ← tensorHigh_vec_smul]
  | measureSel sel dst Pt Pe =>
      simp only [stmtLow, Bool.and_eq_true, decide_eq_true_eq] at hst
      simp only [stmtDenote]
      by_cases hp : xorParity outs sel = true
      · simp only [hp, if_true]
        rw [projHalf_mulVec, projHalf_mulVec,
            mulVec_axis_tensorHigh' n Pt hst.1.1.1 hst.1.1.2 α β ψ,
            ← tensorHigh_vec_smul, ← tensorHigh_vec_add, ← tensorHigh_vec_smul]
      · simp only [hp, Bool.false_eq_true, if_false]
        rw [projHalf_mulVec, projHalf_mulVec,
            mulVec_axis_tensorHigh' n Pe hst.1.2 hst.2 α β ψ,
            ← tensorHigh_vec_smul, ← tensorHigh_vec_add, ← tensorHigh_vec_smul]
  | measureSel2 sel1 sel2 dst P00 P01 P10 P11 =>
      simp only [stmtLow, Bool.and_eq_true, decide_eq_true_eq] at hst
      simp only [stmtDenote]
      by_cases h1 : xorParity outs sel1 = true <;>
        by_cases h2 : xorParity outs sel2 = true <;>
        simp only [h1, h2, Bool.false_eq_true, if_true, if_false] <;>
        rw [projHalf_mulVec, projHalf_mulVec] <;>
        [rw [mulVec_axis_tensorHigh' n P11 hst.1.2 hst.2 α β ψ];
         rw [mulVec_axis_tensorHigh' n P10 hst.1.1.1.2 hst.1.1.2 α β ψ];
         rw [mulVec_axis_tensorHigh' n P01 hst.1.1.1.1.1.2 hst.1.1.1.1.2
            α β ψ];
         rw [mulVec_axis_tensorHigh' n P00 hst.1.1.1.1.1.1.1
            hst.1.1.1.1.1.1.2 α β ψ]] <;>
        rw [← tensorHigh_vec_smul, ← tensorHigh_vec_add, ← tensorHigh_vec_smul]
  | frame P =>
      simp only [stmtLow, Bool.and_eq_true, decide_eq_true_eq] at hst
      simp only [stmtDenote]
      exact mulVec_axis_tensorHigh' n P hst.1 hst.2 α β ψ
  | correct par thn els =>
      simp only [stmtLow, Bool.and_eq_true, decide_eq_true_eq] at hst
      simp only [stmtDenote]
      by_cases hp : xorParity outs par = true
      · rw [if_pos hp, if_pos hp]
        exact mulVec_axis_tensorHigh' n thn hst.1.1.1 hst.1.1.2 α β ψ
      · rw [if_neg hp, if_neg hp]
        exact mulVec_axis_tensorHigh' n els hst.1.2 hst.2 α β ψ
  | correctQ mons thn els =>
      simp only [stmtLow, Bool.and_eq_true, decide_eq_true_eq] at hst
      simp only [stmtDenote]
      by_cases hp : qParity outs mons = true
      · rw [if_pos hp, if_pos hp]
        exact mulVec_axis_tensorHigh' n thn hst.1.1.1 hst.1.1.2 α β ψ
      · rw [if_neg hp, if_neg hp]
        exact mulVec_axis_tensorHigh' n els hst.1.2 hst.2 α β ψ
  | useT q =>
      simp only [stmtDenote]
      rw [Matrix.one_mulVec, Matrix.one_mulVec]
  | useCCZ a b' c =>
      simp only [stmtDenote]
      rw [Matrix.one_mulVec, Matrix.one_mulVec]

/-- **A low program acts through the split.** -/
theorem progDenote_tensorHigh (n : Nat) (ω : Nat → Bool) :
    ∀ (p : PPMProg) (outs : List Bool),
      (∀ st ∈ p, stmtLow n st = true) →
      ∀ (α β : ℂ) (ψ : Fin (2 ^ n) → ℂ),
        (progDenote (n + 1) ω outs p).mulVec (tensorHigh n α β ψ)
          = tensorHigh n α β ((progDenote n ω outs p).mulVec ψ)
  | [], outs, _, α, β, ψ => by
      show (1 : Matrix _ _ ℂ).mulVec _ = _
      rw [Matrix.one_mulVec]
      show _ = tensorHigh n α β ((1 : Matrix _ _ ℂ).mulVec ψ)
      rw [Matrix.one_mulVec]
  | st :: p, outs, hlow, α, β, ψ => by
      show (progDenote (n + 1) ω _ p
          * stmtDenote (n + 1) outs (ω outs.length) st).mulVec _ = _
      rw [← Matrix.mulVec_mulVec,
          stmtDenote_tensorHigh n outs (ω outs.length) st
            (hlow st List.mem_cons_self) α β ψ,
          progDenote_tensorHigh n ω p _
            (fun s hs => hlow s (List.mem_cons_of_mem _ hs)) α β _,
          show progDenote n ω outs (st :: p)
              = progDenote n ω (outs ++ List.replicate st.binds
                  (ω outs.length)) p * stmtDenote n outs (ω outs.length) st
            from rfl,
          ← Matrix.mulVec_mulVec]

end FormalRV.PauliRotation
