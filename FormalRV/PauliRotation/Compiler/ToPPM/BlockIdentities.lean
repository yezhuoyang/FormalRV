/-
  FormalRV.PauliRotation.Compiler.ToPPM.BlockIdentities
  ────────────────────────────────────────────
  Remaining prerequisites for the π/8 teleport-block identities:

    • `yMat_mulVec` — the `Y_t` action collapse (bit flip with `±i` phase),
    • `mulVec_yn_tensorHigh` — ancilla `Y_n`: `(α, β) ↦ (−iβ, iα)`,
    • `axisMat_snoc_split` — the lowering's joint axis `P ++ [Z_n]` splits
      off its ancilla factor (disjoint supports, order-free),
    • `mulVec_joint_tensorHigh` — the joint axis acts as
      `data-action ⊗ (α, −β)`.
-/
import FormalRV.PauliRotation.Compiler.ToPPM.TensorHigh

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-! ## §1. The `Y` collapses. -/

/-- `Y_t` acts on vectors by the bit flip with the `±i` phase. -/
theorem yMat_mulVec (n t : Nat) (ht : t < n) (v : Fin (2 ^ n) → ℂ)
    (i : Fin (2 ^ n)) :
    ((axisMat n [(⟨t, .y⟩ : PFactor)]).mulVec v) i
      = (if ((flipT n t ht i : Fin (2 ^ n)) : Nat).testBit t
          then -Complex.I else Complex.I) * v (flipT n t ht i) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (flipT n t ht i)]
  · rw [axisMat_single_y_apply n t ht]
    have hcond : (i : Nat) = ((flipT n t ht i : Fin (2 ^ n)) : Nat) ^^^ 2 ^ t := by
      rw [flipT_val, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [if_pos hcond]
  · intro k _ hk
    rw [axisMat_single_y_apply n t ht, if_neg, zero_mul]
    intro hik
    apply hk
    apply Fin.ext
    rw [flipT_val, hik, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- **Ancilla `Y_n`: `(α, β) ↦ (−iβ, iα)`.** -/
theorem mulVec_yn_tensorHigh (n : Nat) (α β : ℂ) (ψ : Fin (2 ^ n) → ℂ) :
    (axisMat (n + 1) [(⟨n, .y⟩ : PFactor)]).mulVec (tensorHigh n α β ψ)
      = tensorHigh n (-Complex.I * β) (Complex.I * α) ψ := by
  funext m
  rw [yMat_mulVec (n + 1) n (by omega)]
  show (if ((flipT (n + 1) n (by omega) m : Fin (2 ^ (n + 1))) : Nat).testBit n
        then -Complex.I else Complex.I)
      * tensorHigh n α β ψ (flipT (n + 1) n (by omega) m)
    = (if (m : Nat).testBit n then Complex.I * α else -Complex.I * β)
        * ψ (lowBits n m)
  show _ * ((if ((flipT (n + 1) n (by omega) m : Fin (2 ^ (n + 1))) : Nat).testBit n
        then β else α) * ψ (lowBits n (flipT (n + 1) n (by omega) m))) = _
  rw [lowBits_flip_high, flipT_val, testBit_xor_self_bit]
  by_cases h : (m : Nat).testBit n <;> simp [h] <;> ring

/-! ## §2. The snoc split: the joint axis `P·Z_n`. -/

/-- An axis whose LAST factor sits above all others splits it off
multiplicatively (disjoint supports — no sorting needed beyond the bound). -/
theorem axisMat_snoc_split (n : Nat) (P : PauliProduct) (f : PFactor)
    (hw : ∀ g ∈ P, g.qubit < f.qubit) :
    axisMat n (P ++ [f]) = axisMat n P * axisMat n [f] := by
  unfold axisMat
  rw [opsMat_mul_pointwise n _ _ (fun k => by
    by_cases hf : f.qubit = k
    · left
      subst hf
      show kindFn P f.qubit = Pauli.I
      unfold kindFn
      rw [List.find?_eq_none.mpr (fun g hg => by
        simp only [beq_iff_eq]
        exact Nat.ne_of_lt (hw g hg))]
    · right
      rw [kindFn_single, if_neg hf])]
  congr 1
  funext i
  rw [mulP]
  unfold kindFn
  rw [List.find?_append]
  by_cases hPi : P.find? (fun g => g.qubit == i) = none
  · rw [hPi]
    simp [Option.none_or]
  · obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.mp hPi
    rw [hg]
    simp [Option.some_or, pkindToBQ_ne_I g.kind]

/-! ## §3. The joint axis acts as `data ⊗ (α, −β)`. -/

/-- **The lowering's joint measurement axis**: `P·Z_n` acts on the split as
the data action of `P` with the ancilla sign flip. -/
theorem mulVec_joint_tensorHigh (n : Nat) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (hk : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x)
    (α β : ℂ) (ψ : Fin (2 ^ n) → ℂ) :
    (axisMat (n + 1) (P ++ [⟨n, .z⟩])).mulVec (tensorHigh n α β ψ)
      = tensorHigh n α (-β) ((axisMat n P).mulVec ψ) := by
  have hbound : ∀ (Q : PauliProduct), ∀ g ∈ Q,
      g.qubit + 1 ≤ PauliProduct.width Q := by
    intro Q
    induction Q with
    | nil => intro g hg; cases hg
    | cons f t ih =>
        intro g hg
        simp only [PauliProduct.width]
        rcases List.mem_cons.mp hg with hg | hg
        · subst hg
          omega
        · have := ih g hg
          omega
  have hwq : ∀ g ∈ P, g.qubit < n := fun g hg => by
    have := hbound P g hg
    omega
  rw [axisMat_snoc_split (n + 1) P ⟨n, .z⟩ (fun g hg => hwq g hg),
      ← Matrix.mulVec_mulVec, mulVec_zn_tensorHigh,
      mulVec_axis_tensorHigh n P hs hw hk]

end FormalRV.PauliRotation
