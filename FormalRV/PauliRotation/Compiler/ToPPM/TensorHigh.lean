/-
  FormalRV.PauliRotation.Compiler.ToPPM.TensorHigh
  ───────────────────────────────────────
  THE DATA⊗ANCILLA VECTOR LAYER for the RotProg → PPM lowering.

  The lowering's teleport blocks act on `n` data qubits plus ONE fresh
  ancilla at wire `n` (the HIGH bit, under the layer's qubit-0-is-LSB
  convention).  `tensorHigh α β ψ` is the joint state `ψ ⊗ (α|0⟩ + β|1⟩)`,
  and this file proves how every measurement axis the lowering emits acts
  on it:

    • data-wire `Z_q`/`X_q` singles pass through the split
      (`mulVec_single_z_tensorHigh`, `mulVec_single_x_tensorHigh`),
    • the ancilla factors act on the amplitude pair alone
      (`mulVec_zn_tensorHigh` : `(α,β) ↦ (α,−β)`,
       `mulVec_xn_tensorHigh` : `(α,β) ↦ (β,α)`,
       `mulVec_yn_tensorHigh` : `(α,β) ↦ (−iβ, iα)`),
    • a whole embedded data axis passes through
      (`mulVec_axis_tensorHigh`), by sorted-cons induction,
    • and the lowering's joint axis `P·Z_n` splits off its ancilla factor
      (`axisMat_snoc_zn`).

  Everything is entrywise over the proven `BasisAction` characterizations;
  no new axioms, no normalization conventions — amplitudes are explicit.
-/
import FormalRV.PauliRotation.Correctness.CCXRow

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-! ## §1. The high-bit split. -/

/-- The data part of a joint basis index: the low `n` bits. -/
def lowBits (n : Nat) (m : Fin (2 ^ (n + 1))) : Fin (2 ^ n) :=
  ⟨(m : Nat) % 2 ^ n, Nat.mod_lt _ (by positivity)⟩

/-- `ψ ⊗ (α|0⟩ + β|1⟩)` with the ancilla at the HIGH wire `n`. -/
noncomputable def tensorHigh (n : Nat) (α β : ℂ) (ψ : Fin (2 ^ n) → ℂ) :
    Fin (2 ^ (n + 1)) → ℂ :=
  fun m => (if (m : Nat).testBit n then β else α) * ψ (lowBits n m)

theorem tensorHigh_congr (n : Nat) {α α' β β' : ℂ}
    {ψ ψ' : Fin (2 ^ n) → ℂ} (hα : α = α') (hβ : β = β') (hψ : ψ = ψ') :
    tensorHigh n α β ψ = tensorHigh n α' β' ψ' := by
  rw [hα, hβ, hψ]

/-- Linearity facts used when assembling branches. -/
theorem tensorHigh_smul (n : Nat) (c α β : ℂ) (ψ : Fin (2 ^ n) → ℂ) :
    tensorHigh n (c * α) (c * β) ψ = c • tensorHigh n α β ψ := by
  funext m
  show (if (m : Nat).testBit n then c * β else c * α) * ψ (lowBits n m)
      = c * ((if (m : Nat).testBit n then β else α) * ψ (lowBits n m))
  by_cases h : (m : Nat).testBit n <;> simp [h] <;> ring

/-! ## §2. Index bridges for the high-bit split. -/

theorem lowBits_testBit (n : Nat) (m : Fin (2 ^ (n + 1))) (q : Nat)
    (hq : q < n) :
    ((lowBits n m : Fin (2 ^ n)) : Nat).testBit q = (m : Nat).testBit q := by
  show ((m : Nat) % 2 ^ n).testBit q = (m : Nat).testBit q
  rw [Nat.testBit_mod_two_pow]
  simp [hq]

theorem testBit_high_of_lt (n : Nat) (m : Fin (2 ^ (n + 1))) :
    (m : Nat).testBit n = decide ((m : Nat) ≥ 2 ^ n) := by
  have hm : (m : Nat) < 2 ^ (n + 1) := m.isLt
  have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
  have hbit : ((m : Nat) / 2 ^ n).testBit 0 = (m : Nat).testBit n := by
    rw [Nat.testBit_div_two_pow, Nat.zero_add]
  rw [← hbit]
  by_cases h : (m : Nat) ≥ 2 ^ n
  · have hdiv : (m : Nat) / 2 ^ n = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hdiv]
    simp [h]
  · have hdiv : (m : Nat) / 2 ^ n = 0 := Nat.div_eq_of_lt (by omega)
    rw [hdiv]
    simp [h]

/-- Splitting a joint index from its parts: low bits and the high bit. -/
theorem joint_index_eq (n : Nat) (m : Fin (2 ^ (n + 1))) :
    (m : Nat) = (if (m : Nat).testBit n then 2 ^ n else 0)
      + ((lowBits n m : Fin (2 ^ n)) : Nat) := by
  show (m : Nat) = _ + (m : Nat) % 2 ^ n
  rw [testBit_high_of_lt n m]
  have hm : (m : Nat) < 2 ^ (n + 1) := m.isLt
  have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
  by_cases h : (m : Nat) ≥ 2 ^ n
  · simp only [h, decide_true, if_true]
    have hmod : (m : Nat) % 2 ^ n = (m : Nat) - 2 ^ n := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [h, decide_false]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp

/-! ## §3. mulVec collapses for the proven entry forms. -/

/-- `Z_t` acts diagonally on vectors. -/
theorem zMat_mulVec (n t : Nat) (ht : t < n) (v : Fin (2 ^ n) → ℂ)
    (i : Fin (2 ^ n)) :
    ((axisMat n [(⟨t, .z⟩ : PFactor)]).mulVec v) i
      = (if (i : Nat).testBit t then -1 else 1) * v i := by
  rw [axisMat_single_z_diag n t ht]
  rw [Matrix.mulVec_diagonal]

/-- `X_t` acts on vectors by the bit flip. -/
theorem xMat_mulVec (n t : Nat) (ht : t < n) (v : Fin (2 ^ n) → ℂ)
    (i : Fin (2 ^ n)) :
    ((axisMat n [(⟨t, .x⟩ : PFactor)]).mulVec v) i = v (flipT n t ht i) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (flipT n t ht i)]
  · rw [axisMat_single_x_apply n t ht]
    have hcond : (i : Nat) = ((flipT n t ht i : Fin (2 ^ n)) : Nat) ^^^ 2 ^ t := by
      rw [flipT_val, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [if_pos hcond, one_mul]
  · intro k _ hk
    rw [axisMat_single_x_apply n t ht, if_neg, zero_mul]
    intro hik
    apply hk
    apply Fin.ext
    rw [flipT_val, hik, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-! ## §4. Single-wire actions on the split. -/

/-- Low bits commute with low-wire flips. -/
theorem lowBits_flip (n q : Nat) (hq : q < n) (m : Fin (2 ^ (n + 1))) :
    lowBits n (flipT (n + 1) q (by omega) m)
      = flipT n q hq (lowBits n m) := by
  apply Fin.ext
  show ((m : Nat) ^^^ 2 ^ q) % 2 ^ n = ((m : Nat) % 2 ^ n) ^^^ 2 ^ q
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_xor,
      Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
  by_cases hk : k < n
  · simp [hk]
  · have hqk : ¬ q = k := by omega
    simp [hk, hqk]

/-- High-wire flip leaves the low bits alone. -/
theorem lowBits_flip_high (n : Nat) (m : Fin (2 ^ (n + 1))) :
    lowBits n (flipT (n + 1) n (by omega) m) = lowBits n m := by
  apply Fin.ext
  show ((m : Nat) ^^^ 2 ^ n) % 2 ^ n = (m : Nat) % 2 ^ n
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hk : k < n
  · rw [testBit_xor_other (by omega : k ≠ n) (m : Nat)]
  · simp [hk]

/-- **Data-wire `Z_q` passes through the split.** -/
theorem mulVec_zq_tensorHigh (n q : Nat) (hq : q < n) (α β : ℂ)
    (ψ : Fin (2 ^ n) → ℂ) :
    (axisMat (n + 1) [(⟨q, .z⟩ : PFactor)]).mulVec (tensorHigh n α β ψ)
      = tensorHigh n α β ((axisMat n [(⟨q, .z⟩ : PFactor)]).mulVec ψ) := by
  funext m
  rw [zMat_mulVec (n + 1) q (by omega)]
  show _ = (if (m : Nat).testBit n then β else α)
      * ((axisMat n [(⟨q, .z⟩ : PFactor)]).mulVec ψ) (lowBits n m)
  rw [zMat_mulVec n q hq, lowBits_testBit n m q hq]
  show (if (m : Nat).testBit q then -1 else 1)
      * ((if (m : Nat).testBit n then β else α) * ψ (lowBits n m)) = _
  ring

/-- **Data-wire `X_q` passes through the split.** -/
theorem mulVec_xq_tensorHigh (n q : Nat) (hq : q < n) (α β : ℂ)
    (ψ : Fin (2 ^ n) → ℂ) :
    (axisMat (n + 1) [(⟨q, .x⟩ : PFactor)]).mulVec (tensorHigh n α β ψ)
      = tensorHigh n α β ((axisMat n [(⟨q, .x⟩ : PFactor)]).mulVec ψ) := by
  funext m
  rw [xMat_mulVec (n + 1) q (by omega)]
  show tensorHigh n α β ψ (flipT (n + 1) q (by omega) m)
      = (if (m : Nat).testBit n then β else α)
          * ((axisMat n [(⟨q, .x⟩ : PFactor)]).mulVec ψ) (lowBits n m)
  rw [xMat_mulVec n q hq]
  show (if ((flipT (n + 1) q (by omega) m : Fin (2 ^ (n + 1))) : Nat).testBit n
        then β else α) * ψ (lowBits n (flipT (n + 1) q (by omega) m)) = _
  rw [lowBits_flip n q hq, flipT_val,
      testBit_xor_other (by omega : n ≠ q) (m : Nat)]

/-- **Ancilla `Z_n` negates the `|1⟩` amplitude.** -/
theorem mulVec_zn_tensorHigh (n : Nat) (α β : ℂ) (ψ : Fin (2 ^ n) → ℂ) :
    (axisMat (n + 1) [(⟨n, .z⟩ : PFactor)]).mulVec (tensorHigh n α β ψ)
      = tensorHigh n α (-β) ψ := by
  funext m
  rw [zMat_mulVec (n + 1) n (by omega)]
  show (if (m : Nat).testBit n then -1 else 1)
      * ((if (m : Nat).testBit n then β else α) * ψ (lowBits n m))
    = (if (m : Nat).testBit n then -β else α) * ψ (lowBits n m)
  by_cases h : (m : Nat).testBit n <;> simp [h]

/-- **Ancilla `X_n` swaps the amplitudes.** -/
theorem mulVec_xn_tensorHigh (n : Nat) (α β : ℂ) (ψ : Fin (2 ^ n) → ℂ) :
    (axisMat (n + 1) [(⟨n, .x⟩ : PFactor)]).mulVec (tensorHigh n α β ψ)
      = tensorHigh n β α ψ := by
  funext m
  rw [xMat_mulVec (n + 1) n (by omega)]
  show tensorHigh n α β ψ (flipT (n + 1) n (by omega) m)
      = (if (m : Nat).testBit n then α else β) * ψ (lowBits n m)
  show (if ((flipT (n + 1) n (by omega) m : Fin (2 ^ (n + 1))) : Nat).testBit n
        then β else α) * ψ (lowBits n (flipT (n + 1) n (by omega) m)) = _
  rw [lowBits_flip_high, flipT_val, testBit_xor_self_bit]
  by_cases h : (m : Nat).testBit n <;> simp [h]

/-! ## §5. Embedded data axes pass through the split. -/

/-- A whole SORTED data axis (all wires `< n`) passes through the split:
the joint action is the data action tensored with the identity. -/
theorem mulVec_axis_tensorHigh (n : Nat) :
    ∀ (P : PauliProduct), sortedStrict P = true →
      PauliProduct.width P ≤ n →
      (∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x) →
      ∀ (α β : ℂ) (ψ : Fin (2 ^ n) → ℂ),
        (axisMat (n + 1) P).mulVec (tensorHigh n α β ψ)
          = tensorHigh n α β ((axisMat n P).mulVec ψ)
  | [], _, _, _, α, β, ψ => by
      show (axisMat (n + 1) []).mulVec _ = _
      rw [show axisMat (n + 1) [] = 1 from opsMat_one (n + 1),
          show axisMat n [] = 1 from opsMat_one n,
          Matrix.one_mulVec, Matrix.one_mulVec]
  | ⟨q, k⟩ :: P, hs, hw, hk, α, β, ψ => by
      have hw' := hw
      simp only [PauliProduct.width] at hw'
      have hq : q < n := by omega
      have hwP : PauliProduct.width P ≤ n := by omega
      have hsP : sortedStrict P = true := sorted_cons_tail hs
      have hkP : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x :=
        fun f hf => hk f (List.mem_cons_of_mem _ hf)
      rw [axisMat_cons_split (n + 1) ⟨q, k⟩ P hs, ← Matrix.mulVec_mulVec,
          mulVec_axis_tensorHigh n P hsP hwP hkP α β ψ,
          axisMat_cons_split n ⟨q, k⟩ P hs, ← Matrix.mulVec_mulVec]
      obtain hz | hx := hk ⟨q, k⟩ List.mem_cons_self
      · have : k = PKind.z := hz
        subst this
        exact mulVec_zq_tensorHigh n q hq α β _
      · have : k = PKind.x := hx
        subst this
        exact mulVec_xq_tensorHigh n q hq α β _

end FormalRV.PauliRotation
