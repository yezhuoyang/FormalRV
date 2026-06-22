/-
  FormalRV.PauliRotation.Correctness.Assembly
  ───────────────────────────────
  D5, THE ASSEMBLY — the dictionary leg CLOSED:

      `seqDenote n (gateRots g) = gphase g • applyMat n g`

  for EVERY Gate-IR program `g` (distinct operands, within width): the
  compiled rotation sequence denotes the gate's Boolean semantics
  (`Gate.applyNat`) as a matrix, with the explicit global phase `gphase g`
  (a product of the per-gate constants `−i`, `e^{iπ/4}`, `−e^{−iπ/8}`).

  Composing with the verified scheduler (`gateRotSchedule_denote`) gives the
  capstone `gateRotSchedule_applyNat`: the PARALLELIZED rotation program of
  any arithmetic gadget means exactly the gadget's semantics — the
  compile → schedule → denote → applyNat chain with no specification seam.
-/
import FormalRV.PauliRotation.Correctness.CCXRow
import FormalRV.PauliRotation.Gadgets.CuccaroAdder

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open FormalRV.BQAlgo
open FormalRV.Framework (update update_apply)
open FormalRV.Resource
open Matrix

/-! ## §1. The identity row and the global phase. -/

theorem applyMat_I (n : Nat) :
    applyMat n FormalRV.Framework.Gate.I = 1 := by
  ext i j
  unfold applyMat
  rw [Matrix.one_apply]
  congr 1
  rw [eq_iff_iff]
  constructor
  · intro h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro b
    by_cases hb : b < n
    · exact h b hb
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt
          (Nat.pow_le_pow_right (by norm_num) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le j.isLt
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · intro h
    subst h
    intro b _
    rfl

/-- **The global phase of a compiled Gate program** — the product of the
proven per-gate constants. -/
noncomputable def gphase : FormalRV.Framework.Gate → ℂ
  | .I => 1
  | .X _ => -Complex.I
  | .CX _ _ => phaseC (Real.pi / 4)
  | .CCX _ _ _ => -(phaseC (-(Real.pi / 8)))
  | .seq g₁ g₂ => gphase g₁ * gphase g₂

/-! ## §2. `applyNat` is realized on `Fin (2^n)`. -/

/-- Within width, the Boolean action of any gate on an encoded basis state
is realized by an encoded basis state (agreeing at ALL bit positions). -/
theorem applyNat_realized (n : Nat) :
    ∀ (g : FormalRV.Framework.Gate), width g ≤ n → ∀ (j : Fin (2 ^ n)),
      ∃ k : Fin (2 ^ n), ∀ b : Nat,
        Gate.applyNat g (fun c => (j : Nat).testBit c) b
          = (k : Nat).testBit b := by
  intro g
  induction g with
  | I => exact fun _ j => ⟨j, fun _ => rfl⟩
  | X q =>
      intro hw j
      simp only [width] at hw
      refine ⟨⟨(j : Nat) ^^^ 2 ^ q, Nat.xor_lt_two_pow j.isLt
        (Nat.pow_lt_pow_right (by norm_num) (by omega))⟩, fun b => ?_⟩
      rw [Gate.applyNat_X, update_apply]
      show _ = ((j : Nat) ^^^ 2 ^ q).testBit b
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      by_cases hbq : b = q
      · subst hbq
        simp [Bool.xor_comm]
      · rw [if_neg hbq, decide_eq_false (fun hh => hbq hh.symm)]
        simp
  | CX c t =>
      intro hw j
      simp only [width] at hw
      by_cases hcj : (j : Nat).testBit c
      · refine ⟨⟨(j : Nat) ^^^ 2 ^ t, Nat.xor_lt_two_pow j.isLt
          (Nat.pow_lt_pow_right (by norm_num) (by omega))⟩, fun b => ?_⟩
        rw [Gate.applyNat_CX, update_apply]
        show _ = ((j : Nat) ^^^ 2 ^ t).testBit b
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        by_cases hbt : b = t
        · subst hbt
          simp [hcj, Bool.xor_comm]
        · rw [if_neg hbt, decide_eq_false (fun hh => hbt hh.symm)]
          simp
      · refine ⟨j, fun b => ?_⟩
        rw [Gate.applyNat_CX, update_apply]
        by_cases hbt : b = t
        · subst hbt
          simp [hcj]
        · rw [if_neg hbt]
  | CCX a b' t =>
      intro hw j
      simp only [width] at hw
      by_cases hcj : (j : Nat).testBit a && (j : Nat).testBit b'
      · refine ⟨⟨(j : Nat) ^^^ 2 ^ t, Nat.xor_lt_two_pow j.isLt
          (Nat.pow_lt_pow_right (by norm_num) (by omega))⟩, fun b => ?_⟩
        rw [Gate.applyNat_CCX, update_apply]
        show _ = ((j : Nat) ^^^ 2 ^ t).testBit b
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        by_cases hbt : b = t
        · subst hbt
          simp [hcj, Bool.xor_comm]
        · rw [if_neg hbt, decide_eq_false (fun hh => hbt hh.symm)]
          simp
      · refine ⟨j, fun b => ?_⟩
        rw [Gate.applyNat_CCX, update_apply]
        by_cases hbt : b = t
        · subst hbt
          simp [hcj]
        · rw [if_neg hbt]
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hw j
      simp only [width] at hw
      obtain ⟨k₁, hk₁⟩ := ih₁ (by omega) j
      obtain ⟨k₂, hk₂⟩ := ih₂ (by omega) k₁
      refine ⟨k₂, fun b => ?_⟩
      rw [Gate.applyNat_seq,
          show Gate.applyNat g₁ (fun c => (j : Nat).testBit c)
            = fun c => (k₁ : Nat).testBit c from funext hk₁]
      exact hk₂ b

/-! ## §3. `applyMat` composes contravariantly. -/

theorem applyMat_seq (n : Nat) (g₁ g₂ : FormalRV.Framework.Gate)
    (hw₁ : width g₁ ≤ n) :
    applyMat n (.seq g₁ g₂) = applyMat n g₂ * applyMat n g₁ := by
  ext i j
  obtain ⟨k₀, hk₀⟩ := applyNat_realized n g₁ hw₁ j
  rw [Matrix.mul_apply, Finset.sum_eq_single k₀]
  · show applyMat n (.seq g₁ g₂) i j = _
    unfold applyMat
    rw [if_pos (fun b _ => (hk₀ b).symm), mul_one,
        Gate.applyNat_seq,
        show Gate.applyNat g₁ (fun c => (j : Nat).testBit c)
          = fun c => (k₀ : Nat).testBit c from funext hk₀]
  · intro k _ hk
    show _ * applyMat n g₁ k j = 0
    unfold applyMat
    have hfalse : ¬ ∀ b, b < n → (k : Nat).testBit b
        = Gate.applyNat g₁ (fun c => (j : Nat).testBit c) b := by
      intro hcond
      apply hk
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro b
      by_cases hb : b < n
      · rw [hcond b hb, hk₀ b]
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le k.isLt
            (Nat.pow_le_pow_right (by norm_num) (by omega))),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le k₀.isLt
            (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rw [if_neg hfalse, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-! ## §4. THE ASSEMBLY. -/

/-- **THE DICTIONARY LEG, CLOSED**: every Gate-IR program's compiled
rotation sequence denotes the gate's Boolean semantics, with the explicit
global phase. -/
theorem gateRots_denote_applyNat (n : Nat) :
    ∀ (g : FormalRV.Framework.Gate), opsOK g = true → width g ≤ n →
      seqDenote n (gateRots g) = gphase g • applyMat n g := by
  intro g
  induction g with
  | I =>
      intro _ _
      show (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) = _
      rw [applyMat_I]
      show _ = (1 : ℂ) • 1
      rw [one_smul]
  | X q =>
      intro _ hw
      simp only [width] at hw
      exact xGate_rots_applyNat n q (by omega)
  | CX c t =>
      intro hops hw
      simp only [opsOK, decide_eq_true_eq] at hops
      simp only [width] at hw
      exact cnot_rots_applyNat n c t hops (by omega) (by omega)
  | CCX a b t =>
      intro hops hw
      simp only [opsOK, Bool.and_eq_true, decide_eq_true_eq] at hops
      simp only [width] at hw
      exact ccx_rots_applyNat n a b t hops.1.1 hops.1.2 hops.2
        (by omega) (by omega) (by omega)
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hops hw
      simp only [opsOK, Bool.and_eq_true] at hops
      simp only [width] at hw
      show seqDenote n (gateRots g₁ ++ gateRots g₂) = _
      rw [seqDenote_append, ih₂ hops.2 (by omega), ih₁ hops.1 (by omega),
          applyMat_seq n g₁ g₂ (by omega), Matrix.smul_mul, Matrix.mul_smul,
          smul_smul]
      show _ = (gphase g₁ * gphase g₂) • _
      rw [mul_comm]

/-- **THE CAPSTONE**: the PARALLELIZED rotation program of any Gate-IR
gadget denotes the gadget's Boolean semantics — compile → schedule →
denote → `Gate.applyNat`, no specification seam. -/
theorem gateRotSchedule_applyNat (n : Nat) (g : FormalRV.Framework.Gate)
    (hops : opsOK g = true) (hw : width g ≤ n) :
    RotProg.denote n (gateRotSchedule g) = gphase g • applyMat n g := by
  rw [gateRotSchedule_denote n g hops hw, gateRots_denote_applyNat n g hops hw]

/-! ## §5. A gadget, end to end. -/

/-- **The 4-bit Cuccaro adder, FULLY semantically compiled**: its
parallelized Pauli-rotation program denotes the adder's own Boolean
semantics (the function `cuccaro_n_bit_adder_full_correct` is about), up to
the explicit global phase. -/
theorem cuccaroRot_applyNat_4 :
    RotProg.denote (width (cuccaro_n_bit_adder_full 4 0)) (cuccaroRot 4 0)
      = gphase (cuccaro_n_bit_adder_full 4 0)
          • applyMat _ (cuccaro_n_bit_adder_full 4 0) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

end FormalRV.PauliRotation
