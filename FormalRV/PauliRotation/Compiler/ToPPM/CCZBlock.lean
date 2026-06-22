/-
  FormalRV.PauliRotation.Compiler.ToPPM.CCZBlock
  ─────────────────────────────────────
  **THE 1-CCZ TELEPORT LANE — state machinery.**

  `tensorTriple m f ψ` is `ψ ⊗ |φ_f⟩` with a THREE-ancilla block at wires
  `m, m+1, m+2` whose (possibly ENTANGLED) amplitudes are `f y₁ y₂ y₃` —
  the `|CCZ⟩ = CCZ|+++⟩` resource is `f = cczF` (amplitude `−1` exactly on
  `111`).  The action lemmas:

    • data-wire `Z_d` passes through (`mulVec_zd_tensorTriple`),
    • ancilla `Z_{m+i}` re-signs the `i`-th amplitude slot,
    • ancilla `X_{m+i}` flips the `i`-th amplitude slot,

  from which every axis the CCZ block measures (joints `Z_d·Z_a`, twisted
  destructions `X_a·Z·Z`, corrections `Z_d`) decomposes by the proven
  splits.  The numerically pinned target (verified on all 64 branches):

      Corr(m,b)·Π_b(twisted)·Π_m(joints) (ψ ⊗ cczF)
        = ⅛·(−1)^{⟨m,b⟩} • (CCZ_{d₁d₂d₃} ψ) ⊗ collapse(m,b)

      collapse(m,b) y = (−1)^{⟨b,y⟩ ⊕ m₃y₁y₂ ⊕ m₂y₁y₃ ⊕ m₁y₂y₃}.
-/
import FormalRV.PauliRotation.Compiler.ToPPM.GadgetLowering

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-! ## §1. The triple split. -/

def lowBits3 (m : Nat) (M : Fin (2 ^ (m + 3))) : Fin (2 ^ m) :=
  ⟨(M : Nat) % 2 ^ m, Nat.mod_lt _ (by positivity)⟩

/-- `ψ ⊗ |φ_f⟩`: three ancillas at wires `m, m+1, m+2` with joint
amplitudes `f` (not necessarily a product state). -/
noncomputable def tensorTriple (m : Nat) (f : Bool → Bool → Bool → ℂ)
    (ψ : Fin (2 ^ m) → ℂ) : Fin (2 ^ (m + 3)) → ℂ :=
  fun M => f ((M : Nat).testBit m) ((M : Nat).testBit (m + 1))
      ((M : Nat).testBit (m + 2)) * ψ (lowBits3 m M)

theorem tensorTriple_vec_add (m : Nat) (f : Bool → Bool → Bool → ℂ)
    (ψ φ : Fin (2 ^ m) → ℂ) :
    tensorTriple m f (ψ + φ)
      = tensorTriple m f ψ + tensorTriple m f φ := by
  funext M
  show f _ _ _ * (ψ + φ) (lowBits3 m M) = _
  show f _ _ _ * (ψ (lowBits3 m M) + φ (lowBits3 m M))
      = f _ _ _ * ψ (lowBits3 m M) + f _ _ _ * φ (lowBits3 m M)
  ring

theorem tensorTriple_vec_smul (m : Nat) (f : Bool → Bool → Bool → ℂ)
    (c : ℂ) (ψ : Fin (2 ^ m) → ℂ) :
    tensorTriple m f (c • ψ) = c • tensorTriple m f ψ := by
  funext M
  show f _ _ _ * (c • ψ) (lowBits3 m M) = _
  show f _ _ _ * (c * ψ (lowBits3 m M))
      = c * (f _ _ _ * ψ (lowBits3 m M))
  ring

theorem tensorTriple_f_add (m : Nat) (f g : Bool → Bool → Bool → ℂ)
    (ψ : Fin (2 ^ m) → ℂ) :
    tensorTriple m (fun a b c => f a b c + g a b c) ψ
      = tensorTriple m f ψ + tensorTriple m g ψ := by
  funext M
  show (f _ _ _ + g _ _ _) * ψ (lowBits3 m M) = _
  show _ = f _ _ _ * ψ (lowBits3 m M) + g _ _ _ * ψ (lowBits3 m M)
  ring

theorem tensorTriple_f_smul (m : Nat) (c : ℂ) (f : Bool → Bool → Bool → ℂ)
    (ψ : Fin (2 ^ m) → ℂ) :
    tensorTriple m (fun a b d => c * f a b d) ψ
      = c • tensorTriple m f ψ := by
  funext M
  show (c * f _ _ _) * ψ (lowBits3 m M) = c * (f _ _ _ * ψ (lowBits3 m M))
  ring

/-! ## §2. Index bridges. -/

theorem lowBits3_testBit (m : Nat) (M : Fin (2 ^ (m + 3))) (q : Nat)
    (hq : q < m) :
    ((lowBits3 m M : Fin (2 ^ m)) : Nat).testBit q = (M : Nat).testBit q := by
  show ((M : Nat) % 2 ^ m).testBit q = (M : Nat).testBit q
  rw [Nat.testBit_mod_two_pow]
  simp [hq]

theorem lowBits3_flip (m : Nat) (M : Fin (2 ^ (m + 3))) (i : Nat)
    (hi : m ≤ i) (hi3 : i < m + 3) :
    lowBits3 m (flipT (m + 3) i (by omega) M) = lowBits3 m M := by
  apply Fin.ext
  show ((M : Nat) ^^^ 2 ^ i) % 2 ^ m = (M : Nat) % 2 ^ m
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hk : k < m
  · rw [testBit_xor_other (by omega : k ≠ i) (M : Nat)]
  · simp [hk]

/-! ## §3. Single-wire actions on the triple split. -/

/-- Data-wire `Z_d` passes through. -/
theorem mulVec_zd_tensorTriple (m d : Nat) (hd : d < m)
    (f : Bool → Bool → Bool → ℂ) (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) [(⟨d, .z⟩ : PFactor)]).mulVec (tensorTriple m f ψ)
      = tensorTriple m f ((axisMat m [(⟨d, .z⟩ : PFactor)]).mulVec ψ) := by
  funext M
  rw [zMat_mulVec (m + 3) d (by omega)]
  show _ = f _ _ _ * ((axisMat m [(⟨d, .z⟩ : PFactor)]).mulVec ψ)
      (lowBits3 m M)
  rw [zMat_mulVec m d hd, lowBits3_testBit m M d hd]
  show (if (M : Nat).testBit d then -1 else 1)
      * (f _ _ _ * ψ (lowBits3 m M)) = _
  ring

/-- Ancilla `Z_{m+i}` re-signs the corresponding amplitude slot. -/
theorem mulVec_za_tensorTriple (m : Nat) (i : Fin 3)
    (f : Bool → Bool → Bool → ℂ) (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) [(⟨m + (i : Nat), .z⟩ : PFactor)]).mulVec
        (tensorTriple m f ψ)
      = tensorTriple m
          (fun y₁ y₂ y₃ =>
            (if (match (i : Nat) with | 0 => y₁ | 1 => y₂ | _ => y₃)
             then (-1 : ℂ) else 1) * f y₁ y₂ y₃) ψ := by
  funext M
  rw [zMat_mulVec (m + 3) (m + (i : Nat)) (by omega)]
  have hi := i.isLt
  show (if (M : Nat).testBit (m + (i : Nat)) then -1 else 1)
      * (f ((M : Nat).testBit m) ((M : Nat).testBit (m + 1))
          ((M : Nat).testBit (m + 2)) * ψ (lowBits3 m M))
    = (if (match (i : Nat) with
        | 0 => (M : Nat).testBit m
        | 1 => (M : Nat).testBit (m + 1)
        | _ => (M : Nat).testBit (m + 2)) then (-1 : ℂ) else 1)
      * f ((M : Nat).testBit m) ((M : Nat).testBit (m + 1))
          ((M : Nat).testBit (m + 2)) * ψ (lowBits3 m M)
  rcases (by omega : (i : Nat) = 0 ∨ (i : Nat) = 1 ∨ (i : Nat) = 2)
    with h | h | h <;> rw [h] <;> simp only [Nat.add_zero] <;> ring

/-- Ancilla `X_{m+i}` flips the corresponding amplitude slot. -/
theorem mulVec_xa_tensorTriple (m : Nat) (i : Fin 3)
    (f : Bool → Bool → Bool → ℂ) (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) [(⟨m + (i : Nat), .x⟩ : PFactor)]).mulVec
        (tensorTriple m f ψ)
      = tensorTriple m
          (fun y₁ y₂ y₃ =>
            match (i : Nat) with
            | 0 => f (!y₁) y₂ y₃
            | 1 => f y₁ (!y₂) y₃
            | _ => f y₁ y₂ (!y₃)) ψ := by
  funext M
  rw [xMat_mulVec (m + 3) (m + (i : Nat)) (by omega)]
  have hi := i.isLt
  show tensorTriple m f ψ (flipT (m + 3) (m + (i : Nat)) (by omega) M) = _
  show f (((M : Nat) ^^^ 2 ^ (m + (i : Nat))).testBit m)
      (((M : Nat) ^^^ 2 ^ (m + (i : Nat))).testBit (m + 1))
      (((M : Nat) ^^^ 2 ^ (m + (i : Nat))).testBit (m + 2))
      * ψ (lowBits3 m (flipT (m + 3) (m + (i : Nat)) (by omega) M)) = _
  rw [lowBits3_flip m M (m + (i : Nat)) (by omega) (by omega)]
  rcases (by omega : (i : Nat) = 0 ∨ (i : Nat) = 1 ∨ (i : Nat) = 2)
    with h | h | h <;>
    rw [h] <;>
    simp only [Nat.add_zero] <;>
    rw [testBit_xor_self_bit,
        testBit_xor_other (by omega) (M : Nat),
        testBit_xor_other (by omega) (M : Nat)] <;>
    rfl

/-! ## §4. The block's composite axes, parametrically. -/

/-- The joint measurement axis `Z_d · Z_{m+i}` acts as the data `Z_d`
times the slot-`i` sign. -/
theorem mulVec_joint_tt (m d : Nat) (hd : d < m) (i : Fin 3)
    (f : Bool → Bool → Bool → ℂ) (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) [(⟨d, .z⟩ : PFactor), ⟨m + (i : Nat), .z⟩]).mulVec
        (tensorTriple m f ψ)
      = tensorTriple m
          (fun y₁ y₂ y₃ =>
            (if (match (i : Nat) with | 0 => y₁ | 1 => y₂ | _ => y₃)
             then (-1 : ℂ) else 1) * f y₁ y₂ y₃)
          ((axisMat m [(⟨d, .z⟩ : PFactor)]).mulVec ψ) := by
  rw [axisMat_cons_split (m + 3) ⟨d, .z⟩ [⟨m + (i : Nat), .z⟩]
        (by simp [sortedStrict]; omega),
      ← Matrix.mulVec_mulVec, mulVec_za_tensorTriple,
      mulVec_zd_tensorTriple m d hd]

/-- Specialized clean-index corollaries (defeq instances of the `Fin 3`
lemmas). -/
theorem mulVec_za0_tt (m : Nat) (f : Bool → Bool → Bool → ℂ)
    (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) [(⟨m, .z⟩ : PFactor)]).mulVec (tensorTriple m f ψ)
      = tensorTriple m
          (fun y₁ y₂ y₃ => (if y₁ then (-1 : ℂ) else 1) * f y₁ y₂ y₃) ψ :=
  mulVec_za_tensorTriple m 0 f ψ

theorem mulVec_za1_tt (m : Nat) (f : Bool → Bool → Bool → ℂ)
    (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) [(⟨m + 1, .z⟩ : PFactor)]).mulVec (tensorTriple m f ψ)
      = tensorTriple m
          (fun y₁ y₂ y₃ => (if y₂ then (-1 : ℂ) else 1) * f y₁ y₂ y₃) ψ :=
  mulVec_za_tensorTriple m 1 f ψ

theorem mulVec_za2_tt (m : Nat) (f : Bool → Bool → Bool → ℂ)
    (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) [(⟨m + 2, .z⟩ : PFactor)]).mulVec (tensorTriple m f ψ)
      = tensorTriple m
          (fun y₁ y₂ y₃ => (if y₃ then (-1 : ℂ) else 1) * f y₁ y₂ y₃) ψ :=
  mulVec_za_tensorTriple m 2 f ψ

theorem mulVec_xa0_tt (m : Nat) (f : Bool → Bool → Bool → ℂ)
    (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) [(⟨m, .x⟩ : PFactor)]).mulVec (tensorTriple m f ψ)
      = tensorTriple m (fun y₁ y₂ y₃ => f (!y₁) y₂ y₃) ψ :=
  mulVec_xa_tensorTriple m 0 f ψ

theorem mulVec_xa1_tt (m : Nat) (f : Bool → Bool → Bool → ℂ)
    (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) [(⟨m + 1, .x⟩ : PFactor)]).mulVec (tensorTriple m f ψ)
      = tensorTriple m (fun y₁ y₂ y₃ => f y₁ (!y₂) y₃) ψ :=
  mulVec_xa_tensorTriple m 1 f ψ

theorem mulVec_xa2_tt (m : Nat) (f : Bool → Bool → Bool → ℂ)
    (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) [(⟨m + 2, .x⟩ : PFactor)]).mulVec (tensorTriple m f ψ)
      = tensorTriple m (fun y₁ y₂ y₃ => f y₁ y₂ (!y₃)) ψ :=
  mulVec_xa_tensorTriple m 2 f ψ

/-- The twist factor `(if t ∧ y then −1 else 1)`. -/
noncomputable def twf (t y : Bool) : ℂ := if t && y then -1 else 1

/-- Destruction axis on ancilla 1: `X_m · Z_{m+1}^{t₂} · Z_{m+2}^{t₃}`. -/
theorem mulVec_dest1_tt (m : Nat) (t₂ t₃ : Bool)
    (f : Bool → Bool → Bool → ℂ) (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) ((⟨m, .x⟩ : PFactor)
        :: ((if t₂ then [(⟨m + 1, .z⟩ : PFactor)] else [])
            ++ (if t₃ then [(⟨m + 2, .z⟩ : PFactor)] else [])))).mulVec
        (tensorTriple m f ψ)
      = tensorTriple m
          (fun y₁ y₂ y₃ => twf t₂ y₂ * twf t₃ y₃ * f (!y₁) y₂ y₃) ψ := by
  cases t₂ <;> cases t₃ <;>
    simp only [if_true, if_false, List.nil_append,
      List.cons_append, Bool.false_eq_true]
  · rw [mulVec_xa0_tt]
    congr 1
    funext y₁ y₂ y₃
    simp [twf]
    try ring
  · rw [axisMat_cons_split (m + 3) ⟨m, .x⟩ [⟨m + 2, .z⟩]
          (by simp [sortedStrict]),
        ← Matrix.mulVec_mulVec, mulVec_za2_tt, mulVec_xa0_tt]
    congr 1
    funext y₁ y₂ y₃
    simp [twf]
    try ring
  · rw [axisMat_cons_split (m + 3) ⟨m, .x⟩ [⟨m + 1, .z⟩]
          (by simp [sortedStrict]),
        ← Matrix.mulVec_mulVec, mulVec_za1_tt, mulVec_xa0_tt]
    congr 1
    funext y₁ y₂ y₃
    simp [twf]
    try ring
  · rw [axisMat_cons_split (m + 3) ⟨m, .x⟩ [⟨m + 1, .z⟩, ⟨m + 2, .z⟩]
          (by simp [sortedStrict]),
        ← Matrix.mulVec_mulVec,
        axisMat_cons_split (m + 3) ⟨m + 1, .z⟩ [⟨m + 2, .z⟩]
          (by simp [sortedStrict]),
        ← Matrix.mulVec_mulVec, mulVec_za2_tt, mulVec_za1_tt, mulVec_xa0_tt]
    congr 1
    funext y₁ y₂ y₃
    simp [twf]
    try ring

/-- Destruction axis on ancilla 2: `Z_m^{t₁} · X_{m+1} · Z_{m+2}^{t₃}`. -/
theorem mulVec_dest2_tt (m : Nat) (t₁ t₃ : Bool)
    (f : Bool → Bool → Bool → ℂ) (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) ((if t₁ then [(⟨m, .z⟩ : PFactor)] else [])
        ++ ((⟨m + 1, .x⟩ : PFactor)
            :: (if t₃ then [(⟨m + 2, .z⟩ : PFactor)] else [])))).mulVec
        (tensorTriple m f ψ)
      = tensorTriple m
          (fun y₁ y₂ y₃ => twf t₁ y₁ * twf t₃ y₃ * f y₁ (!y₂) y₃) ψ := by
  cases t₁ <;> cases t₃ <;>
    simp only [if_true, if_false, List.nil_append,
      List.cons_append, Bool.false_eq_true]
  · rw [mulVec_xa1_tt]
    congr 1
    funext y₁ y₂ y₃
    simp [twf]
    try ring
  · rw [axisMat_cons_split (m + 3) ⟨m + 1, .x⟩ [⟨m + 2, .z⟩]
          (by simp [sortedStrict]),
        ← Matrix.mulVec_mulVec, mulVec_za2_tt, mulVec_xa1_tt]
    congr 1
    funext y₁ y₂ y₃
    simp [twf]
    try ring
  · rw [axisMat_cons_split (m + 3) ⟨m, .z⟩ [⟨m + 1, .x⟩]
          (by simp [sortedStrict]),
        ← Matrix.mulVec_mulVec, mulVec_xa1_tt, mulVec_za0_tt]
    congr 1
    funext y₁ y₂ y₃
    simp [twf]
    try ring
  · rw [axisMat_cons_split (m + 3) ⟨m, .z⟩ [⟨m + 1, .x⟩, ⟨m + 2, .z⟩]
          (by simp [sortedStrict]),
        ← Matrix.mulVec_mulVec,
        axisMat_cons_split (m + 3) ⟨m + 1, .x⟩ [⟨m + 2, .z⟩]
          (by simp [sortedStrict]),
        ← Matrix.mulVec_mulVec, mulVec_za2_tt, mulVec_xa1_tt, mulVec_za0_tt]
    congr 1
    funext y₁ y₂ y₃
    simp [twf]
    try ring

/-- Destruction axis on ancilla 3: `Z_m^{t₁} · Z_{m+1}^{t₂} · X_{m+2}`. -/
theorem mulVec_dest3_tt (m : Nat) (t₁ t₂ : Bool)
    (f : Bool → Bool → Bool → ℂ) (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) ((if t₁ then [(⟨m, .z⟩ : PFactor)] else [])
        ++ ((if t₂ then [(⟨m + 1, .z⟩ : PFactor)] else [])
            ++ [(⟨m + 2, .x⟩ : PFactor)]))).mulVec
        (tensorTriple m f ψ)
      = tensorTriple m
          (fun y₁ y₂ y₃ => twf t₁ y₁ * twf t₂ y₂ * f y₁ y₂ (!y₃)) ψ := by
  cases t₁ <;> cases t₂ <;>
    simp only [if_true, if_false, List.nil_append,
      List.cons_append, Bool.false_eq_true]
  · rw [mulVec_xa2_tt]
    congr 1
    funext y₁ y₂ y₃
    simp [twf]
    try ring
  · rw [axisMat_cons_split (m + 3) ⟨m + 1, .z⟩ [⟨m + 2, .x⟩]
          (by simp [sortedStrict]),
        ← Matrix.mulVec_mulVec, mulVec_xa2_tt, mulVec_za1_tt]
    congr 1
    funext y₁ y₂ y₃
    simp [twf]
    try ring
  · rw [axisMat_cons_split (m + 3) ⟨m, .z⟩ [⟨m + 2, .x⟩]
          (by simp [sortedStrict]),
        ← Matrix.mulVec_mulVec, mulVec_xa2_tt, mulVec_za0_tt]
    congr 1
    funext y₁ y₂ y₃
    simp [twf]
    try ring
  · rw [axisMat_cons_split (m + 3) ⟨m, .z⟩ [⟨m + 1, .z⟩, ⟨m + 2, .x⟩]
          (by simp [sortedStrict]),
        ← Matrix.mulVec_mulVec,
        axisMat_cons_split (m + 3) ⟨m + 1, .z⟩ [⟨m + 2, .x⟩]
          (by simp [sortedStrict]),
        ← Matrix.mulVec_mulVec, mulVec_xa2_tt, mulVec_za1_tt, mulVec_za0_tt]
    congr 1
    funext y₁ y₂ y₃
    simp [twf]
    try ring

/-! ## §5. THE 64-BRANCH CCZ-BLOCK THEOREM. -/

/-- Joint specializations at the three concrete ancilla wires. -/
theorem mulVec_joint1_tt (m d : Nat) (hd : d < m)
    (f : Bool → Bool → Bool → ℂ) (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) [(⟨d, .z⟩ : PFactor), ⟨m, .z⟩]).mulVec
        (tensorTriple m f ψ)
      = tensorTriple m
          (fun y₁ y₂ y₃ => (if y₁ then (-1 : ℂ) else 1) * f y₁ y₂ y₃)
          ((axisMat m [(⟨d, .z⟩ : PFactor)]).mulVec ψ) :=
  mulVec_joint_tt m d hd 0 f ψ

theorem mulVec_joint2_tt (m d : Nat) (hd : d < m)
    (f : Bool → Bool → Bool → ℂ) (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) [(⟨d, .z⟩ : PFactor), ⟨m + 1, .z⟩]).mulVec
        (tensorTriple m f ψ)
      = tensorTriple m
          (fun y₁ y₂ y₃ => (if y₂ then (-1 : ℂ) else 1) * f y₁ y₂ y₃)
          ((axisMat m [(⟨d, .z⟩ : PFactor)]).mulVec ψ) :=
  mulVec_joint_tt m d hd 1 f ψ

theorem mulVec_joint3_tt (m d : Nat) (hd : d < m)
    (f : Bool → Bool → Bool → ℂ) (ψ : Fin (2 ^ m) → ℂ) :
    (axisMat (m + 3) [(⟨d, .z⟩ : PFactor), ⟨m + 2, .z⟩]).mulVec
        (tensorTriple m f ψ)
      = tensorTriple m
          (fun y₁ y₂ y₃ => (if y₃ then (-1 : ℂ) else 1) * f y₁ y₂ y₃)
          ((axisMat m [(⟨d, .z⟩ : PFactor)]).mulVec ψ) :=
  mulVec_joint_tt m d hd 2 f ψ

/-- A parity-conditioned `Z_d` correction passes to the data factor with
the parity SYMBOLIC. -/
theorem mulVec_corr_tt (m d : Nat) (hd : d < m) (p : Bool)
    (f : Bool → Bool → Bool → ℂ) (ψ : Fin (2 ^ m) → ℂ) :
    ((if p then axisMat (m + 3) [(⟨d, .z⟩ : PFactor)] else 1)).mulVec
        (tensorTriple m f ψ)
      = tensorTriple m f
          ((if p then axisMat m [(⟨d, .z⟩ : PFactor)] else 1).mulVec ψ) := by
  cases p
  · simp only [Bool.false_eq_true, if_false, Matrix.one_mulVec]
  · simp only [if_true]
    exact mulVec_zd_tensorTriple m d hd f ψ

/-- Symbolic-parity correction at the data-entry level. -/
theorem corr_entry (m d : Nat) (p : Bool) (hd : d < m)
    (v : Fin (2 ^ m) → ℂ) (j : Fin (2 ^ m)) :
    ((if p then axisMat m [(⟨d, .z⟩ : PFactor)] else 1).mulVec v) j
      = (if p && (j : Nat).testBit d then (-1 : ℂ) else 1) * v j := by
  cases p
  · simp only [Bool.false_eq_true, if_false, Matrix.one_mulVec,
      Bool.false_and, one_mul]
  · simp only [if_true, Bool.true_and]
    rw [zMat_mulVec m d hd]

/-- The `|CCZ⟩` resource amplitudes (`−1` exactly on `111`). -/
noncomputable def cczF : Bool → Bool → Bool → ℂ :=
  fun y₁ y₂ y₃ => if y₁ && y₂ && y₃ then -1 else 1

/-- The collapsed ancilla amplitudes on branch `(m, b)` — the
`b`-character times the `m`-driven graph-state quadratic. -/
noncomputable def cczCollapse (m₁ m₂ m₃ b₁ b₂ b₃ : Bool) :
    Bool → Bool → Bool → ℂ :=
  fun y₁ y₂ y₃ =>
    twf b₁ y₁ * twf b₂ y₂ * twf b₃ y₃
      * twf m₃ (y₁ && y₂) * twf m₂ (y₁ && y₃) * twf m₁ (y₂ && y₃)

/-- The branch sign `(−1)^{⟨m,b⟩}`. -/
noncomputable def cczSign (m₁ m₂ m₃ b₁ b₂ b₃ : Bool) : ℂ :=
  twf m₁ b₁ * twf m₂ b₂ * twf m₃ b₃

/-- Sign-atom algebra for the symbolic leaf closure. -/
theorem tw_xor (a b : Bool) :
    (if (a ^^ b) then (-1 : ℂ) else 1)
      = (if a then (-1 : ℂ) else 1) * (if b then (-1 : ℂ) else 1) := by
  cases a <;> cases b <;> norm_num

theorem tw_sq (c : Bool) :
    (if c then (-1 : ℂ) else 1) ^ 2 = 1 := by
  cases c <;> norm_num

theorem tw_cube (c : Bool) :
    (if c then (-1 : ℂ) else 1) ^ 3 = (if c then (-1 : ℂ) else 1) := by
  cases c <;> norm_num

theorem tw_pow_four (c : Bool) :
    (if c then (-1 : ℂ) else 1) ^ 4 = 1 := by
  cases c <;> norm_num

end FormalRV.PauliRotation
