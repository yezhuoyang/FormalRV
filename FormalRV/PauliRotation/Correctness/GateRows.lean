/-
  FormalRV.PauliRotation.Correctness.GateRows
  ───────────────────────────────
  THE n-QUBIT GATE ROWS of the dictionary leg, built from the reusable
  identity library (`CircuitIdentities.lean`) — each row a structural
  derivation, no entrywise n-qubit computations:

    §1  `opsMat_mul_pointwise` / `axisMat_mk2_split` — DISJOINT-SUPPORT
        MULTIPLICATIVITY: the axis matrix of a multi-qubit product is the
        product of its single-qubit axis matrices.  This reduces EVERY
        multi-qubit axis the Gate dictionary emits (Z_cX_t, Z_aZ_b, …) to
        single-qubit ones.
    §2  `rot_controlled_pauli` — THE CONTROLLED-PAULI IDENTITY (abstract):
        for commuting involutions `A`, `B`,
        `B_{−π/4} · A_{−π/4} · (AB)_{π/4} = e^{iπ/4} · ½(1 + A + B − AB)`
        — the projector form of a controlled gate (`½(1+A)` selects the
        `A = +1` sector where nothing happens; `½(1−A)` applies `B`).
    §3  `cnot_rots_denote` — **THE n-QUBIT CX ROW**: at any distinct wires
        `c, t < n`, the dictionary's three rotations denote
        `e^{iπ/4} · ½(1 + Z_c + X_t − Z_cX_t)` — the controlled-X in
        operator (projector) form, with the explicit global phase.

  Remaining for the full assembly (next tranche): the single-qubit
  basis-action lemmas (Z_q = bit-parity diagonal, X_q = bit flip), which
  convert these operator forms into `Gate.applyNat` permutation matrices,
  and the CCZ row (seven commuting Z-type diagonals, phase polynomial from
  `EightTToCCZScheme`).
-/
import FormalRV.PauliRotation.Correctness.CircuitIdentities
import FormalRV.PauliRotation.Compiler.GateBridge

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ## §1. Disjoint-support multiplicativity. -/

/-- Pointwise product of two qubit assignments with disjoint supports. -/
def mulP (f g : Nat → Pauli) (k : Nat) : Pauli :=
  if f k = .I then g k else f k

/-- **Disjoint-support multiplicativity**: when at every qubit at least one
factor is the identity, the Kronecker interpretations multiply pointwise. -/
theorem opsMat_mul_pointwise (n : Nat) (f g : Nat → Pauli)
    (h : ∀ k, f k = .I ∨ g k = .I) :
    opsMat n f * opsMat n g = opsMat n (mulP f g) := by
  induction n generalizing f g with
  | zero => exact one_mul 1
  | succ n ih =>
      show Matrix.reindex finProdFinEquiv finProdFinEquiv
            (Matrix.kroneckerMap (· * · : ℂ → ℂ → ℂ)
              (opsMat n (fun i => f (i + 1))) (f 0).toMatrix)
          * Matrix.reindex finProdFinEquiv finProdFinEquiv
              (Matrix.kroneckerMap (· * ·)
                (opsMat n (fun i => g (i + 1))) (g 0).toMatrix)
          = opsMat (n + 1) (mulP f g)
      rw [reindexKron_mul,
          ih (fun i => f (i + 1)) (fun i => g (i + 1)) (fun i => h (i + 1)),
          opsMat_succ n (mulP f g)]
      have hhead : (f 0).toMatrix * (g 0).toMatrix = (mulP f g 0).toMatrix := by
        rcases h 0 with h0 | h0
        · rw [mulP]
          simp [h0, Pauli.toMatrix_I_eq_one]
        · rw [mulP]
          by_cases hf : f 0 = Pauli.I <;>
            simp [hf, h0, Pauli.toMatrix_I_eq_one]
      rw [hhead]
      rfl

/-- The qubit assignment of a one-factor axis. -/
theorem kindFn_single (q : Nat) (k : PKind) (i : Nat) :
    kindFn [(⟨q, k⟩ : PFactor)] i
      = if q = i then pkindToBQ k else Pauli.I := by
  by_cases h : q = i
  · simp [kindFn, h]
  · have hb : (q == i) = false := by simpa using h
    simp [kindFn, hb, h]

/-- The qubit assignment of a two-factor axis. -/
theorem kindFn_pair (a b : PFactor) (i : Nat) :
    kindFn [a, b] i
      = if a.qubit = i then pkindToBQ a.kind
        else if b.qubit = i then pkindToBQ b.kind else Pauli.I := by
  by_cases ha : a.qubit = i
  · simp [kindFn, List.find?_cons_of_pos, ha]
  · have ha' : (a.qubit == i) = false := by simpa using ha
    by_cases hb : b.qubit = i
    · simp [kindFn, List.find?, ha', ha, hb]
    · have hb' : (b.qubit == i) = false := by simpa using hb
      simp [kindFn, List.find?, ha', hb', ha, hb]

/-- `pkindToBQ` never produces the identity. -/
theorem pkindToBQ_ne_I (k : PKind) : pkindToBQ k ≠ Pauli.I := by
  cases k <;> simp [pkindToBQ]

/-- **The two-qubit axis splits**: the axis matrix of the sorted pair `mk2`
is the product of the two single-qubit axis matrices (either index order). -/
theorem axisMat_mk2_split (n c t : Nat) (kc kt : PKind) (hct : c ≠ t) :
    axisMat n (mk2 c kc t kt)
      = axisMat n [⟨c, kc⟩] * axisMat n [⟨t, kt⟩] := by
  unfold axisMat
  rw [opsMat_mul_pointwise n _ _ (fun i => by
    by_cases hc : c = i
    · right
      rw [kindFn_single, if_neg (by omega)]
    · left
      rw [kindFn_single, if_neg hc])]
  congr 1
  funext i
  rw [mulP, kindFn_single, kindFn_single]
  have hsplit : kindFn (mk2 c kc t kt) i
      = if c = i then pkindToBQ kc
        else if t = i then pkindToBQ kt else Pauli.I := by
    unfold mk2
    by_cases hlt : c < t
    · rw [if_pos hlt, kindFn_pair]
    · rw [if_neg hlt, kindFn_pair]
      by_cases hc : c = i <;> by_cases ht : t = i
      · omega
      · simp [hc, ht]
      · simp [hc, ht]
      · simp [hc, ht]
  rw [hsplit]
  by_cases hc : c = i <;> simp [hc, pkindToBQ_ne_I]

/-- Disjoint single-qubit axes commute syntactically. -/
theorem commF_singles_disjoint (c t : Nat) (kc kt : PKind) (h : t ≠ c) :
    commF [(⟨c, kc⟩ : PFactor)] [(⟨t, kt⟩ : PFactor)] = true := by
  have hb : (t == c) = false := by simpa using h
  simp [commF, acCount, overlapMismatch, hb]

/-! ## §2. The controlled-Pauli identity (abstract). -/

/-- **THE CONTROLLED-PAULI IDENTITY**: for commuting involutions `A`, `B`,
the dictionary's three signed π/4 rotations compose to the projector form
of the controlled gate — `½(1+A)` (the `A = +1` sector) acts as identity,
`½(1−A)` applies `B` — with the explicit global phase `e^{iπ/4}`. -/
theorem rot_controlled_pauli {A B : Matrix m m ℂ}
    (hA : A * A = 1) (hB : B * B = 1) (hAB : A * B = B * A) :
    rotOf (-(Real.pi / 4)) B * rotOf (-(Real.pi / 4)) A
        * rotOf (Real.pi / 4) (A * B)
      = phaseC (Real.pi / 4) • ((2 : ℂ)⁻¹ • (1 + A + B - A * B)) := by
  have h1 : B * (A * B) = A := by
    rw [← Matrix.mul_assoc, ← hAB, Matrix.mul_assoc, hB, Matrix.mul_one]
  have h2 : A * (A * B) = B := by
    rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  have h4 : A * B * (A * B) = 1 := by
    rw [Matrix.mul_assoc, h1, hA]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hs3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℝ) := by
    rw [pow_succ, hs2]
  unfold rotOf
  rw [phaseC_eq, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.mul_one]
  rw [show B * A = A * B from hAB.symm, h1, h2, h4]
  match_scalars <;>
    (try ring_nf) <;>
    (try simp only [Complex.I_sq, hI3, hs3]) <;>
    try ring

/-! ## §3. The n-qubit CX row. -/

/-- **THE n-QUBIT CX ROW**: at any distinct wires `c, t < n`, the
dictionary's three rotations (`cnotGate c t`) denote the controlled-X in
projector form, `e^{iπ/4} · ½(1 + Z_c + X_t − Z_cX_t)` — by splitting the
two-qubit axis and instantiating the controlled-Pauli identity at the axis
matrices.  No entrywise computation. -/
theorem cnot_rots_denote (n c t : Nat) (hct : c ≠ t) (hc : c + 1 ≤ n) :
    seqDenote n (gateRots (.CX c t))
      = phaseC (Real.pi / 4) •
          ((2 : ℂ)⁻¹ • (1 + axisMat n [⟨c, .z⟩] + axisMat n [⟨t, .x⟩]
            - axisMat n [⟨c, .z⟩] * axisMat n [⟨t, .x⟩])) := by
  have hA := axisMat_mul_self n [(⟨c, .z⟩ : PFactor)]
  have hB := axisMat_mul_self n [(⟨t, .x⟩ : PFactor)]
  have hcomm : axisMat n [(⟨c, .z⟩ : PFactor)] * axisMat n [(⟨t, .x⟩ : PFactor)]
      = axisMat n [(⟨t, .x⟩ : PFactor)] * axisMat n [(⟨c, .z⟩ : PFactor)] :=
    axisMat_comm_of_commF n (by simp [sortedStrict])
      (by simp [PauliProduct.width]; omega)
      (commF_singles_disjoint c t .z .x (fun h => hct h.symm))
  show ((1 * Rot.denote n ⟨true, .piQuarter, [⟨t, .x⟩]⟩)
        * Rot.denote n ⟨true, .piQuarter, [⟨c, .z⟩]⟩)
      * Rot.denote n ⟨false, .piQuarter, mk2 c .z t .x⟩ = _
  rw [Matrix.one_mul]
  show (rotOf (Rot.theta ⟨true, .piQuarter, [⟨t, .x⟩]⟩)
          (axisMat n [⟨t, .x⟩])
        * rotOf (Rot.theta ⟨true, .piQuarter, [⟨c, .z⟩]⟩)
            (axisMat n [⟨c, .z⟩]))
      * rotOf (Rot.theta ⟨false, .piQuarter, mk2 c .z t .x⟩)
          (axisMat n (mk2 c .z t .x)) = _
  simp only [Rot.theta, RAngle.val, if_true, Bool.false_eq_true, if_false]
  rw [axisMat_mk2_split n c t .z .x hct]
  exact rot_controlled_pauli hA hB hcomm

end FormalRV.PauliRotation
