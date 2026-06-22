/-
  FormalRV.PauliRotation.Compiler.PushRules
  ────────────────────────────────
  **VERIFIED CLIFFORD PUSHING — the Litinski optimization, syntactically.**

  "A Game of Surface Codes" delays every Clifford (±π/4, ±π/2) rotation past
  the non-Clifford content to the end of the circuit.  The matrix-level push
  rule (`rot_quarter_push`, CircuitIdentities) conjugates axes as MATRICES;
  this file makes the move a verified rewrite on the rotation IR:

      [r] :: [s] :: p   ≡   [r.pushedBy s] :: [r] :: p
                                    (r a ±π/4 rotation, axes anticommuting)

  where `(r.pushedBy s).axis = mulF r.axis s.axis` and the ±i of the
  phase-tracked product (`axisMat_mulF`, PauliPhase) lands in the `neg`
  flag.  Counts are preserved ON THE NOSE (the pushed rotation keeps its
  angle — Clifford pushing NEVER changes the T-count), and so is depth.

    §1  matrix-level chirality twins (`rot_quarter_push_neg`,
        `rot_half_push`/`_neg`, `rotOf_neg_axis`);
    §2  the syntactic pushed rotation and its `theta` bookkeeping;
    §3  the Rot-level DELAY theorems (quarter, both chiralities; half);
    §4  program-level adjacent rewrites + count/depth preservation
        (swap for commuting axes, push for anticommuting).
-/
import FormalRV.PauliRotation.Semantics.PauliPhase
import FormalRV.PauliRotation.Correctness.CircuitIdentities

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open FormalRV.Resource
open Matrix

variable {m : Type*} [DecidableEq m] [Fintype m]

/-! ## §1. Matrix-level chirality twins. -/

omit [Fintype m] in
/-- Negating the axis negates the angle. -/
theorem rotOf_neg_axis (θ : ℝ) (M : Matrix m m ℂ) :
    rotOf θ (-M) = rotOf (-θ) M := by
  unfold rotOf
  rw [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  module

/-- The −π/4 chirality of the push rule: the conjugated axis is `(+i)·MN`. -/
theorem rot_quarter_push_neg {M N : Matrix m m ℂ} (hM : M * M = 1)
    (hMN : M * N = -(N * M)) (φ : ℝ) :
    rotOf (-(Real.pi / 4)) M * rotOf φ N
      = rotOf φ (Complex.I • (M * N)) * rotOf (-(Real.pi / 4)) M := by
  have hMNM : M * N * M = -N := conj_anticomm hM hMN
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  unfold rotOf
  rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four,
      Complex.ofReal_neg]
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.mul_one]
  rw [show M * N * M = -N from hMNM]
  ring_nf
  simp only [Complex.I_sq, hI3]
  module

/-- **The π/2 delay rule**: a π/2 (Pauli) rotation delays past an
anticommuting rotation by flipping its angle sign — already in DELAY form
(`s` first on the left = `s` earlier in the program). -/
theorem rot_half_push {M N : Matrix m m ℂ}
    (hMN : M * N = -(N * M)) (φ : ℝ) :
    rotOf φ N * rotOf (Real.pi / 2) M
      = rotOf (Real.pi / 2) M * rotOf (-φ) N := by
  have hNM : N * M = -(M * N) := by
    rw [hMN]
    exact (neg_neg (N * M)).symm
  rw [rotOf_pi_div_two, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  unfold rotOf
  rw [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  rw [hNM]
  module

/-- The −π/2 chirality (identical conjugation — the scalars cancel). -/
theorem rot_half_push_neg {M N : Matrix m m ℂ}
    (hMN : M * N = -(N * M)) (φ : ℝ) :
    rotOf φ N * rotOf (-(Real.pi / 2)) M
      = rotOf (-(Real.pi / 2)) M * rotOf (-φ) N := by
  have hNM : N * M = -(M * N) := by
    rw [hMN]
    exact (neg_neg (N * M)).symm
  rw [rotOf_neg_pi_div_two, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  unfold rotOf
  rw [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  rw [hNM]
  module

/-! ## §2. The syntactic pushed rotation. -/

/-- `s` as it must appear EARLIER in the program when the ±π/4 Clifford `r`
is DELAYED past it: the axis becomes the frame product `mulF r.axis s.axis`
and the ±i of the phase-tracked product lands in `neg`. -/
def Rot.pushedBy (r s : Rot) : Rot :=
  ⟨s.neg ^^ ((decide (phaseF r.axis s.axis % 4 = 1)) ^^ r.neg),
   s.angle, mulF r.axis s.axis⟩

/-- `s` as it must appear earlier when a ±π/2 (Pauli) rotation is delayed
past it: same axis, angle sign flipped. -/
def Rot.pushedByHalf (s : Rot) : Rot := ⟨!s.neg, s.angle, s.axis⟩

private theorem theta_xor_true (ne : Bool) (a : RAngle)
    (ax ax' : PauliProduct) :
    Rot.theta ⟨ne ^^ true, a, ax'⟩ = -(Rot.theta ⟨ne, a, ax⟩) := by
  cases ne <;> simp [Rot.theta]

private theorem theta_xor_false (ne : Bool) (a : RAngle)
    (ax ax' : PauliProduct) :
    Rot.theta ⟨ne ^^ false, a, ax'⟩ = Rot.theta ⟨ne, a, ax⟩ := by
  cases ne <;> simp [Rot.theta]

/-! ## §3. The Rot-level delay theorems. -/

/-- Anticommutation of the axis matrices from `commF = false`. -/
theorem axisMat_anticomm_of_not_commF (n : Nat) {P Q : PauliProduct}
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (h : commF P Q = false) :
    axisMat n P * axisMat n Q = -(axisMat n Q * axisMat n P) := by
  refine axisMat_anticomm n hs hw ?_
  unfold commF at h
  simp only [beq_eq_false_iff_ne, ne_eq] at h
  omega

/-- **THE QUARTER-PUSH DELAY THEOREM**: a ±π/4 rotation `r` delays past an
anticommuting rotation `s` (any angle), with `s` replaced by the SYNTACTIC
`r.pushedBy s` — axis `mulF r.axis s.axis`, sign in `neg`. -/
theorem Rot.denote_push_delay (n : Nat) (r s : Rot)
    (hr : r.angle = .piQuarter)
    (hsr : sortedStrict r.axis = true)
    (hwr : PauliProduct.width r.axis ≤ n)
    (hss : sortedStrict s.axis = true)
    (hac : commF r.axis s.axis = false) :
    Rot.denote n s * Rot.denote n r
      = Rot.denote n r * Rot.denote n (r.pushedBy s) := by
  set M := axisMat n r.axis with hMdef
  set N := axisMat n s.axis with hNdef
  have hM : M * M = 1 := axisMat_mul_self n r.axis
  have hMN : M * N = -(N * M) :=
    axisMat_anticomm_of_not_commF n hsr hwr hac
  have hkey : M * N
      = (Complex.I ^ phaseF r.axis s.axis) • axisMat n (mulF r.axis s.axis) :=
    axisMat_mulF n _ _ hsr hwr hss
  have hpodd : phaseF r.axis s.axis % 2 = 1 := phaseF_odd_of_not_commF hac
  have h4 : phaseF r.axis s.axis % 4 = 1 ∨ phaseF r.axis s.axis % 4 = 3 := by
    omega
  -- the conjugation factor c with the OPPOSITE chirality of r
  obtain ⟨c, hcpush, hcval⟩ :
      ∃ c : ℂ, (rotOf (-(r.theta)) M * rotOf s.theta N
          = rotOf s.theta (c • (M * N)) * rotOf (-(r.theta)) M)
        ∧ c = (if r.neg then -Complex.I else Complex.I) := by
    cases hneg : r.neg with
    | false =>
        refine ⟨Complex.I, ?_, by simp⟩
        have hθ : r.theta = Real.pi / 4 := by
          rw [show r.theta = if r.neg then -r.angle.val else r.angle.val
                from rfl, hneg, hr]
          simp [RAngle.val]
        rw [hθ]
        exact rot_quarter_push_neg hM hMN s.theta
    | true =>
        refine ⟨-Complex.I, ?_, by simp⟩
        have hθ : r.theta = -(Real.pi / 4) := by
          rw [show r.theta = if r.neg then -r.angle.val else r.angle.val
                from rfl, hneg, hr]
          simp [RAngle.val]
        rw [hθ, neg_neg]
        exact rot_quarter_push hM hMN s.theta
  -- S·X = X·S₂ from X⁻¹·S = S₂·X⁻¹
  have hcancel1 : rotOf r.theta M * rotOf (-(r.theta)) M = 1 :=
    rotOf_cancel hM r.theta
  have hcancel2 : rotOf (-(r.theta)) M * rotOf r.theta M = 1 := by
    have := rotOf_cancel hM (-(r.theta))
    rwa [neg_neg] at this
  have hmain : Rot.denote n s * Rot.denote n r
      = Rot.denote n r * rotOf s.theta (c • (M * N)) := by
    show rotOf s.theta N * rotOf r.theta M = rotOf r.theta M * _
    calc rotOf s.theta N * rotOf r.theta M
        = (rotOf r.theta M * rotOf (-(r.theta)) M)
            * rotOf s.theta N * rotOf r.theta M := by
          rw [hcancel1, Matrix.one_mul]
      _ = rotOf r.theta M
            * (rotOf (-(r.theta)) M * rotOf s.theta N)
            * rotOf r.theta M := by
          simp only [Matrix.mul_assoc]
      _ = rotOf r.theta M
            * (rotOf s.theta (c • (M * N)) * rotOf (-(r.theta)) M)
            * rotOf r.theta M := by
          rw [hcpush]
      _ = rotOf r.theta M * rotOf s.theta (c • (M * N))
            * (rotOf (-(r.theta)) M * rotOf r.theta M) := by
          simp only [Matrix.mul_assoc]
      _ = rotOf r.theta M * rotOf s.theta (c • (M * N)) := by
          rw [hcancel2, Matrix.mul_one]
  rw [hmain]
  congr 1
  -- reduce the conjugated axis to the syntactic pushed rotation
  rw [hkey, smul_smul]
  show rotOf s.theta
      ((c * Complex.I ^ phaseF r.axis s.axis)
        • axisMat n (mulF r.axis s.axis))
    = rotOf (Rot.theta (r.pushedBy s)) (axisMat n (mulF r.axis s.axis))
  have hpush_th : Rot.theta (r.pushedBy s)
      = Rot.theta ⟨s.neg ^^ ((decide (phaseF r.axis s.axis % 4 = 1)) ^^ r.neg),
          s.angle, mulF r.axis s.axis⟩ := rfl
  have hs_th : Rot.theta ⟨s.neg, s.angle, s.axis⟩ = s.theta := rfl
  rcases h4 with h41 | h43
  · have hIp : Complex.I ^ phaseF r.axis s.axis = Complex.I := by
      rw [I_pow_mod, h41, pow_one]
    have hd : decide (phaseF r.axis s.axis % 4 = 1) = true := by
      simp [h41]
    cases hneg : r.neg with
    | false =>
        -- c = i, scalar = i·i = −1 → angle flips
        rw [hcval, hneg, if_neg (by simp), hIp, Complex.I_mul_I, neg_one_smul,
            rotOf_neg_axis, hpush_th, hd, hneg]
        rw [show (true ^^ false) = true from rfl,
            theta_xor_true s.neg s.angle s.axis (mulF r.axis s.axis), hs_th]
    | true =>
        -- c = −i, scalar = (−i)·i = 1 → angle unchanged
        rw [hcval, hneg, if_pos rfl, hIp,
            show (-Complex.I) * Complex.I = 1 from by
              rw [neg_mul, Complex.I_mul_I, neg_neg],
            one_smul, hpush_th, hd, hneg]
        rw [show (true ^^ true) = false from rfl,
            theta_xor_false s.neg s.angle s.axis (mulF r.axis s.axis), hs_th]
  · have hIp : Complex.I ^ phaseF r.axis s.axis = -Complex.I := by
      rw [I_pow_mod, h43, pow_succ, Complex.I_sq]
      ring
    have hd : decide (phaseF r.axis s.axis % 4 = 1) = false := by
      simp [h43]
    cases hneg : r.neg with
    | false =>
        -- c = i, scalar = i·(−i) = 1 → angle unchanged
        rw [hcval, hneg, if_neg (by simp), hIp,
            show Complex.I * (-Complex.I) = 1 from by
              rw [mul_neg, Complex.I_mul_I, neg_neg],
            one_smul, hpush_th, hd, hneg]
        rw [show (false ^^ false) = false from rfl,
            theta_xor_false s.neg s.angle s.axis (mulF r.axis s.axis), hs_th]
    | true =>
        -- c = −i, scalar = (−i)·(−i) = −1 → angle flips
        rw [hcval, hneg, if_pos rfl, hIp,
            show (-Complex.I) * (-Complex.I) = -1 from by
              rw [neg_mul_neg, Complex.I_mul_I],
            neg_one_smul, rotOf_neg_axis, hpush_th, hd, hneg]
        rw [show (false ^^ true) = true from rfl,
            theta_xor_true s.neg s.angle s.axis (mulF r.axis s.axis), hs_th]

/-- **THE HALF-PUSH DELAY THEOREM**: a ±π/2 (Pauli) rotation delays past an
anticommuting rotation by flipping its angle sign — axis untouched. -/
theorem Rot.denote_push_half_delay (n : Nat) (r s : Rot)
    (hr : r.angle = .piHalf)
    (hsr : sortedStrict r.axis = true)
    (hwr : PauliProduct.width r.axis ≤ n)
    (hac : commF r.axis s.axis = false) :
    Rot.denote n s * Rot.denote n r
      = Rot.denote n r * Rot.denote n (Rot.pushedByHalf s) := by
  have hMN : axisMat n r.axis * axisMat n s.axis
      = -(axisMat n s.axis * axisMat n r.axis) :=
    axisMat_anticomm_of_not_commF n hsr hwr hac
  have hflip : Rot.theta (Rot.pushedByHalf s) = -(s.theta) := by
    show Rot.theta ⟨!s.neg, s.angle, s.axis⟩ = _
    cases hneg : s.neg <;>
      simp [Rot.theta, hneg] <;>
      ring_nf <;>
      rw [show s.theta = if s.neg then -s.angle.val else s.angle.val from rfl,
          hneg] <;>
      simp
  show rotOf s.theta (axisMat n s.axis) * rotOf r.theta (axisMat n r.axis)
      = rotOf r.theta (axisMat n r.axis)
        * rotOf (Rot.theta (Rot.pushedByHalf s)) (axisMat n s.axis)
  rw [hflip]
  cases hneg : r.neg with
  | false =>
      have hθ : r.theta = Real.pi / 2 := by
        rw [show r.theta = if r.neg then -r.angle.val else r.angle.val
              from rfl, hneg, hr]
        simp [RAngle.val]
      rw [hθ]
      exact rot_half_push hMN s.theta
  | true =>
      have hθ : r.theta = -(Real.pi / 2) := by
        rw [show r.theta = if r.neg then -r.angle.val else r.angle.val
              from rfl, hneg, hr]
        simp [RAngle.val]
      rw [hθ]
      exact rot_half_push_neg hMN s.theta

/-! ## §4. Program-level adjacent rewrites. -/

private theorem layer_singleton (n : Nat) (x : Rot) :
    RotLayer.denote n [x] = Rot.denote n x := by
  simp [RotLayer.denote]

/-- **THE PUSH REWRITE**: delay an adjacent ±π/4 Clifford past an
anticommuting rotation. -/
theorem denote_push_adjacent (n : Nat) (r s : Rot) (p : RotProg)
    (hr : r.angle = .piQuarter)
    (hsr : sortedStrict r.axis = true)
    (hwr : PauliProduct.width r.axis ≤ n)
    (hss : sortedStrict s.axis = true)
    (hac : commF r.axis s.axis = false) :
    RotProg.denote n ([r] :: [s] :: p)
      = RotProg.denote n ([r.pushedBy s] :: [r] :: p) := by
  show (RotProg.denote n p * RotLayer.denote n [s]) * RotLayer.denote n [r]
      = (RotProg.denote n p * RotLayer.denote n [r])
          * RotLayer.denote n [r.pushedBy s]
  rw [layer_singleton, layer_singleton, layer_singleton,
      Matrix.mul_assoc, Matrix.mul_assoc,
      Rot.denote_push_delay n r s hr hsr hwr hss hac]

/-- **THE HALF-PUSH REWRITE**: delay an adjacent ±π/2 Pauli rotation. -/
theorem denote_push_half_adjacent (n : Nat) (r s : Rot) (p : RotProg)
    (hr : r.angle = .piHalf)
    (hsr : sortedStrict r.axis = true)
    (hwr : PauliProduct.width r.axis ≤ n)
    (hac : commF r.axis s.axis = false) :
    RotProg.denote n ([r] :: [s] :: p)
      = RotProg.denote n ([Rot.pushedByHalf s] :: [r] :: p) := by
  show (RotProg.denote n p * RotLayer.denote n [s]) * RotLayer.denote n [r]
      = (RotProg.denote n p * RotLayer.denote n [r])
          * RotLayer.denote n [Rot.pushedByHalf s]
  rw [layer_singleton, layer_singleton, layer_singleton,
      Matrix.mul_assoc, Matrix.mul_assoc,
      Rot.denote_push_half_delay n r s hr hsr hwr hac]

/-- **THE SWAP REWRITE**: adjacent rotations with commuting axes exchange. -/
theorem denote_swap_adjacent (n : Nat) (r s : Rot) (p : RotProg)
    (hss : sortedStrict s.axis = true)
    (hws : PauliProduct.width s.axis ≤ n)
    (hc : commF s.axis r.axis = true) :
    RotProg.denote n ([r] :: [s] :: p)
      = RotProg.denote n ([s] :: [r] :: p) := by
  show (RotProg.denote n p * RotLayer.denote n [s]) * RotLayer.denote n [r]
      = (RotProg.denote n p * RotLayer.denote n [r]) * RotLayer.denote n [s]
  rw [layer_singleton, layer_singleton,
      Matrix.mul_assoc, Matrix.mul_assoc,
      (Rot.denote_swap n r s hss hws hc).symm]

/-! ### Count and depth preservation: pushing NEVER changes the T-count. -/

theorem countAngle_push_adjacent (a : RAngle) (r s : Rot) (p : RotProg) :
    countAngle a ([r.pushedBy s] :: [r] :: p)
      = countAngle a ([r] :: [s] :: p) := by
  show countAngleL a [r.pushedBy s] + (countAngleL a [r] + countAngle a p)
      = countAngleL a [r] + (countAngleL a [s] + countAngle a p)
  have h1 : countAngleL a [r.pushedBy s] = countAngleL a [s] := by
    simp [countAngleL, Rot.pushedBy]
  omega

/-- **Clifford pushing preserves the T-count on the nose.** -/
theorem countPi8_push_adjacent (r s : Rot) (p : RotProg) :
    countPi8 ([r.pushedBy s] :: [r] :: p) = countPi8 ([r] :: [s] :: p) :=
  countAngle_push_adjacent .piEighth r s p

theorem countRot_push_adjacent (r s : Rot) (p : RotProg) :
    countRot ([r.pushedBy s] :: [r] :: p) = countRot ([r] :: [s] :: p) := rfl

theorem rotDepth_push_adjacent (r s : Rot) (p : RotProg) :
    rotDepth ([r.pushedBy s] :: [r] :: p) = rotDepth ([r] :: [s] :: p) := rfl

/-! ### Smoke examples (`mulF` is WF-compiled, so the axis is rewritten by
its unfold lemmas; everything else reduces). -/

/-- Delaying S(Z₀) past X₀(π/8): the pushed axis is `Z·X = iY` — the
rotation becomes a `−Y` rotation (phase `i`, flip). -/
example :
    (Rot.pushedBy ⟨false, .piQuarter, [⟨0, .z⟩]⟩
        ⟨false, .piEighth, [⟨0, .x⟩]⟩)
      = ⟨true, .piEighth, [⟨0, .y⟩]⟩ := by
  unfold Rot.pushedBy
  rw [show mulF [(⟨0, .z⟩ : PFactor)] [⟨0, .x⟩] = [⟨0, .y⟩] from by
        rw [mulF_cons_combine [] [] (by decide) (by decide) rfl, mulF_nil_left]]
  rfl

/-- Delaying S(Z₀) past Y₀: `Z·Y = −iX` — no flip. -/
example :
    (Rot.pushedBy ⟨false, .piQuarter, [⟨0, .z⟩]⟩
        ⟨false, .piEighth, [⟨0, .y⟩]⟩)
      = ⟨false, .piEighth, [⟨0, .x⟩]⟩ := by
  unfold Rot.pushedBy
  rw [show mulF [(⟨0, .z⟩ : PFactor)] [⟨0, .y⟩] = [⟨0, .x⟩] from by
        rw [mulF_cons_combine [] [] (by decide) (by decide) rfl, mulF_nil_left]]
  rfl

/-- Delaying S(Z₀Z₁) past X₀(π/8): pushed axis `Y₀Z₁`. -/
example :
    (Rot.pushedBy ⟨false, .piQuarter, [⟨0, .z⟩, ⟨1, .z⟩]⟩
        ⟨false, .piEighth, [⟨0, .x⟩]⟩)
      = ⟨true, .piEighth, [⟨0, .y⟩, ⟨1, .z⟩]⟩ := by
  unfold Rot.pushedBy
  rw [show mulF [(⟨0, .z⟩ : PFactor), ⟨1, .z⟩] [⟨0, .x⟩]
        = [⟨0, .y⟩, ⟨1, .z⟩] from by
        rw [mulF_cons_combine [(⟨1, .z⟩ : PFactor)] [] (by decide) (by decide)
              rfl,
            mulF_nil_right]]
  rfl

end FormalRV.PauliRotation
