/-
  FormalRV.PauliRotation.Compiler.Rules
  ────────────────────────────
  Optimization rules for Pauli-rotation programs, each carried by a
  SEMANTIC-PRESERVATION theorem over `Semantics.lean` and (where counts
  change) an honest COUNT theorem over `Resource/RotationCount.lean`:

    • `dropPi`        — π rotations are global phases: removing them changes
                        the denotation by exactly `(−1)^(countAngle .pi p)`
                        (`dropPi_denote`), removes nothing else
                        (`countAngle_dropPi`), and preserves well-formedness
                        and depth.
    • cancellation    — adjacent inverse rotations vanish
                        (`denote_cancel_adjacent`), saving 2 rotations
                        (`countRot_cancel_pair`).
    • angle merging   — adjacent same-axis same-angle rotations fuse into
                        the doubled angle (`denote_double_adjacent`):
                        two T's = one S, two S's = one Pauli, …; a doubled
                        π rotation vanishes outright (`denote_pi_sq_adjacent`).

  SCOPE: the rules below act on ADJACENT rotations (singleton layers).
  The commutation bridge they once waited on is PROVEN — CommBridge.lean
  (`axisMat_comm_of_commF`, `Rot.denote_swap`), Scheduler.lean lifts it to
  the verified ASAP parallelizer, and PushRules.lean adds the Litinski
  ANTICOMMUTING push (`denote_push_adjacent`, via the phase-tracked
  product `axisMat_mulF` of PauliPhase.lean).  Nothing here assumes any of
  them; this file remains the adjacent-rule core.
-/
import FormalRV.PauliRotation.Semantics.Core
import FormalRV.Resource.RotationCount

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource

/-! ## §1. Dropping π rotations (global phases). -/

/-- Remove the π rotations from a layer. -/
def dropPiL (L : RotLayer) : RotLayer := L.filter (fun r => r.angle != .pi)

/-- Remove the π rotations from a program. -/
def dropPi (p : RotProg) : RotProg := p.map dropPiL

theorem dropPiL_denote (n : Nat) (L : RotLayer) :
    RotLayer.denote n L
      = ((-1 : ℂ) ^ countAngleL .pi L) • RotLayer.denote n (dropPiL L) := by
  induction L with
  | nil => simp [dropPiL, countAngleL]
  | cons r t ih =>
      by_cases h : r.angle = .pi
      · have hcnt : countAngleL .pi (r :: t) = countAngleL .pi t + 1 := by
          simp [countAngleL, h]
        have hdrop : dropPiL (r :: t) = dropPiL t := by
          simp [dropPiL, h]
        rw [RotLayer.denote_cons, Rot.denote_pi n r h, ih, hcnt, hdrop, pow_succ,
            neg_one_mul, ← neg_smul]
        congr 1
        ring
      · have hcnt : countAngleL .pi (r :: t) = countAngleL .pi t := by
          simp [countAngleL, h]
        have hdrop : dropPiL (r :: t) = r :: dropPiL t := by
          simp [dropPiL, h]
        rw [RotLayer.denote_cons, ih, hcnt, hdrop, RotLayer.denote_cons,
            mul_smul_comm]

/-- **Soundness of `dropPi`**: removing π rotations changes the denotation by
EXACTLY the global phase `(−1)^(number of π rotations)` — the exponent being
the independent `Resource/` counter. -/
theorem dropPi_denote (n : Nat) (p : RotProg) :
    RotProg.denote n p
      = ((-1 : ℂ) ^ countAngle .pi p) • RotProg.denote n (dropPi p) := by
  induction p with
  | nil => simp [dropPi, countAngle]
  | cons L t ih =>
      show RotProg.denote n t * RotLayer.denote n L
          = ((-1 : ℂ) ^ (countAngleL .pi L + countAngle .pi t))
              • (RotProg.denote n (dropPi t) * RotLayer.denote n (dropPiL L))
      rw [ih, dropPiL_denote n L, smul_mul_assoc, mul_smul_comm, smul_smul,
          ← pow_add, Nat.add_comm]

/-- `dropPi` removes ONLY π rotations: every other angle's count is intact. -/
theorem countAngleL_dropPiL (a : RAngle) (ha : a ≠ .pi) (L : RotLayer) :
    countAngleL a (dropPiL L) = countAngleL a L := by
  induction L with
  | nil => rfl
  | cons r t ih =>
      by_cases h : r.angle = .pi
      · have hfil : dropPiL (r :: t) = dropPiL t := by simp [dropPiL, h]
        have hra : (r.angle == a) = false := by
          rw [h]
          exact beq_eq_false_iff_ne.mpr (Ne.symm ha)
        have hcnt : countAngleL a (r :: t) = countAngleL a t := by
          simp [countAngleL, hra]
        rw [hfil, ih, hcnt]
      · have hfil : dropPiL (r :: t) = r :: dropPiL t := by simp [dropPiL, h]
        rw [hfil]
        simp only [countAngleL, List.countP_cons] at ih ⊢
        omega

theorem countAngle_dropPi (a : RAngle) (ha : a ≠ .pi) (p : RotProg) :
    countAngle a (dropPi p) = countAngle a p := by
  induction p with
  | nil => rfl
  | cons L t ih =>
      show countAngleL a (dropPiL L) + countAngle a (dropPi t) = _
      rw [countAngleL_dropPiL a ha, ih]
      rfl

/-- In particular the T-count is untouched. -/
theorem countPi8_dropPi (p : RotProg) : countPi8 (dropPi p) = countPi8 p :=
  countAngle_dropPi .piEighth (by decide) p

/-- `dropPi` does not change the parallel depth. -/
theorem depth_dropPi (p : RotProg) : rotDepth (dropPi p) = rotDepth p := by
  simp [rotDepth, dropPi]

private theorem all_filter_of_all {α} (q f : α → Bool) (l : List α)
    (h : l.all f = true) : (l.filter q).all f = true := by
  simp only [List.all_eq_true] at h ⊢
  exact fun x hx => h x (List.mem_filter.mp hx).1

private theorem layerComm_filter (q : Rot → Bool) (L : RotLayer)
    (h : layerComm L = true) : layerComm (L.filter q) = true := by
  induction L with
  | nil => simpa using h
  | cons r t ih =>
      simp only [layerComm, Bool.and_eq_true] at h
      rw [List.filter_cons]
      by_cases hq : q r = true
      · rw [if_pos hq]
        show (List.all _ _ && layerComm _) = true
        rw [Bool.and_eq_true]
        exact ⟨all_filter_of_all _ _ _ h.1, ih h.2⟩
      · rw [if_neg hq]
        exact ih h.2

/-- `dropPi` preserves layer well-formedness (a sub-multiset of a pairwise-
commuting layer still pairwise commutes). -/
theorem dropPiL_wf (L : RotLayer) (h : RotLayer.wf L = true) :
    RotLayer.wf (dropPiL L) = true := by
  simp only [RotLayer.wf, Bool.and_eq_true] at h ⊢
  exact ⟨all_filter_of_all _ _ _ h.1, layerComm_filter _ _ h.2⟩

theorem dropPi_wf (p : RotProg) (h : RotProg.wf p = true) :
    RotProg.wf (dropPi p) = true := by
  simp only [RotProg.wf, dropPi, List.all_eq_true] at h ⊢
  intro L hL
  obtain ⟨L0, hL0, rfl⟩ := List.mem_map.mp hL
  exact dropPiL_wf L0 (h L0 hL0)

/-! ## §2. Cancellation of adjacent inverse rotations. -/

theorem Rot.denote_inv_mul (n : Nat) (r : Rot) :
    Rot.denote n r.inv * Rot.denote n r = 1 := by
  rw [Rot.denote_mul_same_axis n r.inv r (Rot.inv_axis r), Rot.inv_theta,
      neg_add_cancel, rotOf_zero]

/-- **The cancellation rule**: adjacent inverse rotations vanish. -/
theorem denote_cancel_adjacent (n : Nat) (r : Rot) (p : RotProg) :
    RotProg.denote n ([r] :: [r.inv] :: p) = RotProg.denote n p := by
  show (RotProg.denote n p * RotLayer.denote n [r.inv]) * RotLayer.denote n [r]
      = RotProg.denote n p
  rw [Matrix.mul_assoc]
  have hl : RotLayer.denote n [r.inv] * RotLayer.denote n [r]
      = Rot.denote n r.inv * Rot.denote n r := by
    simp [RotLayer.denote]
  rw [hl, Rot.denote_inv_mul, Matrix.mul_one]

/-- The cancellation rule saves exactly two rotations … -/
theorem countRot_cancel_pair (r : Rot) (p : RotProg) :
    countRot ([r] :: [r.inv] :: p) = countRot p + 2 := by
  show countRotL [r] + (countRotL [r.inv] + countRot p) = countRot p + 2
  simp [countRotL]
  omega

/-- … and two layers of depth. -/
theorem depth_cancel_pair (r : Rot) (p : RotProg) :
    rotDepth ([r] :: [r.inv] :: p) = rotDepth p + 2 := by
  simp [rotDepth]

/-! ## §3. Merging adjacent same-axis rotations (angle doubling). -/

/-- Doubling an angle level (`none` for π: a doubled π rotation is `e^{-2πi}
= 1`, i.e. it vanishes — see `denote_pi_sq_adjacent`). -/
def RAngle.doubled : RAngle → Option RAngle
  | .pi        => none
  | .piHalf    => some .pi
  | .piQuarter => some .piHalf
  | .piEighth  => some .piQuarter

theorem RAngle.doubled_val {a b : RAngle} (h : a.doubled = some b) :
    b.val = 2 * a.val := by
  cases a <;> simp only [RAngle.doubled, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> simp only [RAngle.val] <;> ring

/-- **The merge rule**: two adjacent equal rotations fuse into the doubled
angle — two T's make an S, two S's make a Pauli, two Paulis make a π phase. -/
theorem denote_double_adjacent (n : Nat) (r : Rot) {b : RAngle}
    (hb : r.angle.doubled = some b) (p : RotProg) :
    RotProg.denote n ([r] :: [r] :: p)
      = RotProg.denote n ([{ r with angle := b }] :: p) := by
  show (RotProg.denote n p * RotLayer.denote n [r]) * RotLayer.denote n [r]
      = RotProg.denote n p * RotLayer.denote n [{ r with angle := b }]
  rw [Matrix.mul_assoc]
  congr 1
  have hl : ∀ s : Rot, RotLayer.denote n [s] = Rot.denote n s := by
    intro s; simp [RotLayer.denote]
  rw [hl, hl, Rot.denote_mul_same_axis n r r rfl]
  show rotOf (r.theta + r.theta) (axisMat n r.axis)
      = rotOf (Rot.theta { r with angle := b }) (axisMat n r.axis)
  congr 1
  show r.theta + r.theta = Rot.theta { r with angle := b }
  cases hneg : r.neg <;>
    simp [Rot.theta, hneg, RAngle.doubled_val hb] <;> try ring

/-- A doubled π rotation vanishes outright (`(−1)² = 1`). -/
theorem denote_pi_sq_adjacent (n : Nat) (r : Rot) (h : r.angle = .pi)
    (p : RotProg) :
    RotProg.denote n ([r] :: [r] :: p) = RotProg.denote n p := by
  show (RotProg.denote n p * RotLayer.denote n [r]) * RotLayer.denote n [r]
      = RotProg.denote n p
  rw [Matrix.mul_assoc]
  have hl : RotLayer.denote n [r] = Rot.denote n r := by simp [RotLayer.denote]
  rw [hl, Rot.denote_pi n r h, neg_mul_neg, one_mul, mul_one]

/-! ## §4. Smoke checks. -/

open FormalRV.PPM.Prog in
example :  -- dropping a π rotation keeps the T-count
    countPi8 (dropPi [[⟨false, .pi, [⟨0, .z⟩]⟩], [⟨false, .piEighth, [⟨1, .z⟩]⟩]])
      = 1 := by decide

open FormalRV.PPM.Prog in
example :  -- two T's about Z[0] fuse into one S
    RAngle.doubled .piEighth = some .piQuarter := by decide

end FormalRV.PauliRotation
