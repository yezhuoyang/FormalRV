import FormalRV.Shor.MainAlgorithm.ContinuedFractionBridge.CFAuxStreamMatchingStrong

namespace FormalRV.SQIRPort

/-- **Convergent recurrence for `GenContFract.of`** (Phase 3 r_found_1
infrastructure, added 2026-05-24 tick 59): the n+1-th convergent of v
equals `⌊v⌋ + 1/(n-th convergent of (Int.fract v)⁻¹)`. Direct from
mathlib's `Real.convergent_succ` + `Real.convs_eq_convergent` (which
bridges `Real.convergent` Rat-valued and `GenContFract.convs` Real-valued).
This is the building block for the dens/nums recurrence relations
needed by the cf_aux ↔ mathlib bridge. -/
theorem of_convs_succ_via_fract (v : ℝ) (n : Nat) :
    (GenContFract.of v).convs (n + 1) =
      (⌊v⌋ : ℝ) + ((GenContFract.of (Int.fract v)⁻¹).convs n)⁻¹ := by
  rw [Real.convs_eq_convergent v, Real.convs_eq_convergent (Int.fract v)⁻¹]
  rw [Real.convergent_succ]
  push_cast
  ring

/-- **Specialized convs swap when `0 < o < m`** (Phase 3 r_found_1,
added 2026-05-24 tick 60): when `o < m`, `⌊o/m⌋ = 0`, so the convergent
recurrence simplifies to a pure SWAP — the (n+1)th convergent of `o/m`
is the inverse of the n-th convergent of `m/o`. Crucial structural
property for the bridge when starting in the "fractional" regime. -/
theorem of_convs_succ_lt (o m : Nat) (h_lt : o < m) (h_o_pos : 0 < o)
    (n : Nat) :
    (GenContFract.of (((o : ℝ)) / ((m : Nat) : ℝ))).convs (n + 1) =
      ((GenContFract.of (((m : Nat) : ℝ) / ((o : Nat) : ℝ))).convs n)⁻¹ := by
  have h_m_pos : 0 < m := by omega
  have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
  have h_o_pos_R : (0 : ℝ) < ((o : Nat) : ℝ) := by exact_mod_cast h_o_pos
  rw [Real.convs_eq_convergent, Real.convs_eq_convergent, Real.convergent_succ]
  have h_floor : ⌊((o : ℕ) : ℝ) / ((m : ℕ) : ℝ)⌋ = 0 := by
    apply Int.floor_eq_zero_iff.mpr
    constructor
    · positivity
    · rw [show (1 : ℝ) = (m : ℝ) / m by field_simp]
      apply div_lt_div_of_pos_right (by exact_mod_cast h_lt) h_pow_pos_R
  have h_fract : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ))
                = ((o : Nat) : ℝ) / ((m : Nat) : ℝ) := by
    unfold Int.fract
    rw [h_floor]
    simp
  rw [h_floor, h_fract, inv_div]
  push_cast
  ring

/-- **`of_correctness_of_terminatedAt` accessor**: when `GenContFract.of v`
terminates at step `n`, the n-th convergent equals `v` exactly. Used
for rational-input correctness — once the CF terminates, we recover the
input rational. -/
theorem mathlib_convs_at_term (v : ℝ) (n : Nat)
    (h_term : (GenContFract.of v).TerminatedAt n) :
    (GenContFract.of v).convs n = v :=
  (GenContFract.of_correctness_of_terminatedAt h_term).symm

/-- Connect `mathlib_dens_int_gen` (general) to `mathlib_OF_post_step`
(specialized to `m = 2^bit`): they agree by spec uniqueness when both
extract the same dens value. -/
theorem mathlib_dens_int_gen_eq_OF_post_step (n o m : Nat) :
    mathlib_dens_int_gen n o (2^m) = mathlib_OF_post_step n o m := by
  have h1 := mathlib_dens_int_gen_spec n o (2^m)
  have h2 := mathlib_OF_post_step_spec n o m
  have h_cast : (((o : ℝ)) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) := by push_cast; rfl
  rw [h_cast] at h1
  have h_eq : ((mathlib_dens_int_gen n o (2^m) : ℤ) : ℝ) =
              ((mathlib_OF_post_step n o m : ℤ) : ℝ) := by
    rw [← h1, ← h2]
  exact_mod_cast h_eq



-- (General bridge scaffold moved later — needs `mathlib_OF_post_step_nat_eq_OF_post_step_div_general`.)

/-- **Bridge for general n in the divisible case** (Phase 3 r_found_1
breakthrough, added 2026-05-24): when `o % 2^m = 0`, both sides equal 1
for all n. Combines `OF_post_step_div_general` and `mathlib_dens_div_general`. -/
theorem mathlib_OF_post_step_nat_eq_OF_post_step_div_general
    (n o m : Nat) (h_mod : o % (2^m) = 0) :
    mathlib_OF_post_step_nat n o m = OF_post_step n o m := by
  unfold mathlib_OF_post_step_nat
  have h_spec := mathlib_OF_post_step_spec n o m
  have h_cast : (((o : ℝ)) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) := by push_cast; rfl
  have h_dens := mathlib_dens_div_general o m n h_mod
  rw [h_cast] at h_dens
  rw [h_dens] at h_spec
  have h_int : mathlib_OF_post_step n o m = 1 := by exact_mod_cast h_spec.symm
  rw [h_int, OF_post_step_div_general n o m h_mod]
  rfl

/-- **Non-boundary bridge** (added 2026-05-24, REPLACES general version per
John's design recommendation): `mathlib_OF_post_step_nat n o m = OF_post_step
n o m` whenever mathlib's CF has NOT terminated by step `(n+1)`. The boundary
case (terminated exactly at `n+1` but not at `n`) is excluded.

The boundary case was proof-engineering debt without conceptual content. For
`r_found_1`'s use, the non-boundary hypothesis is always satisfied (via
N_step + dens_eq_r_at_convs_eq_kr arguments).

Hypothesis `¬ TerminatedAt (n+1)` IMPLIES:
- `¬ TerminatedAt 0` (by terminated_stable contrapositive),
- hence `o % (2^m) ≠ 0` (non-divisibility, via nondiv_of_not_terminated_zero),
- and `¬ TerminatedAt n` (also by contrapositive), letting us apply strong. -/
theorem mathlib_OF_post_step_nat_eq_OF_post_step_nonboundary
    (n o m : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).TerminatedAt (n+1)) :
    mathlib_OF_post_step_nat n o m = OF_post_step n o m := by
  -- Derive ¬ Terminated at 0 from h_not_term (terminated_stable contrapositive).
  have h_not_term_0 : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).TerminatedAt 0 := by
    intro h
    exact h_not_term (GenContFract.terminated_stable (by omega : 0 ≤ n+1) h)
  -- Derive o % (2^m) ≠ 0 (non-divisibility).
  have h_mod : o % (2^m) ≠ 0 := nondiv_of_not_terminated_zero o (2^m) h_not_term_0
  cases n with
  | zero =>
    -- n = 0: both sides equal 1.
    have h_spec := mathlib_OF_post_step_spec 0 o m
    rw [GenContFract.zeroth_den_eq_one] at h_spec
    have h_int : mathlib_OF_post_step 0 o m = 1 := by exact_mod_cast h_spec.symm
    unfold mathlib_OF_post_step_nat
    rw [h_int]
    rw [OF_post_step_zero]
    rfl
  | succ k =>
    -- n = k+1. Apply strong at n' = k. Need ¬ Terminated at (k+1) = n.
    -- From h_not_term (¬ Terminated at n+1) by stable contrapositive.
    have h_term_n : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).TerminatedAt (k+1) := by
      intro h
      exact h_not_term (GenContFract.terminated_stable (by omega : k+1 ≤ k+2) h)
    have h_2pm : 0 < (2^m : Nat) := Nat.two_pow_pos m
    have h_strong := cf_aux_full_matches_mathlib_strong o (2^m) h_2pm k h_term_n
    -- Bridge gives cf_aux's .2.2.2 = dens (k+1) in ℝ. Combine with spec → Nat equality.
    have h_rhs : OF_post_step (k+1) o m = (cf_aux_full (k+2) o (2^m) 0 1 1 0).2.2.2 := by
      unfold OF_post_step ContinuedFraction
      rw [cf_aux_eq_cf_aux_full_proj]
    have h_lhs_R : ((mathlib_OF_post_step_nat (k+1) o m : Nat) : ℝ)
        = (((cf_aux_full (k+2) o (2^m) 0 1 1 0).2.2.2 : Nat) : ℝ) := by
      have h_spec := mathlib_OF_post_step_spec (k+1) o m
      have h_strong_4 := h_strong.2.2.2
      rw [h_strong_4]
      rw [show ((GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).contsAux (k+2)).b
            = (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).dens (k+1) from rfl]
      rw [show (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) from by
        push_cast; rfl]
      rw [h_spec]
      have h_nat_int := mathlib_OF_post_step_nat_int (k+1) o m
      have : ((mathlib_OF_post_step_nat (k+1) o m : Nat) : ℝ)
           = ((mathlib_OF_post_step (k+1) o m : ℤ) : ℝ) := by
        rw [← h_nat_int]; push_cast; rfl
      rw [this]
    have h_eq_Nat : mathlib_OF_post_step_nat (k+1) o m
        = (cf_aux_full (k+2) o (2^m) 0 1 1 0).2.2.2 := by
      exact_mod_cast h_lhs_R
    rw [h_eq_Nat, h_rhs]

end FormalRV.SQIRPort
