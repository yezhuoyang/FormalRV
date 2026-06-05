import FormalRV.Shor.MainAlgorithm.ContinuedFractionBridge.OFPostStepValues

namespace FormalRV.SQIRPort

/-- **Mathlib's `dens 1` for `o/2^m`, divisible case**: when `o % 2^m = 0`,
the input is an integer, the stream terminates immediately, and
`dens 1 = dens 0 = 1`. -/
theorem mathlib_dens_one_div (o m : Nat) (h_mod : o % (2^m) = 0) :
    (GenContFract.of (((o : ℝ)) / ((2^m : Nat) : ℝ))).dens 1 = 1 := by
  have h_pow_pos : 0 < 2^m := Nat.two_pow_pos m
  have h_dvd : (2^m : Nat) ∣ o := Nat.dvd_of_mod_eq_zero h_mod
  have h_pow_ne : ((2^m : Nat) : ℝ) ≠ 0 := by exact_mod_cast h_pow_pos.ne'
  have h_int_eq : (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) = (((o / 2^m : Nat) : ℤ) : ℝ) := by
    have h1 : ((o / 2^m : Nat) : ℝ) = ((o : Nat) : ℝ) / ((2^m : Nat) : ℝ) :=
      Nat.cast_div h_dvd h_pow_ne
    rw [show (((o / 2^m : Nat) : ℤ) : ℝ) = ((o / 2^m : Nat) : ℝ) from by push_cast; rfl]
    exact h1.symm
  rw [h_int_eq]
  have h_s_nil := GenContFract.of_s_of_int ℝ ((o / 2^m : Nat) : ℤ)
  have h_term : (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).TerminatedAt 0 := by
    rw [GenContFract.terminatedAt_iff_s_terminatedAt]
    show (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).s.get? 0 = none
    rw [h_s_nil]
    rfl
  rw [GenContFract.dens_stable_of_terminated (n := 0) (m := 1) (by omega) h_term]
  exact GenContFract.zeroth_den_eq_one

/-- **Mathlib's `dens 1` for `o/2^m`, non-divisible case**: when
`o % 2^m ≠ 0`, applying `of_s_head` + `first_den_eq` +
`Int.fract_div_natCast_eq_div_natCast_mod` + `Rat.floor_natCast_div_natCast`
gives `dens 1 = ⌊2^m / (o % 2^m)⌋ = (2^m) / (o % 2^m)`. -/
theorem mathlib_dens_one_nondiv (o m : Nat) (h_mod : o % (2^m) ≠ 0) :
    (GenContFract.of (((o : ℝ)) / ((2^m : Nat) : ℝ))).dens 1
      = (((2^m) / (o % 2^m) : Nat) : ℝ) := by
  have h_pow_pos : 0 < 2^m := Nat.two_pow_pos m
  have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) ≠ 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_mod_pos : 0 < o % (2^m) := Nat.pos_of_ne_zero h_mod
    have h_num_pos : (0 : ℝ) < ((o % (2^m) : Nat) : ℝ) := by exact_mod_cast h_mod_pos
    have h_pow_pos_R : (0 : ℝ) < ((2^m : Nat) : ℝ) := by exact_mod_cast h_pow_pos
    positivity
  have h_head := GenContFract.of_s_head (K := ℝ)
    (v := (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ))) h_fract_ne
  have h_first := GenContFract.first_den_eq
    (g := GenContFract.of (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ)))
    (gp := { a := 1, b := ↑⌊(Int.fract (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ)))⁻¹⌋ })
    (zeroth_s_eq := by
      show (GenContFract.of (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ))).s.get? 0 = some _
      rw [show (GenContFract.of (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ))).s.get? 0
           = (GenContFract.of (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ))).s.head from rfl]
      exact h_head)
  rw [h_first]
  show (↑⌊(Int.fract ((↑o : ℝ) / ((2 ^ m : Nat) : ℝ)))⁻¹⌋ : ℝ)
       = ((2 ^ m / (o % 2 ^ m) : Nat) : ℝ)
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
  have h_eq : (((2^m : Nat) : ℝ) / ((o % 2^m : Nat) : ℝ))
            = ((((2^m : Nat) : ℚ) / ((o % 2^m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  rw [h_eq, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  push_cast
  rfl

/-- **Cast normalization for the GenContFract.of argument**: the two forms
`(o : ℝ) / (2^m : ℝ)` and `(o : ℝ) / ((2^m : Nat) : ℝ)` are equal. Used
to convert between the form needed by mathlib_OF_post_step_spec and the
form produced by GenContFract.of unfolding. -/
theorem of_arg_cast_norm (o m : Nat) :
    (((o : ℝ)) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) := by push_cast; rfl

/-- **Mathlib's `dens 2` for `o/2^m`, divisible case**: when `o % 2^m = 0`,
the input is an integer, the stream terminates immediately, and
`dens 2 = dens 0 = 1`. Same proof as step-1 divisible case but with
`dens_stable_of_terminated` extended to step 2. -/
theorem mathlib_dens_two_div (o m : Nat) (h_mod : o % (2^m) = 0) :
    (GenContFract.of (((o : ℝ)) / ((2^m : Nat) : ℝ))).dens 2 = 1 := by
  have h_pow_pos : 0 < 2^m := Nat.two_pow_pos m
  have h_dvd : (2^m : Nat) ∣ o := Nat.dvd_of_mod_eq_zero h_mod
  have h_pow_ne : ((2^m : Nat) : ℝ) ≠ 0 := by exact_mod_cast h_pow_pos.ne'
  have h_int_eq : (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) = (((o / 2^m : Nat) : ℤ) : ℝ) := by
    have h1 : ((o / 2^m : Nat) : ℝ) = ((o : Nat) : ℝ) / ((2^m : Nat) : ℝ) :=
      Nat.cast_div h_dvd h_pow_ne
    rw [show (((o / 2^m : Nat) : ℤ) : ℝ) = ((o / 2^m : Nat) : ℝ) from by push_cast; rfl]
    exact h1.symm
  rw [h_int_eq]
  have h_s_nil := GenContFract.of_s_of_int ℝ ((o / 2^m : Nat) : ℤ)
  have h_term : (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).TerminatedAt 0 := by
    rw [GenContFract.terminatedAt_iff_s_terminatedAt]
    show (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).s.get? 0 = none
    rw [h_s_nil]
    rfl
  rw [GenContFract.dens_stable_of_terminated (n := 0) (m := 2) (by omega) h_term]
  exact GenContFract.zeroth_den_eq_one

/-- **Mathlib's `dens n` for `o/2^m`, divisible case (general n)**: when
`o % 2^m = 0`, the input is an integer, the stream terminates immediately,
and `dens n = 1` for all n. Generalization of mathlib_dens_two_div. -/
theorem mathlib_dens_div_general (o m : Nat) (n : Nat) (h_mod : o % (2^m) = 0) :
    (GenContFract.of (((o : ℝ)) / ((2^m : Nat) : ℝ))).dens n = 1 := by
  have h_pow_pos : 0 < 2^m := Nat.two_pow_pos m
  have h_dvd : (2^m : Nat) ∣ o := Nat.dvd_of_mod_eq_zero h_mod
  have h_pow_ne : ((2^m : Nat) : ℝ) ≠ 0 := by exact_mod_cast h_pow_pos.ne'
  have h_int_eq : (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) = (((o / 2^m : Nat) : ℤ) : ℝ) := by
    have h1 : ((o / 2^m : Nat) : ℝ) = ((o : Nat) : ℝ) / ((2^m : Nat) : ℝ) :=
      Nat.cast_div h_dvd h_pow_ne
    rw [show (((o / 2^m : Nat) : ℤ) : ℝ) = ((o / 2^m : Nat) : ℝ) from by push_cast; rfl]
    exact h1.symm
  rw [h_int_eq]
  have h_s_nil := GenContFract.of_s_of_int ℝ ((o / 2^m : Nat) : ℤ)
  have h_term : (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).TerminatedAt 0 := by
    rw [GenContFract.terminatedAt_iff_s_terminatedAt]
    show (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).s.get? 0 = none
    rw [h_s_nil]
    rfl
  by_cases h_n : n = 0
  · rw [h_n]; exact GenContFract.zeroth_den_eq_one
  · rw [GenContFract.dens_stable_of_terminated (n := 0) (m := n) (by omega) h_term]
    exact GenContFract.zeroth_den_eq_one

/-- **KEY RECURRENCE: mathlib's stream Euclidean shift = cf_aux's Euclidean
step** (Phase 3 r_found_1, added 2026-05-24): for `o, m : Nat` with `m > 0`
and `o % m ≠ 0`, mathlib's `IntFractPair.stream` at step `n+1` for `o/m`
equals the stream at step `n` for `m/(o%m)`. This is the structural bridge
between mathlib's `(Int.fract v)⁻¹` recursion and our cf_aux's Euclidean
state update `(o, m) ↦ (m, o%m)`. With this recurrence, the cf_aux ↔
mathlib bridge becomes provable by induction. -/
theorem stream_succ_euclidean (o m : Nat) (h_m_pos : 0 < m)
    (h_mod : o % m ≠ 0) (n : Nat) :
    GenContFract.IntFractPair.stream (((o : ℝ)) / ((m : Nat) : ℝ)) (n+1)
      = GenContFract.IntFractPair.stream (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ)) n := by
  have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) ≠ 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_mod_pos : 0 < o % m := Nat.pos_of_ne_zero h_mod
    have h_num_pos : (0 : ℝ) < ((o % m : Nat) : ℝ) := by exact_mod_cast h_mod_pos
    have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
    positivity
  rw [GenContFract.IntFractPair.stream_succ h_fract_ne n]
  congr 1
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]

/-- **Generalized mathlib int-valued dens for arbitrary `(o, m)`**: extracts
the integer-valued denominator of `(GenContFract.of (o/m))` at step `n` for
arbitrary m (not just powers of 2). Needed for the non-divisible-case bridge
which recurses through arbitrary Euclidean states. -/
noncomputable def mathlib_dens_int_gen (n o m : Nat) : ℤ :=
  Classical.choose (dens_int_valued (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) n)

/-- Spec for `mathlib_dens_int_gen`. -/
theorem mathlib_dens_int_gen_spec (n o m : Nat) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).dens n =
      ((mathlib_dens_int_gen n o m : ℤ) : ℝ) :=
  Classical.choose_spec (dens_int_valued (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) n)

/-- **`mathlib_dens_int_gen 0 o m = 1`**: base case for the generalized
mathlib int-valued dens at step 0 (independent of `o, m`). Follows
directly from mathlib's `zeroth_den_eq_one`. -/
theorem mathlib_dens_int_gen_zero (o m : Nat) :
    mathlib_dens_int_gen 0 o m = 1 := by
  have h_spec := mathlib_dens_int_gen_spec 0 o m
  rw [GenContFract.zeroth_den_eq_one] at h_spec
  exact_mod_cast h_spec.symm

/-- **`mathlib_dens_int_gen n o m ≥ 0`**: non-negativity of the generalized
int-valued dens. From `GenContFract.zero_le_of_den`. -/
theorem mathlib_dens_int_gen_nonneg (n o m : Nat) :
    0 ≤ mathlib_dens_int_gen n o m := by
  have h_nn := GenContFract.zero_le_of_den
    (v := (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) (n := n)
  rw [mathlib_dens_int_gen_spec n o m] at h_nn
  exact_mod_cast h_nn

/-- **`mathlib_dens_int_gen` Fibonacci lower bound** (general version of
`mathlib_OF_post_step_fib_ge`): when not terminated before step `n`,
`fib (n+1) ≤ mathlib_dens_int_gen n o m`. -/
theorem mathlib_dens_int_gen_fib_ge (o m n : Nat)
    (h_not_term : n = 0 ∨
      ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt (n - 1)) :
    (Nat.fib (n + 1) : ℤ) ≤ mathlib_dens_int_gen n o m := by
  have h := GenContFract.succ_nth_fib_le_of_nth_den
    (v := (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) (n := n) h_not_term
  rw [mathlib_dens_int_gen_spec n o m] at h
  exact_mod_cast h

/-- **Mathlib's `nums 0` for `o/m`** (ℝ-version): direct from
`zeroth_num_eq_h` + `of_h_eq_floor` + `Rat.floor_natCast_div_natCast` +
`Rat.floor_cast`. The 0-th convergent numerator equals `o / m` as Nat. -/
theorem mathlib_nums_zero_eq (o m : Nat) (_h_m_pos : 0 < m) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).nums 0
      = ((o / m : Nat) : ℝ) := by
  rw [GenContFract.zeroth_num_eq_h, GenContFract.of_h_eq_floor]
  rw [show ((((o : Nat) : ℝ) / ((m : Nat) : ℝ)) : ℝ)
      = ((((o : Nat) : ℚ) / ((m : Nat) : ℚ) : ℚ) : ℝ) from by push_cast; ring]
  rw [Rat.floor_cast, Rat.floor_natCast_div_natCast]
  push_cast; rfl

/-- **Mathlib's `dens 0` for `o/m`** (ℝ-version): direct from
`zeroth_den_eq_one`. The 0-th convergent denominator is always 1. -/
theorem mathlib_dens_zero_eq (o m : Nat) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).dens 0 = 1 :=
  GenContFract.zeroth_den_eq_one

/-- **Mathlib's `dens 1` for `o/m`, non-terminated** (ℝ-version): when
`o % m ≠ 0`, `dens 1 = m/(o%m)`. Via `of_s_head` + `first_den_eq` +
`Int.fract_div_natCast_eq_div_natCast_mod` + `Rat.floor_natCast_div_natCast`. -/
theorem mathlib_dens_one_eq_nondiv (o m : Nat) (h_m_pos : 0 < m)
    (h_mod : o % m ≠ 0) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).dens 1
      = ((m / (o % m) : Nat) : ℝ) := by
  have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
  have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) ≠ 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_mod_pos : 0 < o % m := Nat.pos_of_ne_zero h_mod
    have h_num_pos : (0 : ℝ) < ((o % m : Nat) : ℝ) := by exact_mod_cast h_mod_pos
    positivity
  have h_head := GenContFract.of_s_head (K := ℝ)
    (v := (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))) h_fract_ne
  have h_first := GenContFract.first_den_eq
    (g := GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ)))
    (gp := { a := 1, b := ↑⌊(Int.fract (((o : ℕ) : ℝ) / ((m : Nat) : ℝ)))⁻¹⌋ })
    (zeroth_s_eq := by
      show (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.get? 0 = some _
      rw [show (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.get? 0
           = (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.head from rfl]
      exact h_head)
  rw [h_first]
  show (↑⌊(Int.fract ((↑o : ℝ) / ((m : Nat) : ℝ)))⁻¹⌋ : ℝ)
       = ((m / (o % m) : Nat) : ℝ)
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
  have h_eq : (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))
            = ((((m : Nat) : ℚ) / ((o % m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  rw [h_eq, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  push_cast
  rfl

/-- **Mathlib's `nums 1` for `o/m`, non-terminated** (ℝ-version): when
`o % m ≠ 0`, `nums 1 = (m/(o%m)) * (o/m) + 1` (Nat-cast). Uses
`first_num_eq` (which gives `nums 1 = b·h + 1` where `a=1` from
SimpContFract) + floor computations + `norm_cast` to clean up Int/Nat
division mismatches. -/
theorem mathlib_nums_one_eq_nondiv (o m : Nat) (h_m_pos : 0 < m)
    (h_mod : o % m ≠ 0) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).nums 1
      = ((m / (o % m) * (o / m) + 1 : Nat) : ℝ) := by
  have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) ≠ 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_mod_pos : 0 < o % m := Nat.pos_of_ne_zero h_mod
    have h_num_pos : (0 : ℝ) < ((o % m : Nat) : ℝ) := by exact_mod_cast h_mod_pos
    have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
    positivity
  have h_head := GenContFract.of_s_head (K := ℝ)
    (v := (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))) h_fract_ne
  have h_first := GenContFract.first_num_eq
    (g := GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ)))
    (gp := { a := 1, b := ↑⌊(Int.fract (((o : ℕ) : ℝ) / ((m : Nat) : ℝ)))⁻¹⌋ })
    (zeroth_s_eq := by
      show (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.get? 0 = some _
      rw [show (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.get? 0
           = (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.head from rfl]
      exact h_head)
  rw [h_first]
  rw [GenContFract.of_h_eq_floor]
  show (↑⌊(Int.fract ((↑o : ℝ) / ((m : Nat) : ℝ)))⁻¹⌋ : ℝ) *
       ⌊((↑o : ℝ) / ((m : Nat) : ℝ))⌋ + 1
       = ((m / (o % m) * (o / m) + 1 : Nat) : ℝ)
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
  have h_eq1 : (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))
            = ((((m : Nat) : ℚ) / ((o % m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  have h_eq2 : (((o : Nat) : ℝ) / ((m : Nat) : ℝ))
            = ((((o : Nat) : ℚ) / ((m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  rw [h_eq1, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  rw [h_eq2, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  norm_cast

end FormalRV.SQIRPort
