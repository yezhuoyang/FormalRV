import FormalRV.Shor.MainAlgorithm.QuantumAndContinuedFractions.KhinchinConvergentRecovery

namespace FormalRV.SQIRPort

/-- **Denominators of `GenContFract.of v` are integer-valued** (paired
form, Phase 3 r_found_1 slice 4b sub-step 1, added 2026-05-23): joint
induction giving `∃ d : ℤ, dens n = d ∧ ∃ d', dens (n+1) = d'` for all
`n`. The base cases use `zeroth_den_eq_one` and either
`first_den_eq` (if not terminated at 0) or `dens_stable_of_terminated`
(if terminated at 0). The inductive step uses `dens_recurrence` for the
non-terminated case (since `GenContFract.of` has partial-numerator 1 by
`of_partNum_eq_one_and_exists_int_partDen_eq`, the recurrence specializes
to `dens(n+2) = b·dens(n+1) + dens(n)` with `b` integer-valued). -/
theorem dens_int_valued_pair (v : ℝ) :
    ∀ n, (∃ d : ℤ, (GenContFract.of v).dens n = (d : ℝ)) ∧
         (∃ d : ℤ, (GenContFract.of v).dens (n+1) = (d : ℝ)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨⟨1, ?_⟩, ?_⟩
    · simp [GenContFract.zeroth_den_eq_one]
    · by_cases h : (GenContFract.of v).s.get? 0 = none
      · refine ⟨1, ?_⟩
        have h_term : (GenContFract.of v).TerminatedAt 0 := h
        rw [GenContFract.dens_stable_of_terminated (n := 0) (m := 1) (by omega) h_term]
        simp [GenContFract.zeroth_den_eq_one]
      · have h' : ∃ gp, (GenContFract.of v).s.get? 0 = some gp := by
          rcases hopt : (GenContFract.of v).s.get? 0 with _ | gp
          · exact absurd hopt h
          · exact ⟨gp, rfl⟩
        obtain ⟨gp, hgp⟩ := h'
        rw [GenContFract.first_den_eq hgp]
        obtain ⟨_, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp
        exact ⟨z, hz⟩
  | succ k ih =>
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    refine ⟨⟨b, hb⟩, ?_⟩
    by_cases h : (GenContFract.of v).s.get? (k+1) = none
    · refine ⟨b, ?_⟩
      have h_term : (GenContFract.of v).TerminatedAt (k+1) := h
      rw [GenContFract.dens_stable_of_terminated (n := k+1) (m := k+2) (by omega) h_term]
      exact hb
    · have h' : ∃ gp, (GenContFract.of v).s.get? (k+1) = some gp := by
        rcases hopt : (GenContFract.of v).s.get? (k+1) with _ | gp
        · exact absurd hopt h
        · exact ⟨gp, rfl⟩
      obtain ⟨gp, hgp⟩ := h'
      have h_rec := GenContFract.dens_recurrence (g := GenContFract.of v) (n := k)
        hgp ha hb
      obtain ⟨ha_eq, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp
      refine ⟨z * b + a, ?_⟩
      show (GenContFract.of v).dens (k + 1 + 1) = _
      rw [show k + 1 + 1 = k + 2 from rfl]
      rw [h_rec, ha_eq, hz]
      push_cast
      ring

/-- Single-`n` corollary: `dens n` of `GenContFract.of v` is integer-valued. -/
theorem dens_int_valued (v : ℝ) (n : Nat) :
    ∃ d : ℤ, (GenContFract.of v).dens n = (d : ℝ) :=
  (dens_int_valued_pair v n).1

/-- **Numerators of `GenContFract.of v` are integer-valued** (paired
form, Phase 3 r_found_1 slice 4b sub-step 2, added 2026-05-23): analogous
to `dens_int_valued_pair`. The base case n=0 uses
`zeroth_num_eq_h` + `of_h_eq_floor` (so `nums 0 = ⌊v⌋`); the n=1
non-terminated case uses `first_num_eq` (giving `nums 1 = b·h + 1`); the
inductive step uses `nums_recurrence` with `a = 1` from
`of_partNum_eq_one_and_exists_int_partDen_eq`. -/
theorem nums_int_valued_pair (v : ℝ) :
    ∀ n, (∃ d : ℤ, (GenContFract.of v).nums n = (d : ℝ)) ∧
         (∃ d : ℤ, (GenContFract.of v).nums (n+1) = (d : ℝ)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨⟨⌊v⌋, ?_⟩, ?_⟩
    · rw [GenContFract.zeroth_num_eq_h, GenContFract.of_h_eq_floor]
    · by_cases h : (GenContFract.of v).s.get? 0 = none
      · refine ⟨⌊v⌋, ?_⟩
        have h_term : (GenContFract.of v).TerminatedAt 0 := h
        rw [GenContFract.nums_stable_of_terminated (n := 0) (m := 1) (by omega) h_term]
        rw [GenContFract.zeroth_num_eq_h, GenContFract.of_h_eq_floor]
      · have h' : ∃ gp, (GenContFract.of v).s.get? 0 = some gp := by
          rcases hopt : (GenContFract.of v).s.get? 0 with _ | gp
          · exact absurd hopt h
          · exact ⟨gp, rfl⟩
        obtain ⟨gp, hgp⟩ := h'
        rw [GenContFract.first_num_eq hgp]
        obtain ⟨ha_eq, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp
        refine ⟨z * ⌊v⌋ + 1, ?_⟩
        rw [ha_eq, hz, GenContFract.of_h_eq_floor]
        push_cast; ring
  | succ k ih =>
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    refine ⟨⟨b, hb⟩, ?_⟩
    by_cases h : (GenContFract.of v).s.get? (k+1) = none
    · refine ⟨b, ?_⟩
      have h_term : (GenContFract.of v).TerminatedAt (k+1) := h
      rw [GenContFract.nums_stable_of_terminated (n := k+1) (m := k+2) (by omega) h_term]
      exact hb
    · have h' : ∃ gp, (GenContFract.of v).s.get? (k+1) = some gp := by
        rcases hopt : (GenContFract.of v).s.get? (k+1) with _ | gp
        · exact absurd hopt h
        · exact ⟨gp, rfl⟩
      obtain ⟨gp, hgp⟩ := h'
      have h_rec := GenContFract.nums_recurrence (g := GenContFract.of v) (n := k)
        hgp ha hb
      obtain ⟨ha_eq, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp
      refine ⟨z * b + a, ?_⟩
      show (GenContFract.of v).nums (k + 1 + 1) = _
      rw [show k + 1 + 1 = k + 2 from rfl]
      rw [h_rec, ha_eq, hz]
      push_cast; ring

/-- Single-`n` corollary: `nums n` of `GenContFract.of v` is integer-valued. -/
theorem nums_int_valued (v : ℝ) (n : Nat) :
    ∃ d : ℤ, (GenContFract.of v).nums n = (d : ℝ) :=
  (nums_int_valued_pair v n).1

/-- **Determinant identity for `GenContFract.of v`** (Phase 3, r_found_1
slice 4b prep, added 2026-05-23): the standard Bezout-like determinant
identity `p_n q_{n+1} - q_n p_{n+1} = (-1)^(n+1)` for the convergents of
`GenContFract.of v`. Re-stated from mathlib's `SimpContFract.determinant`
via the `SimpContFract.of` packaging — `(SimpContFract.of v : GenContFract)
= GenContFract.of v` definitionally. This is what gives gcd(p_n, q_n) = 1
as integers (modulo upgrading int-valuedness; future tick). -/
theorem of_v_determinant (v : ℝ) (n : Nat)
    (h_not_term : ¬ (GenContFract.of v).TerminatedAt n) :
    (GenContFract.of v).nums n * (GenContFract.of v).dens (n+1)
      - (GenContFract.of v).dens n * (GenContFract.of v).nums (n+1)
        = (-1) ^ (n+1) := by
  let s : SimpContFract ℝ := SimpContFract.of v
  have h_eq : (s : GenContFract ℝ) = GenContFract.of v := rfl
  have h_det := SimpContFract.determinant (s := s) (n := n)
    (by rw [h_eq]; exact h_not_term)
  rw [h_eq] at h_det
  exact h_det

/-- **Coprimality of integer-valued numerators and denominators** (Phase 3
r_found_1 slice 4b sub-step 2b, added 2026-05-23): for `GenContFract.of v`
at any non-terminated step `n`, if `nums n = (a : ℝ)` and `dens n = (b : ℝ)`
with `a b : ℤ`, then `Int.gcd a b = 1`. Proof: extract integer-valued
`a' = nums (n+1)`, `b' = dens (n+1)` (via `nums_int_valued` /
`dens_int_valued`), apply `of_v_determinant` (Bezout-like identity
`a·b' - b·a' = (-1)^(n+1)`), cast to ℤ, then case-split on parity of `n+1`:
either way yields a Bezout combination summing to 1, so `Int.gcd a b ∣ 1`
by `Int.gcd_dvd_iff`. -/
theorem of_v_nums_dens_coprime (v : ℝ) (n : Nat)
    (h_not_term : ¬ (GenContFract.of v).TerminatedAt n)
    (a b : ℤ) (ha : (GenContFract.of v).nums n = (a : ℝ))
    (hb : (GenContFract.of v).dens n = (b : ℝ)) :
    Int.gcd a b = 1 := by
  obtain ⟨a', ha'⟩ := nums_int_valued v (n+1)
  obtain ⟨b', hb'⟩ := dens_int_valued v (n+1)
  have h_det := of_v_determinant v n h_not_term
  rw [ha, hb, ha', hb'] at h_det
  have h_int : a * b' - b * a' = (-1) ^ (n + 1) := by
    have h_cast : ((a * b' - b * a' : ℤ) : ℝ) = (((-1 : ℤ) ^ (n + 1) : ℤ) : ℝ) := by
      push_cast
      convert h_det using 1
    exact_mod_cast h_cast
  rcases (Nat.even_or_odd (n+1)) with hev | hod
  · have h_pow : ((-1 : ℤ) ^ (n + 1)) = 1 := Even.neg_one_pow hev
    rw [h_pow] at h_int
    have h2 : a * b' + b * (-a') = 1 := by linarith
    have hdiv : Int.gcd a b ∣ 1 :=
      Int.gcd_dvd_iff.mpr ⟨b', -a', by exact_mod_cast h2.symm⟩
    exact Nat.eq_one_of_dvd_one hdiv
  · have h_pow : ((-1 : ℤ) ^ (n + 1)) = -1 := Odd.neg_one_pow hod
    rw [h_pow] at h_int
    have h2 : a * (-b') + b * a' = 1 := by linarith
    have hdiv : Int.gcd a b ∣ 1 :=
      Int.gcd_dvd_iff.mpr ⟨-b', a', by exact_mod_cast h2.symm⟩
    exact Nat.eq_one_of_dvd_one hdiv

end FormalRV.SQIRPort
