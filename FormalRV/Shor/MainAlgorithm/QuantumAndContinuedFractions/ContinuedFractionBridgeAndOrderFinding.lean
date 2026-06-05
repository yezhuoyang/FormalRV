import FormalRV.Shor.MainAlgorithm.QuantumAndContinuedFractions.ContinuedFractionInvariants

namespace FormalRV.SQIRPort

/-- **Base case for slice 2 bridge** (Phase 3, r_found_1 prep, added
2026-05-23): the 0-th convergent of `o/m` (with `m > 0`) is `(o/m, 1)`.
Matches mathlib's `GenContFract.of`'s zeroth convergent which is the
integer part `⌊o/m⌋`. -/
theorem ContinuedFraction_zero (o m : Nat) (_h_m_pos : 0 < m) :
    ContinuedFraction 0 o m = (o / m, 1) := by
  unfold ContinuedFraction cf_aux
  split
  · omega
  · unfold cf_aux; simp

/-- **n=0 bridge to mathlib's `GenContFract`** (Phase 3, r_found_1 prep,
added 2026-05-23): the 0-th numerator of `GenContFract.of ((o:ℚ)/m)`
matches our `(ContinuedFraction 0 o m).1` cast to ℚ. Uses
`GenContFract.zeroth_num_eq_h` + `GenContFract.of_h_eq_floor` +
`Rat.floor_natCast_div_natCast`. -/
theorem cf_bridge_nums_zero (o m : Nat) (h_m_pos : 0 < m) :
    let q : ℚ := (o : ℚ) / m
    let g := GenContFract.of q
    g.nums 0 = (((ContinuedFraction 0 o m).1 : Nat) : ℚ) := by
  intro q g
  rw [ContinuedFraction_zero o m h_m_pos]
  rw [GenContFract.zeroth_num_eq_h]
  show g.h = ((o / m : Nat) : ℚ)
  rw [GenContFract.of_h_eq_floor]
  rw [Rat.floor_natCast_div_natCast]
  rfl

/-- **n=0 bridge for denominator** (Phase 3, r_found_1 prep, added
2026-05-23): the 0-th denominator of `GenContFract.of` is always 1,
matching our `(ContinuedFraction 0 o m).2 = 1`. -/
theorem cf_bridge_dens_zero (o m : Nat) (h_m_pos : 0 < m) :
    let q : ℚ := (o : ℚ) / m
    let g := GenContFract.of q
    g.dens 0 = (((ContinuedFraction 0 o m).2 : Nat) : ℚ) := by
  intro q g
  rw [ContinuedFraction_zero o m h_m_pos]
  rw [GenContFract.zeroth_den_eq_one]
  simp

/-- **Inductive step of the slice-2 bridge** (Phase 3, r_found_1 prep,
added 2026-05-23): The `(n+1)`-th element of `GenContFract.of (o/m).s`
equals the `n`-th element of `GenContFract.of (m / (o%m)).s` — exactly
the Euclidean step our `cf_aux` performs. Uses
`GenContFract.of_s_succ` + `Int.fract_div_natCast_eq_div_natCast_mod`. -/
theorem cf_of_div_succ_step (o m n : Nat) (h_mod_pos : 0 < o % m) :
    (GenContFract.of ((o:ℚ)/m)).s.get? (n+1) =
      (GenContFract.of ((m:ℚ)/((o % m : Nat) : ℚ))).s.get? n := by
  rw [GenContFract.of_s_succ]
  congr 2
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]

/-- **Joint base case** (Phase 3, r_found_1 prep, added 2026-05-23):
combines `cf_bridge_nums_zero` and `cf_bridge_dens_zero` into the
conjunction form needed by the joint induction (`cf_bridge_full` below). -/
theorem cf_bridge_full_zero (o m : Nat) (h_m_pos : 0 < m) :
    let q : ℚ := (o : ℚ) / m
    let g := GenContFract.of q
    g.nums 0 = (((ContinuedFraction 0 o m).1 : Nat) : ℚ) ∧
    g.dens 0 = (((ContinuedFraction 0 o m).2 : Nat) : ℚ) :=
  ⟨cf_bridge_nums_zero o m h_m_pos, cf_bridge_dens_zero o m h_m_pos⟩

/-- **n=1 denominator bridge** (Phase 3, r_found_1 prep, added 2026-05-23):
For `o, m > 0` with `o % m > 0` (CF doesn't terminate at step 1),
`(GenContFract.of ((o:ℚ)/m)).dens 1 = m/(o%m)` (Nat division), matching
the structure of our `cf_aux` after one Euclidean step. Uses
`GenContFract.of_s_head` (head of stream = `{a:=1, b:=⌊(Int.fract v)⁻¹⌋}`)
+ `Int.fract_div_natCast_eq_div_natCast_mod` + `Rat.floor_natCast_div_natCast`
+ `GenContFract.first_den_eq`. -/
theorem cf_bridge_dens_one (o m : Nat) (h_m_pos : 0 < m)
    (h_mod_pos : 0 < o % m) :
    let q : ℚ := (o : ℚ) / m
    let g := GenContFract.of q
    g.dens 1 = ((m / (o % m) : Nat) : ℚ) := by
  intro q g
  have h_fract : Int.fract q ≠ 0 := by
    show Int.fract ((o : ℚ) / m) ≠ 0
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_m_ne : (m : ℚ) ≠ 0 := by exact_mod_cast h_m_pos.ne'
    intro h_zero
    have : (m : ℚ) * (((o % m : Nat) : ℚ) / m) = (m : ℚ) * 0 := by rw [h_zero]
    rw [mul_div_cancel₀ _ h_m_ne] at this
    simp at this
    exact h_mod_pos.ne' (by exact_mod_cast this)
  have h_head : g.s.get? 0 = some { a := 1, b := ((m / (o % m) : Nat) : ℚ) } := by
    have := GenContFract.of_s_head (v := q) h_fract
    rw [show g.s.get? 0 = g.s.head from rfl, this]
    congr 1
    rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
    rw [Rat.floor_natCast_div_natCast]
    rfl
  rw [GenContFract.first_den_eq h_head]

/-- **n=1 numerator bridge** (Phase 3, r_found_1 prep, added 2026-05-23):
For `o, m > 0` with `o % m > 0`, `(GenContFract.of ((o:ℚ)/m)).nums 1
= (m/(o%m)) · (o/m) + 1` (Nat arithmetic), matching `ContinuedFraction 1 o m`.
Uses `GenContFract.first_num_eq` (`nums 1 = b · h + a` for the head pair) +
the same head computation as `cf_bridge_dens_one` + `Rat.floor_natCast_div_natCast`. -/
theorem cf_bridge_nums_one (o m : Nat) (h_m_pos : 0 < m)
    (h_mod_pos : 0 < o % m) :
    let q : ℚ := (o : ℚ) / m
    let g := GenContFract.of q
    g.nums 1 = (((m / (o % m)) * (o / m) + 1 : Nat) : ℚ) := by
  intro q g
  have h_fract : Int.fract q ≠ 0 := by
    show Int.fract ((o : ℚ) / m) ≠ 0
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_m_ne : (m : ℚ) ≠ 0 := by exact_mod_cast h_m_pos.ne'
    intro h_zero
    have : (m : ℚ) * (((o % m : Nat) : ℚ) / m) = (m : ℚ) * 0 := by rw [h_zero]
    rw [mul_div_cancel₀ _ h_m_ne] at this
    simp at this
    exact h_mod_pos.ne' (by exact_mod_cast this)
  have h_head : g.s.get? 0 = some { a := 1, b := ((m / (o % m) : Nat) : ℚ) } := by
    have := GenContFract.of_s_head (v := q) h_fract
    rw [show g.s.get? 0 = g.s.head from rfl, this]
    congr 1
    rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
    rw [Rat.floor_natCast_div_natCast]
    rfl
  rw [GenContFract.first_num_eq h_head, GenContFract.of_h_eq_floor]
  have h_floor_int : ⌊q⌋ = ((o / m : Nat) : ℤ) := Rat.floor_natCast_div_natCast o m
  have h_floor_R : ((⌊q⌋ : ℤ) : ℚ) = ((o / m : Nat) : ℚ) := by
    rw [h_floor_int]; push_cast; rfl
  rw [show ((⌊q⌋ : ℤ) : ℚ) = ((o / m : Nat) : ℚ) from h_floor_R]
  push_cast
  ring

-- (cf_bridge_full ℚ-version scaffold deleted 2026-05-24 — superseded by the
--  proven ℝ-version `cf_aux_full_matches_mathlib_strong` after the general
--  bridge invariant landed. The ℚ form was unused scaffolding.)

/-- The denominator of the `step`-th continued-fraction convergent of
`o / 2^m` (Coq: `Shor.v` line 47 `OF_post_step`). -/
noncomputable def OF_post_step (step o m : Nat) : Nat :=
  (ContinuedFraction step o (2^m)).2

/-- Iterated continued-fraction post-processor (Coq: `Shor.v` line 49
`OF_post'`).  Walks the convergents; returns the first denominator
that classically verifies as the order, or 0. -/
noncomputable def OF_post' : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, _ => 0
  | step + 1, a, N, o, m =>
      let pre := OF_post' step a N o m
      if pre = 0 then
        (if modexp a (OF_post_step step o m) N = 1
         then OF_post_step step o m
         else 0)
      else pre

/-- The order-finding post-processor (Coq: `Shor.v` line 58 `OF_post`):
runs `2m+2` continued-fraction iterations. -/
noncomputable def OF_post (a N o m : Nat) : Nat := OF_post' (2 * m + 2) a N o m

/-- Did the post-processor recover the order `r` from measurement
outcome `o`? (Coq: `Shor.v` line 63 `r_found`.)  Real-valued 0/1
indicator so it can be summed against measurement probabilities. -/
noncomputable def r_found (o m r a N : Nat) : ℝ :=
  if OF_post a N o m = r then 1 else 0

end FormalRV.SQIRPort
