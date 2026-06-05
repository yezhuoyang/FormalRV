import FormalRV.Shor.MainAlgorithm.ContinuedFractionBridge.MathlibOFPostStep

namespace FormalRV.SQIRPort

/-- **`OF_post_step` at step 0 is 1** (Phase 3 r_found_1 bridge, added
2026-05-23): direct unfold of `cf_aux 1 o (2^m) 0 1 1 0`. Since `2^m ≠ 0`,
one cf_aux step yields `(a, 1)` and the depth-0 base case returns
`(p_curr, q_curr) = (a, 1)`, giving denominator 1. -/
theorem OF_post_step_zero (o m : Nat) : OF_post_step 0 o m = 1 := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux 1 o (2^m) 0 1 1 0).2 = 1
  unfold cf_aux
  simp
  rfl

/-- **`OF_post_step` at step 1 when divisible**: if `o % 2^m = 0` then
`OF_post_step 1 o m = 1`. cf_aux unfolding: first step gives `(a, 1)`
then depth-0 with `m = 0` returns `(p_curr, q_curr) = (a, 1)`. -/
theorem OF_post_step_one_div (o m : Nat) (h_mod : o % (2^m) = 0) :
    OF_post_step 1 o m = 1 := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux 2 o (2^m) 0 1 1 0).2 = 1
  unfold cf_aux
  simp
  unfold cf_aux
  simp [h_mod]

/-- **`OF_post_step` at step 1 when not divisible**: if `o % 2^m ≠ 0`
then `OF_post_step 1 o m = (2^m) / (o % 2^m)`. -/
theorem OF_post_step_one_nondiv (o m : Nat) (h_mod : o % (2^m) ≠ 0) :
    OF_post_step 1 o m = (2^m) / (o % 2^m) := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux 2 o (2^m) 0 1 1 0).2 = (2^m) / (o % 2^m)
  unfold cf_aux
  simp
  unfold cf_aux
  simp [h_mod]
  rfl

/-- **`OF_post_step` at step 2 when divisible**: if `o % 2^m = 0` then
`OF_post_step 2 o m = 1`. cf_aux unfolds 3 times; the m=0 case in the
inner Euclidean step returns `q_curr = 1`. -/
theorem OF_post_step_two_div (o m : Nat) (h_mod : o % (2^m) = 0) :
    OF_post_step 2 o m = 1 := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux 3 o (2^m) 0 1 1 0).2 = 1
  unfold cf_aux
  simp
  unfold cf_aux
  simp [h_mod]

/-- **`OF_post_step` for general n when divisible** (Phase 3 r_found_1,
added 2026-05-24): if `o % 2^m = 0` then `OF_post_step n o m = 1` for
ALL n. cf_aux unfolds once, then the inner state has `m = 0` which
terminates with `q_curr = 1` at any depth ≥ 1. The depth-0 case
specializes to `(cf_aux 0 ...).2 = q_curr = 1`. -/
theorem OF_post_step_div_general (n o m : Nat) (h_mod : o % (2^m) = 0) :
    OF_post_step n o m = 1 := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux (n + 1) o (2^m) 0 1 1 0).2 = 1
  unfold cf_aux
  simp
  cases n with
  | zero => rfl
  | succ k =>
    rw [h_mod]
    unfold cf_aux
    simp

/-- **`OF_post_step` step 1 specialized to `o < 2^m`** (Shor use case,
added 2026-05-24 tick 62): when `o < 2^m` and `o > 0`, the cf_aux step-1
output simplifies via `o % 2^m = o` to `OF_post_step 1 o m = 2^m / o`.
This is the typical case for s_closest (which is < 2^m). -/
theorem OF_post_step_one_shor (o m : Nat) (h_o_pos : 0 < o)
    (h_o_lt : o < 2^m) :
    OF_post_step 1 o m = (2^m) / o := by
  have h_mod_eq : o % (2^m) = o := Nat.mod_eq_of_lt h_o_lt
  unfold OF_post_step ContinuedFraction
  show (cf_aux 2 o (2^m) 0 1 1 0).2 = (2^m) / o
  unfold cf_aux
  simp
  unfold cf_aux
  rw [h_mod_eq]
  simp [h_o_pos.ne']
  rfl

/-- **Shor-case bridge analysis observation** (Phase 3 r_found_1, tick 63):
For `o < 2^m` (the Shor use case for s_closest), cf_aux's first step is
"trivial" (a = o/(2^m) = 0): from initial `(0, 1, 1, 0)` it transitions to
`(1, 0, 0, 1)` and then runs `cf_aux n (2^m) o 1 0 0 1`. This is cf_aux on
the SWAPPED rational `2^m/o` but with a SWAPPED initial state — NOT the
standard ContinuedFraction call. The swap maps cf_aux dens output to
mathlib's nums output for the inverted ratio. Captured as design intent;
formalization is multi-tick. -/
def shor_case_cf_aux_swap_intent : Prop := True  -- placeholder doc

end FormalRV.SQIRPort
