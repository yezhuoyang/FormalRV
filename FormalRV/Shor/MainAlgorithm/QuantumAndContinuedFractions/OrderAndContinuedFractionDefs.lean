import FormalRV.Shor.MainAlgorithm.QuantumAndContinuedFractions.QuantumPrimitives


namespace FormalRV.SQIRPort

/-! ## §2. Number-theoretic primitives. -/

/-- `r` is the (multiplicative) order of `a` mod `N`: `a^r ≡ 1 (mod N)`
and `r` is the least such positive exponent. -/
def Order (a r N : Nat) : Prop :=
  0 < r ∧ a^r % N = 1 ∧ ∀ s, 0 < s → s < r → a^s % N ≠ 1

/-- Modular exponentiation (Coq: `Shor.v` line 48 `modexp`). -/
def modexp (a x N : Nat) : Nat := a^x % N

/-- Helper for `ContinuedFraction`: iterates the Euclidean step,
maintaining the two-back convergent numerators/denominators.
Standard CF recursion: `p_k = a_k * p_{k-1} + p_{k-2}` and
similarly for `q_k`. Initial state `(p_prev, p_curr, q_prev, q_curr)
= (0, 1, 1, 0)` encodes `p_{-2}/q_{-2}` placeholders. -/
def cf_aux : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, _, _, p_curr, _, q_curr => (p_curr, q_curr)
  | n+1, o, m, p_prev, p_curr, q_prev, q_curr =>
      if m = 0 then (p_curr, q_curr)
      else
        let a := o / m
        cf_aux n m (o % m) p_curr (a * p_curr + p_prev)
                                 q_curr (a * q_curr + q_prev)

/-- One step of continued-fraction expansion: `(numerator, denominator)`
of the `step`-th convergent of `o / m`.

**Closed 2026-05-23 as a constructive def** (Phase 2 axiom #1, the
only Phase 2 axiom in `Shor_correct_var`'s chain):
Replaces the previous `axiom` with an explicit Euclidean-step
recursion. Verified on small inputs: `ContinuedFraction k 5 3`
gives convergents `(1,1), (2,1), (5,3)` matching `[1; 1, 2]` for `5/3`.

**Note on spec**: this def's semantic correctness (does it actually
return the k-th convergent of `o/m` for every k?) would be a Phase 3
theorem to discharge `r_found_1`. Here we only replace the axiom with
SOME computable function, eliminating it from the axiom hygiene of
`Shor_correct_var`. The remaining `r_found_1` axiom abstracts over
the semantics. -/
def ContinuedFraction (step o m : Nat) : Nat × Nat :=
  cf_aux (step + 1) o m 0 1 1 0

/-- **`cf_aux` definitional unfold at 0**: returns `(p_curr, q_curr)`. -/
theorem cf_aux_zero (o m p_prev p_curr q_prev q_curr : Nat) :
    cf_aux 0 o m p_prev p_curr q_prev q_curr = (p_curr, q_curr) := rfl

/-- **`cf_aux` definitional unfold at successor with `m > 0`**: one Euclidean
step. Useful for unfolding cf_aux step-by-step in proofs without re-deriving
the case split each time. -/
theorem cf_aux_succ_pos (n o m p_prev p_curr q_prev q_curr : Nat)
    (h_m_pos : 0 < m) :
    cf_aux (n+1) o m p_prev p_curr q_prev q_curr
      = cf_aux n m (o % m) p_curr ((o/m) * p_curr + p_prev)
                                  q_curr ((o/m) * q_curr + q_prev) := by
  show (if m = 0 then (p_curr, q_curr)
        else cf_aux n m (o % m) p_curr ((o/m) * p_curr + p_prev)
                                         q_curr ((o/m) * q_curr + q_prev))
      = cf_aux n m (o % m) p_curr ((o/m) * p_curr + p_prev)
                                  q_curr ((o/m) * q_curr + q_prev)
  rw [if_neg h_m_pos.ne']

/-- **`cf_aux` definitional unfold at successor with `m = 0`**: returns
`(p_curr, q_curr)` (terminates on 0 denominator). -/
theorem cf_aux_succ_zero (n o p_prev p_curr q_prev q_curr : Nat) :
    cf_aux (n+1) o 0 p_prev p_curr q_prev q_curr = (p_curr, q_curr) := by
  show (if (0 : Nat) = 0 then (p_curr, q_curr) else _) = (p_curr, q_curr)
  rfl

/-- **Full-state cf_aux** (Phase 3 r_found_1 infrastructure, added
2026-05-24 tick 66): cf_aux that returns ALL FOUR state values
`(p_prev, p_curr, q_prev, q_curr)` at termination, rather than just
`(p_curr, q_curr)`. Needed for the joint induction proof because the
inductive step requires knowing BOTH the current AND previous convergent
pair to apply mathlib's `nums_recurrence`/`dens_recurrence`. -/
def cf_aux_full : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat × Nat × Nat
  | 0, _, _, p_prev, p_curr, q_prev, q_curr => (p_prev, p_curr, q_prev, q_curr)
  | n+1, o, m, p_prev, p_curr, q_prev, q_curr =>
      if m = 0 then (p_prev, p_curr, q_prev, q_curr)
      else
        let a := o / m
        cf_aux_full n m (o % m) p_curr (a * p_curr + p_prev)
                                       q_curr (a * q_curr + q_prev)

/-- The pair-output cf_aux equals the projection of the full-state version. -/
theorem cf_aux_eq_cf_aux_full_proj (n o m p_prev p_curr q_prev q_curr : Nat) :
    cf_aux n o m p_prev p_curr q_prev q_curr =
      ((cf_aux_full n o m p_prev p_curr q_prev q_curr).2.1,
       (cf_aux_full n o m p_prev p_curr q_prev q_curr).2.2.2) := by
  induction n generalizing o m p_prev p_curr q_prev q_curr with
  | zero => rfl
  | succ k ih =>
    unfold cf_aux cf_aux_full
    by_cases h : m = 0
    · simp [h]
    · simp [h]
      exact ih _ _ _ _ _ _

/-- **`cf_aux_full 2` unfold for non-divisible case** (Phase 3 r_found_1
n=0 base case prep, added 2026-05-24 tick 72): explicit value when
`m > 0` and `o % m ≠ 0`. Two cf_aux steps with the Euclidean transition
fill the state to `(o/m, (m/(o%m))*(o/m)+1, 1, m/(o%m))`. -/
theorem cf_aux_full_2_nondiv (o m : Nat) (h_m_pos : 0 < m)
    (h_mod : o % m ≠ 0) :
    cf_aux_full 2 o m 0 1 1 0
      = (o / m, m / (o % m) * (o / m) + 1, 1, m / (o % m)) := by
  unfold cf_aux_full
  simp [h_m_pos.ne']
  unfold cf_aux_full
  simp [h_mod]
  rfl

/-- **`cf_aux_full 3` unfold for non-divisible chain** (Phase 3 r_found_1
n=1 case prep, added 2026-05-24 tick 75): explicit value when both `o%m ≠ 0`
AND `m%(o%m) ≠ 0`. Three cf_aux steps fill the state. Matches mathlib's
`(nums 1, nums 2, dens 1, dens 2)` for v = o/m by hand-verification of the
conts_recurrence with b_0 = m/(o%m) and b_1 = (o%m)/(m%(o%m)). -/
theorem cf_aux_full_3_nondiv2 (o m : Nat) (h_m_pos : 0 < m)
    (h_mod1 : o % m ≠ 0) (h_mod2 : m % (o % m) ≠ 0) :
    cf_aux_full 3 o m 0 1 1 0 =
      (m / (o % m) * (o / m) + 1,
       (o % m) / (m % (o % m)) * (m / (o % m) * (o / m) + 1) + (o / m),
       m / (o % m),
       (o % m) / (m % (o % m)) * (m / (o % m)) + 1) := by
  unfold cf_aux_full
  simp [h_m_pos.ne']
  unfold cf_aux_full
  simp [h_mod1]
  unfold cf_aux_full
  simp [h_mod2]
  rfl

/-- **Euclidean iteration on `(o, m)` pairs** (Phase 3 r_found_1 helper,
added 2026-05-24 tick 77): captures the state transition `(o, m) ↦
(m, o % m)` that cf_aux performs in its recursive call. At iteration
`k`, returns the k-th Euclidean iterate of the initial `(o, m)`. Stops
if `m = 0` (terminated). -/
def euclidean_iter : Nat → Nat → Nat → Nat × Nat
  | 0, o, m => (o, m)
  | n+1, o, m => if m = 0 then (o, m) else euclidean_iter n m (o % m)

/-- **cf_aux_full stabilizes when m_arg = 0** (added 2026-05-24):
Structural property of cf_aux_full's recursion — once the m parameter hits 0,
the function returns the current state unchanged regardless of remaining depth.

Both base case (n=0) and the m=0 guard in the recursive case yield the
same constant output `(p_prev, p_curr, q_prev, q_curr)`. Useful for the
terminated-case proof in `TODO_non_div_terminated_stable`. -/
theorem cf_aux_full_terminate (n o p_prev p_curr q_prev q_curr : Nat) :
    cf_aux_full n o 0 p_prev p_curr q_prev q_curr = (p_prev, p_curr, q_prev, q_curr) := by
  cases n with
  | zero => rfl
  | succ k =>
    show (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr) else _) = _
    rfl

/-- **cf_aux stabilizes when m_arg = 0** (added 2026-05-24): the pair-output
version. Corollary of `cf_aux_full_terminate` + `cf_aux_eq_cf_aux_full_proj`. -/
theorem cf_aux_terminate (n o p_prev p_curr q_prev q_curr : Nat) :
    cf_aux n o 0 p_prev p_curr q_prev q_curr = (p_curr, q_curr) := by
  rw [cf_aux_eq_cf_aux_full_proj, cf_aux_full_terminate]

/-- **Euclidean iteration terminates** (added 2026-05-24): the standard
Euclidean algorithm always reaches `.2 = 0` after at most `m` iterations
(strict decrease of the second component). Concretely:
`∃ j ≤ m, (euclidean_iter j o m).2 = 0`.

Used downstream to bridge cf_aux termination with mathlib's GenContFract
termination in the terminated case of `TODO_non_div_terminated_stable`. -/
theorem eucl_iter_terminates (o m : Nat) :
    ∃ j, j ≤ m ∧ (euclidean_iter j o m).2 = 0 := by
  -- Strong induction on m.
  induction m using Nat.strong_induction_on generalizing o with
  | _ m ih =>
    by_cases h_m : m = 0
    · refine ⟨0, by omega, ?_⟩
      simp [euclidean_iter, h_m]
    · have h_m_pos : 0 < m := Nat.pos_of_ne_zero h_m
      have h_mod_lt : o % m < m := Nat.mod_lt _ h_m_pos
      obtain ⟨j, h_le, h_eq⟩ := ih (o % m) h_mod_lt m
      refine ⟨j + 1, by omega, ?_⟩
      show (if m = 0 then (o, m) else euclidean_iter j m (o % m)).2 = 0
      rw [if_neg h_m]
      exact h_eq

end FormalRV.SQIRPort
