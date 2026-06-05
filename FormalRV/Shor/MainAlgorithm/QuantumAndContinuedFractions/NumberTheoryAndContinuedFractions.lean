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

/-- **cf_aux_full's "step at end" expression** (added 2026-05-24): when the
Euclidean iteration hasn't terminated at step N (i.e., `.2 > 0`), one extra
iteration `cf_aux_full (N+1)` equals applying ONE cf_aux step to the output
of `cf_aux_full N`. The step's `a = oN/mN` where `(oN, mN) = euclidean_iter N o m`.

This is the "peel from end" lemma needed to extend bridges past the
non-terminated boundary in the terminated case of TODO_non_div_terminated_stable. -/
theorem cf_aux_full_succ_step :
    ∀ (N o m p_prev p_curr q_prev q_curr : Nat),
      0 < (euclidean_iter N o m).2 →
      cf_aux_full (N + 1) o m p_prev p_curr q_prev q_curr =
        let s := cf_aux_full N o m p_prev p_curr q_prev q_curr
        let oN := (euclidean_iter N o m).1
        let mN := (euclidean_iter N o m).2
        (s.2.1, (oN / mN) * s.2.1 + s.1, s.2.2.2, (oN / mN) * s.2.2.2 + s.2.2.1) := by
  intro N
  induction N with
  | zero =>
    intros o m p_prev p_curr q_prev q_curr h_eucl_pos
    -- h_eucl_pos : 0 < (eucl_iter 0 o m).2 = m. So m > 0.
    have h_m_pos : 0 < m := h_eucl_pos
    -- cf_aux_full 1 o m S = step S (since m > 0).
    -- cf_aux_full 0 o m S = S. step-at-end of S using (eucl_iter 0 o m) = (o, m).
    show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
          else cf_aux_full 0 m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                       q_curr ((o / m) * q_curr + q_prev))
        = (p_curr, (o / m) * p_curr + p_prev, q_curr, (o / m) * q_curr + q_prev)
    rw [if_neg h_m_pos.ne']
    rfl
  | succ N' ih =>
    intros o m p_prev p_curr q_prev q_curr h_eucl_pos
    -- h_eucl_pos : (eucl_iter (N'+1) o m).2 > 0.
    -- Need: m > 0 (else eucl_iter would be (o, m) with .2 = m).
    have h_m_pos : 0 < m := by
      by_contra h_m_zero
      push_neg at h_m_zero
      interval_cases m
      simp [euclidean_iter] at h_eucl_pos
    -- Unfold (eucl_iter (N'+1) o m) using m > 0.
    have h_eucl_shift : euclidean_iter (N' + 1) o m = euclidean_iter N' m (o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter N' m (o % m)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_eucl_shift] at h_eucl_pos
    -- h_eucl_pos : (eucl_iter N' m (o%m)).2 > 0.
    -- Apply IH at (m, o%m).
    have h_ih := ih m (o % m) p_curr ((o / m) * p_curr + p_prev)
                    q_curr ((o / m) * q_curr + q_prev) h_eucl_pos
    -- Unfold LHS via cf_aux_full's recursion.
    show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
          else cf_aux_full (N' + 1) m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                              q_curr ((o / m) * q_curr + q_prev))
        = _
    rw [if_neg h_m_pos.ne']
    -- Now LHS = cf_aux_full (N'+1) m (o%m) (mutated state).
    -- By IH: this = step-at-end of cf_aux_full N' m (o%m) (mutated state).
    rw [h_ih]
    -- Unfold RHS's cf_aux_full N+1 = cf_aux_full (N'+1+1) using its def at top level.
    -- Actually RHS = step-at-end of cf_aux_full (N'+1) o m S. And cf_aux_full (N'+1) o m S
    -- = cf_aux_full N' m (o%m) (mutated). So RHS step-at-end is on cf_aux_full N' m (o%m) (mutated).
    -- The (eucl_iter (N'+1) o m) = (eucl_iter N' m (o%m)) by h_eucl_shift. Same a value.
    show (let s := cf_aux_full N' m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                            q_curr ((o / m) * q_curr + q_prev)
          let oN := (euclidean_iter N' m (o % m)).1
          let mN := (euclidean_iter N' m (o % m)).2
          (s.2.1, oN / mN * s.2.1 + s.1, s.2.2.2, oN / mN * s.2.2.2 + s.2.2.1))
        = (let s := cf_aux_full (N' + 1) o m p_prev p_curr q_prev q_curr
           let oN := (euclidean_iter (N' + 1) o m).1
           let mN := (euclidean_iter (N' + 1) o m).2
           (s.2.1, oN / mN * s.2.1 + s.1, s.2.2.2, oN / mN * s.2.2.2 + s.2.2.1))
    -- Both sides have the same structure. Show that cf_aux_full N' m (o%m) (mutated)
    -- = cf_aux_full (N'+1) o m S, and the eucl_iters match by h_eucl_shift.
    have h_unfold : cf_aux_full (N' + 1) o m p_prev p_curr q_prev q_curr
        = cf_aux_full N' m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                   q_curr ((o / m) * q_curr + q_prev) := by
      show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
            else cf_aux_full N' m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                          q_curr ((o / m) * q_curr + q_prev)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_unfold]
    rw [h_eucl_shift]

/-- **cf_aux_full's output is invariant under extra depth, post-termination**
(added 2026-05-24): if there exists `j ≤ N` with `(euclidean_iter j o m).2 = 0`
(cf_aux's Euclidean reaches termination within `N` steps), then adding one
more depth (`N+1`) doesn't change the output.

Proof by induction on N, exploiting that cf_aux's `m = 0` guard returns the
state regardless of remaining depth. The IH at the shifted `(m, o%m)` state
uses the Euclidean shift: if j ≥ 1, then `(euclidean_iter j o m).2 = 0`
implies `(euclidean_iter (j-1) m (o%m)).2 = 0`. -/
theorem cf_aux_full_depth_invariant :
    ∀ N o m p_prev p_curr q_prev q_curr,
      (∃ j, j ≤ N ∧ (euclidean_iter j o m).2 = 0) →
      cf_aux_full (N + 1) o m p_prev p_curr q_prev q_curr
        = cf_aux_full N o m p_prev p_curr q_prev q_curr := by
  intro N
  induction N with
  | zero =>
    -- Condition: ∃ j ≤ 0 with (eucl_iter j o m).2 = 0 → j = 0 → m = 0.
    rintro o m p_prev p_curr q_prev q_curr ⟨j, h_le, h_eq⟩
    have h_j : j = 0 := by omega
    subst h_j
    -- h_eq : (eucl_iter 0 o m).2 = m = 0.
    have h_m : m = 0 := h_eq
    subst h_m
    -- cf_aux_full 1 o 0 = cf_aux_full 0 o 0 = state.
    show (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr) else _)
        = (p_prev, p_curr, q_prev, q_curr)
    rfl
  | succ N' ih =>
    rintro o m p_prev p_curr q_prev q_curr ⟨j, h_le, h_eq⟩
    by_cases h_m : m = 0
    · subst h_m
      -- m = 0: both sides return state via the m=0 guard.
      show (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr) else _)
          = (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr) else _)
      rfl
    · -- m > 0: unfold both sides, apply IH at (m, o%m, mutated state).
      have h_m_pos : 0 < m := Nat.pos_of_ne_zero h_m
      -- Derive condition for IH at (m, o%m): ∃ j' ≤ N', (eucl_iter j' m (o%m)).2 = 0.
      have h_j_pos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h_j0 | h_jp
        · subst h_j0
          -- h_eq : (eucl_iter 0 o m).2 = m = 0. Contradicts m > 0.
          exact absurd h_eq h_m
        · exact h_jp
      have h_eucl_shift : (euclidean_iter (j - 1) m (o % m)).2 = 0 := by
        have h_unfold : euclidean_iter j o m = euclidean_iter (j - 1) m (o % m) := by
          have h_j_eq : j = (j - 1) + 1 := by omega
          conv_lhs => rw [h_j_eq]
          show (if m = 0 then (o, m) else euclidean_iter (j - 1) m (o % m))
              = euclidean_iter (j - 1) m (o % m)
          rw [if_neg h_m]
        rw [h_unfold] at h_eq
        exact h_eq
      have h_ih_cond : ∃ j', j' ≤ N' ∧ (euclidean_iter j' m (o % m)).2 = 0 :=
        ⟨j - 1, by omega, h_eucl_shift⟩
      -- Unfold both sides.
      show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
            else cf_aux_full (N' + 1) m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                   q_curr ((o / m) * q_curr + q_prev))
          = (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
             else cf_aux_full N' m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                   q_curr ((o / m) * q_curr + q_prev))
      rw [if_neg h_m, if_neg h_m]
      exact ih m (o % m) p_curr ((o / m) * p_curr + p_prev)
              q_curr ((o / m) * q_curr + q_prev) h_ih_cond

/-- **Euclidean iteration is monotone-terminating** (added 2026-05-24):
once `(euclidean_iter j o m).2 = 0` (cf_aux's m_arg hit 0 at step j),
the iteration stays terminated at all subsequent steps `j + k`. Proven by
induction on `j` with universal quantification over `o` and `m` (allowing
the inductive hypothesis to apply to the shifted state `(m, o%m)`). -/
theorem eucl_iter_stable :
    ∀ (j : Nat) (o m k : Nat),
      (euclidean_iter j o m).2 = 0 → (euclidean_iter (j + k) o m).2 = 0 := by
  intro j
  induction j with
  | zero =>
    intros o m k h
    -- h : (euclidean_iter 0 o m).2 = m = 0
    have h_m : m = 0 := h
    subst h_m
    -- Need: (euclidean_iter k o 0).2 = 0
    induction k with
    | zero => rfl
    | succ k' _ =>
      show (if (0 : Nat) = 0 then (o, 0) else _).2 = 0
      rfl
  | succ j' ih =>
    intros o m k h
    by_cases h_m : m = 0
    · -- m = 0: subst and recurse.
      subst h_m
      induction k with
      | zero => exact h
      | succ k' _ =>
        show (if (0 : Nat) = 0 then (o, 0) else _).2 = 0
        rfl
    · -- m > 0: unfold via the (n+1) pattern at both ends, apply ih.
      have h_unfold_lhs : euclidean_iter (j' + 1) o m = euclidean_iter j' m (o % m) := by
        show (if m = 0 then (o, m) else euclidean_iter j' m (o % m)) = _
        rw [if_neg h_m]
      rw [h_unfold_lhs] at h
      -- h : (euclidean_iter j' m (o%m)).2 = 0
      have h_succ : (euclidean_iter (j' + k) m (o % m)).2 = 0 := ih m (o % m) k h
      -- Target: (euclidean_iter (j' + 1 + k) o m).2 = 0
      have h_assoc : j' + 1 + k = (j' + k) + 1 := by ring
      rw [h_assoc]
      show (if m = 0 then (o, m) else euclidean_iter (j' + k) m (o % m)).2 = 0
      rw [if_neg h_m]
      exact h_succ

/-- **Structural insight for the joint induction succ case** (Phase 3
r_found_1, documentation tick 76):

The cf_aux_full recursion `(p_prev, p_curr) → (p_curr, a · p_curr + p_prev)`
EXACTLY mirrors mathlib's `conts_recurrence`:
`conts (n+2) = ⟨b · (conts (n+1)).a + a · (conts n).a, ...⟩` with `a = 1`
for SimpContFract.of (i.e., `GenContFract.of`).

The matching: cf_aux's `a` parameter at iteration k = mathlib's `b_k`
(the k-th partial denominator). cf_aux's state (p_prev, p_curr, q_prev,
q_curr) at iteration k = mathlib's (conts(k-1), conts(k)) for v = original
o/m.

**To make the joint induction work**, the invariant needs to be stated in
the most general form: for ANY state and ANY Euclidean shift of the
inputs, cf_aux's K-step result matches mathlib's contsAux applied K times
from the corresponding mathlib starting state. This is the form that
makes induction on K succeed.

**Formalization is multi-tick**: requires (a) stating the predicate
"cf_aux state matches mathlib at offset k for v" precisely, (b) proving
this predicate is preserved under one cf_aux_full step, (c) showing the
initial state (0, 1, 1, 0) at (o, m) matches mathlib at offset "before
the first step", which after one cf_aux iteration becomes offset 0. -/
def cf_aux_general_invariant_intent : Prop := True  -- design docs

/-- **Derive `o % m ≠ 0` from non-termination at step 0** (Phase 3
r_found_1 base case prep, added 2026-05-24 tick 73): when
`GenContFract.of (o/m)` is not terminated at step 0 (i.e., the stream
hasn't ended), the fractional part is non-zero, which for `v = o/m`
means `o % m ≠ 0`. -/
theorem nondiv_of_not_terminated_zero (o m : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0) :
    o % m ≠ 0 := by
  intro h_mod
  apply h_not_term
  rw [GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none]
  have h_stream_0 : GenContFract.IntFractPair.stream
      (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 0
      = some (GenContFract.IntFractPair.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) := rfl
  apply GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero h_stream_0
  show Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) = 0
  rw [Int.fract_div_natCast_eq_div_natCast_mod, h_mod]
  simp

-- (cf_aux_full_matches_mathlib_zero moved later — depends on mathlib_*_eq_* defs.)
-- (The old scaffold `TODO_cf_aux_full_matches_mathlib` was deleted 2026-05-24 —
--  superseded by the proven `cf_aux_full_matches_mathlib_strong` after the
--  general bridge invariant landed.)

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
