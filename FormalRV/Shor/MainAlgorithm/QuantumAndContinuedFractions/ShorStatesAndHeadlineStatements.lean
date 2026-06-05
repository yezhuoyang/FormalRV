import FormalRV.Shor.MainAlgorithm.QuantumAndContinuedFractions.NumberTheoryAndContinuedFractions

namespace FormalRV.SQIRPort

/-! ## §3. SQIR `Shor.v` definitions (lines 14–65). -/

/-- **`BasicSetting a r N m n`** (`Shor.v:14`).  The Shor parameter
regime: `a ∈ (0, N)` has order `r` mod `N`, the QPE precision register
satisfies `N² < 2^m ≤ 2N²`, and the data register satisfies
`N < 2^n ≤ 2N`. -/
def BasicSetting (a r N m n : Nat) : Prop :=
  (0 < a ∧ a < N) ∧
  Order a r N ∧
  (N^2 < 2^m ∧ 2^m ≤ 2 * N^2) ∧
  (N < 2^n ∧ 2^n ≤ 2 * N)

/-- **`MultiplyCircuitProperty a N n anc c`** (`Shor.v:28`).  Spec
that `c` is a faithful "multiply-by-`a` mod `N`" oracle: for every
`x ∈ [0, N)`, `c · |x⟩|0_anc⟩ = |a·x mod N⟩|0_anc⟩`.

**Closed 2026-05-24**: realized as a Prop-level operational equality on
`uc_eval c`. The encoding `|x⟩|0_anc⟩ = basis_vector (2^(n+anc)) (x · 2^anc)`
uses the integer factorization of the combined-register Hilbert space
(n-qubit "data" + anc-qubit "ancilla" → joint basis state `|x · 2^anc⟩`
when the ancilla starts at zero). -/
def MultiplyCircuitProperty (a N n anc : Nat) (c : BaseUCom (n + anc)) : Prop :=
  ∀ x : Nat, x < N →
    uc_eval c (basis_vector (2^(n + anc)) (x * 2^anc))
      = basis_vector (2^(n + anc)) ((a * x % N) * 2^anc)

/-- **`ModMulImpl a N n anc f`** (`Shor.v:35`).  For every iterate `i`,
the supplied unitary `f i` implements multiplication by `a^(2^i)`
mod `N`.  This is the full set of "squared-power" oracles QPE
consumes. -/
def ModMulImpl (a N n anc : Nat) (f : Nat → BaseUCom (n + anc)) : Prop :=
  ∀ i : Nat, MultiplyCircuitProperty (a^(2^i)) N n anc (f i)

/-- Cast a `QState a` to `QState b` along a dimensional equality `a = b`.
Reindexes the underlying column vector via `Fin.cast`; preserves entries
at corresponding numerical indices. Used to bridge between the `2^(m+(n+anc))`
form produced by `uc_eval ∘ QPE_var` and the `2^m * 2^n * 2^anc` form
required by `Shor_final_state`'s signature. -/
noncomputable def QState.cast {a b : Nat} (h : a = b) (ψ : QState a) : QState b :=
  fun i _ => ψ (Fin.cast h.symm i) 0

/-- The Shor input state `|0⟩_m ⊗ |1⟩_n ⊗ |0⟩_anc` on `(m + (n + anc))` qubits.
Built from `Framework.QuantumLib.kron_vec`; casted from the
left-associative form `2^((m+n)+anc)` to the right-associative form
`2^(m+(n+anc))` (which matches `BaseUCom (m + (n + anc))`). -/
noncomputable def Shor_initial_state (m n anc : Nat) :
    QState (2^(m + (n + anc))) :=
  QState.cast (by rw [Nat.add_assoc])
    (FormalRV.Framework.kron_vec
      (FormalRV.Framework.kron_vec
        (FormalRV.Framework.kron_zeros m)
        (FormalRV.Framework.basis_vector (2^n) 1))
      (FormalRV.Framework.kron_zeros anc))

/-- **`Shor_final_state`** (`Shor.v:39`).  The post-circuit pure state
before measurement: QPE applied to the modular-multiplication oracle
family `f`, on input `|0⟩_m ⊗ |1⟩_n ⊗ |0⟩_anc`.

**Closed 2026-05-24 as an operational definition.** Realized as
`uc_eval (QPE_var m (n + anc) f) (Shor_initial_state m n anc)`, casted
from the unitary-acting dimension `2^(m + (n + anc))` to the
constructor-product dimension `2^m * 2^n * 2^anc` via `QState.cast`
(value-preserving on corresponding numerical indices).

`QPE_var` itself remains axiomatized (separate Phase-3 obligation), but
`Shor_final_state` is no longer a free symbol — it is now a concrete
function of `(m, n, anc, f)`. -/
noncomputable def Shor_final_state (m n anc : Nat)
    (f : Nat → BaseUCom (n + anc)) : QState (2^m * 2^n * 2^anc) :=
  QState.cast (by rw [pow_add, pow_add, mul_assoc])
    (uc_eval (QPE_var_lsb m (n + anc) f) (Shor_initial_state m n anc))

/-- **`probability_of_success a r N m n anc f`** (`Shor.v:64`).  Sum
over all `2^m` measurement outcomes `x` of
`r_found(x) · P(measure x on first register)`.  This is the headline
quantity SQIR bounds. -/
noncomputable def probability_of_success
    (a r N m n anc : Nat) (f : Nat → BaseUCom (n + anc)) : ℝ :=
  ∑ x ∈ Finset.range (2^m),
    r_found x m r a N *
      prob_partial_meas (basis_vector (2^m) x) (Shor_final_state m n anc f)

/-! ## §4. The headline theorems (statements only; proofs = `sorry`). -/

/-- **The Shor success-probability constant** `κ = 4·exp(−2) / π²
≈ 0.0548` (Coq: `Shor.v:1073`). -/
noncomputable def κ : ℝ := 4 * Real.exp (-2) / Real.pi^2

/-- κ is strictly positive: `exp(−2) > 0`, `π² > 0`. -/
theorem κ_pos : κ > 0 := by
  unfold κ
  have h1 : Real.exp (-2) > 0 := Real.exp_pos (-2)
  have h2 : Real.pi^2 > 0 := pow_pos Real.pi_pos 2
  positivity

/-! ### Tier-2 quantitative axioms used by `Shor_correct_var`'s proof.

Each axiom corresponds to a substantial lemma in SQIR (Coq) that
would itself be a multi-hundred-line Lean port.  We use them as
black-box facts here; Tier-3 work will replace them with Lean
proofs.  -/

/-- **`Order_r_lt_N`** (Coq: `NumTheory.v`).  The multiplicative order
of `a` mod `N` is strictly less than `N` (when `N > 0` and `a` has an
order).  Standard number-theoretic fact.

**Closed 2026-05-23 via Euler's theorem** (Phase 1 axiom #1):
- N = 1 case: `a^r % 1 = 0 ≠ 1` contradicts the order definition.
- N ≥ 2 case: derive `Nat.Coprime a N` from `a^r % N = 1` via
  `Nat.dvd_mod_iff`. Apply `Nat.pow_totient_mod_eq_one` (Euler) to
  get `a^(totient N) % N = 1`. By the minimality clause of `Order`,
  this forces `totient N ≥ r`. Combined with `Nat.totient_lt`
  (`totient N < N` for N ≥ 2), conclude `r ≤ totient N < N`. -/
theorem Order_r_lt_N (a r N : Nat) (h_N : 0 < N) (h_ord : Order a r N) : r < N := by
  obtain ⟨h_r_pos, h_arN, h_min⟩ := h_ord
  rcases Nat.lt_or_eq_of_le h_N with h_N_ge_2 | h_N_eq_1
  · -- N ≥ 2 case: Euler + minimality
    have h_coprime : Nat.Coprime a N := by
      rw [Nat.Coprime]
      have h1 : Nat.gcd a N ∣ a := Nat.gcd_dvd_left a N
      have h2 : Nat.gcd a N ∣ N := Nat.gcd_dvd_right a N
      have h3 : Nat.gcd a N ∣ a^r := dvd_pow h1 (Nat.pos_iff_ne_zero.mp h_r_pos)
      have h4 : Nat.gcd a N ∣ a^r % N := (Nat.dvd_mod_iff h2).mpr h3
      rw [h_arN] at h4
      exact Nat.eq_one_of_dvd_one h4
    have h_euler : a^(Nat.totient N) % N = 1 :=
      Nat.pow_totient_mod_eq_one h_N_ge_2 h_coprime
    have h_tot_pos : 0 < Nat.totient N := Nat.totient_pos.mpr h_N
    have h_tot_lt : Nat.totient N < N := Nat.totient_lt N h_N_ge_2
    by_contra h_r_ge_N
    exact h_min (Nat.totient N) h_tot_pos
      (lt_of_lt_of_le h_tot_lt (not_lt.mp h_r_ge_N)) h_euler
  · -- N = 1 case: a^r % 1 = 0 ≠ 1, contradiction with h_arN
    subst h_N_eq_1
    simp [Nat.mod_one] at h_arN

/-- **`s_closest m k r`** (Coq: `Shor.v:594`).  The closest integer
to `k · 2^m / r`, used as the measurement outcome that is "as close
as possible" to the rational `k/r`. -/
noncomputable def s_closest (m k r : Nat) : Nat :=
  (k * 2^m + r / 2) / r

/-- **`s_closest_ub`** (Coq: `Shor.v:634`).  When the QPE precision
satisfies `BasicSetting`, the closest-outcome `s_closest m k r` lies
in `[0, 2^m)`.

**Closed 2026-05-23 via Nat arithmetic** (Phase 1 axiom #2):
Unpack `BasicSetting` to get `0 < r`, `r < N` (via `Order_r_lt_N`),
`N² < 2^m`. Chain `r < N ≤ N² < 2^m`. Then `s_closest m k r =
(k·2^m + r/2)/r < 2^m` iff `k·2^m + r/2 < 2^m · r` (via
`Nat.div_lt_iff_lt_mul`); the latter follows from `(k+1)·2^m ≤ r·2^m`
and `r/2 < 2^m`. -/
theorem s_closest_ub (a r N m n k : Nat) (h_basic : BasicSetting a r N m n)
    (h_k_lt : k < r) : s_closest m k r < 2^m := by
  obtain ⟨⟨h_a_pos, h_a_lt_N⟩, h_ord, ⟨h_Nsq_lt, _⟩, _⟩ := h_basic
  have h_r_pos : 0 < r := h_ord.1
  have h_N_pos : 0 < N := by omega
  have h_r_lt_N : r < N := Order_r_lt_N a r N h_N_pos h_ord
  have h_N_le_Nsq : N ≤ N^2 := by nlinarith
  have h_r_lt_2m : r < 2^m := by omega
  unfold s_closest
  rw [Nat.div_lt_iff_lt_mul h_r_pos]
  have h_k_succ : k + 1 ≤ r := h_k_lt
  have h_k_mul : (k + 1) * 2^m ≤ r * 2^m := Nat.mul_le_mul_right _ h_k_succ
  have h_r_half : r / 2 < 2^m := by omega
  have h_expand : (k + 1) * 2^m = k * 2^m + 2^m := by ring
  have h_comm : r * 2^m = 2^m * r := Nat.mul_comm _ _
  omega

/-- **`s_closest_injective`** (Coq: `Shor.v:670`).  Distinct `k`s in
`[0, r)` produce distinct `s_closest m k r` outcomes.

**Closed 2026-05-23 via Nat arithmetic** (Phase 1 axiom #3):
After unpacking `BasicSetting` to get `r < N ≤ N² < 2^m`, decompose
both `i*2^m + r/2` and `j*2^m + r/2` via `Nat.div_add_mod`. The
hypothesis `s_closest m i r = s_closest m j r` says both share the
same quotient `r * Q`; substituting yields
`i*2^m + j_mod = j*2^m + i_mod` (the symmetric rearrangement). With
`i_mod, j_mod < r`, this forces `|i*2^m - j*2^m| < r`. But for any
`i ≠ j`, `|i*2^m - j*2^m| ≥ 2^m > r`. Contradiction (case-split
on `Nat.lt_trichotomy`); closed by `omega` after providing
`(j-i)·2^m ≥ 2^m` via `nlinarith`. -/
theorem s_closest_injective (a r N m n : Nat)
    (h_basic : BasicSetting a r N m n) :
    ∀ i j : Nat, i < r → j < r → s_closest m i r = s_closest m j r → i = j := by
  intros i j h_i h_j h_eq
  obtain ⟨⟨h_a_pos, h_a_lt_N⟩, h_ord, ⟨h_Nsq_lt, _⟩, _⟩ := h_basic
  have h_r_pos : 0 < r := h_ord.1
  have h_N_pos : 0 < N := by omega
  have h_r_lt_N : r < N := Order_r_lt_N a r N h_N_pos h_ord
  have h_N_le_Nsq : N ≤ N^2 := by nlinarith
  have h_r_lt_2m : r < 2^m := by omega
  unfold s_closest at h_eq
  have h_i_div : r * ((i * 2^m + r/2) / r) + (i * 2^m + r/2) % r = i * 2^m + r/2 :=
    Nat.div_add_mod (i * 2^m + r/2) r
  have h_j_div : r * ((j * 2^m + r/2) / r) + (j * 2^m + r/2) % r = j * 2^m + r/2 :=
    Nat.div_add_mod (j * 2^m + r/2) r
  have h_i_mod_lt : (i * 2^m + r/2) % r < r := Nat.mod_lt _ h_r_pos
  have h_j_mod_lt : (j * 2^m + r/2) % r < r := Nat.mod_lt _ h_r_pos
  -- Identify the shared quotient via h_eq
  rw [h_eq] at h_i_div
  rcases Nat.lt_trichotomy i j with h_lt | h_eq_ij | h_gt
  · exfalso
    have h_ij_step : i * 2^m + 2^m ≤ j * 2^m := by
      have h1 : i + 1 ≤ j := h_lt
      nlinarith
    have h_rearrange : i * 2^m + (j * 2^m + r/2) % r
                       = j * 2^m + (i * 2^m + r/2) % r := by omega
    omega
  · exact h_eq_ij
  · exfalso
    have h_ij_step : j * 2^m + 2^m ≤ i * 2^m := by
      have h1 : j + 1 ≤ i := h_gt
      nlinarith
    have h_rearrange : i * 2^m + (j * 2^m + r/2) % r
                       = j * 2^m + (i * 2^m + r/2) % r := by omega
    omega

end FormalRV.SQIRPort
