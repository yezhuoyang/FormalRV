import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.ShorFromVerifiedModMulFamily
import FormalRV.Shor.VerifiedShor.RelaxedSetting

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-- `BasicSetting → BasicSettingRelaxed` (drops the upper-bound conjunct). -/
theorem BasicSettingRelaxed_of_BasicSetting
    {a r N m n : Nat} (h : FormalRV.SQIRPort.BasicSetting a r N m n) :
    BasicSettingRelaxed a r N m n := by
  obtain ⟨ha, hord, hm, hn, _⟩ := h
  exact ⟨ha, hord, hm, hn⟩

/-- **Canonical sizing**: `bits = Nat.log2 N + 1` gives `2*N ≤ 2^bits`
when `N` is a power of 2 minus 1 or smaller; we use `Nat.log2 (2*N) + 1`
as a generic choice. -/
theorem VerifiedCircuitSizing_canonical_pow2_succ
    (N : Nat) (hN : 0 < N) :
    VerifiedCircuitSizing N (Nat.log2 (2 * N) + 1) := by
  set bits := Nat.log2 (2 * N) + 1 with h_bits_def
  have h_2N_pos : 0 < 2 * N := by omega
  have h_log2_le : 2 ^ (Nat.log2 (2 * N)) ≤ 2 * N := Nat.log2_self_le (by omega)
  have h_pow_bits_ge : 2 ^ bits = 2 * 2 ^ (Nat.log2 (2 * N)) := by
    rw [h_bits_def, pow_succ]; ring
  refine ⟨?_, ?_, ?_⟩
  · omega
  · have : N ≤ 2 * N := by omega
    have h_2N_le : 2 * N ≤ 2 ^ bits := by
      rw [h_pow_bits_ge]
      have h_strict : 2 * N < 2 ^ (Nat.log2 (2 * N) + 1) := Nat.lt_log2_self
      omega
    omega
  · rw [h_pow_bits_ge]
    have h_strict : 2 * N < 2 ^ (Nat.log2 (2 * N) + 1) := Nat.lt_log2_self
    omega

/-! ## Tick 81 — Relaxed sub-lemmas (copies of original proofs with
relaxed hypothesis). -/

/-- **Relaxed s_closest_ub.** -/
theorem s_closest_ub_relaxed (a r N m n k : Nat)
    (h_basic : BasicSettingRelaxed a r N m n) (h_k_lt : k < r) :
    FormalRV.SQIRPort.s_closest m k r < 2^m := by
  obtain ⟨⟨h_a_pos, h_a_lt_N⟩, h_ord, ⟨h_Nsq_lt, _⟩, _⟩ := h_basic
  have h_r_pos : 0 < r := h_ord.1
  have h_N_pos : 0 < N := by omega
  have h_r_lt_N : r < N := FormalRV.SQIRPort.Order_r_lt_N a r N h_N_pos h_ord
  have h_N_le_Nsq : N ≤ N^2 := by nlinarith
  have h_r_lt_2m : r < 2^m := by omega
  unfold FormalRV.SQIRPort.s_closest
  rw [Nat.div_lt_iff_lt_mul h_r_pos]
  have h_k_succ : k + 1 ≤ r := h_k_lt
  have h_k_mul : (k + 1) * 2^m ≤ r * 2^m := Nat.mul_le_mul_right _ h_k_succ
  have h_r_half : r / 2 < 2^m := by omega
  have h_expand : (k + 1) * 2^m = k * 2^m + 2^m := by ring
  have h_comm : r * 2^m = 2^m * r := Nat.mul_comm _ _
  omega

/-- **Relaxed s_closest_injective** — same proof as the original, just
adjusted for the relaxed hypothesis. -/
theorem s_closest_injective_relaxed
    (a r N m n : Nat) (h_basic : BasicSettingRelaxed a r N m n) :
    ∀ i j : Nat, i < r → j < r →
      FormalRV.SQIRPort.s_closest m i r = FormalRV.SQIRPort.s_closest m j r → i = j := by
  intros i j h_i h_j h_eq
  obtain ⟨⟨h_a_pos, h_a_lt_N⟩, h_ord, ⟨h_Nsq_lt, _⟩, _⟩ := h_basic
  have h_r_pos : 0 < r := h_ord.1
  have h_N_pos : 0 < N := by omega
  have h_r_lt_N : r < N := FormalRV.SQIRPort.Order_r_lt_N a r N h_N_pos h_ord
  have h_N_le_Nsq : N ≤ N^2 := by nlinarith
  have h_r_lt_2m : r < 2^m := by omega
  unfold FormalRV.SQIRPort.s_closest at h_eq
  have h_i_div : r * ((i * 2^m + r/2) / r) + (i * 2^m + r/2) % r = i * 2^m + r/2 :=
    Nat.div_add_mod (i * 2^m + r/2) r
  have h_j_div : r * ((j * 2^m + r/2) / r) + (j * 2^m + r/2) % r = j * 2^m + r/2 :=
    Nat.div_add_mod (j * 2^m + r/2) r
  have h_i_mod_lt : (i * 2^m + r/2) % r < r := Nat.mod_lt _ h_r_pos
  have h_j_mod_lt : (j * 2^m + r/2) % r < r := Nat.mod_lt _ h_r_pos
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

/-- **Relaxed r_found_1**: Since the existing `r_found_1` proof chain
discards the n-bound throughout, it lifts to the relaxed setting via a
constructed-BasicSetting argument with a placeholder upper bound.

Pragmatic implementation: the existing `r_found_1` works at `BasicSetting`,
which requires `2^n ≤ 2*N`.  We don't have this, but the proof
doesn't use it.  Rather than re-proving the entire chain, we use the
relaxed-from-BasicSetting bridge in reverse: state the relaxed theorem
with an extra `(h_fake : 2^n ≤ 2*N)` parameter that we discard at call
sites by NOT using this lemma when the bound is unavailable.

For the SQIR `Shor_correct_var` chain, the bound IS available (since
BasicSetting holds), so the relaxed lemma can fall through to the
existing one.  For our verified family with `bits = n + 1`, the bound
is NOT available — but we sidestep this by USING THE EXISTING
`Shor_correct_var` AT `n = bits` where BasicSetting also holds, which
is the route we've taken in Tick 80. -/
theorem r_found_1_relaxed_with_bound
    (a r N m n k : Nat) (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_2n_bound : 2 ^ n ≤ 2 * N) (h_k_lt : k < r) (h_coprime : Nat.gcd k r = 1) :
    FormalRV.SQIRPort.r_found (FormalRV.SQIRPort.s_closest m k r) m r a N = 1 := by
  obtain ⟨ha, hord, hm, hn⟩ := h_basic_r
  exact FormalRV.SQIRPort.r_found_1 a r N m n k
    ⟨ha, hord, hm, hn, h_2n_bound⟩ h_k_lt h_coprime

/-! ## Tick 81 — Relaxed Shor_correct_var_relaxed_with_bound.

The relaxed variant still threads the `2^n ≤ 2*N` upper bound through
because `r_found_1` cannot yet be fully relaxed without re-proving the
continued-fraction chain.  However, the SIGNATURE makes the upper-bound
visible as a SEPARATE hypothesis, which clarifies the obstruction. -/

/-- **Relaxed Shor_correct_var (with bound)**: takes the upper bound
explicitly so that the proof obligations are visible. -/
theorem Shor_correct_var_relaxed_with_bound
    (a r N m n anc : Nat) (u : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_2n_bound : 2 ^ n ≤ 2 * N)
    (h_modmul : FormalRV.SQIRPort.ModMulImpl a N n anc u)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (u i)) :
    FormalRV.SQIRPort.probability_of_success a r N m n anc u
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  obtain ⟨ha, hord, hm, hn⟩ := h_basic_r
  exact FormalRV.SQIRPort.Shor_correct_var a r N m n anc u
    ⟨ha, hord, hm, hn, h_2n_bound⟩ h_modmul h_wt

/-! ## Tick 81 — Final verified Shor theorem with relaxed setup.

The final theorem cleanly SEPARATES:
- `BasicSettingRelaxed a r N m bits`: the Shor mathematical setup at
  data-register size `bits`.
- `VerifiedCircuitSizing N bits`: the verified-circuit sizing
  requirements.
- A residual `2 ^ bits ≤ 2 * N` hypothesis surfaced from the
  un-relaxed-yet `r_found_1` chain.

The residual hypothesis is the EXACT obstruction documented in the
Tick 80 caveat — it forces `2^bits = 2*N` (knife-edge case) when
combined with `VerifiedCircuitSizing`.  Future ticks would relax
`r_found_1` (via continued-fraction proof restructuring) to remove
this last constraint. -/
theorem Shor_correct_with_sqir_verified_modmult_relaxed
    (a r N m bits ainv : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m bits)
    (h_bits : VerifiedCircuitSizing N bits)
    (h_2n_bound : 2 ^ bits ≤ 2 * N)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
      (sqir_modmult_rev_anc bits)
      (f_modmult_circuit_verified_bits a ainv N bits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have hbits : 1 ≤ bits := h_bits.1
  have hN : N ≤ 2^bits := h_bits.2.1
  have hN2 : 2 * N ≤ 2^bits := h_bits.2.2
  have h_a_pos : 0 < a := h_basic_r.1.1
  have h_a_lt : a < N := h_basic_r.1.2
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have h_N_ge_2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h_lt | h_ge
    · exfalso
      have hN_eq : N = 1 := by omega
      rw [hN_eq, Nat.mod_one] at h_inv
      exact absurd h_inv (by decide)
    · exact h_ge
  exact Shor_correct_var_relaxed_with_bound a r N m bits
    (sqir_modmult_rev_anc bits) (f_modmult_circuit_verified_bits a ainv N bits)
    h_basic_r h_2n_bound
    (f_modmult_circuit_verified_bits_MMI a ainv N bits hbits h_N_ge_2 hN hN2 h_inv)
    (fun i _ => f_modmult_circuit_verified_bits_uc_well_typed a ainv N bits
                  hbits hN_pos hN hN2 i)

/-! ## Tick 82 — Canonical-n bridge + relaxed continued-fraction chain.

### Key insight
Lemma conclusions that do NOT mention `n` (e.g., `r_found_1`,
`s_closest_ub`) can be invoked at ANY `n` where `BasicSetting` holds.
From `BasicSettingRelaxed a r N m bits`, we construct
`BasicSetting a r N m (Nat.log2 (2*N))` (the canonical n where the
tight upper bound holds automatically), then invoke the original
theorems. -/

/-- **Canonical-n bridge**: From `BasicSettingRelaxed` at any `bits`, we
can construct `BasicSetting` at `n_canonical = Nat.log2 (2*N)`. -/
theorem BasicSetting_at_canonical_n_of_BasicSettingRelaxed
    (a r N m bits : Nat) (h_basic_r : BasicSettingRelaxed a r N m bits) :
    FormalRV.SQIRPort.BasicSetting a r N m (Nat.log2 (2 * N)) := by
  obtain ⟨⟨h_a_pos, h_a_lt⟩, h_ord, hm, _⟩ := h_basic_r
  have hN_pos : 0 < N := by omega
  refine ⟨⟨h_a_pos, h_a_lt⟩, h_ord, hm, ?_, ?_⟩
  · -- N < 2^log2(2N): from 2*N < 2^(log2(2N)+1) = 2 * 2^log2(2N).
    have h_lt : 2 * N < 2 ^ (Nat.log2 (2 * N) + 1) := Nat.lt_log2_self
    have h_eq : 2 ^ (Nat.log2 (2 * N) + 1) = 2 * 2 ^ Nat.log2 (2 * N) := by
      rw [pow_succ]; ring
    omega
  · exact Nat.log2_self_le (by omega : 2 * N ≠ 0)

/-- **Relaxed `r_found_1`**: same conclusion as the original, but
hypothesis weakened to `BasicSettingRelaxed`.  Uses the canonical-n
bridge since the conclusion `r_found (...) = 1` does not mention `n`. -/
theorem r_found_1_relaxed (a r N m bits k : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m bits)
    (h_k_lt : k < r) (h_coprime : Nat.gcd k r = 1) :
    FormalRV.SQIRPort.r_found (FormalRV.SQIRPort.s_closest m k r) m r a N = 1 :=
  FormalRV.SQIRPort.r_found_1 a r N m (Nat.log2 (2 * N)) k
    (BasicSetting_at_canonical_n_of_BasicSettingRelaxed a r N m bits h_basic_r)
    h_k_lt h_coprime

/-! ### Blocker for full relaxation: QPE_MMI_correct's deep machinery.

The review shows that `qpe_semantics_measurement_eq_from_lsb` (PostQFT.lean:3330),
`QPE_MMI_correct_modulo_qpe_semantics` (Shor.lean:4980), and
`QPE_MMI_correct_assuming_orbit_factorization` all use only
`h_n_bounds.1.le` (= `N ≤ 2^n`) from BasicSetting — never the upper
bound `2^n ≤ 2*N`.  However, relaxing them requires re-stating each
with `BasicSettingRelaxed` and updating callers; this is a 4-6 lemma
copy-modify chain that requires modifying Shor.lean/PostQFT.lean.

The Tick 82 review confirms the mathematical relaxability of the
entire chain.  Implementing it requires either:
- modifying Shor.lean / PostQFT.lean to weaken the BasicSetting
  hypothesis everywhere (invasive);
- or duplicating ~200-300 lines of proof scaffolding in this file.

For Tick 82, we land the canonical-n bridge + `r_found_1_relaxed`
(which removes one of the residual obstructions) but the QPE_MMI
chain remains a future-tick blocker.  Status B per task spec. -/

end FormalRV.BQAlgo
