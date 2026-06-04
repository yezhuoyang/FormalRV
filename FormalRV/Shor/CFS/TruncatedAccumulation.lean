/-
  FormalRV.Shor.CFS.TruncatedAccumulation — the FUSION of the truncation count (layer 4) and the
  modular-deviation metric (layer 5): a single integer-model statement that the CFS truncated
  accumulator deviates from the exact value by `≤ A · 2^t`, i.e. `Δ_N ≤ |P|·ℓ·2^{-f}` (eq:modevbound).

  Per "semantic proof BEFORE resource proof".  Layer 4 (`TruncationBound`) counted the `|P|·ℓ`
  truncated additions in the real-valued model; layer 5 (`ModularDeviation`) gave the paper's integer
  `Δ_N` metric and its linear accumulation.  This file welds them: it models the paper's ACTUAL
  integer truncation (`x ↦ (x ≫ t) ≪ t`, dropping the low `t` bits, eq:deviated-sum) and proves, by
  induction over the operation chain, that the deviation between the exact running sum and the
  truncated accumulator is `≤ A·2^t`.

  Key new metric facts (proved here, axiom-clean):
    * `modDev_add_right` — translation invariance of `Δ_N` (via the `ZMod` characterisation
      `fwdDist_cast`).  This is what lets the per-step truncation error be isolated.
    * `modDev_le_sub`    — `Δ_N(a,b) ≤ a − b` for `b ≤ a` (deviation ≤ linear gap).
    * `modDev_truncAcc`  — **the fused bound**: `Δ_N(exactAcc A, apprAcc A) ≤ A · 2^t`.
    * `modDev_truncAcc_normalized` — the paper's normalised form `Δ_N/N ≤ |P|·ℓ·2^{-f}` (eq:modevbound),
      under `2^{t+f} ≤ N` (i.e. `t = len N − f`, eq for `t`), with `A = |P|·ℓ`.
-/
import FormalRV.Shor.CFS.ModularDeviation

namespace FormalRV.CFS

open scoped BigOperators

/-! ### New `Δ_N` metric facts: translation invariance and the linear-gap bound. -/

/-- `ZMod` characterisation of the forward distance: `↑(fwdDist N a b) = ↑a − ↑b` in `ZMod N`. -/
theorem fwdDist_cast (N a b : ℕ) [NeZero N] : (fwdDist N a b : ZMod N) = (a : ZMod N) - b := by
  have hb : b % N ≤ N := le_of_lt (Nat.mod_lt b (NeZero.pos N))
  unfold fwdDist
  rw [ZMod.natCast_mod]
  push_cast [Nat.cast_sub hb]
  simp [ZMod.natCast_mod]
  ring

/-- The forward distance is TRANSLATION INVARIANT: `fwdDist N (a+c) (b+c) = fwdDist N a b`. -/
theorem fwdDist_add_right (N a b c : ℕ) (hN : 0 < N) :
    fwdDist N (a + c) (b + c) = fwdDist N a b := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have h : (fwdDist N (a + c) (b + c) : ZMod N) = (fwdDist N a b : ZMod N) := by
    rw [fwdDist_cast, fwdDist_cast]; push_cast; ring
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have l1 := fwdDist_lt N (a + c) (b + c) hN; have l2 := fwdDist_lt N a b hN
  rw [Nat.ModEq, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at hmod
  exact hmod

/-- **Translation invariance of the modular deviation**: shifting both arguments by `c` is free. -/
theorem modDev_add_right (N a b c : ℕ) (hN : 0 < N) :
    modDev N (a + c) (b + c) = modDev N a b := by
  unfold modDev; rw [fwdDist_add_right N a b c hN, fwdDist_add_right N b a c hN]

/-- The deviation of `x` from `0` is at most `x`. -/
theorem modDev_zero_le (N x : ℕ) : modDev N x 0 ≤ x :=
  le_trans (min_le_left _ _)
    (le_trans (le_of_eq (by simp [fwdDist, Nat.add_mod_right])) (Nat.mod_le x N))

/-- **Deviation is bounded by the linear gap**: `Δ_N(a,b) ≤ a − b` when `b ≤ a`. -/
theorem modDev_le_sub (N a b : ℕ) (hN : 0 < N) (hba : b ≤ a) : modDev N a b ≤ a - b := by
  have h := modDev_add_right N (a - b) 0 b hN
  rw [Nat.sub_add_cancel hba, Nat.zero_add] at h
  rw [h]; exact modDev_zero_le N (a - b)

/-! ### Integer truncation and the truncated accumulator (paper eq:deviated-sum). -/

/-- Integer truncation: drop the low `t` bits (`(x ≫ t) ≪ t`). -/
def truncShift (x t : ℕ) : ℕ := 2 ^ t * (x / 2 ^ t)

theorem truncShift_le (x t : ℕ) : truncShift x t ≤ x := by
  unfold truncShift; have h := Nat.div_add_mod x (2 ^ t); omega

theorem sub_truncShift_lt (x t : ℕ) : x - truncShift x t < 2 ^ t := by
  unfold truncShift
  have h := Nat.div_add_mod x (2 ^ t)
  have hlt := Nat.mod_lt x (show 0 < 2 ^ t by positivity)
  omega

/-- Exact running sum (no truncation, no mod): `exactAcc s A = ∑_{k<A} s k`. -/
def exactAcc (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => exactAcc s k + s k

/-- Approximate accumulator: truncate to `t` bits after each addition (the paper's `≫t … ≪t`). -/
def apprAcc (s : ℕ → ℕ) (t : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => truncShift (apprAcc s t k + s k) t

/-- **THE FUSED DEVIATION BOUND** (paper eq:deviated-sum).  After `A` truncated additions, the
    approximate accumulator deviates from the exact sum by at most `A · 2^t` in the `Δ_N` metric.
    Proof: induction on `A`; each step contributes `≤ 2^t` (truncation drops `< 2^t`, and deviation
    `≤` that linear gap), and the carried-over deviation is preserved by translation invariance. -/
theorem modDev_truncAcc (N : ℕ) (hN : 0 < N) (s : ℕ → ℕ) (t : ℕ) :
    ∀ A, modDev N (exactAcc s A) (apprAcc s t A) ≤ A * 2 ^ t
  | 0 => by simp [exactAcc, apprAcc, modDev_self N 0 hN]
  | A + 1 => by
      have ih := modDev_truncAcc N hN s t A
      have hle := truncShift_le (apprAcc s t A + s A) t
      have step : modDev N (apprAcc s t A + s A) (truncShift (apprAcc s t A + s A) t) ≤ 2 ^ t :=
        le_trans (modDev_le_sub N _ _ hN hle) (le_of_lt (sub_truncShift_lt _ _))
      calc modDev N (exactAcc s (A + 1)) (apprAcc s t (A + 1))
          = modDev N (exactAcc s A + s A) (truncShift (apprAcc s t A + s A) t) := by
              rw [exactAcc, apprAcc]
        _ ≤ modDev N (exactAcc s A + s A) (apprAcc s t A + s A)
              + modDev N (apprAcc s t A + s A) (truncShift (apprAcc s t A + s A) t) :=
              modDev_triangle N _ _ _ hN
        _ = modDev N (exactAcc s A) (apprAcc s t A)
              + modDev N (apprAcc s t A + s A) (truncShift (apprAcc s t A + s A) t) := by
              rw [modDev_add_right N (exactAcc s A) (apprAcc s t A) (s A) hN]
        _ ≤ A * 2 ^ t + 2 ^ t := add_le_add ih step
        _ = (A + 1) * 2 ^ t := by ring

/-- **The paper's normalised modular-deviation bound** (eq:modevbound).  With `A = |P|·ℓ` truncated
    additions and `2^{t+f} ≤ N` (the choice `t = len N − f`), the normalised deviation
    `Δ_N = modDev / N` is at most `|P|·ℓ·2^{-f}`. -/
theorem modDev_truncAcc_normalized (N : ℕ) (hN : 0 < N) (s : ℕ → ℕ) (t f P ell : ℕ)
    (htf : 2 ^ (t + f) ≤ N) :
    (modDev N (exactAcc s (P * ell)) (apprAcc s t (P * ell)) : ℚ) / N
      ≤ (P * ell : ℕ) / 2 ^ f := by
  have hb := modDev_truncAcc N hN s t (P * ell)
  have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
  have hfpos : (0 : ℚ) < (2 : ℚ) ^ f := by positivity
  have h1 : (modDev N (exactAcc s (P * ell)) (apprAcc s t (P * ell)) : ℚ) ≤ (P * ell : ℕ) * 2 ^ t := by
    exact_mod_cast hb
  have h3 : ((P * ell : ℕ) : ℚ) * 2 ^ (t + f) ≤ (P * ell : ℕ) * N := by
    have : (2 : ℚ) ^ (t + f) ≤ N := by exact_mod_cast htf
    gcongr
  rw [div_le_div_iff₀ hNpos hfpos]
  calc (modDev N (exactAcc s (P * ell)) (apprAcc s t (P * ell)) : ℚ) * 2 ^ f
      ≤ ((P * ell : ℕ) * 2 ^ t) * 2 ^ f := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (P * ell : ℕ) * 2 ^ (t + f) := by rw [pow_add]; ring
    _ ≤ (P * ell : ℕ) * N := h3

/-! ## The fusion theorems pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean modDev_add_right
#verify_clean modDev_le_sub
#verify_clean modDev_truncAcc
#verify_clean modDev_truncAcc_normalized

end FormalRV.CFS
