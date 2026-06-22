/-
  FormalRV.Shor.CFS.ModularDeviation — the paper's MODULAR-DEVIATION metric `Δ_N` and the proof
  that it accumulates linearly with the number of operations (Gidney 2025, main.tex line 296–311).

  Per "semantic proof BEFORE resource proof".  CFS replaces exact arithmetic by truncated arithmetic,
  and tracks the resulting error in a special metric — the "modular deviation"

      Δ_N(a - b) = min((a - b) mod N, (b - a) mod N) / N

  the (normalised) minimum number of ±1 increments needed to turn `a` into `b` modulo `N`.  The
  whole approximation argument rests on TWO facts about this metric: it is `0` exactly when the
  values agree mod `N`, and it satisfies the triangle inequality, so the deviation of a chain of
  `A` operations is at most the sum of the per-operation deviations (line 311: "accumulate linearly
  with the number of operations, meaning a series of `A` truncated additions has a modular deviation
  of at most `O(A · 2^{-f})`").

  We work with the integer NUMERATOR `modDev N a b = min(fwd a b, fwd b a)` (the count of ±1 steps;
  the paper's `Δ_N` is this divided by `N`).  Proved here, all axiom-clean:

    * `modDev_self`         — `Δ_N(a,a) = 0`.
    * `modDev_comm`         — symmetry.
    * `modDev_eq_zero_iff`  — `Δ_N(a,b) = 0 ↔ a ≡ b (mod N)` (deviation detects exact agreement).
    * `modDev_triangle`     — the triangle inequality on the cycle `ℤ/N`.
    * `modDev_chain`        — **linear accumulation**: `Δ_N(s₀, sₙ) ≤ ∑ᵢ Δ_N(sᵢ, sᵢ₊₁)`, the formal
                              version of "deviation accumulates linearly with the number of
                              operations".  This is what makes the `A · 2^{-f}` bound (eq:deviated-sum)
                              follow from a per-operation `O(2^{-f})` bound.
-/
import Mathlib
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS

open scoped BigOperators

/-- Forward cyclic distance: the number of `+1` steps from `b` to `a` modulo `N` (`≡ a − b mod N`). -/
def fwdDist (N a b : ℕ) : ℕ := (a % N + (N - b % N)) % N

/-- **Modular-deviation count** (the numerator of the paper's `Δ_N`): the minimum number of `±1`
    increments/decrements needed to turn `a` into `b` modulo `N`. -/
def modDev (N a b : ℕ) : ℕ := min (fwdDist N a b) (fwdDist N b a)

theorem fwdDist_lt (N a b : ℕ) (hN : 0 < N) : fwdDist N a b < N := Nat.mod_lt _ hN

theorem fwdDist_self (N a : ℕ) (hN : 0 < N) : fwdDist N a a = 0 := by
  have ha : a % N < N := Nat.mod_lt _ hN
  unfold fwdDist; rw [show a % N + (N - a % N) = N by omega, Nat.mod_self]

/-- Forward distances compose additively on the cycle: `fwd a b + fwd b c ≡ fwd a c (mod N)`. -/
theorem fwdDist_add (N a b c : ℕ) (hN : 0 < N) :
    (fwdDist N a b + fwdDist N b c) % N = fwdDist N a c := by
  have hb : b % N < N := Nat.mod_lt _ hN
  unfold fwdDist
  conv_lhs => rw [Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [show a % N + (N - b % N) + (b % N + (N - c % N)) = (a % N + (N - c % N)) + N by omega,
     Nat.add_mod_right]

/-- For `x < 2N`, the reduction `x % N` is either `x` (no wrap) or `x − N` (one wrap). -/
theorem mod_lt_two_mul (x N : ℕ) (hx : x < 2 * N) : x % N = x ∨ x % N + N = x := by
  rcases lt_or_ge x N with h | h
  · left; exact Nat.mod_eq_of_lt h
  · right; rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega

/-- The two forward distances between `a` and `b` are antipodal: they sum to `0` (if equal) or `N`. -/
theorem fwdDist_antipodal (N a b : ℕ) (hN : 0 < N) :
    fwdDist N a b + fwdDist N b a = 0 ∨ fwdDist N a b + fwdDist N b a = N := by
  have h := fwdDist_add N a b a hN
  rw [fwdDist_self N a hN] at h
  have l1 := fwdDist_lt N a b hN; have l2 := fwdDist_lt N b a hN
  rcases mod_lt_two_mul (fwdDist N a b + fwdDist N b a) N (by omega) with e | e <;> omega

theorem fwdDist_eq_zero_iff (N a b : ℕ) (hN : 0 < N) : fwdDist N a b = 0 ↔ a % N = b % N := by
  have ha : a % N < N := Nat.mod_lt _ hN
  have hb : b % N < N := Nat.mod_lt _ hN
  have hm : (a % N + (N - b % N)) % N < N := Nat.mod_lt _ hN
  have e := mod_lt_two_mul (a % N + (N - b % N)) N (by omega)
  unfold fwdDist
  constructor
  · intro h; rcases e with e | e <;> omega
  · intro h; rcases e with e | e <;> omega

/-- `Δ_N(a, a) = 0`. -/
theorem modDev_self (N a : ℕ) (hN : 0 < N) : modDev N a a = 0 := by
  simp [modDev, fwdDist_self N a hN]

/-- The modular deviation is symmetric. -/
theorem modDev_comm (N a b : ℕ) : modDev N a b = modDev N b a := Nat.min_comm _ _

/-- **The deviation is zero exactly when the values agree mod `N`.** -/
theorem modDev_eq_zero_iff (N a b : ℕ) (hN : 0 < N) : modDev N a b = 0 ↔ a ≡ b [MOD N] := by
  unfold modDev
  rw [Nat.min_eq_zero_iff, fwdDist_eq_zero_iff N a b hN, fwdDist_eq_zero_iff N b a hN]
  constructor
  · rintro (h | h) <;> [exact h; exact h.symm]
  · intro h; exact Or.inl h

/-- **Triangle inequality** on the cycle `ℤ/N`: deviation is a pseudometric. -/
theorem modDev_triangle (N a b c : ℕ) (hN : 0 < N) :
    modDev N a c ≤ modDev N a b + modDev N b c := by
  have hac := fwdDist_add N a b c hN
  have hca := fwdDist_add N c b a hN
  have pab := fwdDist_antipodal N a b hN
  have pbc := fwdDist_antipodal N b c hN
  have pac := fwdDist_antipodal N a c hN
  have l1 := fwdDist_lt N a b hN; have l2 := fwdDist_lt N b a hN
  have l3 := fwdDist_lt N b c hN; have l4 := fwdDist_lt N c b hN
  have l5 := fwdDist_lt N a c hN; have l6 := fwdDist_lt N c a hN
  have e1 := mod_lt_two_mul (fwdDist N a b + fwdDist N b c) N (by omega)
  have e2 := mod_lt_two_mul (fwdDist N c b + fwdDist N b a) N (by omega)
  rw [hac] at e1; rw [hca] at e2
  unfold modDev; omega

/-- **Linear accumulation of deviation** (paper line 311).  For a chain of values `s 0, …, s n`,
    the deviation between the endpoints is at most the sum of the per-step deviations.  Hence a
    series of `A` truncated operations, each of deviation `≤ δ`, has total deviation `≤ A·δ` — the
    `A·2^{-f}` bound of eq:deviated-sum follows from a per-operation `O(2^{-f})` bound. -/
theorem modDev_chain (N : ℕ) (hN : 0 < N) (s : ℕ → ℕ) :
    ∀ n, modDev N (s 0) (s n) ≤ ∑ i ∈ Finset.range n, modDev N (s i) (s (i + 1))
  | 0 => by simp [modDev_self N (s 0) hN]
  | n + 1 => by
      have ih := modDev_chain N hN s n
      calc modDev N (s 0) (s (n + 1))
          ≤ modDev N (s 0) (s n) + modDev N (s n) (s (n + 1)) := modDev_triangle N _ _ _ hN
        _ ≤ (∑ i ∈ Finset.range n, modDev N (s i) (s (i + 1))) + modDev N (s n) (s (n + 1)) := by
              gcongr
        _ = ∑ i ∈ Finset.range (n + 1), modDev N (s i) (s (i + 1)) :=
              (Finset.sum_range_succ _ n).symm

/-! ## The deviation-metric theorems pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean modDev_eq_zero_iff
#verify_clean modDev_triangle
#verify_clean modDev_chain

end FormalRV.CFS
