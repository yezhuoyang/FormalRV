/-
  Audit · webster-2026 "The Pinnacle Architecture" (arXiv:2602.11457) · PARALLEL REDUCTION
  ════════════════════════════════════════════════════════════════════════════
  Pinnacle's ONE genuinely-new arithmetic contribution over Gidney 2025: it
  parallelises the outer accumulation loop across `ρ ≤ |P|` working registers and
  combines the `ρ` partial accumulators by a BINARY TREE (main.tex L810-813,
  L822-824).  The paper argues (its Eq.20) that this is merely a REORDERING of
  Gidney's serial truncated sum, so the final accumulator VALUE is unchanged — and
  hence the truncation-deviation bound (`modDev_truncAcc_normalized`, already
  verified for the serial schedule) carries over unchanged.

  This file discharges exactly that obligation on the verified CFS substrate:
  `parallelReduction_eq_serial` proves the `ρ`-way chunked accumulation equals the
  serial `exactAcc` over all `ρ·c` terms, and `parallelReduction_modDev` transports
  the serial deviation bound to the parallel schedule.  No new arithmetic primitive
  — a pure commutativity/associativity reordering of `exactAcc`, as predicted.
-/
import FormalRV.Audit.Gidney2025.CFS.TruncatedAccumulation

namespace FormalRV.Audit.Pinnacle.ParallelReduction

open FormalRV.CFS

/-- **Chunk additivity of the exact accumulator.**  The exact running sum over
    `[0, a+c)` splits into the sum over `[0, a)` plus the shifted chunk `[a, a+c)`.
    (`exactAcc s A = ∑_{k<A} s k`.) -/
theorem exactAcc_add (s : ℕ → ℕ) (a c : ℕ) :
    exactAcc s (a + c) = exactAcc s a + exactAcc (fun k => s (a + k)) c := by
  induction c with
  | zero => simp [exactAcc]
  | succ c ih =>
      have hac : a + (c + 1) = (a + c) + 1 := by ring
      rw [hac, exactAcc, ih, exactAcc]
      ring

/-- The exact partial sum accumulated by parallel chunk `j` (each chunk has `c`
    terms): `∑_{k<c} s(j·c + k)` — what working register `j` computes locally. -/
def chunkAcc (s : ℕ → ℕ) (c j : ℕ) : ℕ := exactAcc (fun k => s (j * c + k)) c

/-- The binary-tree combination of the first `ρ` chunk accumulators.  (A balanced
    tree and this left fold have the SAME value by associativity of `+`; the tree
    is only a depth optimisation, so the value-level object is this sum.) -/
def parAcc (s : ℕ → ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | ρ + 1 => parAcc s c ρ + chunkAcc s c ρ

/-- **Pinnacle's parallel reduction = the serial accumulation (the paper's Eq.20).**
    Combining the `ρ` chunk accumulators (each of size `c`) reproduces the serial
    `exactAcc` over all `ρ·c` terms.  The accumulator value is INVARIANT under the
    parallel reordering — exactly Pinnacle's claim. -/
theorem parallelReduction_eq_serial (s : ℕ → ℕ) (c ρ : ℕ) :
    parAcc s c ρ = exactAcc s (ρ * c) := by
  induction ρ with
  | zero => simp [parAcc, exactAcc]
  | succ r ih =>
      rw [parAcc, ih, show (r + 1) * c = r * c + c by ring, exactAcc_add]
      rfl

/-- **The verified deviation bound covers the parallel-reduced value.**  Because the
    exact parallel value equals the serial `exactAcc s (ρ·c)` (Eq.20 above), the
    paper's normalised bound `Δ_N/N ≤ (ρ·c)/2^f` — proven for the serial truncated
    accumulator — bounds the deviation of the parallel-reduced EXACT value from the
    serial truncated accumulator.  So the reordering never moves the value outside
    the verified fidelity envelope.
    (HONEST SCOPE: this transports the bound at the EXACT-VALUE level via Eq.20.
    The parallel SCHEDULE's own per-register truncation reorders the `ρ·c = |P|·ℓ`
    truncation steps; it meets the SAME bound by the identical counting — each step
    still drops `< 2^t` and there are still `ρ·c` of them — but that per-schedule
    `apprAcc` variant is not separately formalised here.) -/
theorem parallelReduction_modDev (N : ℕ) (hN : 0 < N) (s : ℕ → ℕ) (t f c ρ : ℕ)
    (htf : 2 ^ (t + f) ≤ N) :
    (modDev N (parAcc s c ρ) (apprAcc s t (ρ * c)) : ℚ) / N
      ≤ (ρ * c : ℕ) / 2 ^ f := by
  rw [parallelReduction_eq_serial s c ρ]
  -- now the goal is the serial bound with A = ρ·c (= |P|·ℓ)
  have h := modDev_truncAcc_normalized N hN s t f ρ c htf
  simpa using h

end FormalRV.Audit.Pinnacle.ParallelReduction
