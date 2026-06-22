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
import FormalRV.Shor.CFS.TruncatedAccumulation

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
    (SCOPE: this transports the bound at the EXACT-VALUE level via Eq.20.  The parallel
    SCHEDULE's own per-register truncation — which reorders the `ρ·c = |P|·ℓ` truncation
    steps across `ρ` registers + a combine tree — is formalised separately and proven to
    meet the SAME bound in `parallelSchedule_apprAcc_modDev` below.) -/
theorem parallelReduction_modDev (N : ℕ) (hN : 0 < N) (s : ℕ → ℕ) (t f c ρ : ℕ)
    (htf : 2 ^ (t + f) ≤ N) :
    (modDev N (parAcc s c ρ) (apprAcc s t (ρ * c)) : ℚ) / N
      ≤ (ρ * c : ℕ) / 2 ^ f := by
  rw [parallelReduction_eq_serial s c ρ]
  -- now the goal is the serial bound with A = ρ·c (= |P|·ℓ)
  have h := modDev_truncAcc_normalized N hN s t f ρ c htf
  simpa using h

/-! ## Closing the seam: the parallel SCHEDULE's OWN approximate accumulator meets the bound.

    `parallelReduction_modDev` above compares the EXACT parallel value `parAcc` against the SERIAL
    truncated accumulator `apprAcc s t (ρ·c)`.  But the parallel schedule never builds the serial
    `apprAcc`: each working register `j` runs its OWN truncated accumulation over its `c` local terms
    (truncating to `t` bits after each of its `c` additions), and the `ρ` register results are then
    combined by the binary tree.  The paper argues in prose that this still meets the same bound
    ("each step still drops `< 2^t`, and there are still `ρ·c` of them") — and its v1 had an error in
    exactly this accumulator-combine step (fixed by M. Hinsche).  Below we FORMALISE the parallel
    schedule's approximate accumulator (`parApprAcc`) and prove the STRONGER fact `parApprAcc_eq_serial`:
    the per-register-truncated, tree-combined value is *EXACTLY EQUAL* to the serial truncated
    accumulator `apprAcc s t (ρ·c)` — not merely within the bound.  Reason (structural): truncation only
    ever yields `2^t`-multiples and adding such a multiple commutes with the next truncation
    (`truncShift_add_multiple`), so re-truncating across chunk boundaries is a no-op; the reordering is
    value-exact at the truncated level.  Hence the serial deviation bound applies to the parallel
    schedule VERBATIM — `parallelSchedule_apprAcc_deviation`/`_modDev` restate it on `parApprAcc` for
    convenience, but the load-bearing content is the exact equality, not a separate re-derivation. -/

/-- **Subadditivity of the modular deviation over a sum.**  `Δ_N(a+a', b+b') ≤ Δ_N(a,b) + Δ_N(a',b')`
    — two independent components' deviations add.  (Triangle inequality + translation invariance.) -/
theorem modDev_add_add (N a a' b b' : ℕ) (hN : 0 < N) :
    modDev N (a + a') (b + b') ≤ modDev N a b + modDev N a' b' := by
  have e1 : modDev N (a + a') (b + a') = modDev N a b := modDev_add_right N a b a' hN
  have e2 : modDev N (b + a') (b + b') = modDev N a' b' := by
    rw [Nat.add_comm b a', Nat.add_comm b b']; exact modDev_add_right N a' b' b hN
  calc modDev N (a + a') (b + b')
      ≤ modDev N (a + a') (b + a') + modDev N (b + a') (b + b') := modDev_triangle N _ _ _ hN
    _ = modDev N a b + modDev N a' b' := by rw [e1, e2]

/-- The approximate accumulator working register `j` computes LOCALLY: truncate to `t` bits after each
    of its `c` additions over its own chunk `s(j·c + ·)`. -/
def chunkApprAcc (s : ℕ → ℕ) (t c j : ℕ) : ℕ := apprAcc (fun k => s (j * c + k)) t c

/-- The parallel SCHEDULE's approximate accumulator: combine the first `ρ` registers' LOCAL truncated
    accumulators by the (exact, associative) binary tree — the genuine object the parallel schedule
    produces (cf. the exact `parAcc`, which this approximates register-wise). -/
def parApprAcc (s : ℕ → ℕ) (t c : ℕ) : ℕ → ℕ
  | 0 => 0
  | ρ + 1 => parApprAcc s t c ρ + chunkApprAcc s t c ρ

/-- **Truncation commutes with adding a `2^t`-multiple.**  `truncShift` drops the low `t` bits, so a
    summand that is already a multiple of `2^t` passes straight through. -/
theorem truncShift_add_multiple (x t M : ℕ) :
    truncShift (2 ^ t * M + x) t = 2 ^ t * M + truncShift x t := by
  unfold truncShift
  rw [Nat.add_comm (2 ^ t * M) x, Nat.add_mul_div_left x M (by positivity : 0 < 2 ^ t)]
  ring

/-- The approximate accumulator is always a multiple of `2^t` (every step ends in a `truncShift`). -/
theorem apprAcc_dvd (s : ℕ → ℕ) (t A : ℕ) : 2 ^ t ∣ apprAcc s t A := by
  cases A with
  | zero => simp [apprAcc]
  | succ k => exact ⟨(apprAcc s t k + s k) / 2 ^ t, by rw [apprAcc, truncShift]⟩

/-- **Chunk additivity of the TRUNCATED accumulator** (the truncated analogue of `exactAcc_add`).
    Because each running value is a `2^t`-multiple, restarting the truncated accumulation at offset `A`
    and adding the truncated prefix reproduces the serial truncated accumulation over `[0, A+c)`. -/
theorem apprAcc_add (s : ℕ → ℕ) (t A c : ℕ) :
    apprAcc s t (A + c) = apprAcc s t A + apprAcc (fun k => s (A + k)) t c := by
  induction c with
  | zero => simp [apprAcc]
  | succ c ih =>
      obtain ⟨M, hM⟩ := apprAcc_dvd s t A
      rw [show A + (c + 1) = (A + c) + 1 by ring]
      simp only [apprAcc]
      rw [ih, hM,
          show 2 ^ t * M + apprAcc (fun k => s (A + k)) t c + s (A + c)
             = 2 ^ t * M + (apprAcc (fun k => s (A + k)) t c + s (A + c)) by ring,
          truncShift_add_multiple]

/-- **THE PARALLEL SCHEDULE'S APPROXIMATE ACCUMULATOR IS *EXACTLY* THE SERIAL ONE.**  The per-register
    locally-truncated accumulators, combined by the (exact) binary tree, equal the serial truncated
    accumulator over all `ρ·c` terms — IDENTICALLY (not merely within the deviation bound).  Reason:
    truncation only ever produces `2^t`-multiples, and adding such a multiple commutes with the next
    truncation (`truncShift_add_multiple`), so re-truncating across chunk boundaries is a no-op.  So
    the parallel REORDERING is value-exact at the truncated level too — the serial deviation bound
    (`modDev_truncAcc_normalized`) applies to it verbatim. -/
theorem parApprAcc_eq_serial (s : ℕ → ℕ) (t c ρ : ℕ) :
    parApprAcc s t c ρ = apprAcc s t (ρ * c) := by
  induction ρ with
  | zero => simp [parApprAcc, apprAcc]
  | succ r ih =>
      rw [parApprAcc, ih, chunkApprAcc, show (r + 1) * c = r * c + c by ring, apprAcc_add]

/-- **The parallel schedule's approximate accumulator meets the serial deviation bound.**  After
    `ρ` registers each locally truncating `c` additions, the parallel-combined approximate value
    deviates from the EXACT sum over all `ρ·c` terms by at most `(ρ·c)·2^t` — IDENTICAL to the serial
    `modDev_truncAcc` bound.  This is the per-schedule statement the paper only argued in prose. -/
theorem parallelSchedule_apprAcc_deviation (N : ℕ) (hN : 0 < N) (s : ℕ → ℕ) (t c : ℕ) :
    ∀ ρ, modDev N (exactAcc s (ρ * c)) (parApprAcc s t c ρ) ≤ (ρ * c) * 2 ^ t := by
  intro ρ
  induction ρ with
  | zero => simp [parApprAcc, exactAcc, modDev_self N 0 hN]
  | succ r ih =>
      have hsplit : exactAcc s ((r + 1) * c)
          = exactAcc s (r * c) + exactAcc (fun k => s (r * c + k)) c := by
        rw [show (r + 1) * c = r * c + c by ring, exactAcc_add]
      have hchunk : modDev N (exactAcc (fun k => s (r * c + k)) c) (chunkApprAcc s t c r) ≤ c * 2 ^ t := by
        unfold chunkApprAcc; exact modDev_truncAcc N hN (fun k => s (r * c + k)) t c
      calc modDev N (exactAcc s ((r + 1) * c)) (parApprAcc s t c (r + 1))
          = modDev N (exactAcc s (r * c) + exactAcc (fun k => s (r * c + k)) c)
              (parApprAcc s t c r + chunkApprAcc s t c r) := by rw [hsplit, parApprAcc]
        _ ≤ modDev N (exactAcc s (r * c)) (parApprAcc s t c r)
              + modDev N (exactAcc (fun k => s (r * c + k)) c) (chunkApprAcc s t c r) :=
              modDev_add_add N _ _ _ _ hN
        _ ≤ (r * c) * 2 ^ t + c * 2 ^ t := add_le_add ih hchunk
        _ = (r + 1) * c * 2 ^ t := by ring

/-- **The parallel schedule's NORMALISED deviation bound (paper eq:modevbound, per-schedule).**  Under
    `2^{t+f} ≤ N`, the parallel-schedule approximate accumulator's normalised deviation from the exact
    value is `≤ (ρ·c)/2^f` — the SAME `Δ_N/N` envelope as the serial schedule (`modDev_truncAcc_normalized`).
    This addresses the seam left open by `parallelReduction_modDev`: the bound holds for the parallel
    schedule's actual per-register truncated accumulator — which, by `parApprAcc_eq_serial`, is in fact
    the IDENTICAL value to the serial truncated accumulator, so the serial bound transfers exactly. -/
theorem parallelSchedule_apprAcc_modDev (N : ℕ) (hN : 0 < N) (s : ℕ → ℕ) (t f c ρ : ℕ)
    (htf : 2 ^ (t + f) ≤ N) :
    (modDev N (exactAcc s (ρ * c)) (parApprAcc s t c ρ) : ℚ) / N ≤ (ρ * c : ℕ) / 2 ^ f := by
  have hb := parallelSchedule_apprAcc_deviation N hN s t c ρ
  have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
  have hfpos : (0 : ℚ) < (2 : ℚ) ^ f := by positivity
  have h1 : (modDev N (exactAcc s (ρ * c)) (parApprAcc s t c ρ) : ℚ) ≤ (ρ * c : ℕ) * 2 ^ t := by
    exact_mod_cast hb
  have h3 : ((ρ * c : ℕ) : ℚ) * 2 ^ (t + f) ≤ (ρ * c : ℕ) * N := by
    have : (2 : ℚ) ^ (t + f) ≤ N := by exact_mod_cast htf
    gcongr
  rw [div_le_div_iff₀ hNpos hfpos]
  calc (modDev N (exactAcc s (ρ * c)) (parApprAcc s t c ρ) : ℚ) * 2 ^ f
      ≤ ((ρ * c : ℕ) * 2 ^ t) * 2 ^ f := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (ρ * c : ℕ) * 2 ^ (t + f) := by rw [pow_add]; ring
    _ ≤ (ρ * c : ℕ) * N := h3

end FormalRV.Audit.Pinnacle.ParallelReduction
