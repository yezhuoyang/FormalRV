/-
  FormalRV.Shor.RunwayWindowed.RunwayFold — M4: the window FOLD.
  ════════════════════════════════════════════════════════════════════════════

  Folding `numWin` window steps over the runway-windowed multiplier accumulates
  the coset-word sum `Σ_{j<numWin} (a·(2^w)^j·window_j) mod N` (each chunked to the
  `k·gSep`-bit runway) into the contiguous accumulator, and preserves the
  `RunwayReady` structural invariant throughout — by induction on the window
  count, each step discharged by `runwayWindowStep_value` (accumulator += word_j)
  and `runwayWindowStep_preserves_ready` (invariant maintained).

  HONEST OPEN OBLIGATION (the runway-sizing condition).  `runwayWindowStep_value`
  requires, at each window `t`, a per-segment NO-OVERFLOW bound
  `segReg m (accumulator_t) + (word_t / 2^(m·gSep)) % 2^gSep < 2^(gSep+1)`.  The
  base-0 runway-adder layer does NOT prove this for a SEQUENCE of additions — its
  `runwayAddK_advance` is self-caveated as "structurally trivial", and the
  deferred-carry VALUE bound over many adds is explicitly left open there.  The
  paper guarantees it by choosing `g_sep` large enough (`g_sep ≳ log₂(numWin)`).
  So we carry it as an EXPLICIT, FLAGGED hypothesis `hno` (a named, satisfiable
  parameter-regime obligation) — surfaced, NOT faked.  Everything else (the value
  accumulation + the full structural-invariant preservation) is proven rigorously
  on the ACTUAL `runwayWindowedMul` circuit.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.RunwayWindowed.RunwayMulCorrect

namespace FormalRV.Shor.RunwayWindowed.RunwayFold

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.RunwayWindowed.RunwayLayout (runwayWindowStep runwayWindowedMul)
open FormalRV.Shor.RunwayWindowed.RunwayMulCorrect
  (yBaseR RunwayReady runwayWindowStep_value runwayWindowStep_preserves_ready)
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional (segReg)
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderContiguous (contiguousDecode)
open FormalRV.Shor.WindowedCircuit (encodeReg)

/-- The window fold as an explicit recursion (`= runwayWindowedMul`, proved below):
    `runwayFoldGate t` is the gate of the first `t` window steps, based at the
    faithful layout `base = 1+2w`, `yBase = yBaseR`. -/
def runwayFoldGate (w gSep a N k : Nat) : Nat → Gate
  | 0 => Gate.I
  | t + 1 =>
      Gate.seq (runwayFoldGate w gSep a N k t)
        (runwayWindowStep w gSep a N k (1 + 2 * w) (yBaseR w gSep k) t)

/-- `runwayFoldGate` IS the `runwayWindowedMul` left-fold (the `List.range` fold
    appends the next window step). -/
theorem runwayWindowedMul_eq_foldGate (w gSep a N k : Nat) : ∀ t,
    runwayWindowedMul w gSep a N k (1 + 2 * w) (yBaseR w gSep k) t
      = runwayFoldGate w gSep a N k t := by
  intro t
  induction t with
  | zero => rfl
  | succ n ih =>
      have hexp : runwayWindowedMul w gSep a N k (1 + 2 * w) (yBaseR w gSep k) (n + 1)
          = Gate.seq (runwayWindowedMul w gSep a N k (1 + 2 * w) (yBaseR w gSep k) n)
              (runwayWindowStep w gSep a N k (1 + 2 * w) (yBaseR w gSep k) n) := by
        unfold runwayWindowedMul
        rw [List.range_succ, List.foldl_append]
        rfl
      rw [hexp, ih]
      rfl

/-- **M4 — the fold accumulates the coset-word sum + preserves `RunwayReady`.**
    On a `RunwayReady` input with a CLEAR accumulator, after `t ≤ numWin` window
    steps the contiguous accumulator holds `Σ_{i<t} (a·(2^w)^i·window_i mod N)`
    (each chunked to `2^(k·gSep)`) and the state is still `RunwayReady`.  The
    per-step runway no-overflow `hno` is the FLAGGED runway-sizing obligation. -/
theorem runwayFold_value_ready (w gSep a N k numWin y : Nat) (g0 : Nat → Bool)
    (hw : 0 < w) (hgSep : 0 < gSep) (hk : 0 < k)
    (hr0 : RunwayReady w gSep k numWin y g0)
    (hacc0 : contiguousDecode gSep k (fun q => g0 (q + (1 + 2 * w))) = 0)
    (hno : ∀ t, t < numWin → ∀ m, m < k →
      segReg gSep m (fun q => Gate.applyNat (runwayFoldGate w gSep a N k t) g0 (q + (1 + 2 * w)))
        + ((a * (2 ^ w) ^ t * WindowedArith.window w y t) % N / 2 ^ (m * gSep)) % 2 ^ gSep
        < 2 ^ (gSep + 1)) :
    ∀ t, t ≤ numWin →
      RunwayReady w gSep k numWin y (Gate.applyNat (runwayFoldGate w gSep a N k t) g0)
      ∧ contiguousDecode gSep k
          (fun q => Gate.applyNat (runwayFoldGate w gSep a N k t) g0 (q + (1 + 2 * w)))
        = (Finset.range t).sum
            (fun i => ((a * (2 ^ w) ^ i * WindowedArith.window w y i) % N) % 2 ^ (k * gSep)) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · show RunwayReady w gSep k numWin y g0; exact hr0
    · rw [Finset.sum_range_zero]
      show contiguousDecode gSep k (fun q => g0 (q + (1 + 2 * w))) = 0; exact hacc0
  | succ n ih =>
    intro hn1
    obtain ⟨hr_n, hacc_n⟩ := ih (by omega)
    have hstep_eq : Gate.applyNat (runwayFoldGate w gSep a N k (n + 1)) g0
        = Gate.applyNat (runwayWindowStep w gSep a N k (1 + 2 * w) (yBaseR w gSep k) n)
            (Gate.applyNat (runwayFoldGate w gSep a N k n) g0) := by
      show Gate.applyNat (Gate.seq (runwayFoldGate w gSep a N k n)
        (runwayWindowStep w gSep a N k (1 + 2 * w) (yBaseR w gSep k) n)) g0 = _
      rw [Gate.applyNat_seq]
    obtain ⟨hctrl, haddr, hand, haddend, hyfull, hready⟩ := hr_n
    have hy : ∀ i, i < w →
        Gate.applyNat (runwayFoldGate w gSep a N k n) g0 (yBaseR w gSep k + n * w + i)
          = encodeReg (yBaseR w gSep k) (numWin * w) y (yBaseR w gSep k + n * w + i) := by
      intro i hi
      have hjw : n * w + i < numWin * w := by
        calc n * w + i < n * w + w := by omega
          _ = (n + 1) * w := by ring
          _ ≤ numWin * w := Nat.mul_le_mul_right w (by omega)
      have h := hyfull (n * w + i) hjw
      rwa [show yBaseR w gSep k + (n * w + i) = yBaseR w gSep k + n * w + i from by omega] at h
    refine ⟨?_, ?_⟩
    · rw [hstep_eq]
      exact runwayWindowStep_preserves_ready w gSep a N k numWin y n _ hw hgSep hk (by omega)
        ⟨hctrl, haddr, hand, haddend, hyfull, hready⟩
    · rw [hstep_eq, Finset.sum_range_succ, ← hacc_n]
      exact runwayWindowStep_value w gSep a N k numWin y n _ hw hgSep (by omega)
        hctrl haddr hand haddend hy hready (hno n (by omega))

/-- **M4 corollary — on the ACTUAL `runwayWindowedMul` circuit.**  All `numWin`
    windows leave the contiguous accumulator holding the full coset-word sum and
    the state `RunwayReady`. -/
theorem runwayWindowedMul_value_ready (w gSep a N k numWin y : Nat) (g0 : Nat → Bool)
    (hw : 0 < w) (hgSep : 0 < gSep) (hk : 0 < k)
    (hr0 : RunwayReady w gSep k numWin y g0)
    (hacc0 : contiguousDecode gSep k (fun q => g0 (q + (1 + 2 * w))) = 0)
    (hno : ∀ t, t < numWin → ∀ m, m < k →
      segReg gSep m (fun q => Gate.applyNat (runwayFoldGate w gSep a N k t) g0 (q + (1 + 2 * w)))
        + ((a * (2 ^ w) ^ t * WindowedArith.window w y t) % N / 2 ^ (m * gSep)) % 2 ^ gSep
        < 2 ^ (gSep + 1)) :
    RunwayReady w gSep k numWin y
        (Gate.applyNat (runwayWindowedMul w gSep a N k (1 + 2 * w) (yBaseR w gSep k) numWin) g0)
      ∧ contiguousDecode gSep k
          (fun q => Gate.applyNat
            (runwayWindowedMul w gSep a N k (1 + 2 * w) (yBaseR w gSep k) numWin) g0 (q + (1 + 2 * w)))
        = (Finset.range numWin).sum
            (fun i => ((a * (2 ^ w) ^ i * WindowedArith.window w y i) % N) % 2 ^ (k * gSep)) := by
  rw [runwayWindowedMul_eq_foldGate]
  exact runwayFold_value_ready w gSep a N k numWin y g0 hw hgSep hk hr0 hacc0 hno numWin (le_refl _)

end FormalRV.Shor.RunwayWindowed.RunwayFold
