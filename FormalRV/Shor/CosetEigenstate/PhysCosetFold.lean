/-
  FormalRV.Shor.CosetEigenstate.PhysCosetFold — the physical-coset WINDOWED FOLD: the
  composition of `numWin` literal cuccaro addConst gates acts as `+∑cᵢ` on the
  interleaved-target coset state (exact, under the no-wrap fit).
  ════════════════════════════════════════════════════════════════════════════

  Composes the per-step gate theorem `CuccaroPhysCoset.uc_eval_cuccaro_physCoset` over the
  `numWin` window additions.  The composed unitary `foldUnitary n` (= the product of the
  first `n` cuccaro addConst gates' `uc_eval`s) carries `physCosetState k` to
  `physCosetState (k + ∑_{i<n} cᵢ)` — EXACTLY (no bad set), under the single cumulative
  no-wrap fit `k + (∑_{i<numWin} cᵢ) + (2^m-1)·N < 2^bits` (each partial step's fit
  follows since partial sums are monotone).

  Why exact / no wrap-mass here: the per-step gate `uc_eval_cuccaro_physCoset` is itself
  EXACT under its fit — the coset deviation is NOT at the gate level but at the
  coset-vs-canonical embedding level (`PhysEmbedMarginal`, the E_phys isometry).  So the
  fold is a clean deterministic shift; the windowed multiplier's running sum `∑cᵢ` is the
  unreduced accumulator, whose reduction-vs-canonical deviation is paid by the marginal
  frontier, not here.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.CuccaroPhysCoset

namespace FormalRV.Shor.CosetEigenstate.PhysCosetFold

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.CosetEigenstate.CuccaroPhysCoset (physCosetState uc_eval_cuccaro_physCoset)

/-- The composed unitary of the first `n` cuccaro addConst gates (constants `c 0 … c (n-1)`),
    applied in order (gate `0` first). -/
noncomputable def foldUnitary (dim bits q_start : Nat) (c : Nat → Nat) : Nat → Square dim
  | 0 => 1
  | n + 1 => Framework.uc_eval (Gate.toUCom dim (cuccaro_addConstGate bits q_start (c n)))
              * foldUnitary dim bits q_start c n

/-- **THE PHYSICAL-COSET WINDOWED FOLD.**  The composition of the first `n` window
    addConst gates carries the interleaved-target coset state `physCosetState k` to
    `physCosetState (k + ∑_{i<n} cᵢ)`, exactly, under the cumulative no-wrap fit. -/
theorem physCoset_windowed_fold (dim N m bits q_start : Nat) (c : Nat → Nat) (k : Nat)
    (hdim : q_start + 2 * bits + 1 ≤ dim) :
    ∀ (n : Nat), (∀ i, i < n → c i < 2 ^ bits) →
      k + (∑ i ∈ Finset.range n, c i) + (2 ^ m - 1) * N < 2 ^ bits →
      ∀ (s : Matrix (Fin (2 ^ dim)) (Fin 1) ℂ), s = physCosetState dim N m q_start k →
        foldUnitary dim bits q_start c n * s
          = physCosetState dim N m q_start (k + ∑ i ∈ Finset.range n, c i) := by
  intro n
  induction n with
  | zero =>
      intro _ _ s hs
      simp only [foldUnitary, Finset.range_zero, Finset.sum_empty, Nat.add_zero, Matrix.one_mul]
      exact hs
  | succ p ih =>
      intro hc hfit s hs
      have hsum_succ : ∑ i ∈ Finset.range (p + 1), c i = (∑ i ∈ Finset.range p, c i) + c p :=
        Finset.sum_range_succ c p
      have fit_p : k + (∑ i ∈ Finset.range p, c i) + (2 ^ m - 1) * N < 2 ^ bits := by
        rw [hsum_succ] at hfit; omega
      have ih' := ih (fun i hi => hc i (by omega)) fit_p s hs
      have fit_step :
          (k + ∑ i ∈ Finset.range p, c i) + (2 ^ m - 1) * N + c p < 2 ^ bits := by
        rw [hsum_succ] at hfit; omega
      show Framework.uc_eval (Gate.toUCom dim (cuccaro_addConstGate bits q_start (c p)))
            * foldUnitary dim bits q_start c p * s = _
      rw [Matrix.mul_assoc,
          uc_eval_cuccaro_physCoset dim N m bits q_start (c p) (k + ∑ i ∈ Finset.range p, c i)
            (hc p (by omega)) hdim fit_step (foldUnitary dim bits q_start c p * s) ih',
          hsum_succ]
      congr 1
      omega

end FormalRV.Shor.CosetEigenstate.PhysCosetFold
