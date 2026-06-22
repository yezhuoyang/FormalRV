/-
  FormalRV.Shor.GidneyInPlace.UniformState — the uniform-superposition state.
  ════════════════════════════════════════════════════════════════════════════

  The orbit basis of the coset eigenstate is a UNIFORM SUPERPOSITION over a finite
  set of basis indices (a coset `C_j = {v < 2^bits : v ≡ aʲ mod N}`):

      uniformSuperposition dim S  =  (1/√|S|) · ∑_{i ∈ S} |i⟩.

  This file builds that constructor and its three load-bearing facts, reusing the
  already-proven Born-weight machinery (`bornWeightOn`, `uniformAmp_normSq`):

    * per-entry Born mass `= 1/|S|` on `S`, `0` off it;
    * `bornWeightOn` on any `B` = the COUNTING FRACTION `|B ∩ S| / |S|`
      (this is exactly how the wrap weight `W = bornWeightOn ψ (wrap set)` becomes
      `|wrap|/|S|` — the concrete, never-assumed quantity);
    * total Born weight `= 1` (a genuine normalized state, for `S` nonempty).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetBornWeight

namespace FormalRV.Shor.GidneyInPlace.UniformState

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetBornWeight (bornWeightOn)

/-- The uniform superposition over a finite index set `S` (each amplitude
    `1/√|S|`, all real and equal). -/
noncomputable def uniformSuperposition (dim : Nat) (S : Finset (Fin dim)) : QState dim :=
  fun i _ => if i ∈ S then ((1 / Real.sqrt S.card : ℝ) : ℂ) else 0

theorem uniformSuperposition_apply (dim : Nat) (S : Finset (Fin dim)) (i : Fin dim) :
    uniformSuperposition dim S i 0
      = if i ∈ S then ((1 / Real.sqrt S.card : ℝ) : ℂ) else 0 := rfl

/-- **Per-entry Born mass.**  `‖ψ i‖² = 1/|S|` on `S`, `0` off it. -/
theorem uniformSuperposition_normSq_entry (dim : Nat) (S : Finset (Fin dim)) (i : Fin dim) :
    Complex.normSq (uniformSuperposition dim S i 0)
      = if i ∈ S then (1 / S.card : ℝ) else 0 := by
  rw [uniformSuperposition_apply]
  by_cases h : i ∈ S
  · rw [if_pos h, if_pos h, Complex.normSq_ofReal, div_mul_div_comm, one_mul,
        Real.mul_self_sqrt (Nat.cast_nonneg S.card)]
  · rw [if_neg h, if_neg h, Complex.normSq_zero]

/-- **Born weight = counting fraction.**  `bornWeightOn ψ B = |B ∩ S| / |S|`.  This
    is the exact, concrete form of the wrap weight `W`: take `B` = the wrap set. -/
theorem uniformSuperposition_bornWeightOn (dim : Nat) (S B : Finset (Fin dim)) :
    bornWeightOn (uniformSuperposition dim S) B = ((B ∩ S).card : ℝ) / S.card := by
  unfold bornWeightOn
  rw [Finset.sum_congr rfl (fun i _ => uniformSuperposition_normSq_entry dim S i),
      Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- **A genuine normalized state.**  Total Born weight `= 1` for nonempty `S`. -/
theorem uniformSuperposition_total (dim : Nat) (S : Finset (Fin dim)) (hS : 0 < S.card) :
    bornWeightOn (uniformSuperposition dim S) Finset.univ = 1 := by
  rw [uniformSuperposition_bornWeightOn dim S Finset.univ, Finset.univ_inter,
      div_self (Nat.cast_pos.mpr hS).ne']

end FormalRV.Shor.GidneyInPlace.UniformState
