/-
  FormalRV.Shor.CosetEigenstate.CuccaroPhysCoset — THE DELIVERABLE: the literal
  `uc_eval` of `cuccaro_addConstGate` acts as `addConst` (+c) on the interleaved-target
  coset state, with clean ancilla/frame preserved.
  ════════════════════════════════════════════════════════════════════════════

  Option (ii), completed.  Rather than construct an explicit layout permutation `L`
  (a sparse-image permutation of `Fin (2^dim)` — hard), we define the coset state
  DIRECTLY on the SPREAD support: `physCosetState` is the coset superposition over the
  spread basis indices `spreadIdx (k+jN)` (the structured interleaved layout
  `funboolNat (cuccaro_input_F q_start false 0 ·)`).  The gate action then closes as a
  clean `∃`-rewrite through `cuccaro_gateToPerm_spread` — NO `L`, NO off-window case:

    `uc_eval_cuccaro_physCoset` :  under the no-wrap target-register fit
      `k + (2^m-1)·N + c < 2^bits`,
      `uc_eval (toUCom cuccaro_addConstGate c) · physCosetState k = physCosetState (k+c)`.

  The membership crux `(gateToPerm cuccaro).symm i ∈ physWindow k ↔ i ∈ physWindow (k+c)`
  is `Equiv.symm_apply_eq` + `cuccaro_gateToPerm_spread` + `Nat.mod_eq_of_lt` (fit ⇒ the
  cuccaro mod-2^bits wrap never fires) + `k+jN+c = (k+c)+jN`.

  This IS the gate-acts-as-addConst-on-the-interleaved-target-coset-state theorem.  The
  remaining connection to the contiguous-`cosetState` sound route is the readout-marginal
  invariance under data-register relabeling (`phaseMarginal_relabel_invariant`): the
  spread layout does not change the phase/readout marginal, so the coset-deviation bound
  carries over without threading the layout through the whole QPE assembly.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.  Proof
  de-risked via 3 parallel verified attempts.
-/
import FormalRV.Shor.CosetEigenstate.CuccaroGatePerm
import FormalRV.Shor.CosetEigenstate.UCEvalBridge

namespace FormalRV.Shor.CosetEigenstate.CuccaroPhysCoset

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.CosetEigenstate.GatePerm
open FormalRV.Shor.CosetEigenstate.CuccaroGatePerm (cuccaro_gateToPerm_spread)
open FormalRV.Shor.CosetEigenstate.ApproxOp (permState)
open FormalRV.Shor.CosetEigenstate.UCEvalBridge (uc_eval_eq_permState)

/-- The spread basis index of value `v`: `funboolNat` of the structured cuccaro input
    (target bits at the interleaved positions `q_start+2i+1`). -/
noncomputable def spreadIdx (dim q_start v : Nat) : Fin (2 ^ dim) :=
  funboolNat dim (fun (l : Fin dim) => cuccaro_input_F q_start false 0 v l.val)

/-- The physical (interleaved) coset window: the spread indices of the `2^m` reps `k+j·N`. -/
noncomputable def physWindow (dim N m q_start k : Nat) : Finset (Fin (2 ^ dim)) :=
  (Finset.range (2 ^ m)).image (fun j => spreadIdx dim q_start (k + j * N))

/-- The interleaved-target coset state: amplitude `1/√2^m` on the spread window. -/
noncomputable def physCosetState (dim N m q_start k : Nat) : QState (2 ^ dim) :=
  fun i _ => if i ∈ physWindow dim N m q_start k then ((1 / Real.sqrt (2 ^ m) : ℝ) : ℂ) else 0

/-- **THE DELIVERABLE.**  Under the no-wrap target-register fit, the literal `uc_eval` of
    `cuccaro_addConstGate` carries the interleaved-target coset state `physCosetState k`
    to `physCosetState (k+c)` — i.e. it acts as `addConst` (+c) on the (interleaved)
    coset state, ancilla/frame preserved (the spread support encodes clean ancilla). -/
theorem uc_eval_cuccaro_physCoset (dim N m bits q_start c k : Nat)
    (hc : c < 2 ^ bits) (hdim : q_start + 2 * bits + 1 ≤ dim)
    (hfit : k + (2 ^ m - 1) * N + c < 2 ^ bits)
    (s : Matrix (Fin (2 ^ dim)) (Fin 1) ℂ) (hs : s = physCosetState dim N m q_start k) :
    Framework.uc_eval (Gate.toUCom dim (cuccaro_addConstGate bits q_start c)) * s
      = physCosetState dim N m q_start (k + c) := by
  subst hs
  set hwt := cuccaro_addConstGate_wellTyped bits q_start c dim hdim with hhwt
  set σ := gateToPerm (cuccaro_addConstGate bits q_start c) dim hwt with hσ
  funext i z
  rw [uc_eval_eq_permState (cuccaro_addConstGate bits q_start c) dim hwt]
  -- LHS = permState σ.symm (physCosetState .. k) i z = physCosetState .. k (σ.symm i) z.
  -- The membership-iff crux.
  have hmem : σ.symm i ∈ physWindow dim N m q_start k
      ↔ i ∈ physWindow dim N m q_start (k + c) := by
    simp only [physWindow, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, hji⟩
      refine ⟨j, hj, ?_⟩
      -- hji : spreadIdx .. (k + j*N) = σ.symm i  ⟹  i = σ (spreadIdx ..)
      have hi : i = σ (spreadIdx dim q_start (k + j * N)) := by
        rw [hji, Equiv.apply_symm_apply]
      have hjle : j ≤ 2 ^ m - 1 := by omega
      have hjN : j * N ≤ (2 ^ m - 1) * N := Nat.mul_le_mul_right N hjle
      have hx : k + j * N < 2 ^ bits := by omega
      rw [hi, hσ]
      unfold spreadIdx
      rw [cuccaro_gateToPerm_spread bits q_start c (k + j * N) dim hc hx hdim]
      have hmod : (k + j * N + c) % 2 ^ bits = (k + c) + j * N := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [hmod]
    · rintro ⟨j, hj, hji⟩
      refine ⟨j, hj, ?_⟩
      -- hji : spreadIdx .. ((k+c)+j*N) = i  ⟹  spreadIdx .. (k+j*N) = σ.symm i
      have hjle : j ≤ 2 ^ m - 1 := by omega
      have hjN : j * N ≤ (2 ^ m - 1) * N := Nat.mul_le_mul_right N hjle
      have hx : k + j * N < 2 ^ bits := by omega
      rw [Eq.comm, Equiv.symm_apply_eq, ← hji, hσ]
      unfold spreadIdx
      rw [cuccaro_gateToPerm_spread bits q_start c (k + j * N) dim hc hx hdim]
      have hmod : (k + j * N + c) % 2 ^ bits = (k + c) + j * N := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [hmod]
  -- finish: both sides are the indicator, controlled by hmem.
  rw [← hσ]
  simp only [permState, physCosetState, hmem]

end FormalRV.Shor.CosetEigenstate.CuccaroPhysCoset
