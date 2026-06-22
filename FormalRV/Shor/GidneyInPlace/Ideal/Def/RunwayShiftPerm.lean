/-
  FormalRV.Shor.GidneyInPlace.RunwayShiftPerm — P1.1a of the hybrid route:
  the CLEAN IDEAL residue-shift permutation on the a-block runway value.
  ════════════════════════════════════════════════════════════════════════════

  The ideal clean coset shift `cosetInputVec z 0 ↦ cosetInputVec ((mult·z)%N) 0` is realized,
  at the a-block VALUE level, by the runway-preserving map

      va = q·N + r   ↦   q·N + (mult·r)%N        (preserve offset q = va/N, shift residue r)

  — NOT "multiply the full a-index by mult mod N".  `RunwayMul.runwayMul_cosetState_shift`
  already turns such a permutation into the coset-state shift, but it TAKES the permutation as a
  hypothesis (the named gap, COSET_MULTIPLIER_DESIGN.md:312-313).  This file BUILDS it.

  THE GLOBAL-BIJECTIVITY DEVICE — `guardedShift`: the bare residue shift can leave `[0, D)` on the
  partial last block (when `D = 2^bits` is not a multiple of `N`), so we GUARD it: do the shift
  only when the whole block `[q·N, q·N+N)` fits in `[0, D)`, else act as identity.  This is a
  genuine self-bijection of `Fin D` for ANY `D` (inverse = the same `guardedShift` with the
  inverse multiplier `kInv`), with NO `Equiv.ofBijective` needed.  On the SUPPORT (runway reps
  `z + j·N`, `j < 2^cm`), under the FULL-BLOCKS budget `2^cm·N ≤ D` the guard never fires, so it
  does the exact runway shift (`guarded_on_support`).  ⚠ The full-blocks budget is REQUIRED (a
  verified counterexample exists under runway-fit alone); it is the pervasive coset hypothesis.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Primitives.Def.CosetModArith

namespace FormalRV.Shor.GidneyInPlace.RunwayShiftPerm

/-- The guarded runway residue-shift on a raw value `v`: shift the residue `v%N` by `mult` mod
    `N` while keeping the offset `v/N`, but ONLY when the whole block `[v/N·N, v/N·N+N)` fits in
    `[0, D)`; otherwise identity.  Globally bijective on `Fin D` (inverse via `kInv`). -/
def guardedShift (D N c v : Nat) : Nat :=
  if (v / N) * N + N ≤ D then (v / N) * N + (c * (v % N)) % N else v

/-- `guardedShift` stays in range `[0, D)`. -/
theorem guarded_lt (D N c v : Nat) (hN : 0 < N) (hv : v < D) : guardedShift D N c v < D := by
  unfold guardedShift
  split
  · rename_i hg
    have : (c * (v % N)) % N < N := Nat.mod_lt _ hN
    omega
  · exact hv

/-- The shifted value's offset is unchanged: `(q·N + (c·r)%N)/N = q`. -/
theorem guarded_div (N c v : Nat) (hN : 0 < N) :
    ((v / N) * N + (c * (v % N)) % N) / N = v / N := by
  rw [Nat.mul_comm (v / N) N, Nat.mul_add_div hN, Nat.div_eq_of_lt (Nat.mod_lt _ hN), Nat.add_zero]

/-- The shifted value's residue is `(c·r)%N`: `(q·N + (c·r)%N)%N = (c·r)%N`. -/
theorem guarded_mod (N c v : Nat) (hN : 0 < N) :
    ((v / N) * N + (c * (v % N)) % N) % N = (c * (v % N)) % N := by
  rw [Nat.mul_comm (v / N) N, Nat.mul_add_mod, Nat.mod_mod]

/-- **The inverse law.**  `guardedShift kInv` undoes `guardedShift mult` when `(mult·kInv)%N = 1`.
    The guard is determined by the offset `v/N`, which the shift preserves (`guarded_div`), so it
    fires identically on both passes; the residue round-trips via `kInv·(mult·r) ≡ r [MOD N]`. -/
theorem guarded_leftinv (D N mult kInv v : Nat) (hN : 1 < N) (hinv : (mult * kInv) % N = 1) :
    guardedShift D N kInv (guardedShift D N mult v) = v := by
  have hN0 : 0 < N := by omega
  by_cases hg : (v / N) * N + N ≤ D
  · have hinner : guardedShift D N mult v = (v / N) * N + (mult * (v % N)) % N := by
      unfold guardedShift; rw [if_pos hg]
    rw [hinner]
    unfold guardedShift
    simp only [guarded_div N mult v hN0, guarded_mod N mult v hN0]
    rw [if_pos hg]
    have hrt : (kInv * ((mult * (v % N)) % N)) % N = v % N := by
      have hkm : kInv * mult ≡ 1 [MOD N] := by
        show (kInv * mult) % N = 1 % N
        rw [Nat.mul_comm kInv mult, hinv, Nat.mod_eq_of_lt hN]
      have h1 : kInv * ((mult * (v % N)) % N) ≡ kInv * (mult * (v % N)) [MOD N] :=
        (Nat.ModEq.refl kInv).mul (Nat.mod_modEq _ _)
      have h2 : kInv * (mult * (v % N)) ≡ v % N [MOD N] := by
        have heq : kInv * (mult * (v % N)) = (kInv * mult) * (v % N) :=
          (mul_assoc kInv mult (v % N)).symm
        rw [heq]
        have hmr : (kInv * mult) * (v % N) ≡ 1 * (v % N) [MOD N] := Nat.ModEq.mul_right (v % N) hkm
        rwa [Nat.one_mul] at hmr
      have h3 := h1.trans h2
      unfold Nat.ModEq at h3
      rwa [Nat.mod_mod] at h3
    rw [hrt]
    exact Nat.div_add_mod' v N
  · have hinner : guardedShift D N mult v = v := by unfold guardedShift; rw [if_neg hg]
    rw [hinner]
    unfold guardedShift; rw [if_neg hg]

/-- **The ideal a-value runway shift, as an `Equiv.Perm (Fin D)`.**  `toFun = guardedShift mult`,
    `invFun = guardedShift kInv`; both inverse laws fall out of `guarded_leftinv` under
    `(mult·kInv)%N = (kInv·mult)%N = 1`. -/
noncomputable def resShiftPerm (D N mult kInv : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1) : Equiv.Perm (Fin D) where
  toFun i := ⟨guardedShift D N mult i.val, guarded_lt D N mult i.val (by omega) i.isLt⟩
  invFun i := ⟨guardedShift D N kInv i.val, guarded_lt D N kInv i.val (by omega) i.isLt⟩
  left_inv i := Fin.ext (guarded_leftinv D N mult kInv i.val hN hfwd)
  right_inv i := Fin.ext (guarded_leftinv D N kInv mult i.val hN hbwd)

/-- **On-support correctness (under the FULL-BLOCKS budget).**  On a runway representative
    `z + j·N` with `z < N` and `j < 2^cm`, when `2^cm·N ≤ D` (so block `j` is full and the guard
    fires), `guardedShift mult` maps it to the `j`-th rep of the TARGET window:
    `z + j·N ↦ (mult·z)%N + j·N`. -/
theorem guarded_on_support (D N cm mult z j : Nat) (hN : 0 < N) (hz : z < N) (hj : j < 2 ^ cm)
    (hbudget : 2 ^ cm * N ≤ D) :
    guardedShift D N mult (z + j * N) = (mult * z) % N + j * N := by
  have hdiv : (z + j * N) / N = j := by
    rw [Nat.add_mul_div_right z j hN, Nat.div_eq_of_lt hz, Nat.zero_add]
  have hmod : (z + j * N) % N = z := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]
  have hcond : j * N + N ≤ D := by
    have hstep : j * N + N = (j + 1) * N := (Nat.succ_mul j N).symm
    rw [hstep]
    exact le_trans (Nat.mul_le_mul (by omega) (le_refl N)) hbudget
  unfold guardedShift
  rw [hdiv, hmod, if_pos hcond]
  exact Nat.add_comm (j * N) (mult * z % N)

end FormalRV.Shor.GidneyInPlace.RunwayShiftPerm
