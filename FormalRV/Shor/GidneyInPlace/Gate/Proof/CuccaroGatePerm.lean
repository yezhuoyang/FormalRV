/-
  FormalRV.Shor.GidneyInPlace.CuccaroGatePerm — the permutation-level cuccaro value
  action: `gateToPerm(cuccaro)(spread x) = spread((x+c) mod 2^bits)`.
  ════════════════════════════════════════════════════════════════════════════

  Transports `CuccaroStructuredOutput.cuccaro_addConstGate_structured_output` (a funbool
  equality) through the `funboolNat` coordinatization that `uc_eval` uses, to an
  `Equiv.Perm (Fin (2^dim))` statement:  the cuccaro gate's basis permutation maps the
  "spread" index of value `x` (the structured interleaved layout, `funboolNat` of
  `cuccaro_input_F q_start false 0 x`) to the spread index of `(x+c) mod 2^bits`.

    * `gateToPerm_funboolNat` — GENERIC: `gateToPerm g (funboolNat φ) = funboolNat
      (applyFin g φ)` (the `permCongr` coordinate identity; reusable).
    * `cuccaro_gateToPerm_spread` — the cuccaro instance, via the generic helper +
      `extendBool (spread x) = cuccaro_input_F q_start false 0 x` (the structured input is
      zero outside the block, from the fit `q_start+2·bits+1 ≤ dim`) + structured-output.

  This is the `Equiv.Perm`-level fact the layout-conjugation hypothesis `hconj`
  (`CosetLayoutTransport`) is built from: combined with the spread permutation `L`
  (`L(spread v) = v`) and off-wrap no-mod, it gives `uc_eval(cuccaro)` acting as the coset
  `addConst` shift on the laid-out coset state.

  De-risked via 3 parallel verified attempts; this is the cleanest.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Gate.Proof.CuccaroStructuredOutput
import FormalRV.Shor.GidneyInPlace.Gate.Def.GatePerm

namespace FormalRV.Shor.GidneyInPlace.CuccaroGatePerm

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.GatePerm

/-- **Generic helper.**  `gateToPerm` on a funbool index is the funbool index of
    `applyFin` — the `permCongr` coordinate identity. -/
theorem gateToPerm_funboolNat (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (φ : Fin dim → Bool) :
    gateToPerm g dim hwt (funboolNat dim φ) = funboolNat dim (applyFin g dim φ) := by
  unfold gateToPerm
  rw [Equiv.permCongr_apply]
  -- (funboolEquiv dim) (gateClassicalPerm g dim hwt ((funboolEquiv dim).symm (funboolNat dim φ)))
  have hsym : (funboolEquiv dim).symm (funboolNat dim φ) = φ := by
    have hval : funboolNat dim φ = (funboolEquiv dim) φ := rfl
    rw [hval, Equiv.symm_apply_apply]
  rw [hsym, gateClassicalPerm_apply]
  -- (funboolEquiv dim) (applyFin g dim φ) = funboolNat dim (applyFin g dim φ)
  rfl

/-- **THE PERMUTATION-LEVEL CUCCARO VALUE ACTION.**  In the funbool coordinatization, the
    cuccaro addConst gate maps the spread index of value `x` to the spread index of
    `(x+c) mod 2^bits`. -/
theorem cuccaro_gateToPerm_spread (bits q_start c x dim : Nat)
    (hc : c < 2 ^ bits) (hx : x < 2 ^ bits) (hdim : q_start + 2 * bits + 1 ≤ dim) :
    gateToPerm (cuccaro_addConstGate bits q_start c) dim
        (cuccaro_addConstGate_wellTyped bits q_start c dim hdim)
        (funboolNat dim (fun i => cuccaro_input_F q_start false 0 x i.val))
      = funboolNat dim (fun i => cuccaro_input_F q_start false 0 ((x + c) % 2 ^ bits) i.val) := by
  -- `phix` is the structured input restricted to `Fin dim`.
  set phix : Fin dim → Bool := fun i => cuccaro_input_F q_start false 0 x i.val with hphix
  -- Zero-outside-block fact for the structured input.
  have hzero : ∀ k, dim ≤ k → cuccaro_input_F q_start false 0 x k = false := by
    intro k hk
    -- k ≥ dim ≥ q_start + 2*bits + 1, so set i := k - q_start ≥ 2*bits + 1.
    unfold cuccaro_input_F
    have hge : ¬ (k < q_start) := by omega
    rw [if_neg hge]
    set i := k - q_start with hidef
    have hige : 2 * bits + 1 ≤ i := by omega
    have hi0 : ¬ (i = 0) := by omega
    rw [if_neg hi0]
    by_cases hpar : i % 2 = 1
    · -- b-register (= x). index (i-1)/2 ≥ bits, so x.testBit (..) = false.
      rw [if_pos hpar]
      have hidx : bits ≤ (i - 1) / 2 := by omega
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hidx))
    · -- a-register (= 0).
      rw [if_neg hpar]
      exact Nat.zero_testBit _
  -- extendBool dim phix = cuccaro_input_F q_start false 0 x  (as Nat → Bool).
  have hext : extendBool dim phix = cuccaro_input_F q_start false 0 x := by
    funext k
    unfold extendBool
    by_cases hkd : k < dim
    · rw [dif_pos hkd]
    · rw [dif_neg hkd]
      exact (hzero k (by omega)).symm
  -- Use the generic helper, then rewrite via the structured-output theorem.
  rw [gateToPerm_funboolNat]
  congr 1
  funext i
  unfold applyFin
  rw [hext]
  rw [cuccaro_addConstGate_structured_output bits q_start c x hc hx]

end FormalRV.Shor.GidneyInPlace.CuccaroGatePerm
