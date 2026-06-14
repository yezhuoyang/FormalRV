/-
  FormalRV.Shor.CosetEigenstate.CosetEigenstateShift — obligation (2), checkpoint 2 START:
  the eigenstate-from-cyclic-shift principle (the clean core of the coset eigenstate analysis).
  ════════════════════════════════════════════════════════════════════════════

  The deep coset-Shor content is the COSET APPROXIMATE-EIGENSTATE analysis: the coset-encoded
  Shor eigenstate must be an (approximate) eigenstate of the coset multiplier, with the right
  eigenvalue, so QPE extracts the phase.  This file proves the EXACT linear-algebra CORE of
  that analysis and reduces it to a SINGLE hypothesis (the orbit-shift):

    * `eigenstate_from_cyclic_shift` — for a linear operator `U` that CYCLICALLY SHIFTS an
      orbit of states (`U * ψ t = ψ (t+1)`, `t : ZMod r`) and any quasi-character coefficient
      family `χ` with `χ (t-1) = lam · χ t`, the superposition `∑_t χ t • ψ t` is an EIGENSTATE
      of `U` with eigenvalue `lam`.  (Reindex the orbit sum by the `+1` shift; `χ`'s
      quasi-character relation pulls out `lam`.)
    * `addChar_quasi_character` — ANY additive character `χ : AddChar (ZMod r) ℂ` is such a
      quasi-character with `lam = χ(-1)` (this IS character multiplicativity — no `.val`
      wraparound bookkeeping).
    * `rootOfUnity_quasi_character` / `eigenstate_rootOfUnity` — the concrete instantiation:
      for any `r`-th root of unity `ζ` (think `ζ = ω^{-s}`, `ω = exp(2πi/r)`), the standard
      character `χ t = ζ^{t.val}` gives `∑_t ζ^{t.val} • ψ t` as an eigenstate with eigenvalue
      `ζ⁻¹` (`= ω^s`) — the coset-encoded Shor eigenstate, modulo the orbit-shift.

  HOW THIS REDUCES THE DEEP GAP.  Instantiate `ψ t = |coset(a^t mod N)⟩` (the coset-encoded
  orbit, period `r = ord_N(a)`) and `U = ` the coset multiplier.  Then the coset eigenstate
  intertwining (`U` acts as the eigenvalue `ω^s`) follows from `eigenstate_rootOfUnity` GIVEN
  the single hypothesis `hshift : U |coset(a^t)⟩ = |coset(a^{t+1} mod N)⟩` — the per-residue
  COSET ORBIT-SHIFT.

  ⚠ THE GENUINE REMAINING DEEP PIECE (`hshift`).  Proving `hshift` for the literal coset
  multiplier is the real Gidney/Zalka approximate-eigenstate content and is NOT closed here:
  the IN-PLACE multiply `|v⟩ ↦ |cv mod 2^bits⟩` SCALES the coset runway step (`N ↦ cN`), so
  `|coset(k)⟩ ↦ |coset(ck mod N)⟩` holds only APPROXIMATELY / with a runway-coarsening
  deviation absorbed off-wrap.  `PhysCosetFold.physCoset_windowed_fold` gives the ADDER-level
  shift (window center `+c`, step `N` preserved); lifting that to the MULTIPLIER's orbit-shift
  (with the step-scaling deviation) is the remaining deep analysis.  This file makes that the
  SOLE residual hypothesis of the eigenstate intertwining.

  Self-contained Mathlib lemmas (no FormalRV deps).  Kernel-clean: no `sorry`, no
  `native_decide`, no axioms beyond the prelude.  De-risked via 3 parallel verified attempts.
-/
import Mathlib

namespace FormalRV.Shor.CosetEigenstate.CosetEigenstateShift

open scoped BigOperators

/-- **The eigenstate-from-cyclic-shift principle.**  A linear operator `U` that cyclically
    shifts an orbit of states (`U * ψ t = ψ (t+1)`) has, for any quasi-character coefficient
    family `χ` with `χ (t-1) = lam * χ t`, the eigenstate `∑ t, χ t • ψ t` with eigenvalue
    `lam`. -/
theorem eigenstate_from_cyclic_shift {D r : Nat} [NeZero r]
    (U : Matrix (Fin D) (Fin D) ℂ)
    (ψ : ZMod r → Matrix (Fin D) (Fin 1) ℂ) (χ : ZMod r → ℂ) (lam : ℂ)
    (hshift : ∀ t : ZMod r, U * ψ t = ψ (t + 1))
    (hχ : ∀ t : ZMod r, χ (t - 1) = lam * χ t) :
    U * (∑ t : ZMod r, χ t • ψ t) = lam • (∑ t : ZMod r, χ t • ψ t) := by
  rw [Matrix.mul_sum]
  simp_rw [Matrix.mul_smul, hshift]
  -- now: ∑ t, χ t • ψ (t+1) = lam • ∑ t, χ t • ψ t
  rw [Finset.smul_sum]
  -- transform RHS summand: lam • (χ t • ψ t) = χ (t-1) • ψ t
  have hRHS : ∀ t : ZMod r, lam • (χ t • ψ t) = χ (t - 1) • ψ t := by
    intro t
    rw [smul_smul, ← hχ t]
  simp_rw [hRHS]
  -- reindex LHS t ↦ t+1 via the shift equiv e := Equiv.addRight (1 : ZMod r), e t = t + 1
  rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod r)) (fun u => χ (u - 1) • ψ u)]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Equiv.coe_addRight, add_sub_cancel_right]

/-- Any additive character `χ : AddChar (ZMod r) ℂ` is a quasi-character in the sense required
    by `eigenstate_from_cyclic_shift`: `χ (t - 1) = χ(-1) * χ t` (character multiplicativity). -/
theorem addChar_quasi_character {r : Nat} [NeZero r] (χ : AddChar (ZMod r) ℂ) :
    ∀ t : ZMod r, χ (t - 1) = (χ (-1 : ZMod r)) * χ t := by
  intro t
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, mul_comm]

/-- Concrete root-of-unity instantiation. For any `r`-th root of unity `ζ` (think `ζ = ω^{-s}`
    with `ω = exp(2πi/r)`), the standard character `χ t = ζ^{t.val}` (`AddChar.zmodChar`)
    satisfies the quasi-character relation with eigenvalue `lam = ζ⁻¹`. -/
theorem rootOfUnity_quasi_character {r : Nat} [NeZero r] {ζ : ℂ} (hζ : ζ ^ r = 1) :
    ∀ t : ZMod r, (AddChar.zmodChar r hζ) (t - 1)
      = ζ⁻¹ * (AddChar.zmodChar r hζ) t := by
  intro t
  have hζne : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (NeZero.ne r)] at hζ
    exact zero_ne_one hζ
  have hone : (AddChar.zmodChar r hζ) (1 : ZMod r) = ζ := by
    have := AddChar.zmodChar_apply' hζ 1
    simpa using this
  have hlam : (AddChar.zmodChar r hζ) (-1 : ZMod r) = ζ⁻¹ := by
    have hmul : (AddChar.zmodChar r hζ) (-1 : ZMod r) * (AddChar.zmodChar r hζ) (1 : ZMod r)
        = 1 := by
      rw [← AddChar.map_add_eq_mul]
      simp [AddChar.map_zero_eq_one]
    rw [hone] at hmul
    exact eq_inv_of_mul_eq_one_left hmul
  rw [addChar_quasi_character (AddChar.zmodChar r hζ) t, hlam]

/-- **End-to-end: the coset-encoded eigenstate (modulo the orbit-shift).**  With a cyclically
    shifting `U` and the standard root-of-unity character, `∑ t, ζ^{t.val} • ψ t` is an
    eigenstate of `U` with eigenvalue `ζ⁻¹`.  Instantiating `ψ t = |coset(a^t mod N)⟩`,
    `ζ = ω^{-s}`, this is the coset Shor eigenstate — its only residual hypothesis is the
    per-residue coset orbit-shift `hshift` (the remaining deep piece; see file header). -/
theorem eigenstate_rootOfUnity {D r : Nat} [NeZero r]
    (U : Matrix (Fin D) (Fin D) ℂ)
    (ψ : ZMod r → Matrix (Fin D) (Fin 1) ℂ) {ζ : ℂ} (hζ : ζ ^ r = 1)
    (hshift : ∀ t : ZMod r, U * ψ t = ψ (t + 1)) :
    U * (∑ t : ZMod r, (AddChar.zmodChar r hζ) t • ψ t)
      = ζ⁻¹ • (∑ t : ZMod r, (AddChar.zmodChar r hζ) t • ψ t) :=
  eigenstate_from_cyclic_shift U ψ (AddChar.zmodChar r hζ) ζ⁻¹ hshift
    (rootOfUnity_quasi_character hζ)

end FormalRV.Shor.CosetEigenstate.CosetEigenstateShift
