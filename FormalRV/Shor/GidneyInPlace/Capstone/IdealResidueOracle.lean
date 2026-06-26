/-
  FormalRV.Shor.GidneyInPlace.IdealResidueOracle — a CONCRETE exact residue oracle at the coset
  dimension `bits + cosetAnc w bits`, for window `w ≥ 2`.
  ════════════════════════════════════════════════════════════════════════════

  The coset-Shor capstone (`E2RunwayShorCapstone`) carries the IDEAL residue oracle `f_residueIdeal`
  at dimension `bits + cosetAnc w bits` (= `cosetDim = 2 + 2w + 3·bits`) as a hypothesis.  No existing
  EXACT modular multiplier sits at that tight budget: the windowed exact multiplier needs
  `cosetDim + 1` (the mod-N comparison flag), and the coset gate AT `cosetDim` is the APPROXIMATE one.

  KEY OBSERVATION.  The ideal oracle's INTERNAL window is independent of the coset machine's `w`.
  The verified exact `windowedModNEncodeGate` at INTERNAL WINDOW 1 has footprint `3·bits + 5`, which
  fits `cosetDim = 2 + 2w + 3·bits` exactly when `w ≥ 2` (`3·bits+5 ≤ 2+2w+3·bits ⟺ 3 ≤ 2w`).  And
  `encodeDataZeroAnc n anc x = nat_to_funbool (n+anc) (x·2^anc)` is INDEPENDENT of `anc` (for `anc ≥ 1`,
  `x < 2^n`): the data lives in the top `n` big-endian positions, everything else is `false`.  So the
  exact multiplier's round-trip transfers verbatim to the larger `cosetAnc` ancilla, and its
  well-typedness lifts by `Gate.wellTyped_le`.

  RESULT.  `idealResidueMultiplier` is an `EncodeRoundTripModMul N bits (cosetAnc w bits)` (for `w ≥ 2`)
  built by REUSING the verified `windowedModNEncodeGate` (internal window 1) — no new arithmetic.  Its
  `toVerifiedModMulFamily` gives `idealResidueFamily`, a `VerifiedModMulFamily` at the coset dimension,
  hence a genuine `ModMulImpl a N bits (cosetAnc w bits)` — discharging the κ-bound input the
  coset-Shor capstone needs from the ideal oracle.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.WindowedModNShor
import FormalRV.Shor.WindowedShorConnection
import FormalRV.Shor.GidneyInPlace.InPlace.Def.InPlaceCosetGate

namespace FormalRV.Shor.GidneyInPlace.IdealResidueOracle

open FormalRV.BQAlgo
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.BQAlgo.WindowedShorConnection
open FormalRV.BQAlgo.MultiplierInstances (modInv modInv_spec)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)

/-- **`encodeDataZeroAnc` is independent of the ancilla width** (for `anc, anc' ≥ 1`, `x < 2^n`).
    The data sits in the top `n` big-endian positions; every other position is `false`, regardless of
    how many zero ancillas are declared. -/
theorem encodeDataZeroAnc_anc_irrelevant {n anc anc' x : Nat}
    (hx : x < 2 ^ n) (h1 : 1 ≤ anc) (h1' : 1 ≤ anc') :
    encodeDataZeroAnc n anc x = encodeDataZeroAnc n anc' x := by
  have hfalse : ∀ a, 1 ≤ a → ∀ i, n ≤ i → encodeDataZeroAnc n a x i = false := by
    intro a ha i hi
    rcases Nat.lt_or_ge i (n + a) with hia | hia
    · obtain ⟨j, hj, hij⟩ : ∃ j, j < a ∧ i = n + j := ⟨i - n, by omega, by omega⟩
      rw [hij]; exact encodeDataZeroAnc_anc hx hj
    · unfold encodeDataZeroAnc FormalRV.Framework.nat_to_funbool
      have hz : n + a - 1 - i = 0 := by omega
      rw [hz, pow_zero, Nat.div_one]
      have heven : x * 2 ^ a % 2 = 0 := by
        have h2 : 2 ^ a = 2 ^ (a - 1) * 2 := by rw [← pow_succ]; congr 1; omega
        rw [h2, show x * (2 ^ (a - 1) * 2) = x * 2 ^ (a - 1) * 2 from by ring]
        exact Nat.mul_mod_left _ 2
      simp [heven]
  funext i
  rcases Nat.lt_or_ge i n with hi | hi
  · rw [encodeDataZeroAnc_data hx hi, encodeDataZeroAnc_data hx hi]
  · rw [hfalse anc h1 i hi, hfalse anc' h1' i hi]

/-- **The ideal exact residue multiplier at the coset dimension** (window `w ≥ 2`).  Its per-constant
    gate is the verified `windowedModNEncodeGate` at INTERNAL window 1 (footprint `3·bits+5`), reused at
    the larger total dimension `bits + cosetAnc w bits = cosetDim`.  Well-typedness lifts by
    `Gate.wellTyped_le` (needs `w ≥ 2`); the round-trip transfers from `windowedModNEncodeGate_apply`
    via `encodeDataZeroAnc_anc_irrelevant`. -/
noncomputable def idealResidueMultiplier (w bits N : Nat)
    (hw2 : 2 ≤ w) (hb1 : 1 ≤ bits) (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) :
    EncodeRoundTripModMul N bits (cosetAnc w bits) where
  gate := fun c => windowedModNEncodeGate 1 bits N bits (c % N) (modInv N c)
  wellTyped := fun c =>
    Gate.wellTyped_le
      (windowedModNEncodeGate_wellTyped 1 bits N bits (c % N) (modInv N c) (by norm_num)
        (by omega))
      (by unfold cosetAnc; omega)
  roundTrip := by
    intro c x hx hinv_ex
    have hN_pos : 0 < N := by omega
    have hNle : N ≤ 2 ^ bits := by omega
    have hxb : x < 2 ^ bits := lt_of_lt_of_le hx hNle
    have hcxb : (c * x) % N < 2 ^ bits := lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hNle
    have hanc1 : 1 ≤ cosetAnc w bits := by unfold cosetAnc; omega
    have hanc2 : 1 ≤ 2 * 1 + 2 * bits + 3 := by omega
    obtain ⟨mlt, minv⟩ := modInv_spec N c hN_pos hinv_ex
    have hcxN : (c % N) * x % N = (c * x) % N := by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [encodeDataZeroAnc_anc_irrelevant hxb hanc1 hanc2,
        encodeDataZeroAnc_anc_irrelevant hcxb hanc1 hanc2, ← hcxN]
    exact windowedModNEncodeGate_apply 1 bits bits N (c % N) (modInv N c) x
      (by norm_num) (by omega) hb1 hN_pos hN2 hx mlt
      (by rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]; exact minv)

/-- **The ideal residue oracle as a `VerifiedModMulFamily` at the coset dimension** (window `w ≥ 2`).
    A genuine `ModMulImpl a N bits (cosetAnc w bits)` family: every QPE iterate multiplies by
    `a^(2^i) mod N` on the encoded subspace.  This is exactly the ideal-oracle input the coset-Shor
    capstone needs to obtain the explicit Shor floor `κ/(log₂N)⁴` (via `Shor_correct_var`). -/
noncomputable def idealResidueFamily (w bits N a ainv0 : Nat)
    (hw2 : 2 ≤ w) (hb1 : 1 ≤ bits) (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1) :
    VerifiedShor.VerifiedModMulFamily a N bits (cosetAnc w bits) :=
  (idealResidueMultiplier w bits N hw2 hb1 hN1 hN2).toVerifiedModMulFamily a (by omega) ainv0 hN1
    h_inv0

end FormalRV.Shor.GidneyInPlace.IdealResidueOracle
