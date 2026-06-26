/-
  Audit · Gidney–Ekerå 2021 · PADDING THE REVERSIBLE FAMILY TO A WIDE ANCILLA
  ════════════════════════════════════════════════════════════════════════════
  ADDITIVE de-risk module: re-types the verified windowed mod-N multiplier
  (`windowedModNMultiplier`, native ancilla `2·w + 2·bits + 3`) at ANY wider
  ancilla `ancBig ≥ 2·w + 2·bits + 3`, with idle padding wires, and restates the
  GE2021 consumer bridge `egate_matches_rev_of_modExpAtResidue` at that wide anc.

  ────────────────────────────────────────────────────────────────────────────
  WHY.  To make the GE2021 Shor bound ride a measured `EGate eg` that contains the
  LITERAL stacked `multiplyAddAt` (which needs the NATIVE wide ancilla `ancBig`,
  not the canonical `2·w + 2·bits + 3`), the consumer
  `ShorComposedFinal.egate_matches_rev_of_modExpAtResidue` compares `eg` against the
  reversible family `windowedModNMultiplier_verifiedModMulFamily`, which lives at
  ancilla `2·w + 2·bits + 3`.  To compare at `ancBig`, the reversible family must be
  PADDED with idle ancilla up to `ancBig`.  This module supplies that padding and
  the wide-anc bridge, WITHOUT editing `ShorComposedFinal` (purely additive); the
  existing native version is the `ancBig := 2·w + 2·bits + 3` special case.

  ────────────────────────────────────────────────────────────────────────────
  THE PADDING IS GENUINELY FREE (no verified file weakened).
  ────────────────────────────────────────────────────────────────────────────
  The SAME gate term `windowedModNEncodeGate w bits N numWin c cinv` is reused at
  the wider dimension `bits + ancBig`.  Three facts make this sound:

    * **Well-typedness lifts**: `Gate.WellTyped.mono ∘ windowedModNEncodeGate_wellTyped`
      — a gate well-typed at `bits + (2w+2bits+3)` is well-typed at any `bits + ancBig`
      with `ancBig ≥ 2w+2bits+3`.
    * **The round trip lifts** (`windowedModNEncodeGate_roundTrip_pad`, §1): on the
      low wires `[0, bits + (2w+2bits+3))` the wide input `encodeDataZeroAnc bits ancBig x`
      AGREES with the canonical `encodeDataZeroAnc bits (2w+2bits+3) x` (data bits
      identical, padded ancilla still `false`), so `Gate.applyNat_congr` transports
      `windowedModNEncodeGate_apply` to the wide layout; on the high wires
      `≥ bits + (2w+2bits+3)` the gate is FRAME-idle (`Gate.applyNat_oob`), leaving the
      input — which is `false` there because it is the padded-ancilla region of
      `encodeDataZeroAnc` (`encodeDataZeroAnc_anc` / `_oob`).
    * **The `EncodeRoundTripModMul` instance lifts** (`paddedRevFamily`, §2): feed the
      wide round trip through `toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc`.

  Mirrors the frame argument of `ge2021_adaptIn_clean`
  (`ModExpAtLayoutAdapterInstance`): low wires via `_congr`, high wires via `_oob`.

  Kernel-clean: no `sorry`, no `native_decide`, axioms exactly
  `[propext, Classical.choice, Quot.sound]`.
-/
import FormalRV.Audit.GidneyEkera2021.ShorComposedFinal

namespace FormalRV.Audit.GidneyEkera2021.PaddedRevFamily

open FormalRV.Framework FormalRV.BQAlgo
open FormalRV.SQIRPort
open VerifiedShor
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.WindowedComposedAt
open FormalRV.Shor.EGateToUnitaryBridge
open FormalRV.BQAlgo.WindowedShorConnection
open FormalRV.BQAlgo.MultiplierInstances
open FormalRV.BQAlgo.WindowedModNShor

noncomputable section

/-! ## §0. Agreement of the canonical and the padded `encodeDataZeroAnc` inputs.

On the low wire band `[0, bits + (2w+2bits+3))` the WIDE encoding
`encodeDataZeroAnc bits ancBig x` agrees with the CANONICAL encoding
`encodeDataZeroAnc bits (2w+2bits+3) x`: the data bits `[0, bits)` are
anc-independent (`encodeDataZeroAnc_data`), and the canonical ancilla band
`[bits, bits + (2w+2bits+3))` is `false` in BOTH (`encodeDataZeroAnc_anc`). -/

/-- **Low-band agreement of the padded and canonical encodings.**  For `x < 2^bits`
    and `2w+2bits+3 ≤ ancBig`, the wide input `encodeDataZeroAnc bits ancBig x` and
    the canonical input `encodeDataZeroAnc bits (2w+2bits+3) x` agree on every wire
    `p < bits + (2w+2bits+3)`.  (Data bits anc-independent; canonical ancilla band
    `false` in both.) -/
theorem encodeDataZeroAnc_low_agree
    (w bits : Nat) {ancBig x : Nat}
    (hxbits : x < 2 ^ bits)
    (hpad : 2 * w + 2 * bits + 3 ≤ ancBig) :
    ∀ p, p < bits + (2 * w + 2 * bits + 3) →
      encodeDataZeroAnc bits ancBig x p
        = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x p := by
  intro p hp
  by_cases hpb : p < bits
  · -- data band: both equal `nat_to_funbool bits x p`, anc-independent.
    rw [encodeDataZeroAnc_data hxbits hpb, encodeDataZeroAnc_data hxbits hpb]
  · -- canonical-ancilla band `[bits, bits + (2w+2bits+3))`: both `false`.
    have hj : p - bits < 2 * w + 2 * bits + 3 := by omega
    have hjBig : p - bits < ancBig := by omega
    have hp_eq : p = bits + (p - bits) := by omega
    rw [hp_eq, encodeDataZeroAnc_anc hxbits hjBig, encodeDataZeroAnc_anc hxbits hj]

/-! ## §1. The padded round trip. -/

/-- **★ DELIVERABLE (1) — the round trip lifts to a wider ancilla ★.**  For
    `2w+2bits+3 ≤ ancBig`, `x < N`, `N ≤ 2^bits`, and an invertible constant
    (`cinv < N`, `c·cinv ≡ 1`), the SAME gate `windowedModNEncodeGate w bits N numWin
    c cinv` round-trips the WIDE canonical layout:

      `Gate.applyNat g (encodeDataZeroAnc bits ancBig x) = encodeDataZeroAnc bits ancBig ((c·x)%N)`.

    Proof.  Reconstruct the output function via
    `Gate.applyNat_eq_encodeDataZeroAnc_of_data_anc`.  On the low band
    `[0, bits + (2w+2bits+3))` `Gate.applyNat_congr` (against `encodeDataZeroAnc_low_agree`)
    reduces the wide action to the CANONICAL action `windowedModNEncodeGate_apply`, whose
    data bits decode `(c·x)%N` (`encodeDataZeroAnc_data`) and whose canonical-ancilla
    band is `false` (`encodeDataZeroAnc_anc`).  On the padded band
    `[bits + (2w+2bits+3), bits + ancBig)` and beyond, the gate is FRAME-idle
    (`Gate.applyNat_oob`), leaving the input, which is `false` there because it is the
    padded-ancilla / out-of-range region of `encodeDataZeroAnc` (`encodeDataZeroAnc_anc`/`_oob`). -/
theorem windowedModNEncodeGate_roundTrip_pad
    (w bits numWin N c cinv : Nat) {ancBig x : Nat}
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hx : x < N) (hcinv : cinv < N) (hinv : c * cinv % N = 1)
    (hpad : 2 * w + 2 * bits + 3 ≤ ancBig) :
    Gate.applyNat (windowedModNEncodeGate w bits N numWin c cinv)
        (encodeDataZeroAnc bits ancBig x)
      = encodeDataZeroAnc bits ancBig (c * x % N) := by
  -- abbreviations.
  set cAnc : Nat := 2 * w + 2 * bits + 3 with hcAnc
  set g : Gate := windowedModNEncodeGate w bits N numWin c cinv with hg
  have hN_le : N ≤ 2 ^ bits := by omega
  have hxbits : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN_le
  have hyN : c * x % N < N := Nat.mod_lt _ hN_pos
  have hybits : c * x % N < 2 ^ bits := Nat.lt_of_lt_of_le hyN hN_le
  have hancBig_pos : 0 < ancBig := by omega
  -- well-typedness at the canonical width and (by monotonicity) at the wide width.
  have hwt_can : Gate.WellTyped (bits + cAnc) g :=
    windowedModNEncodeGate_wellTyped w bits N numWin c cinv hw hbits
  have hwt_big : Gate.WellTyped (bits + ancBig) g :=
    Gate.WellTyped.mono hwt_can (by omega)
  -- the CANONICAL round trip (native ancilla) — the verified workhorse.
  have h_can :
      Gate.applyNat g (encodeDataZeroAnc bits cAnc x)
        = encodeDataZeroAnc bits cAnc (c * x % N) :=
    windowedModNEncodeGate_apply w bits numWin N c cinv x hw hbits hb1 hN_pos hN2 hx hcinv hinv
  -- the wide and canonical inputs agree on the low band `[0, bits + cAnc)`.
  have h_agree : ∀ p, p < bits + cAnc →
      encodeDataZeroAnc bits ancBig x p = encodeDataZeroAnc bits cAnc x p :=
    encodeDataZeroAnc_low_agree w bits hxbits hpad
  -- low band: wide action = canonical action (congr), then decode via the canonical RT.
  -- high band: gate is frame-idle, input is the padded-ancilla / oob region (false).
  apply Gate.applyNat_eq_encodeDataZeroAnc_of_data_anc hancBig_pos hybits hwt_big
  · -- data band `[0, bits)`: output bit = `nat_to_funbool bits ((c·x)%N) i`.
    intro i hi
    have hlt : i < bits + cAnc := by omega
    rw [Gate.applyNat_congr hwt_can _ _ h_agree i hlt, h_can,
        encodeDataZeroAnc_data hybits hi]
  · -- ancilla band `[bits, bits + ancBig)`: output bit `false`.
    intro j hj
    by_cases hjc : bits + j < bits + cAnc
    · -- inside the canonical ancilla band: use the canonical RT, ancilla `false`.
      have hjcAnc : j < cAnc := by omega
      rw [Gate.applyNat_congr hwt_can _ _ h_agree (bits + j) hjc, h_can,
          encodeDataZeroAnc_anc hybits hjcAnc]
    · -- padded ancilla band `[bits + cAnc, bits + ancBig)`: gate is frame-idle.
      have hge : bits + cAnc ≤ bits + j := Nat.not_lt.mp hjc
      rw [Gate.applyNat_oob hwt_can _ hge]
      -- the wide input is `false` on the padded-ancilla wire `bits + j` (j < ancBig).
      exact encodeDataZeroAnc_anc hxbits hj
  · -- input OOB `≥ bits + ancBig`: `false`.
    intro i hi
    exact encodeDataZeroAnc_oob hancBig_pos hi

/-! ## §2. The padded `EncodeRoundTripModMul` instance at the wide ancilla. -/

/-- **★ DELIVERABLE (2) — the verified family re-typed at the wide ancilla ★.**  The
    EXACT verified gate `windowedModNEncodeGate w bits N numWin (c%N) (modInv N c)`,
    re-typed at `EncodeRoundTripModMul N bits ancBig` for any `ancBig ≥ 2w+2bits+3`.
    Well-typedness via `Gate.WellTyped.mono ∘ windowedModNEncodeGate_wellTyped`; the
    round-trip field via DELIVERABLE (1).  The native instance
    `windowedModNMultiplier … : EncodeRoundTripModMul N bits (2w+2bits+3)` is exactly
    the `ancBig := 2w+2bits+3` case (definitionally the same `gate` field). -/
noncomputable def paddedRevFamily
    (w bits numWin N : Nat) {ancBig : Nat}
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hpad : 2 * w + 2 * bits + 3 ≤ ancBig) :
    EncodeRoundTripModMul N bits ancBig where
  gate := fun c => windowedModNEncodeGate w bits N numWin (c % N) (modInv N c)
  wellTyped := fun c =>
    Gate.WellTyped.mono
      (windowedModNEncodeGate_wellTyped w bits N numWin (c % N) (modInv N c) hw hbits)
      (by omega)
  roundTrip := by
    intro c x hx hc
    have hN_pos : 0 < N := by omega
    obtain ⟨h_lt, h_inv⟩ := modInv_spec N c hN_pos hc
    have h_inv' : (c % N) * modInv N c % N = 1 := by
      rw [Nat.mod_mul_mod]; exact h_inv
    show Gate.applyNat
        (windowedModNEncodeGate w bits N numWin (c % N) (modInv N c))
        (encodeDataZeroAnc bits ancBig x)
      = encodeDataZeroAnc bits ancBig ((c * x) % N)
    rw [windowedModNEncodeGate_roundTrip_pad w bits numWin N (c % N) (modInv N c)
          hw hbits hb1 hN_pos hN2 hx h_lt h_inv' hpad,
        Nat.mod_mul_mod]

/-- **The padded family as a `VerifiedModMulFamily` at the wide ancilla.**  One line
    via `EncodeRoundTripModMul.toVerifiedModMulFamily`, given a base inverse
    `a·ainv0 ≡ 1 (mod N)`.  Carries the full Shor success bound at ancilla `ancBig`
    (`shorCorrect`), exactly like the native `windowedModNMultiplier_verifiedModMulFamily`
    but with the wide idle padding. -/
noncomputable def paddedRevFamily_verifiedModMulFamily
    (w bits numWin N a ainv0 : Nat) {ancBig : Nat}
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (hpad : 2 * w + 2 * bits + 3 ≤ ancBig) :
    VerifiedModMulFamily a N bits ancBig :=
  (paddedRevFamily w bits numWin N hw hbits hb1 hN1 hN2 hpad).toVerifiedModMulFamily
    a (by omega) ainv0 hN1 h_inv0

/-! ## §3. The wide-ancilla restatement of the consumer bridge.

`ShorComposedFinal.egate_matches_rev_of_modExpAtResidue` is the discharge that ties
the bound to a measured EGate `eg` whose `applyNat` realises the residue encoding
(`ModExpAtEncodedMatchesResidue`), but it is HARD-WIRED to the native ancilla
`2w+2bits+3` (it uses `windowedModNMultiplier_verifiedModMulFamily`).  The wide-anc
version below mirrors it exactly but with a FREE `ancBig ≥ 2w+2bits+3`, using the
padded family `paddedRevFamily_verifiedModMulFamily` and the padded round trip
DELIVERABLE (1) in place of the native-anc family.  The native version is the
`ancBig := 2w+2bits+3` special case. -/

/-- **★ DELIVERABLE (3) — the wide-ancilla consumer bridge ★.**  Anc-generic
    restatement of `egate_matches_rev_of_modExpAtResidue`: IF the measured family
    `eg`'s `applyNat` realises the canonical residue encoding at ancilla `ancBig`
    (`ModExpAtEncodedMatchesResidue … ancBig …`), THEN the PADDED verified family
    `paddedRevFamily_verifiedModMulFamily … ancBig` and `eg` agree on every encoded
    basis state at ancilla `ancBig`.  This is the `egate_matches_rev` field shape for a
    measured `eg` that lives at the NATIVE wide ancilla of the stacked `multiplyAddAt`
    (rather than the canonical `2w+2bits+3`).

    Proof.  Same shape as the native version: rewrite by the residue identity, build the
    inverse witness (`modInv_spec` + `mul_pow_mod_one`), invoke the padded round trip
    DELIVERABLE (1) for the reversible side, then close with `uc_eval_toUCom_acts_on_basis`.
    The padded family's `family i = Gate.toUCom (bits + ancBig) (windowedModNEncodeGate …)`
    holds definitionally (`toVerifiedModMulFamily.family`). -/
theorem egate_matches_rev_of_modExpAtResidue_pad
    (w bits numWin N a ainv0 : Nat) {ancBig : Nat}
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (hpad : 2 * w + 2 * bits + 3 ≤ ancBig)
    (eg : Nat → EGate)
    (H : FormalRV.Audit.GidneyEkera2021.ShorComposedFinal.ModExpAtEncodedMatchesResidue
          a N bits ancBig eg
          (fun _ x => FormalRV.BQAlgo.encodeDataZeroAnc bits ancBig x)) :
    ∀ i x, x < N →
      Framework.uc_eval
          ((paddedRevFamily_verifiedModMulFamily w bits numWin N a ainv0
              hw hbits hb1 hN1 hN2 h_inv0 hpad).family i)
        * f_to_vec (bits + ancBig)
            (FormalRV.BQAlgo.encodeDataZeroAnc bits ancBig x)
        = f_to_vec (bits + ancBig)
            (EGate.applyNat (eg i)
              (FormalRV.BQAlgo.encodeDataZeroAnc bits ancBig x)) := by
  intro i x hx
  -- the measured side IS the canonical residue encoding (the named residual `H`).
  rw [H.block_matches_residue i x hx]
  have hN_pos : 0 < N := by omega
  -- the inverse witness for the iterate constant `a^(2^i)`.
  obtain ⟨_h_lt, h_inv⟩ := modInv_spec N (a ^ (2 ^ i)) hN_pos
    ⟨ainv0 ^ (2 ^ i), by
      rw [Nat.mul_mod]; exact mul_pow_mod_one a ainv0 N (2 ^ i) hN1 h_inv0⟩
  -- the reversible side's basis action: the canonical encoding of `(a^(2^i)·x) % N`.
  have h_rt :
      Gate.applyNat
          (windowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
            (modInv N (a ^ (2 ^ i))))
          (FormalRV.BQAlgo.encodeDataZeroAnc bits ancBig x)
        = FormalRV.BQAlgo.encodeDataZeroAnc bits ancBig
            (((a ^ (2 ^ i)) * x) % N) := by
    have h_inv' : ((a ^ (2 ^ i)) % N) * modInv N (a ^ (2 ^ i)) % N = 1 := by
      rw [Nat.mod_mul_mod]; exact h_inv
    rw [windowedModNEncodeGate_roundTrip_pad w bits numWin N ((a ^ (2 ^ i)) % N)
          (modInv N (a ^ (2 ^ i))) hw hbits hb1 hN_pos hN2 hx _h_lt h_inv' hpad,
        Nat.mod_mul_mod]
  -- `family i = Gate.toUCom (bits + ancBig) (windowedModNEncodeGate …)` definitionally.
  show Framework.uc_eval
        (Gate.toUCom (bits + ancBig)
          (windowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
            (modInv N (a ^ (2 ^ i)))))
      * f_to_vec (bits + ancBig) _
      = f_to_vec (bits + ancBig) _
  rw [uc_eval_toUCom_acts_on_basis (bits + ancBig)
        (windowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
          (modInv N (a ^ (2 ^ i))))
        (Gate.WellTyped.mono
          (windowedModNEncodeGate_wellTyped w bits N numWin ((a ^ (2 ^ i)) % N)
            (modInv N (a ^ (2 ^ i))) hw hbits)
          (by omega))
        (FormalRV.BQAlgo.encodeDataZeroAnc bits ancBig x),
      h_rt]

/-! ## §4. The native version is the `ancBig := 2w+2bits+3` special case.

A sanity equation: at `ancBig := 2w+2bits+3`, the padded round trip
DELIVERABLE (1) is exactly the native `windowedModNEncodeGate_apply`, and the padded
family DELIVERABLE (2) lives at the SAME ancilla as `windowedModNMultiplier`.  This
records that the additive padding does NOT change anything at the native width — no
verified result is weakened.  (Stated as the round-trip equation; both sides reduce to
`windowedModNEncodeGate_apply` definitionally up to the `2*w+2*bits+3 ≤ 2*w+2*bits+3`
padding hypothesis being `le_refl`.) -/

/-- **The padded round trip degenerates to the native round trip at `ancBig := 2w+2bits+3`.**
    Confirms DELIVERABLE (1) is a strict generalisation of `windowedModNEncodeGate_apply`;
    the existing native multiplier is unchanged. -/
theorem windowedModNEncodeGate_roundTrip_pad_native
    (w bits numWin N c cinv x : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hx : x < N) (hcinv : cinv < N) (hinv : c * cinv % N = 1) :
    Gate.applyNat (windowedModNEncodeGate w bits N numWin c cinv)
        (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)
      = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) (c * x % N) :=
  windowedModNEncodeGate_roundTrip_pad w bits numWin N c cinv
    hw hbits hb1 hN_pos hN2 hx hcinv hinv (le_refl _)

end

end FormalRV.Audit.GidneyEkera2021.PaddedRevFamily
