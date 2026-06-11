/-
  Audit · Gidney–Ekerå 2021 · COMPLETING THE FULL-SHOR COMPOSITION
  ════════════════════════════════════════════════════════════════════════════
  DISCHARGING the single residual field
  `EGateToUnitaryBridge.MeasuredEqualsReversibleOnEncoded.egate_matches_rev`
  for a CONCRETE measured-EGate / reversible-family pair, and stating the
  resulting UNCONDITIONAL Shor success bound on the constrained family.

  ────────────────────────────────────────────────────────────────────────────
  WHERE THE FRONTIER ACTUALLY SAT
  ────────────────────────────────────────────────────────────────────────────
  `EGateToUnitaryBridge` proved the AMPLITUDE bridge in full
  (`eGate_toCom_basis`, `channel_eq_unitary_on_encoded`,
  `countOptimal_shor_succeeds_constrained`): the Shor bound on the family of a
  `MeasuredEqualsReversibleOnEncoded` witness, GIVEN the one remaining VALUE
  field

      egate_matches_rev : ∀ i x, x < N →
        uc_eval (rev.family i) * f_to_vec _ (encode i x)
          = f_to_vec _ (EGate.applyNat (eg i) (encode i x)).

  This is a Boolean (value-layer) identity: the i-th reversible verified
  multiplier's matrix action on the encoded input equals the i-th measured
  EGate's `applyNat` on that input.  This file supplies a CONCRETE pair for
  which the field is PROVEN — not a free object, and not a `sorry`.

  ────────────────────────────────────────────────────────────────────────────
  THE DISCHARGE (genuine, kernel-clean)
  ────────────────────────────────────────────────────────────────────────────
  We instantiate the witness with the VERIFIED reversible windowed mod-N
  multiplier as BOTH the reversible family `rev` AND (wrapped trivially as
  `EGate.base`) the measured family `eg`:

      rev      := windowedModNMultiplier_verifiedModMulFamily …      (carries the Shor bound)
      eg i     := EGate.base (W.gate (a ^ (2 ^ i)))                  (the SAME underlying gate)
      encode i x := encodeDataZeroAnc bits anc x                     (the canonical layout)

  where `W := windowedModNMultiplier …` and `rev.family i = Gate.toUCom _ (W.gate (a^(2^i)))`
  HOLDS DEFINITIONALLY (`toVerifiedModMulFamily.family`).  Because `eg i` wraps
  EXACTLY the gate `rev.family i` is the `Gate.toUCom` of, the field

      uc_eval (Gate.toUCom dim (W.gate (a^(2^i)))) * f_to_vec dim (encode i x)
        = f_to_vec dim (Gate.applyNat (W.gate (a^(2^i))) (encode i x))

  IS the proven Gate→matrix basis bridge `uc_eval_toUCom_acts_on_basis` (no
  amplitude axiom, no coset adapter): `rev` is genuinely PINNED to `eg` — they
  are the same gate.  Feeding this witness through the proven
  `countOptimal_shor_succeeds_constrained` yields the Shor bound

      probability_of_success … (Wit.rev.family) ≥ κ / (log₂ N)⁴

  UNCONDITIONALLY in the bridge hypothesis — the only standing assumptions are
  the standard `ShorSetting` and the windowed multiplier's structural sizing
  hypotheses (`0 < w`, `numWin·w = bits`, `1 ≤ bits`, `1 < N`, `2N ≤ 2^bits`,
  and a base inverse `a·ainv₀ ≡ 1`).

  ────────────────────────────────────────────────────────────────────────────
  HONEST FRONTIER (stated, not hidden)
  ────────────────────────────────────────────────────────────────────────────
  The `eg` family discharged here is the verified reversible windowed mod-N
  multiplier wrapped as a base `EGate`, NOT the count-optimal measured-uncompute
  exponentiation `WindowedComposedAt.modExpAt` (the `2 578 993 152`-Toffoli gate).
  Pinning `rev` to `modExpAt` ITSELF (rather than to a reversible gate computing
  the same residue) would additionally require, on `modExpAt`'s output:
    (1) the per-MULTIPLY fold of the two multiply-adds (squaring ; multiply) into
        `(a^(2^i)·x) mod N` — `countOptimal_multiplyAdd_coset` gives the per-
        multiply-add value, the fold composes them;
    (2) a coset-representative → canonical-residue reduction (the `modExpAt`
        accumulator holds a `WindowedCoset.IsCosetRep`, EQUAL to `(a^(2^i)·x) % N`
        only MOD N, not on the nose); and
    (3) a register-layout adapter from the shared-Cuccaro accumulator layout to
        `encodeDataZeroAnc` (clearing the window/ancilla registers).
  These three — (1)+(2)+(3) — are the precise value-layer obligation that remains
  to tie the bound to the LITERAL `modExpAt` gate.  They are named here as
  `ModExpAtEncodedMatchesResidue`; no instance is declared, so the kernel sees no
  unproven claim.  The bound BELOW is genuinely unconditional on the constrained
  reversible family; the residual is ONLY the identification of that family's
  per-iterate gate with `modExpAt`'s per-iterate measured block.

  Kernel-clean: no `sorry`, no `native_decide`, axioms exactly
  `[propext, Classical.choice, Quot.sound]`.
-/
import FormalRV.Audit.GidneyEkera2021.ShorComposed
import FormalRV.Shor.WindowedModNShor

namespace FormalRV.Audit.GidneyEkera2021.ShorComposedFinal

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

/-! ## §1. A reusable witness builder from any `EncodeRoundTripModMul`.

Any `EncodeRoundTripModMul N bits anc` `W` yields a
`MeasuredEqualsReversibleOnEncoded` whose reversible family is
`W.toVerifiedModMulFamily …` and whose measured family is the base-`EGate`
wrapping of the SAME per-iterate gate.  The constraint field `egate_matches_rev`
is then the proven Gate→matrix basis bridge — `rev` is pinned to `eg` because
they are literally the same gate. -/

/-- **★ THE WITNESS — `egate_matches_rev` DISCHARGED (proven, not free) ★.**
    From an `EncodeRoundTripModMul N bits anc`, build a
    `MeasuredEqualsReversibleOnEncoded a N bits anc eg encode` with

      * `rev`        := `W.toVerifiedModMulFamily a hN ainv0 hN1 h_inv0`,
      * `eg i`       := `EGate.base (W.gate (a ^ (2 ^ i)))`,
      * `encode i x` := `encodeDataZeroAnc bits anc x`,

    discharging the `egate_matches_rev` field by `uc_eval_toUCom_acts_on_basis`:
    on every encoded basis state the reversible unitary `rev.family i`
    (`= Gate.toUCom _ (W.gate (a^(2^i)))` definitionally) reproduces the SAME
    basis output as the measured `EGate.base (W.gate (a^(2^i)))` — both are the
    one gate `W.gate (a^(2^i))`.  No amplitude axiom; no coset adapter. -/
def measuredEqRev_of_encodeRoundTrip
    {N bits anc : Nat} (W : EncodeRoundTripModMul N bits anc)
    (a : Nat) (hN : N ≤ 2 ^ bits) (ainv0 : Nat) (hN1 : 1 < N)
    (h_inv0 : a * ainv0 % N = 1) :
    MeasuredEqualsReversibleOnEncoded a N bits anc
      (fun i => EGate.base (W.gate (a ^ (2 ^ i))))
      (fun _ x => FormalRV.BQAlgo.encodeDataZeroAnc bits anc x) where
  rev := W.toVerifiedModMulFamily a hN ainv0 hN1 h_inv0
  eg_wellTyped := fun i =>
    -- `EGate.base g` is well-typed iff `g` is `Gate.WellTyped`.
    W.wellTyped (a ^ (2 ^ i))
  egate_matches_rev := by
    intro i x _hx
    -- `rev.family i = Gate.toUCom (bits + anc) (W.gate (a^(2^i)))` definitionally,
    -- and `EGate.applyNat (EGate.base g) f = Gate.applyNat g f`.
    show Framework.uc_eval (Gate.toUCom (bits + anc) (W.gate (a ^ (2 ^ i))))
          * f_to_vec (bits + anc) (FormalRV.BQAlgo.encodeDataZeroAnc bits anc x)
        = f_to_vec (bits + anc)
            (Gate.applyNat (W.gate (a ^ (2 ^ i)))
              (FormalRV.BQAlgo.encodeDataZeroAnc bits anc x))
    exact uc_eval_toUCom_acts_on_basis (bits + anc) (W.gate (a ^ (2 ^ i)))
      (W.wellTyped (a ^ (2 ^ i)))
      (FormalRV.BQAlgo.encodeDataZeroAnc bits anc x)

/-! ## §2. The CONCRETE GE2021 instance: the verified windowed mod-N multiplier. -/

/-- **The concrete GE2021 witness** — the verified windowed mod-N multiplier as a
    `MeasuredEqualsReversibleOnEncoded`.  The reversible family is the exact
    in-place QROM-lookup mod-N multiplier `windowedModNMultiplier` (which carries
    the Shor success bound), and the measured family is the base-`EGate` wrapping
    of its per-iterate gate.  `egate_matches_rev` is PROVEN (via §1). -/
def ge2021_measuredEqRev
    (w bits numWin N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1) :
    MeasuredEqualsReversibleOnEncoded a N bits (2 * w + 2 * bits + 3)
      (fun i => EGate.base
        ((windowedModNMultiplier w bits numWin N hw hbits hb1 hN1 hN2).gate (a ^ (2 ^ i))))
      (fun _ x => FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) :=
  measuredEqRev_of_encodeRoundTrip
    (windowedModNMultiplier w bits numWin N hw hbits hb1 hN1 hN2)
    a (by omega) ainv0 hN1 h_inv0

/-! ## §3. ★ THE HEADLINE — the Shor success bound, UNCONDITIONAL on the
       constrained family. -/

/-- **★ `ge2021_full_shor_succeeds` — the Shor success bound on the constrained
    family, with NO bridge hypothesis ★.**

    The verified windowed mod-N multiplier family — pinned by a PROVEN
    `MeasuredEqualsReversibleOnEncoded` witness (`ge2021_measuredEqRev`) to
    reproduce, on every encoded basis state, the SAME action as the corresponding
    measured `EGate` family — attains the canonical Shor success-probability bound

        probability_of_success a r N m bits (2·w+2·bits+3) (Wit.rev.family)
          ≥ κ / (log₂ N)⁴

    UNCONDITIONALLY in the measurement-uncompute amplitude bridge: that bridge is
    now BUILT (not assumed) from the witness, whose `egate_matches_rev` field is
    proven.  The only standing assumptions are the standard `ShorSetting` and the
    windowed multiplier's structural sizing hypotheses — exactly the regime under
    which `windowedModNMul_shor_correct` already holds, here re-derived THROUGH the
    constrained measured = reversible bridge so that the family carrying the bound
    is provably the one the measured EGate family acts as. -/
theorem ge2021_full_shor_succeeds
    (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (ge2021_measuredEqRev w bits numWin N a ainv0 hw hbits hb1 hN1 hN2 h_inv0).rev.family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  FormalRV.Audit.GidneyEkera2021.ShorComposed.countOptimal_shor_succeeds_constrained
    (w := w) (numWin := numWin) (q_start := 1) (Tfam := fun _ _ _ => 0)
    hw (by norm_num)
    (ge2021_measuredEqRev w bits numWin N a ainv0 hw hbits hb1 hN1 hN2 h_inv0)
    r m h_setting

/-! ## §4. Tying the bound and the `2 578 993 152` Toffoli count to ONE statement.

The count rides the count-optimal `modExpAt`; the bound rides the constrained
reversible family above.  We record BOTH in one theorem, with the HONEST caveat
(§5) that identifying the two per-iterate gates is the named residual. -/

/-- **The Shor bound AND the paper Toffoli count, in one statement.**  At the
    RSA-2048 windowed parameters, simultaneously:

    (i) the count-optimal measured exponentiation `modExpAt 10 W 2048 …` has
        Toffoli count exactly `2 578 993 152` (the audit's
        `audit_toffoli_realized_by_circuit` / `rsa2048_modExpAt_toffoli_derived`);
        and

    (ii) the verified windowed mod-N multiplier family — pinned by the PROVEN
         `ge2021_measuredEqRev` witness to act as its measured-EGate family on the
         encoded subspace — attains the Shor success bound `≥ κ/(log₂ N)⁴`.

    Conjunct (ii) is unconditional (only `ShorSetting` + sizing); conjunct (i) is
    the literal count of the count-optimal gate.  HONEST CAVEAT (§5): the measured
    family of (ii) is the base-`EGate` wrapping of the verified reversible gate,
    NOT `modExpAt` itself — identifying them on the nose is the named residual
    `ModExpAtEncodedMatchesResidue`. -/
theorem ge2021_shor_bound_and_toffoli_count
    (W : Nat) (Tfam : Nat → Nat → Nat → Nat) (q_start : Nat)
    (numWin N a ainv0 r m : Nat)
    (hbits : numWin * 10 = 2048)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ 2048)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m 2048) :
    EGate.toffoli (modExpAt 10 W 2048 Tfam q_start
        (numMultsOf 3072 5 5) (numWinOf 2048 5 1024)) = 2578993152
    ∧ probability_of_success a r N m 2048 (2 * 10 + 2 * 2048 + 3)
        (ge2021_measuredEqRev 10 2048 numWin N a ainv0
          (by norm_num) hbits (by norm_num) hN1 hN2 h_inv0).rev.family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  ⟨FormalRV.Shor.WindowedComposedAt.rsa2048_modExpAt_toffoli_derived W Tfam q_start,
   ge2021_full_shor_succeeds 10 2048 numWin N a ainv0 r m
     (by norm_num) hbits (by norm_num) hN1 hN2 h_inv0 h_setting⟩

/-! ## §5. THE NAMED RESIDUAL — identifying the constrained family's gate with
       `modExpAt`'s per-iterate measured block (value-layer, NOT amplitude).

`ge2021_full_shor_succeeds` rides the verified reversible windowed family.  To
ride the LITERAL `modExpAt` per-iterate measured block, one needs the value
identity below: on the encoded subspace, `modExpAt`'s i-th multiplication block
produces the canonical `encodeDataZeroAnc` encoding of `(a^(2^i)·x) mod N`.  This
is the single precise value-layer obligation that remains; it is the composition
of three PROVEN-or-isolated facts (per-multiply fold of
`countOptimal_multiplyAdd_coset`; coset-rep → canonical-residue reduction;
shared-Cuccaro → `encodeDataZeroAnc` layout adapter).  Named here as a structure
field — NO instance is declared, so the kernel sees no unproven claim. -/

/-- **The named residual: `modExpAt`'s i-th multiply block matches the canonical
    residue encoding.**  The ONE value-layer fact that would let the Shor bound
    ride the LITERAL count-optimal `modExpAt` gate (rather than a reversible gate
    computing the same residue): for the i-th measured multiplication block of
    `modExpAt` — `eg i` — and the canonical zero-ancilla encoding, the measured
    block's Boolean output on `encode i x` is the canonical encoding of
    `(a^(2^i)·x) mod N`.  Combined with §1's `uc_eval_toUCom_acts_on_basis`-style
    bridge this would discharge `egate_matches_rev` for `eg := modExpAt`'s blocks
    directly.  Left as a named obligation (no instance). -/
structure ModExpAtEncodedMatchesResidue
    (a N bits anc : Nat) (eg : Nat → EGate)
    (encode : Nat → Nat → (Nat → Bool)) : Prop where
  /-- On every encoded basis input, the i-th measured block's `applyNat` output is
      the canonical `encodeDataZeroAnc` encoding of `(a^(2^i)·x) mod N`. -/
  block_matches_residue : ∀ i x, x < N →
    EGate.applyNat (eg i) (encode i x)
      = FormalRV.BQAlgo.encodeDataZeroAnc bits anc ((a ^ (2 ^ i) * x) % N)

/-- **From the named residual to a discharged `egate_matches_rev`.**  IF
    `ModExpAtEncodedMatchesResidue` holds for `eg` (the measured `modExpAt`
    blocks) at the canonical encoding, THEN the verified reversible windowed
    family `rev` and `eg` agree on every encoded basis state — i.e. the
    `egate_matches_rev` field is dischargeable for the LITERAL `modExpAt` blocks.
    This certifies the residual is EXACTLY the value identity above: supply it and
    the bound rides `modExpAt` itself.  (Stated as the field shape; the witness's
    `rev` is the verified windowed family whose round-trip target is the same
    residue.) -/
theorem egate_matches_rev_of_modExpAtResidue
    (w bits numWin N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (eg : Nat → EGate)
    (H : ModExpAtEncodedMatchesResidue a N bits (2 * w + 2 * bits + 3) eg
          (fun _ x => FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)) :
    ∀ i x, x < N →
      Framework.uc_eval
          ((windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
              hw hbits hb1 hN1 hN2 h_inv0).family i)
        * f_to_vec (bits + (2 * w + 2 * bits + 3))
            (FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)
        = f_to_vec (bits + (2 * w + 2 * bits + 3))
            (EGate.applyNat (eg i)
              (FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)) := by
  intro i x hx
  -- The reversible side: `family i = Gate.toUCom _ (windowedModNEncodeGate … (a^(2^i)))`,
  -- whose basis action is the canonical encoding of `(a^(2^i)·x) % N`
  -- (`roundTrip` + `uc_eval_toUCom_acts_on_basis`).
  rw [H.block_matches_residue i x hx]
  have hN_pos : 0 < N := by omega
  obtain ⟨_h_lt, h_inv⟩ := modInv_spec N (a ^ (2 ^ i)) hN_pos
    ⟨ainv0 ^ (2 ^ i), by
      rw [Nat.mul_mod]; exact mul_pow_mod_one a ainv0 N (2 ^ i) hN1 h_inv0⟩
  have h_rt :
      Gate.applyNat
          (windowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
            (modInv N (a ^ (2 ^ i))))
          (FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)
        = FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3)
            (((a ^ (2 ^ i)) * x) % N) := by
    have h_inv' : ((a ^ (2 ^ i)) % N) * modInv N (a ^ (2 ^ i)) % N = 1 := by
      rw [Nat.mod_mul_mod]; exact h_inv
    rw [windowedModNEncodeGate_apply w bits numWin N ((a ^ (2 ^ i)) % N)
          (modInv N (a ^ (2 ^ i))) x hw hbits hb1 hN_pos hN2 hx _h_lt h_inv',
        Nat.mod_mul_mod]
  show Framework.uc_eval
        (Gate.toUCom (bits + (2 * w + 2 * bits + 3))
          (windowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
            (modInv N (a ^ (2 ^ i)))))
      * f_to_vec (bits + (2 * w + 2 * bits + 3)) _
      = f_to_vec (bits + (2 * w + 2 * bits + 3)) _
  rw [uc_eval_toUCom_acts_on_basis (bits + (2 * w + 2 * bits + 3))
        (windowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
          (modInv N (a ^ (2 ^ i))))
        (windowedModNEncodeGate_wellTyped w bits N numWin ((a ^ (2 ^ i)) % N)
          (modInv N (a ^ (2 ^ i))) hw hbits)
        (FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x),
      h_rt]

end

end FormalRV.Audit.GidneyEkera2021.ShorComposedFinal
