/-
  Audit · Gidney–Ekerå 2021 · CLOSING GAP-4 — THE MEASURED-WELD RESIDUE READ-OUT
  ════════════════════════════════════════════════════════════════════════════
  Supplying a CONCRETE, UNCONDITIONAL instance of the named residual
  `ShorComposedFinal.ModExpAtEncodedMatchesResidue` so the GE2021 Shor success
  bound rides a count-bearing MEASURED gate — discharged via the proven
  `block_matches_residue` value identity, NOT a `sorry` and NOT an un-built
  layout adapter.

  ────────────────────────────────────────────────────────────────────────────
  WHAT GAP-4 IS (recap)
  ────────────────────────────────────────────────────────────────────────────
  `ShorComposedFinal` proved the amplitude/bridge spine in full: GIVEN any
  `MeasuredEqualsReversibleOnEncoded a N bits anc eg encode` witness, the verified
  reversible family `rev` attains the Shor bound `≥ κ/(log₂N)⁴`.  Its §5 NAMED —
  but did NOT instantiate — the residual

      ModExpAtEncodedMatchesResidue a N bits anc eg encode
        : ∀ i x, x < N → EGate.applyNat (eg i) (encode i x)
            = encodeDataZeroAnc bits anc ((a^(2^i)·x) % N)

  and proved `egate_matches_rev_of_modExpAtResidue`: ONE instance of
  `block_matches_residue` discharges `egate_matches_rev` for the SAME measured `eg`
  family, feeding `countOptimal_shor_succeeds_constrained` directly.

  Gap-4 = supply that residue read-out concretely so the bound rides a MEASURED
  (measurement-uncompute, `EGate.mz`-modelled) gate.

  ────────────────────────────────────────────────────────────────────────────
  THE DISCHARGE (genuine, kernel-clean, UNCONDITIONAL)
  ────────────────────────────────────────────────────────────────────────────
  We instantiate `eg i` with the COUNT-BEARING MEASURED encode gate

      eg i := measWindowedModNEncodeGate w bits N numWin ((a^(2^i)) % N) (modInv N (a^(2^i)))

  (`MeasuredWindowedModN.measWindowedModNEncodeGate`, the canonical-layout wrapper
  of the count-optimal measurement-uncompute in-place multiplier
  `measWindowedModNMulInPlace`, with the measured `EGate.mz` clears literally
  inside).  Its encoded-basis action is the PROVEN

      EGate.applyNat (eg i) (encodeDataZeroAnc bits (2w+2bits+3) x)
        = encodeDataZeroAnc bits (2w+2bits+3) (((a^(2^i)) % N · x) % N)
        = encodeDataZeroAnc bits (2w+2bits+3) ((a^(2^i)·x) % N)   [Nat.mod_mul_mod]

  via `measWindowedModNEncodeGate_apply` (`MeasuredWindowedModN`).  This is
  EXACTLY `block_matches_residue` at the canonical Cuccaro ancilla width
  `anc = 2w + 2·bits + 3` the residual structure uses — so the instance is built
  with NO extra hypotheses beyond the standard sizing + base-inverse, and NO
  layout adapter.

  Feeding it through `egate_matches_rev_of_modExpAtResidue`
  (ShorComposedFinal §5) and then `countOptimal_shor_succeeds_constrained` puts
  the Shor bound on the verified reversible family, PINNED to the measured gate by
  the proven residue identity.  The measured gate's measurement-optimized Toffoli
  count `2·numWin·(4·w·2^w + 8·bits)` is attached on the SAME object.

  ────────────────────────────────────────────────────────────────────────────
  HONEST FRONTIER — WHICH gate the bound rides vs. WHICH gate the 2.58e9 count is
  ────────────────────────────────────────────────────────────────────────────
  The MEASURED gate this instance pins is `measWindowedModNEncodeGate` (the
  Cuccaro-layout measurement-uncompute multiplier), whose measured count is
  `2·numWin·(4·w·2^w + 8·bits)`.  This is a genuine measured, count-bearing gate
  — the residue read-out is DISCHARGED, not assumed — but it is NOT the literal
  `WindowedComposedAt.modExpAt` block (`multiplyAddAt`, the `2 578 993 152`-Toffoli
  shared-Cuccaro object).  Pinning the bound to `multiplyAddAt` ITSELF is the
  subject of `ShorModExpAt.lean`, which discharges the same residue identity on
  the LITERAL `multiplyAddAt` block but ONLY GIVEN an un-built
  `ModExpAtLayoutAdapter` (the per-window-address ↔ big-endian-band layout
  reconciliation) plus a no-wrap hypothesis — a conditional bound.

  So the precise state of gap-4 after this file:
    • the residue read-out (`block_matches_residue`) is now discharged
      UNCONDITIONALLY for a count-bearing MEASURED gate
      (`measWindowedModNEncodeGate`); and
    • the ONLY thing separating that gate from the `2.58e9`-Toffoli `multiplyAddAt`
      is the named `ModExpAtLayoutAdapter` (T-free layout permutation) — the count
      figure attaches to `multiplyAddAt`, the unconditional bound to
      `measWindowedModNEncodeGate`, and they coincide exactly when that adapter is
      built.

  Kernel-clean: no `sorry`, no `native_decide`, axioms exactly
  `[propext, Classical.choice, Quot.sound]`.  ADDITIVE: no existing file weakened.
-/
import FormalRV.Audit.GidneyEkera2021.ShorComposedFinal
import FormalRV.Shor.MeasuredWindowedShorCapstone

namespace FormalRV.Audit.GidneyEkera2021.ModExpAtResidueInstance

open FormalRV.Framework FormalRV.BQAlgo
open FormalRV.SQIRPort
open VerifiedShor
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasuredWindowedModN
open FormalRV.Shor.EGateToUnitaryBridge
open FormalRV.BQAlgo.WindowedShorConnection
open FormalRV.BQAlgo.MultiplierInstances
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.Audit.GidneyEkera2021.ShorComposed
open FormalRV.Audit.GidneyEkera2021.ShorComposedFinal

noncomputable section

/-! ## §1. The residue read-out, DISCHARGED on the measured encode gate.

The per-iterate measured gate `measWindowedModNEncodeGate w bits N numWin
((a^(2^i))%N) (modInv N (a^(2^i)))` maps `encodeDataZeroAnc bits anc x` to
`encodeDataZeroAnc bits anc ((a^(2^i)·x) % N)` on every encoded basis state with
`x < N`.  This is the EXACT `block_matches_residue` field shape — proven from
`measWindowedModNEncodeGate_apply` and `Nat.mod_mul_mod` (mirroring
`MeasuredWindowedShorCapstone.measWindowedShorWitness`'s `egate_matches_rev`
discharge, but stated as the residue read-out the residual structure consumes). -/

/-- **★ THE GAP-4 RESIDUE READ-OUT — `block_matches_residue` DISCHARGED ★.**
    For QPE iterate `i` (constant `a^(2^i)`), the count-bearing MEASURED encode
    gate's `applyNat` on the canonical zero-ancilla encoding of `x < N` is the
    canonical encoding of the true residue `(a^(2^i)·x) % N`.  Proven from the
    measured gate's round-trip `measWindowedModNEncodeGate_apply` plus
    `Nat.mod_mul_mod` (folding `((a^(2^i))%N · x) % N = (a^(2^i)·x) % N`); the base
    inverse `modInv N (a^(2^i))` and its specs come from `modInv_spec`
    /`mul_pow_mod_one`.  NO no-wrap, NO layout adapter, NO `sorry`. -/
theorem measEncode_block_matches_residue
    (w bits numWin N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (i x : Nat) (hx : x < N) :
    EGate.applyNat
        (measWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
          (modInv N (a ^ (2 ^ i))))
        (FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)
      = FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3)
          ((a ^ (2 ^ i) * x) % N) := by
  have hN_pos : 0 < N := by omega
  -- The base inverse of the per-iterate constant, with its `< N` and product-mod specs.
  obtain ⟨h_lt, h_inv⟩ := modInv_spec N (a ^ (2 ^ i)) hN_pos
    ⟨ainv0 ^ (2 ^ i), by rw [Nat.mul_mod]; exact mul_pow_mod_one a ainv0 N (2 ^ i) hN1 h_inv0⟩
  have h_inv' : ((a ^ (2 ^ i)) % N) * modInv N (a ^ (2 ^ i)) % N = 1 := by
    rw [Nat.mod_mul_mod]; exact h_inv
  -- The measured round-trip: `x ↦ ((a^(2^i))%N · x) % N`; then fold the inner `%N`.
  rw [measWindowedModNEncodeGate_apply w bits numWin N ((a ^ (2 ^ i)) % N)
        (modInv N (a ^ (2 ^ i))) x hw hbits hb1 hN_pos hN2 hx h_lt h_inv',
      Nat.mod_mul_mod]

/-! ## §2. The CONCRETE `ModExpAtEncodedMatchesResidue` instance (UNCONDITIONAL). -/

/-- **★ THE GAP-4 INSTANCE — `ModExpAtEncodedMatchesResidue`, BUILT (no `sorry`) ★.**
    The named residual of `ShorComposedFinal` §5, instantiated for the MEASURED
    family `eg i := measWindowedModNEncodeGate … ((a^(2^i))%N) (modInv N (a^(2^i)))`
    at the canonical `encodeDataZeroAnc` layout and Cuccaro ancilla width
    `anc = 2w + 2·bits + 3`.  Its `block_matches_residue` field is §1's discharged
    residue read-out — an UNCONDITIONAL instance (only standard sizing + base
    inverse), unlike `ShorModExpAt.modExpAtEncodedMatchesResidue_of_layoutAdapter`
    which needs an un-built layout adapter. -/
def ge2021_modExpAtResidue
    (w bits numWin N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1) :
    ModExpAtEncodedMatchesResidue a N bits (2 * w + 2 * bits + 3)
      (fun i => measWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
        (modInv N (a ^ (2 ^ i))))
      (fun _ x => FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) where
  block_matches_residue := fun i x hx =>
    measEncode_block_matches_residue w bits numWin N a ainv0
      hw hbits hb1 hN1 hN2 h_inv0 i x hx

/-! ## §3. THE WITNESS — `egate_matches_rev` PROVEN for the measured family via §2.

Feed the discharged residual through `ShorComposedFinal.egate_matches_rev_of_modExpAtResidue`
to build a `MeasuredEqualsReversibleOnEncoded` whose measured family `eg` is the
count-bearing measured encode gate and whose reversible family `rev` is the
verified windowed mod-N multiplier.  Because `egate_matches_rev` is now PROVEN
from the residue identity (not the trivial base-EGate identity of
`ShorComposedFinal.ge2021_measuredEqRev`), `rev` is genuinely pinned to the
MEASURED gate's encoded action. -/

/-- **★ THE MEASURED WITNESS — bound family pinned to the measured gate by the
    DISCHARGED residue ★.**  A `MeasuredEqualsReversibleOnEncoded` whose measured
    family is the count-bearing `measWindowedModNEncodeGate` (measurement-uncompute
    inside) and whose reversible family is the verified
    `windowedModNMultiplier_verifiedModMulFamily`.  `egate_matches_rev` is PROVEN
    via `egate_matches_rev_of_modExpAtResidue ∘ ge2021_modExpAtResidue` — i.e. from
    the §1 residue read-out, NOT a trivial wrapping. -/
def ge2021_measEncode_measuredEqRev
    (w bits numWin N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1) :
    MeasuredEqualsReversibleOnEncoded a N bits (2 * w + 2 * bits + 3)
      (fun i => measWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
        (modInv N (a ^ (2 ^ i))))
      (fun _ x => FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) where
  rev := windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
    hw hbits hb1 hN1 hN2 h_inv0
  eg_wellTyped := fun i =>
    measWindowedModNEncodeGate_wellTypedAt w bits N numWin ((a ^ (2 ^ i)) % N)
      (modInv N (a ^ (2 ^ i))) hw hbits
  egate_matches_rev :=
    egate_matches_rev_of_modExpAtResidue w bits numWin N a ainv0
      hw hbits hb1 hN1 hN2 h_inv0
      (fun i => measWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
        (modInv N (a ^ (2 ^ i))))
      (ge2021_modExpAtResidue w bits numWin N a ainv0 hw hbits hb1 hN1 hN2 h_inv0)

/-! ## §4. THE HEADLINE — the Shor bound riding the measured count-bearing gate. -/

/-- **★ GAP-4 HEADLINE — the Shor bound, pinned to the MEASURED gate by a
    DISCHARGED residue read-out ★.**  The Shor success probability of the family
    that the count-bearing MEASURED gate `measWindowedModNEncodeGate`
    (measurement-uncompute `EGate.mz` clears literally inside) PROVABLY acts as on
    the encoded subspace attains `≥ κ/(log₂N)⁴` — UNCONDITIONALLY in the bridge
    (only standard `ShorSetting` + sizing + a base inverse).

    Unlike `ShorComposedFinal.ge2021_exactMultiplier_shor_bound` (whose `eg` was the
    reversible gate wrapped trivially as `EGate.base`, so `egate_matches_rev` was
    the trivial identity), here `egate_matches_rev` is PROVEN from the §1 residue
    read-out — the measurement-uncompute gate's Boolean output is genuinely the
    canonical residue.  HONEST SCOPE: the measured gate is
    `measWindowedModNEncodeGate` (count `2·numWin·(4·w·2^w + 8·bits)`), NOT the
    `2.58·10⁹`-Toffoli `modExpAt`/`multiplyAddAt`; see §5. -/
theorem ge2021_measEncode_shor_succeeds
    (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (ge2021_measEncode_measuredEqRev w bits numWin N a ainv0
          hw hbits hb1 hN1 hN2 h_inv0).rev.family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  countOptimal_shor_succeeds_constrained
    (w := w) (numWin := numWin) (q_start := 1 + 2 * w) (Tfam := fun _ _ _ => 0)
    hw (by omega)
    (ge2021_measEncode_measuredEqRev w bits numWin N a ainv0 hw hbits hb1 hN1 hN2 h_inv0)
    r m h_setting

/-! ## §5. THE CAPSTONE — Shor success ∧ the MEASURED count on the SAME gate. -/

/-- **★ GAP-4 CAPSTONE — Shor success ∧ the measured Toffoli count, ONE gate ★.**
    Simultaneously, on the IDENTICAL count-bearing measured gate
    `measWindowedModNEncodeGate … ((a^(2^i))%N) …` (per QPE iterate `i`):

    (i) the Shor success bound `≥ κ/(log₂N)⁴` holds for the family it PROVABLY acts
        as on the encoded subspace — pinned to the measured gate by the DISCHARGED
        residue read-out of §1 (`egate_matches_rev` PROVEN, not trivial); and

    (ii) each per-iterate MEASURED gate has the measurement-optimized Toffoli count
         `2·numWin·(4·w·2^w + 8·bits)` (`toffoli_measWindowedModNEncodeGate`).

    Both faces ride the SAME syntactic measured object (measurement-uncompute
    contained), so gap-4's residue read-out is closed for a count-bearing measured
    gate UNCONDITIONALLY.  HONEST CAVEAT: this gate is the Cuccaro-layout
    `measWindowedModNEncodeGate`, NOT the `2.58·10⁹`-Toffoli `modExpAt`; tying the
    bound to `modExpAt`'s literal `multiplyAddAt` block additionally needs the
    named (un-built) `ShorModExpAt.ModExpAtLayoutAdapter`. -/
theorem ge2021_measEncode_shor_AND_count
    (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (ge2021_measEncode_measuredEqRev w bits numWin N a ainv0
          hw hbits hb1 hN1 hN2 h_inv0).rev.family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4
    ∧ ∀ i, EGate.toffoli
        (measWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
          (modInv N (a ^ (2 ^ i))))
        = 2 * (numWin * (4 * w * 2 ^ w + 8 * bits)) :=
  ⟨ge2021_measEncode_shor_succeeds w bits numWin N a ainv0 r m
      hw hbits hb1 hN1 hN2 h_inv0 h_setting,
   fun i => FormalRV.Shor.MeasuredWindowedShorCapstone.toffoli_measWindowedModNEncodeGate
     w bits N numWin ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i)))⟩

end

end FormalRV.Audit.GidneyEkera2021.ModExpAtResidueInstance
