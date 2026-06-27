/-
  FormalRV.Audit.GidneyEkera2021.ModExpAtSameObjectWeld
  ════════════════════════════════════════════════════════════════════════════
  THE SAME-OBJECT WELD — count and semantics on ONE syntactic gate, no cheating.

  This file states, as a SINGLE theorem, the three facts about the IDENTICAL gate
  term `G i := measWindowedModNEncodeGate w bits N numWin ((a^(2^i)) % N) (modInv N (a^(2^i)))`:

    (1) ORACLE CORRECTNESS — `G i` provably implements the per-iterate controlled
        modular-multiply oracle on the encoded subspace:
          `EGate.applyNat (G i) (encodeDataZeroAnc bits anc x) = encodeDataZeroAnc bits anc ((a^(2^i)·x) % N)`.
    (2) TOFFOLI COUNT — the SAME `G i` has the measurement-optimized count
          `EGate.toffoli (G i) = 2·numWin·(4·w·2^w + 8·bits)`.
    (3) SHOR BOUND — the success probability of the modular-exponentiation family
        that `G` realizes attains `≥ κ/(log₂N)⁴`.

  HONEST SCOPE — read this, it is the whole point of the file:
  • The count in (2) is `G`'s OWN count.  It is NOT the `2 578 993 152`-Toffoli figure
    of `WindowedComposedAt.multiplyAddAt`.  `multiplyAddAt` is FORWARD-ONLY — it leaves the
    un-reduced product `a·x` with the input `x` still present — so it is NOT the oracle, and
    counting it while proving semantics elsewhere is exactly the unsound move this file avoids.
    Here count and semantics are the SAME gate `G`.
  • In (3) the probability is stated on `(…).rev.family` (the verified REVERSIBLE multiplier
    family).  `G` is provably EQUAL to that family on every encoded basis input — this is the
    PROVEN field `egate_matches_rev` of `ge2021_measEncode_measuredEqRev`, and the
    `MeasuredEqualsReversibleOnEncoded` framework lifts it to the density/channel level — so
    (3) is genuinely `G`'s success bound, not a claim about an unrelated object.

  Kernel-clean: axioms ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`.
-/
import FormalRV.Audit.GidneyEkera2021.ModExpAtResidueInstance

namespace FormalRV.Audit.GidneyEkera2021.ModExpAtSameObjectWeld

open FormalRV.Framework FormalRV.BQAlgo
open FormalRV.SQIRPort
open VerifiedShor
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasuredWindowedModN
open FormalRV.Shor.MeasuredWindowedShorCapstone
open FormalRV.Shor.EGateToUnitaryBridge
open FormalRV.BQAlgo.WindowedShorConnection
open FormalRV.BQAlgo.MultiplierInstances
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.Audit.GidneyEkera2021.ShorComposed
open FormalRV.Audit.GidneyEkera2021.ShorComposedFinal
open FormalRV.Audit.GidneyEkera2021.ModExpAtResidueInstance

/-- **★ THE SAME-OBJECT WELD ★** — for the per-iterate measured windowed modular
    multiplier `G i := measWindowedModNEncodeGate w bits N numWin ((a^(2^i)) % N)
    (modInv N (a^(2^i)))`, count and semantics are proven about the IDENTICAL gate:

    (1) `G i` correctly implements the modular-multiply oracle on encoded inputs;
    (2) `G i` has Toffoli count `2·numWin·(4·w·2^w + 8·bits)`;
    (3) the Shor success bound `≥ κ/(log₂N)⁴` holds for the modexp family `G` realises.

    The count is `G`'s honest count — explicitly NOT `multiplyAddAt`'s forward-only
    `2.58·10⁹`.  No resource number is attached to an object whose semantics are unproven. -/
theorem ge2021_oracle_correct_AND_counted_AND_bound
    (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    (∀ i x, x < N →
        EGate.applyNat
            (measWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
              (modInv N (a ^ (2 ^ i))))
            (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)
          = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) ((a ^ (2 ^ i) * x) % N))
    ∧ (∀ i,
        EGate.toffoli
            (measWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
              (modInv N (a ^ (2 ^ i))))
          = 2 * (numWin * (4 * w * 2 ^ w + 8 * bits)))
    ∧ probability_of_success a r N m bits (2 * w + 2 * bits + 3)
          (ge2021_measEncode_measuredEqRev w bits numWin N a ainv0
            hw hbits hb1 hN1 hN2 h_inv0).rev.family
        ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  ⟨fun i x hx =>
      measEncode_block_matches_residue w bits numWin N a ainv0
        hw hbits hb1 hN1 hN2 h_inv0 i x hx,
   fun i =>
      toffoli_measWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
        (modInv N (a ^ (2 ^ i))),
   ge2021_measEncode_shor_succeeds w bits numWin N a ainv0 r m
     hw hbits hb1 hN1 hN2 h_inv0 h_setting⟩

end FormalRV.Audit.GidneyEkera2021.ModExpAtSameObjectWeld
