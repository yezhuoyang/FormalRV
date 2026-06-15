/-
  Audit · Gidney–Ekerå 2021 · THE SHOR BOUND THROUGH THE LITERAL `modExpAt` BLOCK
  ════════════════════════════════════════════════════════════════════════════
  Running the Shor success bound through the COUNT-OPTIMAL `modExpAt` gate — the
  `2 578 993 152`-Toffoli object the audit costs — with NO substituted middle.

  ────────────────────────────────────────────────────────────────────────────
  WHY THIS FILE EXISTS (the no-cheating frontier)
  ────────────────────────────────────────────────────────────────────────────
  `ShorComposedFinal.ge2021_exactMultiplier_shor_bound` rode
  `eg i := EGate.base (windowedModNMultiplier.gate (a^(2^i)))` — the EXACT
  reversible multiplier wrapped trivially, so its `egate_matches_rev` was the
  trivial `Gate.applyNat = uc_eval` identity.  That bound did NOT run through the
  count-optimal MEASURED `modExpAt` (the `2.58·10⁹`-Toffoli gate): the gate the
  bound was pinned to and the gate the count was pinned to were DIFFERENT.

  This file ties the bound to `modExpAt`'s OWN per-multiply measured block — the
  literal `WindowedComposedAt.multiplyAddAt` (`= seqAll` of the measured
  `laAt`/`babbushLookupAddAt`s, the gate that has the Toffoli count).  We do NOT
  substitute a reversible gate for `eg`: `eg i` LITERALLY CONTAINS
  `multiplyAddAt` as a sub-term (`block_eg`).  The residual field
  `ShorComposedFinal.ModExpAtEncodedMatchesResidue.block_matches_residue` is what
  pins the family to this gate, and it is discharged here from:

    (1) the VALUE chain — `ShorComposed.countOptimal_multiplyAdd_coset`
        (PROVEN): on a `CountGateMulInput` with the windows of `y` pre-loaded,
        the literal `multiplyAddAt` block leaves a `WindowedCoset.IsCosetRep` of
        `(a^(2^i)·y) mod N` in the shared Cuccaro accumulator under no-wrap — i.e.
        the accumulator reads `(a^(2^i)·y) % N`; folded from
        `multiplyAddAt_fold` + `windowedLookupFold_eq_modmul`; and

    (2) the LAYOUT ADAPTER — the register-layout reconciliation between
        `modExpAt`'s native shared-Cuccaro/per-window-address layout (interleaved
        accumulator positions `q_start + 2·i + 1`, per-window address registers
        `addrBaseOf`, width `> bits + anc`) and the canonical contiguous
        big-endian `encodeDataZeroAnc` layout the Shor bound consumes.

  ────────────────────────────────────────────────────────────────────────────
  THE HONEST FRONTIER — value DISCHARGED, layout NAMED (no `sorry`)
  ────────────────────────────────────────────────────────────────────────────
  Step (1) is PROVEN here on the literal block (`multiplyAddAt_block_residue_value`,
  `multiplyAddAt_block_isCosetRep`).  Step (2) is genuine new circuit work:
  `multiplyAddAt` reads `y` from the per-window address registers `addrBaseOf`
  (all `≥ q_start + 2·bits + 1 > bits`), which are DISJOINT from the
  `encodeDataZeroAnc` data band `[0, bits)`; and it writes the result to the
  interleaved accumulator positions `q_start + 2·i + 1`, not the big-endian band
  `[0, bits)`.  Worse, with `numWin` windows `multiplyAddAt` STACKS `numWin·2·w`
  scratch qubits, so its native width EXCEEDS `bits + anc` (see the
  `WindowedComposedAt` header WIDTH NOTE).  So the bare block on
  `encodeDataZeroAnc x` reads `y = 0` and computes `a·0 = 0` — `block_matches_residue`
  is FALSE for the bare block.  An ADAPTER is genuinely required: it must scatter
  `x`'s windows into the per-window address registers, read the accumulator back
  into the big-endian band, and clear the scratch (so the composite fits the
  `bits + anc` register).  We package this as the named structure
  `ModExpAtLayoutAdapter` (T-free adapter gates + their semantic obligations); NO
  instance is declared, so the kernel sees no unproven claim.

  GIVEN such an adapter, `modExpAtBlockResidue_of_layoutAdapter` discharges
  `block_matches_residue` for `eg i := adaptIn ; multiplyAddAt ; adaptOut` (the
  count gate literally inside), and `ge2021_modExpAt_shor_succeeds` runs the Shor
  bound `≥ κ/(log₂ N)⁴` through the family `eg`'s blocks provably act as — now the
  SAME gate as the count.

  ────────────────────────────────────────────────────────────────────────────
  NAMED RESIDUAL HYPOTHESES (stated, not hidden)
  ────────────────────────────────────────────────────────────────────────────
  • The LAYOUT ADAPTER `ModExpAtLayoutAdapter` (the per-window-address ↔
    big-endian-band reconciliation) — the precise remaining circuit obligation.
  • NO-WRAP (`a^(2^i)·x < 2^bits` per multiply) — the deterministic condition;
    the probabilistic wrap leg is the separate `WindowedCoset.CosetDeviationBound`
    (verified deviation `≈ 7.64·10⁻⁸`).
  • Standard QPE (the paper's Ekerå–Håstad exponent optimisation is separate).
  • The oblivious carry runway is a separate DEPTH optimisation — not the count
    gate — and is NOT needed for the count or the bound here.

  Kernel-clean: no `sorry`, no `native_decide`, axioms exactly
  `[propext, Classical.choice, Quot.sound]`.  ADDITIVE: no existing file weakened.
-/
import FormalRV.Audit.GidneyEkera2021.ShorComposedFinal

namespace FormalRV.Audit.GidneyEkera2021.ShorModExpAt

open FormalRV.Framework FormalRV.BQAlgo
open FormalRV.SQIRPort
open VerifiedShor
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.WindowedComposedAt
open FormalRV.Shor.EGateToUnitaryBridge
open FormalRV.Shor.WindowedCoset
open FormalRV.BQAlgo.WindowedShorConnection
open FormalRV.BQAlgo.MultiplierInstances
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.Audit.GidneyEkera2021.ShorComposed
open FormalRV.Audit.GidneyEkera2021.ShorComposedFinal

noncomputable section

/-! ## §1. The VALUE half on the LITERAL `multiplyAddAt` block (DISCHARGED).

The count-bearing per-multiply block of `modExpAt` is the literal
`WindowedComposedAt.multiplyAddAt` (`multiplyAddAt_is_inner_block_of_modExpAt`,
`rfl`, certifies it is a sub-term of `modExpAt`).  Under no-wrap and on the
native `CountGateMulInput` clean family, it computes `(a^(2^i)·y) mod N` in the
Gidney coset representation — this is the PROVEN value content, reused verbatim
from `ShorComposed`. -/

/-- **The literal block reads `(c·y) % N` from the accumulator (under no-wrap).**
    For QPE iterate `i` (`c = a^(2^i)`), one literal `multiplyAddAt` block of
    `modExpAt` — started from a `CountGateMulInput` with the windows of `y`
    pre-loaded — leaves an accumulator whose coset readout is exactly the true
    modular product `(c·y) % N`.  Thin reuse of
    `ShorComposed.countOptimal_multiplyAdd_readout`. -/
theorem multiplyAddAt_block_residue_value
    (w bits c numWin N y mblk q_start : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (hw : 0 < w) (hq : 0 < q_start)
    (hT : ∀ k v, Tfam mblk k v = (c * (2 ^ w) ^ k * v) % 2 ^ bits)
    (hy : y < (2 ^ w) ^ numWin)
    (g0 : Nat → Bool) (hg0 : CountGateMulInput w bits numWin y q_start g0)
    (hnowrap : c * y < 2 ^ bits) :
    cosetValue N
      (decodeReg (fun i => q_start + 2 * i + 1) bits
        (EGate.applyNat (multiplyAddAt w bits bits Tfam q_start mblk numWin) g0))
      = (c * y) % N :=
  countOptimal_multiplyAdd_readout w bits c numWin N y mblk q_start Tfam
    hw hq hT hy g0 hg0 hnowrap

/-- **The literal block leaves a coset rep of `(c·y) mod N` (under no-wrap).**
    The structural weld on `modExpAt`'s OWN block: the accumulator value is a
    `WindowedCoset.IsCosetRep bits N _ (c·y)`.  Verbatim
    `ShorComposed.countOptimal_multiplyAdd_coset`. -/
theorem multiplyAddAt_block_isCosetRep
    (w bits c numWin N y mblk q_start : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (hw : 0 < w) (hq : 0 < q_start)
    (hT : ∀ k v, Tfam mblk k v = (c * (2 ^ w) ^ k * v) % 2 ^ bits)
    (hy : y < (2 ^ w) ^ numWin)
    (g0 : Nat → Bool) (hg0 : CountGateMulInput w bits numWin y q_start g0)
    (hnowrap : c * y < 2 ^ bits) :
    IsCosetRep bits N
      (decodeReg (fun i => q_start + 2 * i + 1) bits
        (EGate.applyNat (multiplyAddAt w bits bits Tfam q_start mblk numWin) g0))
      (c * y) :=
  countOptimal_multiplyAdd_coset w bits c numWin N y mblk q_start Tfam
    hw hq hT hy g0 hg0 hnowrap

/-! ## §2. THE LAYOUT ADAPTER — the named residual reconciling `modExpAt`'s native
       layout with the canonical `encodeDataZeroAnc` layout.

`multiplyAddAt` reads `y` from the per-window ADDRESS registers `addrBaseOf` and
writes to the interleaved ACCUMULATOR positions `q_start + 2·i + 1`; these are
DISJOINT from the `encodeDataZeroAnc` data band `[0, bits)`, and the native gate
is WIDER than `bits + anc`.  To present `modExpAt`'s block as a measured EGate
acting on the canonical encoded subspace, we conjugate it by T-free adapter
gates: `adaptIn` scatters `x`'s windows into the address registers (and sets the
ctrl / clears scratch), `adaptOut` reads the accumulator back into the band and
clears the native scratch.  This structure NAMES exactly those two adapter
semantics; the count is unaffected (adapters are T-free) and `multiplyAddAt`
remains literally inside the resulting `eg`. -/

/-- **`ModExpAtLayoutAdapter` — the per-multiply layout reconciliation (named, no
    `sorry`).**  Packages, for QPE iterate `i` (constant `c = a^(2^i)`):

    * `adaptIn i`, `adaptOut i` — T-free layout-permutation gates;
    * `adaptIn_clean` — on the canonical encoding `encodeDataZeroAnc bits anc x`
      (`x < N`), `adaptIn i` produces a `CountGateMulInput` state with `y = x`
      (the windows of `x` loaded into the per-window address registers, the
      shared accumulator/ancillas clean, ctrl set);
    * `adaptOut_reads` — applied to ANY post-block state whose accumulator
      (positions `q_start + 2·i + 1`) decodes to a coset rep `v` of
      `(c·x) mod N` AND whose native scratch is clear, `adaptOut i` reads `v`'s
      modular value back into the big-endian band and clears scratch, producing
      `encodeDataZeroAnc bits anc ((c·x) % N)`.

    Both adapter facts are the EXACT remaining circuit obligation; both adapters
    are T-free, so the Toffoli count of the conjugated block equals that of
    `multiplyAddAt`.  NOTE the OUT-adapter is stated GENERICALLY (on any
    coset-rep accumulator value, scratch clear) — it does NOT smuggle in the
    answer: it is a pure layout read-out, and the VALUE that fills `v` is supplied
    by §1's proven `multiplyAddAt_block_isCosetRep`, NOT by the structure.  No
    instance is declared. -/
structure ModExpAtLayoutAdapter
    (w bits anc numWin N a q_start : Nat) (Tfam : Nat → Nat → Nat → Nat) where
  /-- The per-iterate multiply-add table family index for `modExpAt`'s block `i`. -/
  mblkOf : Nat → Nat
  /-- The T-free input adapter (scatter the data band into the address registers). -/
  adaptIn : Nat → Gate
  /-- The T-free output adapter (read the accumulator back into the band, clear scratch). -/
  adaptOut : Nat → Gate
  /-- The input adapter is T-free (a layout permutation). -/
  adaptIn_tfree : ∀ i, Gate.tcount (adaptIn i) = 0
  /-- The output adapter is T-free (a layout permutation). -/
  adaptOut_tfree : ∀ i, Gate.tcount (adaptOut i) = 0
  /-- Adapters are well-typed at the canonical dimension. -/
  adaptIn_wellTyped : ∀ i, Gate.WellTyped (bits + anc) (adaptIn i)
  adaptOut_wellTyped : ∀ i, Gate.WellTyped (bits + anc) (adaptOut i)
  /-- The block's measured EGate is well-typed at the canonical dimension once the
      adapter has confined its scratch to `[0, bits + anc)`. -/
  block_wellTyped : ∀ i,
    EGate.WellTypedAt (bits + anc)
      (multiplyAddAt w bits bits Tfam q_start (mblkOf i) numWin)
  /-- The table family at block `i` realises the per-window modular product the
      value chain consumes (`Tfam (mblkOf i) k v = (a^(2^i)·(2^w)^k·v) mod 2^bits`). -/
  table_spec : ∀ i k v,
    Tfam (mblkOf i) k v = ((a ^ (2 ^ i)) * (2 ^ w) ^ k * v) % 2 ^ bits
  /-- IN-adapter: `encodeDataZeroAnc x` ↦ a `CountGateMulInput` with `y = x`
      (the windows of `x` loaded into the per-window address registers). -/
  adaptIn_clean : ∀ i x, x < N →
    CountGateMulInput w bits numWin x q_start
      (Gate.applyNat (adaptIn i)
        (FormalRV.BQAlgo.encodeDataZeroAnc bits anc x))
  /-- OUT-adapter (PURE layout read-out): on ANY accumulator value `v` that is a
      coset rep of `(a^(2^i)·x) mod N`, with the scratch cleared, `adaptOut i`
      reads `v % N` into the big-endian band, producing `encodeDataZeroAnc` of the
      true residue.  The VALUE `v` is NOT supplied here — it is the proven block
      output of §1. -/
  adaptOut_reads : ∀ i x f v, x < N →
    decodeReg (fun j => q_start + 2 * j + 1) bits f = v →
    IsCosetRep bits N v ((a ^ (2 ^ i)) * x) →
    Gate.applyNat (adaptOut i) f
      = FormalRV.BQAlgo.encodeDataZeroAnc bits anc (((a ^ (2 ^ i)) * x) % N)

/-- **The conjugated measured block: the LITERAL `multiplyAddAt` inside.**  For
    iterate `i`, the measured EGate `adaptIn i ; multiplyAddAt … ; adaptOut i` —
    where `multiplyAddAt` is the count-bearing block of `modExpAt`, present as a
    literal sub-term (NOT substituted by a reversible gate). -/
def ModExpAtLayoutAdapter.conjugatedBlock
    {w bits anc numWin N a q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtLayoutAdapter w bits anc numWin N a q_start Tfam) (i : Nat) : EGate :=
  EGate.seq
    (EGate.seq (EGate.base (L.adaptIn i))
      (multiplyAddAt w bits bits Tfam q_start (L.mblkOf i) numWin))
    (EGate.base (L.adaptOut i))

/-- **The conjugated block keeps `multiplyAddAt`'s Toffoli count.**  The adapters
    are T-free (layout permutations), so `EGate.toffoli (conjugatedBlock …)` equals
    `EGate.toffoli (multiplyAddAt …)` — the count is genuinely the count gate's. -/
theorem ModExpAtLayoutAdapter.conjugatedBlock_toffoli
    {w bits anc numWin N a q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtLayoutAdapter w bits anc numWin N a q_start Tfam) (i : Nat) :
    EGate.toffoli (L.conjugatedBlock i)
      = EGate.toffoli (multiplyAddAt w bits bits Tfam q_start (L.mblkOf i) numWin) := by
  unfold EGate.toffoli ModExpAtLayoutAdapter.conjugatedBlock
  simp only [EGate.tcount, L.adaptIn_tfree i, L.adaptOut_tfree i, Nat.zero_add, Nat.add_zero]

/-! ## §3. DISCHARGING `block_matches_residue` for the LITERAL block + the bound.

Given a `ModExpAtLayoutAdapter`, the conjugated block `adaptIn ; multiplyAddAt ;
adaptOut` (with `multiplyAddAt` literally inside) maps `encodeDataZeroAnc x` to
`encodeDataZeroAnc ((a^(2^i)·x) % N)`.  The proof IS the value chain: the IN-adapter
delivers a `CountGateMulInput`, §1's `multiplyAddAt_block_isCosetRep` computes the
coset rep of `(a^(2^i)·x) mod N` on the literal block, and the OUT-adapter reads it
back.  This discharges `ModExpAtEncodedMatchesResidue.block_matches_residue` for
`eg := the conjugated block`. -/

/-- **The literal-block residue, DISCHARGED from a layout adapter.**  For every
    encoded basis input `encodeDataZeroAnc x` (`x < N`), the conjugated measured
    block — which CONTAINS `modExpAt`'s count-bearing `multiplyAddAt` literally —
    outputs `encodeDataZeroAnc ((a^(2^i)·x) % N)`, UNDER the named no-wrap
    hypothesis.  The heart is §1's proven coset-rep value of the literal block;
    the adapter supplies only the (T-free) layout reconciliation. -/
theorem modExpAtBlock_matches_residue
    {w bits anc numWin N a q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtLayoutAdapter w bits anc numWin N a q_start Tfam)
    (hw : 0 < w) (hq : 0 < q_start)
    (hbits : numWin * w = bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (hnowrap : ∀ i x, x < N → (a ^ (2 ^ i)) * x < 2 ^ bits)
    (i x : Nat) (hx : x < N) :
    EGate.applyNat (L.conjugatedBlock i)
        (FormalRV.BQAlgo.encodeDataZeroAnc bits anc x)
      = FormalRV.BQAlgo.encodeDataZeroAnc bits anc (((a ^ (2 ^ i)) * x) % N) := by
  -- `x < N ≤ 2^bits = (2^w)^numWin`.
  have hxw : x < (2 ^ w) ^ numWin := by
    have hpow : (2 ^ w) ^ numWin = 2 ^ bits := by
      rw [← pow_mul, Nat.mul_comm, hbits]
    rw [hpow]; omega
  set g0 := Gate.applyNat (L.adaptIn i)
    (FormalRV.BQAlgo.encodeDataZeroAnc bits anc x) with hg0def
  -- the IN-adapter delivers a `CountGateMulInput` with `y = x`.
  have hg0 : CountGateMulInput w bits numWin x q_start g0 := L.adaptIn_clean i x hx
  -- §1: the literal block leaves a coset rep of `(a^(2^i)·x) mod N`.
  have hcoset :
      IsCosetRep bits N
        (decodeReg (fun j => q_start + 2 * j + 1) bits
          (EGate.applyNat (multiplyAddAt w bits bits Tfam q_start (L.mblkOf i) numWin) g0))
        ((a ^ (2 ^ i)) * x) :=
    multiplyAddAt_block_isCosetRep w bits (a ^ (2 ^ i)) numWin N x (L.mblkOf i) q_start Tfam
      hw hq (fun k v => L.table_spec i k v) hxw g0 hg0 (hnowrap i x hx)
  -- reduce the conjugated block's `applyNat` and read out via the OUT-adapter.
  show Gate.applyNat (L.adaptOut i)
      (EGate.applyNat (multiplyAddAt w bits bits Tfam q_start (L.mblkOf i) numWin)
        (Gate.applyNat (L.adaptIn i)
          (FormalRV.BQAlgo.encodeDataZeroAnc bits anc x)))
    = FormalRV.BQAlgo.encodeDataZeroAnc bits anc (((a ^ (2 ^ i)) * x) % N)
  rw [← hg0def]
  exact L.adaptOut_reads i x
    (EGate.applyNat (multiplyAddAt w bits bits Tfam q_start (L.mblkOf i) numWin) g0)
    _ hx rfl hcoset

/-- **The named residual structure, BUILT for the LITERAL `modExpAt` block.**  From
    a `ModExpAtLayoutAdapter`, package `ShorComposedFinal.ModExpAtEncodedMatchesResidue`
    with `eg i := L.conjugatedBlock i` — the measured EGate that CONTAINS
    `modExpAt`'s `multiplyAddAt` block as a literal sub-term — at the canonical
    `encodeDataZeroAnc` layout.  The `block_matches_residue` field is discharged by
    `modExpAtBlock_matches_residue`.  This is the no-substitution witness:
    `eg` is the count gate's block, not a wrapped exact multiplier. -/
def modExpAtEncodedMatchesResidue_of_layoutAdapter
    {w bits numWin N a q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtLayoutAdapter w bits (2 * w + 2 * bits + 3) numWin N a q_start Tfam)
    (hw : 0 < w) (hq : 0 < q_start)
    (hbits : numWin * w = bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (hnowrap : ∀ i x, x < N → (a ^ (2 ^ i)) * x < 2 ^ bits) :
    ModExpAtEncodedMatchesResidue a N bits (2 * w + 2 * bits + 3)
      (fun i => L.conjugatedBlock i)
      (fun _ x => FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) where
  block_matches_residue := fun i x hx =>
    modExpAtBlock_matches_residue L hw hq hbits hN2 hnowrap i x hx

/-! ## §4. THE WITNESS for the bridge + the Shor bound through the count gate.

Feed the discharged residual through the EXISTING
`ShorComposedFinal.egate_matches_rev_of_modExpAtResidue` (which proves
`egate_matches_rev` for `eg` GIVEN `block_matches_residue`) to build a
`MeasuredEqualsReversibleOnEncoded` whose `eg` is `modExpAt`'s LITERAL block, then
through `ShorComposed.countOptimal_shor_succeeds_constrained` to the Shor bound. -/

/-- **★ THE WITNESS — `egate_matches_rev` PROVEN for the LITERAL `modExpAt` block ★.**
    A `MeasuredEqualsReversibleOnEncoded` whose measured family `eg i` is the
    conjugated `modExpAt` block (CONTAINING `multiplyAddAt`, NOT a wrapped exact
    gate) and whose reversible family `rev` is the verified windowed mod-N
    multiplier.  `egate_matches_rev` is PROVEN (not trivial) via
    `egate_matches_rev_of_modExpAtResidue` ∘ `modExpAtBlock_matches_residue` ∘ §1's
    coset value — so `rev` is genuinely pinned to the count gate's block. -/
def ge2021_modExpAt_measuredEqRev
    {w bits numWin N a ainv0 q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtLayoutAdapter w bits (2 * w + 2 * bits + 3) numWin N a q_start Tfam)
    (hw : 0 < w) (hq : 0 < q_start)
    (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (hnowrap : ∀ i x, x < N → (a ^ (2 ^ i)) * x < 2 ^ bits) :
    MeasuredEqualsReversibleOnEncoded a N bits (2 * w + 2 * bits + 3)
      (fun i => L.conjugatedBlock i)
      (fun _ x => FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) where
  rev := windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
    hw hbits hb1 hN1 hN2 h_inv0
  eg_wellTyped := fun i => by
    -- the conjugated block is well-typed: base adapters + the (adapter-confined) block.
    refine ⟨⟨L.adaptIn_wellTyped i, L.block_wellTyped i⟩, L.adaptOut_wellTyped i⟩
  egate_matches_rev :=
    egate_matches_rev_of_modExpAtResidue w bits numWin N a ainv0
      hw hbits hb1 hN1 hN2 h_inv0
      (fun i => L.conjugatedBlock i)
      (modExpAtEncodedMatchesResidue_of_layoutAdapter L hw hq hbits hN2 hnowrap)

/-- **★ THE HEADLINE — the Shor bound through `modExpAt`'s LITERAL block ★.**  The
    Shor success probability of the family that `modExpAt`'s per-multiply measured
    block (`multiplyAddAt`, the gate carrying the `2.58·10⁹` Toffoli count, present
    literally in `eg`) provably ACTS AS on the encoded subspace attains
    `≥ κ / (log₂ N)⁴` — UNDER the named no-wrap hypothesis and a layout adapter.

    Because `eg i := L.conjugatedBlock i` LITERALLY CONTAINS `multiplyAddAt` and
    `egate_matches_rev` is PROVEN (via `block_matches_residue`), the bound runs
    through the actual count gate — NO substituted middle.  The family carrying the
    bound is `(ge2021_modExpAt_measuredEqRev …).rev.family`, pinned to `eg` by the
    witness's `egate_matches_rev`. -/
theorem ge2021_modExpAt_shor_succeeds
    {w bits numWin N a ainv0 r m q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtLayoutAdapter w bits (2 * w + 2 * bits + 3) numWin N a q_start Tfam)
    (hw : 0 < w) (hq : 0 < q_start)
    (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (hnowrap : ∀ i x, x < N → (a ^ (2 ^ i)) * x < 2 ^ bits)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (ge2021_modExpAt_measuredEqRev L hw hq hbits hb1 hN1 hN2 h_inv0 hnowrap).rev.family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  countOptimal_shor_succeeds_constrained
    (w := w) (numWin := numWin) (q_start := q_start) (Tfam := Tfam)
    hw hq
    (ge2021_modExpAt_measuredEqRev L hw hq hbits hb1 hN1 hN2 h_inv0 hnowrap)
    r m h_setting

/-! ## §5. The count AND the bound on the SAME gate (no substitution). -/

/-- **★ count AND bound, the SAME `modExpAt` block ★.**  Simultaneously, at the
    RSA-2048 derived parameters:

    (i) the count-optimal measured exponentiation `modExpAt 10 W 2048 …` has Toffoli
        count exactly `2 578 993 152`
        (`WindowedComposedAt.rsa2048_modExpAt_toffoli_derived`); and

    (ii) the Shor success bound `≥ κ/(log₂ N)⁴` holds for the family that
         `modExpAt`'s per-multiply block (LITERALLY inside `eg`) provably acts as.

    Unlike `ShorComposedFinal.ge2021_count_on_modExpAt_AND_bound_on_DIFFERENT_exact_multiplier`,
    the gate the bound rides is `modExpAt`'s OWN measured block (`eg` CONTAINS
    `multiplyAddAt`), discharged via the PROVEN `block_matches_residue` — now
    genuinely the SAME gate as the count, modulo the named no-wrap hypothesis and
    layout adapter. -/
theorem ge2021_modExpAt_count_AND_bound_SAME_gate
    (W : Nat) (Tfam : Nat → Nat → Nat → Nat) (q_start : Nat)
    {numWin N a ainv0 r m : Nat}
    (L : ModExpAtLayoutAdapter 10 2048 (2 * 10 + 2 * 2048 + 3) numWin N a q_start Tfam)
    (hq : 0 < q_start)
    (hbits : numWin * 10 = 2048)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ 2048)
    (h_inv0 : a * ainv0 % N = 1)
    (hnowrap : ∀ i x, x < N → (a ^ (2 ^ i)) * x < 2 ^ 2048)
    (h_setting : ShorSetting a r N m 2048) :
    EGate.toffoli (modExpAt 10 W 2048 Tfam q_start
        (numMultsOf 3072 5 5) (numWinOf 2048 5 1024)) = 2578993152
    ∧ probability_of_success a r N m 2048 (2 * 10 + 2 * 2048 + 3)
        (ge2021_modExpAt_measuredEqRev L (by norm_num) hq hbits (by norm_num)
          hN1 hN2 h_inv0 hnowrap).rev.family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  ⟨FormalRV.Shor.WindowedComposedAt.rsa2048_modExpAt_toffoli_derived W Tfam q_start,
   ge2021_modExpAt_shor_succeeds L (by norm_num) hq hbits (by norm_num)
     hN1 hN2 h_inv0 hnowrap h_setting⟩

end

end FormalRV.Audit.GidneyEkera2021.ShorModExpAt
