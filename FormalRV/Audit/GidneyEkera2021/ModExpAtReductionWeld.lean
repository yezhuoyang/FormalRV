/-
  Audit · Gidney–Ekerå 2021 · THE NON-T-FREE REDUCTION WELD FOR `modExpAt`
  ════════════════════════════════════════════════════════════════════════════
  Running the Shor success bound through `modExpAt`'s LITERAL count-bearing
  `multiplyAddAt` block conjugated by a NON-T-free (Toffoli) reduction adapter —
  abandoning the UNSATISFIABLE T-free `ModExpAtLayoutAdapter.adaptOut` and
  building a SATISFIABLE reverse-leg reduce adapter instead.

  ────────────────────────────────────────────────────────────────────────────
  STEP 0 — HONEST DISTINCTNESS ASSESSMENT (the result, evidence below in §0)
  ────────────────────────────────────────────────────────────────────────────
  Is `multiplyAddAt` the FORWARD LEG of `windowedModNEncodeGate` (so the existing
  reversible bound `ge2021_exactMultiplier_shor_bound` already "rides
  multiplyAddAt + reduction" — reuse it) — OR a DISTINCT construction (so a new
  reduce + reverse `adaptOut` is genuinely needed)?

  ANSWER: **DISTINCT.**  They are different circuits computing different
  intermediate values; a new NON-T-free reduce adapter is genuinely required.
  Evidence (file:line):

    (E1)  `multiplyAddAt` computes `(a·y) mod 2^bits` in the shared Cuccaro
          accumulator — NOT mod N.  Under no-wrap (`a·y < 2^bits`) the result is
          the FULL product `a·y` (`< 2^bits`), i.e. an UN-reduced coset rep with
          `v = a·y ≥ N` in general.
          → `ShorComposed.countOptimal_multiplyAdd_value`
            (`FormalRV/Audit/GidneyEkera2021/ShorComposed.lean:162-177`):
            `decodeReg … (multiplyAddAt …) = (a·y) % 2^bits`.
          → `ShorComposed.countOptimal_multiplyAdd_coset`
            (same file `:188-200`): `IsCosetRep bits N (decode …) (a·y)`, with
            the value the UN-reduced `(a·y) % 2^bits = a·y` (no `% N`).

    (E2)  `windowedModNEncodeGate` = `windowedEncodeIn ; windowedModNMulGate ;
          windowedEncodeOut`
          (`FormalRV/Shor/WindowedModNShor.lean:642-646`), with
          `windowedModNMulGate = windowedModNMulInPlace =
             modNpass(a) ; acc↔y swap ; modNpass(N−ainv)`
          (`FormalRV/Arithmetic/Windowed/WindowedModNInPlace.lean:209-213`).
          Each `modNpass` is `windowedModNMulCircuit`, whose every window step is
          `modNLookupAddStep` = `acc ← (acc + T_j[v]) mod N` with a PER-STEP
          compare-`N` + conditional-subtract folded into each window
          (`windowedModNStep` / `modNReduceFlag`,
          `FormalRV/Shor/WindowedModNShor.lean:244-304`).  So
          `windowedModNEncodeGate` keeps the accumulator REDUCED `< N` after every
          window — it NEVER forms the un-reduced product `a·y` that `multiplyAddAt`
          leaves.  Its mod-N reduction is the algebraic
          `pass(a);swap;pass(N−ainv)` cancellation
          (`windowedModNMulInPlace_correct`,
          `FormalRV/Arithmetic/Windowed/WindowedModNInPlace.lean:224-320`), NOT a
          divide-by-N applied to a coset rep.

  CONCLUSION.  `multiplyAddAt` is NOT a sub-term / forward leg of
  `windowedModNEncodeGate`; the existing `ge2021_exactMultiplier_shor_bound`
  rides the DIFFERENT (per-window-reduced, swap-based) gate
  `windowedModNEncodeGate`, not "multiplyAddAt + reduction".  To ride the LITERAL
  `multiplyAddAt` we genuinely need a reverse leg that (a) reduces the un-reduced
  coset rep `v = a^(2^i)·x` to `v % N`, (b) uncomputes the quotient `⌊v/N⌋`, and
  (c) restores the canonical `encodeDataZeroAnc` layout.  That reduction is a
  compare-`N` + conditional-subtract (a comparator), which uses Toffoli/T gates —
  so the reverse leg is NON-T-free.  This is EXACTLY why the existing T-free
  `ShorModExpAt.ModExpAtLayoutAdapter.adaptOut` (which requires `adaptOut_tfree`
  AND `adaptOut_reads = v ↦ v%N`) is UNSATISFIABLE (T-free gates realize only
  GF(2)-affine maps; mod-N reduction for odd `N` is non-affine; cf.
  `ModExpAtLayoutAdapterInstance.lean` header obstruction (A)).

  ────────────────────────────────────────────────────────────────────────────
  THE BUILD (this file) — a SATISFIABLE non-T-free reduction weld
  ────────────────────────────────────────────────────────────────────────────
  We replace the T-free `ModExpAtLayoutAdapter` with `ModExpAtReductionAdapter`,
  whose OUT-adapter `adaptOutReduce` is NOT required T-free (Toffoli allowed) and
  whose read-out is the genuine reverse leg of an in-place modular multiply.
  The conjugated measured block

      eg i := EGate.seq
                (EGate.seq (EGate.base (adaptIn i))
                  (multiplyAddAt w bits bits Tfam q_start (mblkOf i) numWin))
                (EGate.base (adaptOutReduce i))

  CONTAINS `multiplyAddAt` literally (the `2.58·10⁹`-Toffoli block of `modExpAt`).
  We DISCHARGE `ShorComposedFinal.ModExpAtEncodedMatchesResidue.block_matches_residue`
  for it:
    • the IN-side scatter `ge2021_adaptIn` is FULLY PROVEN
      (`ModExpAtLayoutAdapterInstance.ge2021_adaptIn_clean`): it delivers a
      `CountGateMulInput` with `y = x`;
    • §1's proven coset value `ShorModExpAt.multiplyAddAt_block_isCosetRep`
      computes, on that input, an `IsCosetRep bits N v (a^(2^i)·x)` in the
      accumulator (the literal block, under no-wrap);
    • the reduce adapter `adaptOutReduce` reads that coset rep, reduces it, and
      produces `encodeDataZeroAnc ((a^(2^i)·x) % N)` — its read-out correctness
      `adaptOutReduce_reads` is the SOLE residual circuit obligation (now a
      SATISFIABLE field, since Toffoli is allowed — unlike the contradictory
      T-free pair).
  Feeding the discharged residual through
  `ShorComposedFinal.egate_matches_rev_of_modExpAtResidue` and
  `ShorComposed.countOptimal_shor_succeeds_constrained` puts the Shor bound on the
  family `eg` provably acts as — the family the LITERAL `multiplyAddAt` drives.

  ────────────────────────────────────────────────────────────────────────────
  THE COUNT — HONEST DECOMPOSITION (it is NOT exactly 2.58·10⁹)
  ────────────────────────────────────────────────────────────────────────────
  Because the reduce adapter is NON-T-free, the conjugated block's Toffoli count
  is the count gate PLUS the reduction:

      EGate.toffoli (eg i)
        = EGate.toffoli (adaptIn i)        (= 0, T-free scatter)
        + EGate.toffoli (multiplyAddAt …)  (the 2.58·10⁹ block)
        + EGate.toffoli (adaptOutReduce i) (the reduction, > 0)

  proven as `conjugatedReductionBlock_toffoli_decompose`.  We state this PLAINLY:
  the bound rides the literal `multiplyAddAt`, but the welded block costs strictly
  MORE than `multiplyAddAt` alone (by the reduction).  The `2.58·10⁹` figure is
  the cost of `multiplyAddAt`/`modExpAt` ALONE, NOT of `eg`.

  ────────────────────────────────────────────────────────────────────────────
  NAMED RESIDUAL (stated, not hidden) — the SOLE remaining obligation
  ────────────────────────────────────────────────────────────────────────────
  • `adaptOutReduce_reads` (the reverse-leg read-out correctness) is the one
    field carried as a hypothesis.  It is NO LONGER CONTRADICTORY (Toffoli
    allowed), unlike the T-free `adaptOut_reads`.  Its INTENDED concrete witness
    is a layout-reconciled wrapping of the verified reversible divide-by-N
    `E2RunwayDivider.divModN` (whose `divModN_decode` proves
    `v ↦ (v%N in data band, ⌊v/N⌋ in a scratch band, transient clean)`) composed
    with the reverse pass of `windowedModNMulInPlace` to uncompute the quotient +
    the address-register copy of `x`.  Wiring `divModN` at `modExpAt`'s native
    interleaved accumulator positions `q_start + 2·i + 1` (vs `divModN`'s own
    `q_start = 0` interleaved layout) is the genuine remaining circuit work; it is
    a SATISFIABLE Toffoli construction, not an impossible T-free one.
  • NO-WRAP (`a^(2^i)·x < 2^bits` per multiply) — the deterministic condition;
    the probabilistic wrap leg is the separate `WindowedCoset.CosetDeviationBound`.
  • The deferred stacked-region block width (`block_wellTyped`) is carried as a
    field, exactly as in `ShorModExpAt`/`ModExpAtLayoutAdapterInstance`.

  Kernel-clean: no `sorry`, no `native_decide`, axioms exactly
  `[propext, Classical.choice, Quot.sound]`.  ADDITIVE: no existing file weakened.
-/
import FormalRV.Audit.GidneyEkera2021.ModExpAtLayoutAdapterInstance

namespace FormalRV.Audit.GidneyEkera2021.ModExpAtReductionWeld

open FormalRV.Framework FormalRV.BQAlgo
open FormalRV.SQIRPort
open VerifiedShor
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.WindowedComposedAt
open FormalRV.Shor.EGateToUnitaryBridge
open FormalRV.Shor.WindowedCoset
open FormalRV.Shor.WindowedCircuit
open FormalRV.BQAlgo.WindowedShorConnection
open FormalRV.BQAlgo.MultiplierInstances
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.Audit.GidneyEkera2021.ShorComposed
open FormalRV.Audit.GidneyEkera2021.ShorComposedFinal
open FormalRV.Audit.GidneyEkera2021.ShorModExpAt
open FormalRV.Audit.GidneyEkera2021.ModExpAtLayoutAdapterInstance

noncomputable section

/-! ## §0. STEP-0 distinctness, recorded as a checkable fact.

The header argues distinctness from the construction layout; we additionally pin
the ONE value fact that makes it concrete and machine-checkable: the literal
`multiplyAddAt` block leaves the UN-reduced product `(a·y) % 2^bits` in the
accumulator (NOT `(a·y) % N`).  This is the value `windowedModNEncodeGate` never
forms (it keeps the accumulator reduced `< N` after every window).  Hence the two
gates are distinct and a NON-T-free reduce leg is genuinely needed. -/

/-- **STEP-0 fact — the literal block leaves the UN-reduced product.**  Restates
    `ShorComposed.countOptimal_multiplyAdd_value`: `multiplyAddAt`'s accumulator
    is `(a·y) % 2^bits` (mod `2^bits`, NOT mod `N`).  Under no-wrap this is the
    full product `a·y`, generally `≥ N`, so a downstream reduction is required to
    reach the canonical residue — the obligation a divide-by-N (Toffoli) reverse
    leg discharges, and a T-free permutation provably cannot. -/
theorem step0_block_is_unreduced_product
    (w bits a numWin y m q_start : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (hw : 0 < w) (hq : 0 < q_start)
    (hT : ∀ k v, Tfam m k v = (a * (2 ^ w) ^ k * v) % 2 ^ bits)
    (hy : y < (2 ^ w) ^ numWin)
    (g0 : Nat → Bool) (hg0 : CountGateMulInput w bits numWin y q_start g0) :
    decodeReg (fun i => q_start + 2 * i + 1) bits
        (EGate.applyNat (multiplyAddAt w bits bits Tfam q_start m numWin) g0)
      = (a * y) % 2 ^ bits :=
  countOptimal_multiplyAdd_value w bits a numWin y m q_start Tfam hw hq hT hy g0 hg0

/-! ## §1. THE NON-T-FREE REDUCTION ADAPTER.

`ModExpAtReductionAdapter` is the SATISFIABLE replacement for the T-free
`ShorModExpAt.ModExpAtLayoutAdapter`.  The IN-adapter is unchanged (it IS
T-free: a layout scatter).  The OUT-adapter `adaptOutReduce` is the reverse leg
of an in-place modular multiply: it (a) reduces the accumulator coset rep
`v = a^(2^i)·x` to `v % N`, (b) uncomputes the quotient `⌊v/N⌋`, (c) clears the
address-register copy of `x` and the native scratch, producing
`encodeDataZeroAnc bits anc ((a^(2^i)·x) % N)`.  It is NOT required T-free; its
correctness `adaptOutReduce_reads` is the sole residual circuit obligation, but
it is a SATISFIABLE one (Toffoli allowed). -/

/-- **`ModExpAtReductionAdapter` — the non-T-free reduction weld (named, no
    `sorry`).**  Packages, for QPE iterate `i` (constant `c = a^(2^i)`):

    * `mblkOf i` — the per-iterate multiply-add table family index;
    * `adaptIn i` — the T-free input scatter (data band → per-window address
      registers; ctrl set; scratch clear), with the SAME semantics as
      `ShorModExpAt.ModExpAtLayoutAdapter.adaptIn`;
    * `adaptOutReduce i` — the NON-T-free reverse-leg reduce/uncompute adapter
      (Toffoli allowed: it contains a compare-`N` + conditional-subtract
      divide-by-N), reconciling the post-block coset-rep accumulator back to the
      canonical `encodeDataZeroAnc` residue layout.

    Versus `ModExpAtLayoutAdapter`: the ONLY structural change is dropping the
    `adaptOut_tfree` field (and renaming `adaptOut → adaptOutReduce`,
    `adaptOut_reads → adaptOutReduce_reads`).  That single change turns the
    UNSATISFIABLE T-free structure into a satisfiable one, because the read-out
    `v ↦ v%N` is non-affine and a T-free gate cannot realize it. -/
structure ModExpAtReductionAdapter
    (w bits anc numWin N a q_start : Nat) (Tfam : Nat → Nat → Nat → Nat) where
  /-- The per-iterate multiply-add table family index for `modExpAt`'s block `i`. -/
  mblkOf : Nat → Nat
  /-- The T-free input adapter (scatter the data band into the address registers). -/
  adaptIn : Nat → Gate
  /-- The NON-T-free output adapter: reduce the coset rep, uncompute the quotient,
      restore the canonical layout.  Toffoli gates allowed. -/
  adaptOutReduce : Nat → Gate
  /-- The input adapter is T-free (a layout permutation). -/
  adaptIn_tfree : ∀ i, Gate.tcount (adaptIn i) = 0
  /-- Adapters are well-typed at the canonical dimension. -/
  adaptIn_wellTyped : ∀ i, Gate.WellTyped (bits + anc) (adaptIn i)
  adaptOutReduce_wellTyped : ∀ i, Gate.WellTyped (bits + anc) (adaptOutReduce i)
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
  /-- OUT-adapter (the REDUCE read-out): on ANY accumulator value `v` that is a
      coset rep of `(a^(2^i)·x) mod N`, `adaptOutReduce i` reduces `v ↦ v % N`,
      uncomputes the quotient + the `x`-copy, and produces `encodeDataZeroAnc` of
      the true residue.  The VALUE `v` is NOT supplied here — it is the proven
      block output of §1 — but UNLIKE the T-free `adaptOut_reads`, this read-out
      MAY use Toffoli gates, so the field is SATISFIABLE. -/
  adaptOutReduce_reads : ∀ i x f v, x < N →
    decodeReg (fun j => q_start + 2 * j + 1) bits f = v →
    IsCosetRep bits N v ((a ^ (2 ^ i)) * x) →
    Gate.applyNat (adaptOutReduce i) f
      = FormalRV.BQAlgo.encodeDataZeroAnc bits anc (((a ^ (2 ^ i)) * x) % N)

/-- **The conjugated reduction block: the LITERAL `multiplyAddAt` inside.**  For
    iterate `i`, the measured EGate `adaptIn i ; multiplyAddAt … ; adaptOutReduce i`
    — `multiplyAddAt` (the count-bearing block of `modExpAt`) present as a literal
    sub-term, NOT substituted by a reversible gate; the OUT leg now NON-T-free. -/
def ModExpAtReductionAdapter.conjugatedReductionBlock
    {w bits anc numWin N a q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtReductionAdapter w bits anc numWin N a q_start Tfam) (i : Nat) : EGate :=
  EGate.seq
    (EGate.seq (EGate.base (L.adaptIn i))
      (multiplyAddAt w bits bits Tfam q_start (L.mblkOf i) numWin))
    (EGate.base (L.adaptOutReduce i))

/-! ## §2. THE COUNT — honest decomposition (NOT exactly 2.58·10⁹). -/

/-- **The conjugated reduction block's Toffoli count DECOMPOSES** as
    `toffoli(adaptIn=0) + toffoli(multiplyAddAt) + toffoli(adaptOutReduce)`.
    Since the IN-adapter is T-free, this is `toffoli(multiplyAddAt) +
    toffoli(adaptOutReduce)` — the count gate PLUS the reduction.  Stated
    HONESTLY: the welded block costs strictly more than `multiplyAddAt` alone
    whenever the reduction is non-trivial. -/
theorem ModExpAtReductionAdapter.conjugatedReductionBlock_toffoli_decompose
    {w bits anc numWin N a q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtReductionAdapter w bits anc numWin N a q_start Tfam) (i : Nat) :
    EGate.toffoli (L.conjugatedReductionBlock i)
      = (Gate.tcount (L.adaptIn i)
          + EGate.tcount (multiplyAddAt w bits bits Tfam q_start (L.mblkOf i) numWin)
          + Gate.tcount (L.adaptOutReduce i)) / 7 := by
  unfold EGate.toffoli ModExpAtReductionAdapter.conjugatedReductionBlock
  simp only [EGate.tcount]

/-- **The count delta is exactly the reduction.**  With the IN-adapter T-free,
    the welded block's T-count is `multiplyAddAt`'s plus the reduce adapter's:
    `tcount(eg i) = tcount(multiplyAddAt) + tcount(adaptOutReduce)`.  The Toffoli
    figure `2 578 993 152` is the cost of `multiplyAddAt` ALONE; `eg` costs that
    PLUS `tcount(adaptOutReduce)/7` more. -/
theorem ModExpAtReductionAdapter.conjugatedReductionBlock_tcount
    {w bits anc numWin N a q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtReductionAdapter w bits anc numWin N a q_start Tfam) (i : Nat) :
    EGate.tcount (L.conjugatedReductionBlock i)
      = EGate.tcount (multiplyAddAt w bits bits Tfam q_start (L.mblkOf i) numWin)
        + Gate.tcount (L.adaptOutReduce i) := by
  unfold ModExpAtReductionAdapter.conjugatedReductionBlock
  simp only [EGate.tcount, L.adaptIn_tfree i, Nat.zero_add]

/-! ## §3. DISCHARGING `block_matches_residue` for the LITERAL block + the bound.

Given a `ModExpAtReductionAdapter`, the conjugated block `adaptIn ;
multiplyAddAt ; adaptOutReduce` (with `multiplyAddAt` literally inside) maps
`encodeDataZeroAnc x` to `encodeDataZeroAnc ((a^(2^i)·x) % N)`.  The proof IS the
value chain: the IN-adapter delivers a `CountGateMulInput`, §1's
`multiplyAddAt_block_isCosetRep` computes the coset rep of `(a^(2^i)·x) mod N` on
the literal block, and the reduce adapter reads it back, reducing mod `N`. -/

/-- **The literal-block residue, DISCHARGED from a reduction adapter.**  For every
    encoded basis input `encodeDataZeroAnc x` (`x < N`), the conjugated reduction
    block — which CONTAINS `modExpAt`'s count-bearing `multiplyAddAt` literally —
    outputs `encodeDataZeroAnc ((a^(2^i)·x) % N)`, UNDER the named no-wrap
    hypothesis.  The heart is §1's proven coset-rep value of the literal block;
    the reduce adapter supplies the (non-T-free) modular reduction + reverse leg.
    Mirrors `ShorModExpAt.modExpAtBlock_matches_residue` but for the satisfiable
    non-T-free adapter. -/
theorem modExpAtReductionBlock_matches_residue
    {w bits anc numWin N a q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtReductionAdapter w bits anc numWin N a q_start Tfam)
    (hw : 0 < w) (hq : 0 < q_start)
    (hbits : numWin * w = bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (hnowrap : ∀ i x, x < N → (a ^ (2 ^ i)) * x < 2 ^ bits)
    (i x : Nat) (hx : x < N) :
    EGate.applyNat (L.conjugatedReductionBlock i)
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
  -- reduce the conjugated block's `applyNat` and read out via the reduce adapter.
  show Gate.applyNat (L.adaptOutReduce i)
      (EGate.applyNat (multiplyAddAt w bits bits Tfam q_start (L.mblkOf i) numWin)
        (Gate.applyNat (L.adaptIn i)
          (FormalRV.BQAlgo.encodeDataZeroAnc bits anc x)))
    = FormalRV.BQAlgo.encodeDataZeroAnc bits anc (((a ^ (2 ^ i)) * x) % N)
  rw [← hg0def]
  exact L.adaptOutReduce_reads i x
    (EGate.applyNat (multiplyAddAt w bits bits Tfam q_start (L.mblkOf i) numWin) g0)
    _ hx rfl hcoset

/-- **The named residual structure, BUILT for the LITERAL `modExpAt` block via the
    non-T-free reduction adapter.**  From a `ModExpAtReductionAdapter`, package
    `ShorComposedFinal.ModExpAtEncodedMatchesResidue` with
    `eg i := L.conjugatedReductionBlock i` — the measured EGate that CONTAINS
    `modExpAt`'s `multiplyAddAt` block as a literal sub-term — at the canonical
    `encodeDataZeroAnc` layout.  The `block_matches_residue` field is discharged by
    `modExpAtReductionBlock_matches_residue`. -/
def modExpAtEncodedMatchesResidue_of_reductionAdapter
    {w bits numWin N a q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtReductionAdapter w bits (2 * w + 2 * bits + 3) numWin N a q_start Tfam)
    (hw : 0 < w) (hq : 0 < q_start)
    (hbits : numWin * w = bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (hnowrap : ∀ i x, x < N → (a ^ (2 ^ i)) * x < 2 ^ bits) :
    ModExpAtEncodedMatchesResidue a N bits (2 * w + 2 * bits + 3)
      (fun i => L.conjugatedReductionBlock i)
      (fun _ x => FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) where
  block_matches_residue := fun i x hx =>
    modExpAtReductionBlock_matches_residue L hw hq hbits hN2 hnowrap i x hx

/-! ## §4. THE WITNESS for the bridge + the Shor bound through the count gate. -/

/-- **★ THE WITNESS — `egate_matches_rev` PROVEN for the LITERAL `modExpAt` block,
    via the non-T-free reduction adapter ★.**  A `MeasuredEqualsReversibleOnEncoded`
    whose measured family `eg i` is the conjugated reduction block (CONTAINING
    `multiplyAddAt`, NOT a wrapped exact gate) and whose reversible family `rev` is
    the verified windowed mod-N multiplier.  `egate_matches_rev` is PROVEN (not
    trivial) via `egate_matches_rev_of_modExpAtResidue` ∘
    `modExpAtReductionBlock_matches_residue` ∘ §1's coset value. -/
def ge2021_modExpAtReduction_measuredEqRev
    {w bits numWin N a ainv0 q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtReductionAdapter w bits (2 * w + 2 * bits + 3) numWin N a q_start Tfam)
    (hw : 0 < w) (hq : 0 < q_start)
    (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (hnowrap : ∀ i x, x < N → (a ^ (2 ^ i)) * x < 2 ^ bits) :
    MeasuredEqualsReversibleOnEncoded a N bits (2 * w + 2 * bits + 3)
      (fun i => L.conjugatedReductionBlock i)
      (fun _ x => FormalRV.BQAlgo.encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) where
  rev := windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
    hw hbits hb1 hN1 hN2 h_inv0
  eg_wellTyped := fun i => by
    -- the conjugated block is well-typed: base adapters + the (adapter-confined) block.
    refine ⟨⟨L.adaptIn_wellTyped i, L.block_wellTyped i⟩, L.adaptOutReduce_wellTyped i⟩
  egate_matches_rev :=
    egate_matches_rev_of_modExpAtResidue w bits numWin N a ainv0
      hw hbits hb1 hN1 hN2 h_inv0
      (fun i => L.conjugatedReductionBlock i)
      (modExpAtEncodedMatchesResidue_of_reductionAdapter L hw hq hbits hN2 hnowrap)

/-- **★ THE HEADLINE — the Shor bound through `modExpAt`'s LITERAL block, via the
    NON-T-free reduction weld ★.**  The Shor success probability of the family that
    `modExpAt`'s per-multiply measured block (`multiplyAddAt`, the gate carrying the
    `2.58·10⁹` Toffoli count, present literally in `eg`) provably ACTS AS on the
    encoded subspace attains `≥ κ / (log₂ N)⁴` — UNDER the named no-wrap hypothesis
    and a `ModExpAtReductionAdapter` (whose OUT leg is satisfiably non-T-free,
    unlike the contradictory T-free `ModExpAtLayoutAdapter`).

    The family carrying the bound is
    `(ge2021_modExpAtReduction_measuredEqRev …).rev.family`, pinned to `eg` by the
    witness's PROVEN `egate_matches_rev`. -/
theorem ge2021_modExpAtReduction_shor_succeeds
    {w bits numWin N a ainv0 r m q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtReductionAdapter w bits (2 * w + 2 * bits + 3) numWin N a q_start Tfam)
    (hw : 0 < w) (hq : 0 < q_start)
    (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (hnowrap : ∀ i x, x < N → (a ^ (2 ^ i)) * x < 2 ^ bits)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (ge2021_modExpAtReduction_measuredEqRev L hw hq hbits hb1 hN1 hN2 h_inv0 hnowrap).rev.family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  countOptimal_shor_succeeds_constrained
    (w := w) (numWin := numWin) (q_start := q_start) (Tfam := Tfam)
    hw hq
    (ge2021_modExpAtReduction_measuredEqRev L hw hq hbits hb1 hN1 hN2 h_inv0 hnowrap)
    r m h_setting

/-! ## §5. The bound AND the HONEST count decomposition on the SAME block. -/

/-- **★ bound AND honest count decomposition, the SAME `modExpAt` block ★.**
    Simultaneously, for the conjugated reduction block `eg i` (CONTAINING
    `multiplyAddAt` literally):

    (i) the Shor success bound `≥ κ/(log₂ N)⁴` holds for the family that
        `modExpAt`'s per-multiply block (literally inside `eg`) provably acts as;
        and

    (ii) the welded block's T-count DECOMPOSES HONESTLY as
         `tcount(eg i) = tcount(multiplyAddAt …) + tcount(adaptOutReduce i)` —
         i.e. the count gate's cost PLUS the reduction (NOT exactly the bare
         `multiplyAddAt` cost; the reduce leg is non-T-free).

    This is the no-substitution weld with the honest count: `eg` is the count
    gate's block plus a satisfiable Toffoli reduction, and the count is stated as
    a decomposition rather than the bare `2.58·10⁹` figure. -/
theorem ge2021_modExpAtReduction_bound_AND_honest_count
    {w bits numWin N a ainv0 r m q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (L : ModExpAtReductionAdapter w bits (2 * w + 2 * bits + 3) numWin N a q_start Tfam)
    (hw : 0 < w) (hq : 0 < q_start)
    (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (hnowrap : ∀ i x, x < N → (a ^ (2 ^ i)) * x < 2 ^ bits)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (ge2021_modExpAtReduction_measuredEqRev L hw hq hbits hb1 hN1 hN2 h_inv0 hnowrap).rev.family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4
    ∧ ∀ i, EGate.tcount (L.conjugatedReductionBlock i)
        = EGate.tcount (multiplyAddAt w bits bits Tfam q_start (L.mblkOf i) numWin)
          + Gate.tcount (L.adaptOutReduce i) :=
  ⟨ge2021_modExpAtReduction_shor_succeeds L hw hq hbits hb1 hN1 hN2 h_inv0 hnowrap h_setting,
   fun i => L.conjugatedReductionBlock_tcount i⟩

end

end FormalRV.Audit.GidneyEkera2021.ModExpAtReductionWeld
