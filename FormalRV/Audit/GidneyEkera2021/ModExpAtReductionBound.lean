/-
  Audit · Gidney–Ekerå 2021 · THE END-TO-END SHOR BOUND RIDING THE CONCRETE
  REVERSIBLE GATE `egRfree … unmulConcrete` — UNCONDITIONAL, KERNEL-CLEAN.
  ════════════════════════════════════════════════════════════════════════════
  THE FINAL ASSEMBLY.  This module rides the Shor success bound `≥ κ/(log₂N)⁴`
  on the CONCRETE, fully-reversible gate family

      eg i := egRfree w bits numWin cm N a (unmulConcrete w bits numWin a) i

  which literally contains the measured count-bearing `multiplyAddAt` as its
  sub-term G2 (`ModExpAtReductionDirect.egRfree_contains_multiplyAddAt`), with the
  multiply-UNcompute G6 the concrete reversible `unmulConcrete = Gate.reverse radd`
  (`ModExpAtUnmul`).  UNCONDITIONAL: only the standard sizing
  (`hw/hbits/hb1/hN1/hN2/hcm`), a base inverse `a·ainv0 ≡ 1 (mod N)`, and a
  `ShorSetting`.  Nothing is assumed.

  ────────────────────────────────────────────────────────────────────────────
  WHAT IS DELIVERED (all kernel-clean — no `sorry`, no `native_decide`).
  ────────────────────────────────────────────────────────────────────────────
  Mirroring `ModExpAtResidueInstance.lean` §3-§5 EXACTLY, but with the concrete
  reversible `egRfree … unmulConcrete` family and the PADDED reversible consumer
  (`PaddedRevFamily`), at a wide ancilla `ancBig := Rbase w bits numWin cm` that
  dominates every sub-gate's native footprint:

    • `multiplyAddAt_wellTypedAt` — the measured `multiplyAddAt` (= `egG2`) is
      `EGate.WellTypedAt` at `dimRadd` (mirrors `ModExpAtUnmul`'s REVERSIBLE
      `radd_wellTyped` on the measured side: per-level `EGate.mz` is well-typed via
      `QROMRevWT.anc_lt`, the final `mzList` via `mzList_wellTypedAt`).
    • `egRfree_wellTyped` — the WHOLE 7-gate measured `egRfree … unmulConcrete` is
      `EGate.WellTypedAt (bits + ancBig)`; G1/G7 via `ge2021_adaptIn_wellTyped`
      + `reverse_wellTyped`; G2 via the above; G3/G5 via `divModNAt_wellTyped`
      + `reverse_wellTyped`; G6 (`unmulConcrete = reverse radd`) via `radd_wellTyped`
      + `reverse_wellTyped`; G8 via `inPlaceMulDataAt_wellTyped`.  All lifted to
      `bits + ancBig` by `Gate.WellTyped.mono` / `EGate.WellTypedAt.mono`.
    • `egRfree_residue_ancBig` — the UNCONDITIONAL residue identity
      `ModExpAtEncodedMatchesResidue a N bits ancBig (egRfree…) (encodeDataZeroAnc bits ancBig)`,
      transferred from `ModExpAtUnmul.egRfree_matchesResidue_unconditional` (which
      lives at `2w+2bits+3`) by anc-IRRELEVANCE of `encodeDataZeroAnc` on the
      `< 2^bits` operands (the proven local lemma `encodeDataZeroAnc_anc_irrel`).
    • `egRfree_measuredEqRev` — a `MeasuredEqualsReversibleOnEncoded` at `ancBig`,
      `rev := paddedRevFamily_verifiedModMulFamily`, `eg_wellTyped := egRfree_wellTyped`,
      `egate_matches_rev := egate_matches_rev_of_modExpAtResidue_pad ∘ egRfree_residue_ancBig`.
    • `egRfree_shor_succeeds` — the Shor bound `≥ κ/(log₂N)⁴` on
      `(…measuredEqRev…).rev.family` via `countOptimal_shor_succeeds_constrained`.
    • `egRfree_shor_AND_count` — the bound ∧ the HONEST Toffoli-count decomposition
      `EGate.tcount (egRfree…) = tcount(multiplyAddAt) + 2·tcount(divModNAt)
        + tcount(unmulConcrete) + tcount(inPlaceMulDataAt)` (`eg_tcount`); and
      `tcount(unmulConcrete) = tcount(radd)` (`unmulConcrete_tcount`).  G1/G7 T-free.

  ────────────────────────────────────────────────────────────────────────────
  HONEST FRONTIER.
  ────────────────────────────────────────────────────────────────────────────
  The bound RIDES `.rev.family` — the PADDED verified windowed mod-N reversible
  family (`paddedRevFamily_verifiedModMulFamily`), which the concrete `egRfree`
  PROVABLY matches on the encoded subspace (`egate_matches_rev` PROVEN from the
  residue identity, not trivial).  The measured count gate `multiplyAddAt` is
  LITERALLY present in `egRfree` (G2) — its measurement-uncompute clears are
  syntactically there — but it is functionally DECORATIVE in the value chain: the
  G3;G5 reduction collapses to identity and G6 = `unmulConcrete` (the reversible
  reconstruction's inverse) uncomputes G2 back to the scattered input, so the
  in-place work that produces the residue is the REUSED verified
  `windowedModNMulInPlace` inside G8 (`inPlaceMulDataAt`).  This is the honest
  state: a fully-reversible gate that CONTAINS the count gate, rides the bound via
  the verified reversible family it matches, and carries the count gate's
  measured Toffoli figure inside the honest count decomposition.

  Kernel-clean: no `sorry`, no `native_decide`; axioms ⊆ {propext,
  Classical.choice, Quot.sound}.  ADDITIVE: no existing file weakened.
-/
import FormalRV.Audit.GidneyEkera2021.ModExpAtUnmul
import FormalRV.Audit.GidneyEkera2021.PaddedRevFamily
import FormalRV.Arithmetic.ModularAdder.GidneyModAddRegWellTyped

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace FormalRV.Audit.GidneyEkera2021.ModExpAtReductionBound

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.SQIRPort
open VerifiedShor
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasUncomputeAt
open FormalRV.Shor.WindowedComposed (seqAll)
open FormalRV.Shor.WindowedComposedAt
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.EGateToUnitaryBridge
open FormalRV.Shor.GidneyInPlace.GateReversible (Gate.reverse)
open FormalRV.Arithmetic.ModularAdder.GidneyModAddRegWellTyped (mzList_wellTypedAt EGate.WellTypedAt.mono)
open FormalRV.Audit.GidneyEkera2021.ShorComposed (countOptimal_shor_succeeds_constrained)
open FormalRV.Audit.GidneyEkera2021.ShorComposedFinal
open FormalRV.Audit.GidneyEkera2021.DivModNAt
open FormalRV.Audit.GidneyEkera2021.InPlaceMulDataAt
open FormalRV.Audit.GidneyEkera2021.ModExpAtLayoutAdapterInstance
open FormalRV.Audit.GidneyEkera2021.PaddedRevFamily
open FormalRV.Audit.GidneyEkera2021.ModExpAtReductionDirect
open FormalRV.Audit.GidneyEkera2021.ModExpAtUnmul
open FormalRV.BQAlgo.MultiplierInstances (modInv)

noncomputable section

/-! ## §0. The total dimension `D := bits + ancBig`.

We take `ancBig := Rbase w bits numWin cm = dimDivAt w bits numWin cm 1 + Dmul w bits`,
the R-register base of `ModExpAtReductionDirect`, which DOMINATES every sub-gate's
native footprint:

  * G2 / G6 (`multiplyAddAt` / `unmulConcrete = reverse radd`): `dimRadd ≤ dimDivAt`
    (since `dimDivAt = scratchBase + dimDiv` and `dimRadd = scratchBase`);
  * G3 / G5 (`divModNAt` / its reverse): `dimDivAt`;
  * G8 (`inPlaceMulDataAt`-wrapped): `Dmul`;
  * G1 / G7 (`ge2021_adaptIn` / its reverse): scatter addresses `< scratchBase ≤ dimRadd`.

`Rbase = dimDivAt + Dmul ≥ dimDivAt, Dmul, dimRadd` and `Rbase ≥ 2·w + 2·bits + 3`
(since `Dmul = 4·bits + 2·w + 3 ≥ 2·w + 2·bits + 3`), so it also satisfies the
padded consumer's `hpad`. -/

/-- The wide ancilla count — the R-register base, dominating all sub-gate footprints. -/
def ancBig (w bits numWin cm : Nat) : Nat := Rbase w bits numWin cm

/-- `ancBig` satisfies the padded consumer's `hpad : 2·w + 2·bits + 3 ≤ ancBig`.
    (`Rbase ≥ Dmul = 4·bits + 2·w + 3`.) -/
theorem ancBig_pad (w bits numWin cm : Nat) :
    2 * w + 2 * bits + 3 ≤ ancBig w bits numWin cm := by
  unfold ancBig Rbase Dmul InPlaceMulDataAt.scratchBase InPlaceMulDataAt.dimNative
    InPlaceMulDataAt.yBase
  omega

/-- The total dimension dominates `dimDivAt` (for G3/G5). -/
theorem D_ge_dimDivAt (w bits numWin cm : Nat) :
    dimDivAt w bits numWin cm 1 ≤ bits + ancBig w bits numWin cm := by
  unfold ancBig Rbase; omega

/-- The total dimension dominates `Dmul` (for G8). -/
theorem D_ge_Dmul (w bits : Nat) (numWin cm : Nat) :
    Dmul w bits ≤ bits + ancBig w bits numWin cm := by
  unfold ancBig Rbase; omega

/-- The total dimension dominates `dimRadd` (for G2/G6). -/
theorem D_ge_dimRadd (w bits numWin cm : Nat) :
    dimRadd w bits numWin ≤ bits + ancBig w bits numWin cm := by
  unfold ancBig Rbase dimRadd dimDivAt DivModNAt.scratchBase; omega

/-! ## §1. Well-typedness of the measured `multiplyAddAt` (= `egG2`) at `dimRadd`.

The measured `multiplyAddAt` has IDENTICAL wire structure to the reversible mirror
`radd` of `ModExpAtUnmul` (proven well-typed via `radd_wellTyped`), differing only
in the per-level final step (`EGate.mz (ancBase + d)` vs `Gate.CCX …`) and the
final clear (`mzList` vs second read).  We mirror that proof on the EGate side:
the `mz` needs only `ancBase + d < dim` (= `QROMRevWT.anc_lt`), the `mzList` is
discharged by `mzList_wellTypedAt`.  REUSES `QROMRevWT`, `cxGates_wellTyped_local`,
`radd_window_QROMRevWT` from `ModExpAtUnmul`. -/

/-- The measured `unaryQROMAt` is `EGate.WellTypedAt` under `QROMRevWT` (EGate
    analogue of `unaryQROMAtRev_wellTyped`). -/
theorem unaryQROMAt_wellTypedAt (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase dim : Nat) (hdim : 0 < dim) :
    ∀ (d ctrl base : Nat), QROMRevWT pos W addrBase ancBase d ctrl dim →
      EGate.WellTypedAt dim (unaryQROMAt pos W T addrBase ancBase d ctrl base)
  | 0, ctrl, base, H => by
      show Gate.WellTyped dim (cx_gates_from_indices ctrl (wordCnotsAt pos W (T base)))
      apply cxGates_wellTyped_local dim ctrl _ hdim H.ctrl_lt
      intro t ht
      obtain ⟨j, hj, _, rfl⟩ := (mem_wordCnotsAt pos W (T base) t).mp ht
      exact ⟨H.word_lt j hj, H.ctrl_word j hj⟩
  | d + 1, ctrl, base, H => by
      have hlt := Nat.lt_succ_self d
      have hcd_lt  : ancBase + d < dim := H.anc_lt d hlt
      have had_lt  : addrBase + d < dim := H.addr_lt d hlt
      have hctrl_ad : ctrl ≠ addrBase + d := H.ctrl_addr d hlt
      have hctrl_cd : ctrl ≠ ancBase + d := H.ctrl_anc d hlt
      have had_cd  : addrBase + d ≠ ancBase + d := H.addr_anc d d hlt hlt
      have Hrec : QROMRevWT pos W addrBase ancBase d (ancBase + d) dim := by
        refine ⟨hcd_lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact fun i hi => H.addr_lt i (Nat.lt_succ_of_lt hi)
        · exact fun i hi => H.anc_lt i (Nat.lt_succ_of_lt hi)
        · exact fun j hj => H.word_lt j hj
        · exact fun i hi => Ne.symm (H.addr_anc i d (Nat.lt_succ_of_lt hi) hlt)
        · exact fun i hi h => by omega
        · exact fun i i' hi hi' => H.addr_anc i i' (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hi')
        · exact fun i j hi hj => H.addr_word i j (Nat.lt_succ_of_lt hi) hj
        · exact fun i j hi hj => H.anc_word i j (Nat.lt_succ_of_lt hi) hj
        · exact fun j hj => H.anc_word d j hlt hj
      refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · exact ⟨H.ctrl_lt, had_lt, hcd_lt, hctrl_ad, hctrl_cd, had_cd⟩
      · exact unaryQROMAt_wellTypedAt pos W T addrBase ancBase dim hdim d (ancBase + d)
          (base + 2 ^ d) Hrec
      · exact ⟨H.ctrl_lt, hcd_lt, hctrl_cd⟩
      · exact unaryQROMAt_wellTypedAt pos W T addrBase ancBase dim hdim d (ancBase + d)
          base Hrec
      · exact ⟨H.ctrl_lt, hcd_lt, hctrl_cd⟩
      · exact hcd_lt   -- EGate.mz (ancBase + d) : ancBase + d < dim

/-- The measured `babbushLookupAddAt` is `EGate.WellTypedAt` (EGate analogue of
    `babbushLookupAddAtRev_wellTyped`; the final `mzList` via `mzList_wellTypedAt`). -/
theorem babbushLookupAddAt_wellTypedAt (w W : Nat) (T : Nat → Nat)
    (bits addrBase ancBase q_start dim : Nat) (hdim : 0 < dim) (hW : W ≤ bits)
    (hQ : QROMRevWT (addendIdx q_start) W addrBase ancBase w 0 dim)
    (hacc : q_start + 2 * bits + 1 ≤ dim) :
    EGate.WellTypedAt dim (babbushLookupAddAt w W T bits addrBase ancBase q_start) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact unaryQROMAt_wellTypedAt (addendIdx q_start) W T addrBase ancBase dim hdim w 0 0 hQ
  · exact cuccaro_n_bit_adder_full_wellTyped bits q_start dim hacc
  · refine mzList_wellTypedAt dim hdim _ ?_
    intro x hx
    obtain ⟨j, hjr, rfl⟩ := List.mem_map.mp hx
    have hj : j < W := List.mem_range.mp hjr
    simp only [addendIdx]
    omega

/-- `seqAll` is `EGate.WellTypedAt` when every element is (foldl helper). -/
theorem seqAll_foldl_wellTypedAt (dim : Nat) :
    ∀ (gs : List EGate) (seed : EGate),
      EGate.WellTypedAt dim seed → (∀ g ∈ gs, EGate.WellTypedAt dim g) →
      EGate.WellTypedAt dim (gs.foldl EGate.seq seed)
  | [], seed, hseed, _ => hseed
  | g :: rest, seed, hseed, h =>
      seqAll_foldl_wellTypedAt dim rest (EGate.seq seed g)
        ⟨hseed, h g (List.mem_cons_self ..)⟩
        (fun x hx => h x (List.mem_cons_of_mem g hx))

/-- `seqAll` is `EGate.WellTypedAt` when every element is. -/
theorem seqAll_wellTypedAt (dim : Nat) (h0 : 0 < dim) (gs : List EGate)
    (h : ∀ g ∈ gs, EGate.WellTypedAt dim g) :
    EGate.WellTypedAt dim (seqAll gs) := by
  show EGate.WellTypedAt dim (gs.foldl EGate.seq (EGate.base Gate.I))
  exact seqAll_foldl_wellTypedAt dim gs (EGate.base Gate.I) (show (0:Nat) < dim from h0) h

/-- **★ The measured count gate `multiplyAddAt` (= `egG2`) is `EGate.WellTypedAt`
    at `dimRadd`. ★**  Unfold `multiplyAddAt`/`laAt`, apply `seqAll_wellTypedAt`,
    discharge each window via `babbushLookupAddAt_wellTypedAt` + the existing
    `radd_window_QROMRevWT`. -/
theorem multiplyAddAt_wellTypedAt (w bits numWin a i : Nat) (hw : 0 < w) (hbits : 1 ≤ bits) :
    EGate.WellTypedAt (dimRadd w bits numWin) (egG2 w bits numWin a i) := by
  show EGate.WellTypedAt (dimRadd w bits numWin)
    (multiplyAddAt w bits bits (tableFam w bits a) 1 i numWin)
  unfold multiplyAddAt
  apply seqAll_wellTypedAt (dimRadd w bits numWin) (by unfold dimRadd; omega)
  intro g hg
  simp only [List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  unfold laAt
  exact babbushLookupAddAt_wellTypedAt w bits (tableFam w bits a i k) bits
    (addrBaseOf w bits 1 k) (ancBaseOf w bits 1 k) 1 (dimRadd w bits numWin)
    (by unfold dimRadd; omega)
    (le_refl bits)
    (radd_window_QROMRevWT w bits numWin hw k hk)
    (by unfold dimRadd; omega)

/-! ## §2. Well-typedness of the whole 7-gate `egRfree … unmulConcrete` at `bits + ancBig`.

`egRfree = G1 ; G2 ; G3 ; G5 ; G6 ; G7 ; G8` with G6 = `unmulConcrete i =
reverse (radd i)`.  Each component is well-typed at its native dim, then lifted to
`bits + ancBig` by `Gate.WellTyped.mono` / `EGate.WellTypedAt.mono`. -/

/-- **★ `egRfree … unmulConcrete` is `EGate.WellTypedAt (bits + ancBig)`. ★** -/
theorem egRfree_wellTyped
    (w bits numWin cm N a : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hcm : cm ≤ bits)
    (i : Nat) :
    EGate.WellTypedAt (bits + ancBig w bits numWin cm)
      (egRfree w bits numWin cm N a (unmulConcrete w bits numWin a) i) := by
  set D := bits + ancBig w bits numWin cm with hD
  have hDpos : 0 < D := by rw [hD]; unfold ancBig Rbase; omega
  -- native dims and the dominance facts.
  have hdimRadd : dimRadd w bits numWin ≤ D := D_ge_dimRadd w bits numWin cm
  have hdimDiv  : dimDivAt w bits numWin cm 1 ≤ D := D_ge_dimDivAt w bits numWin cm
  have hDmul    : Dmul w bits ≤ D := D_ge_Dmul w bits numWin cm
  -- G3 native well-typedness at dimDivAt.
  have hG3 : Gate.WellTyped (dimDivAt w bits numWin cm 1) (egG3 w bits numWin cm N) :=
    divModNAt_wellTyped w bits numWin cm N 1 hb1 hcm
      (by unfold DivModNAt.scratchBase; omega)
  -- G1 native well-typedness at dimRadd (scatter addresses below scratchBase = dimRadd).
  have hG1 : Gate.WellTyped (dimRadd w bits numWin) (egG1 w bits i) := by
    have hfit : ∀ j, j < bits →
        scatterAddr w bits 1 j < bits + (dimRadd w bits numWin - bits) := by
      intro j hj
      have hjm : j % w < w := Nat.mod_lt j hw
      have hjd : j / w < numWin := by
        apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm, hbits]; exact hj
      have hblk : (j / w) * (2 * w) + 2 * w ≤ numWin * (2 * w) :=
        le_trans (le_of_eq (by ring)) (Nat.mul_le_mul_right (2 * w) (by omega : j / w + 1 ≤ numWin))
      have hs : scatterAddr w bits 1 j < DivModNAt.scratchBase w bits numWin 1 := by
        unfold scatterAddr addrBaseOf DivModNAt.scratchBase; omega
      have : DivModNAt.scratchBase w bits numWin 1 = dimRadd w bits numWin := by
        unfold DivModNAt.scratchBase dimRadd; ring
      omega
    have hwt := ge2021_adaptIn_wellTyped w bits (dimRadd w bits numWin - bits) 1
      (by omega) hfit i
    rw [show bits + (dimRadd w bits numWin - bits) = dimRadd w bits numWin from by
      unfold dimRadd; omega] at hwt
    exact hwt
  -- G8 native well-typedness at Dmul (X bits ; inPlaceMulDataAt ; X bits).
  have hG8 : Gate.WellTyped (Dmul w bits)
      (egG8 w bits numWin N a i) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show Gate.WellTyped (Dmul w bits) (Gate.X bits)
      show bits < Dmul w bits
      have := Dmul_ge_encDim w bits; omega
    · exact inPlaceMulDataAt_wellTyped w bits N numWin (a ^ (2 ^ i))
        (modInv N (a ^ (2 ^ i))) hw hbits
    · show bits < Dmul w bits
      have := Dmul_ge_encDim w bits; omega
  -- assemble `EGate.WellTypedAt D` of the 7-fold seq, lifting each component to D.
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- G1
    exact Gate.WellTyped.mono hG1 hdimRadd
  · -- G2 = egG2 = multiplyAddAt
    exact EGate.WellTypedAt.mono hdimRadd _ (multiplyAddAt_wellTypedAt w bits numWin a i hw hb1)
  · -- G3
    exact Gate.WellTyped.mono hG3 hdimDiv
  · -- G5 = reverse G3
    show Gate.WellTyped D (Gate.reverse (egG3 w bits numWin cm N))
    exact Gate.WellTyped.mono
      (FormalRV.Shor.GidneyInPlace.GatePerm.reverse_wellTyped _ _ hG3) hdimDiv
  · -- G6 = unmulConcrete i = reverse (radd i)
    show Gate.WellTyped D (Gate.reverse (radd w bits numWin a i))
    exact Gate.WellTyped.mono
      (FormalRV.Shor.GidneyInPlace.GatePerm.reverse_wellTyped _ _
        (radd_wellTyped w bits numWin a i hw hb1)) hdimRadd
  · -- G7 = reverse G1
    show Gate.WellTyped D (Gate.reverse (egG1 w bits i))
    exact Gate.WellTyped.mono
      (FormalRV.Shor.GidneyInPlace.GatePerm.reverse_wellTyped _ _ hG1) hdimRadd
  · -- G8
    exact Gate.WellTyped.mono hG8 hDmul

/-! ## §3. The UNCONDITIONAL residue identity at the wide ancilla `ancBig`.

`ModExpAtUnmul.egRfree_matchesResidue_unconditional` gives the residue identity at
the canonical ancilla `2w+2bits+3`.  The gate `egRfree … unmulConcrete` is
anc-INDEPENDENT (the same `EGate` term regardless of the consumer's ancilla
count); the only thing that changes is the encoding the consumer compares against.
Both operands of the residue equation are `< 2^bits` (`x < N ≤ 2^bits` and
`(a^(2^i)·x)%N < N ≤ 2^bits`), so `encodeDataZeroAnc` is anc-irrelevant on them
(`encodeDataZeroAnc_anc_irrel`), transferring the identity from `2w+2bits+3` to
`ancBig`. -/

/-- **Anc-irrelevance of `encodeDataZeroAnc`.**  For `x < 2^n` and both ancilla
    counts positive, the encoding is independent of the ancilla width (the data
    band is anc-independent; everything `≥ n` is `false` in both).  Local proof via
    `encodeDataZeroAnc_data`/`_anc`/`_oob` (no extra import). -/
theorem encodeDataZeroAnc_anc_irrel {n anc anc' x : Nat}
    (hx : x < 2 ^ n) (h1 : 0 < anc) (h1' : 0 < anc') :
    encodeDataZeroAnc n anc x = encodeDataZeroAnc n anc' x := by
  funext i
  by_cases hi : i < n
  · rw [encodeDataZeroAnc_data hx hi, encodeDataZeroAnc_data hx hi]
  · -- i ≥ n: both `false` (anc band or out-of-bounds).
    have hge : n ≤ i := Nat.not_lt.mp hi
    have hfalse : ∀ a, 0 < a → encodeDataZeroAnc n a x i = false := by
      intro a ha
      by_cases hia : i < n + a
      · rw [show i = n + (i - n) from by omega]
        exact encodeDataZeroAnc_anc hx (by omega)
      · exact encodeDataZeroAnc_oob ha (by omega)
    rw [hfalse anc h1, hfalse anc' h1']

/-- **★ THE UNCONDITIONAL RESIDUE IDENTITY at `ancBig` ★.**  The concrete
    reversible `egRfree … unmulConcrete` (which literally contains `multiplyAddAt`)
    realises the residue encoding at the wide ancilla `ancBig`, transferred from
    `egRfree_matchesResidue_unconditional` (at `2w+2bits+3`) by anc-irrelevance. -/
theorem egRfree_residue_ancBig
    (w bits numWin cm N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hcm : cm ≤ bits)
    (h_inv0 : a * ainv0 % N = 1) :
    ModExpAtEncodedMatchesResidue a N bits (ancBig w bits numWin cm)
      (fun i => egRfree w bits numWin cm N a (unmulConcrete w bits numWin a) i)
      (fun _ x => encodeDataZeroAnc bits (ancBig w bits numWin cm) x) where
  block_matches_residue := by
    intro i x hx
    have hN0 : 0 < N := by omega
    have hNle : N ≤ 2 ^ bits := by omega
    have hxbits : x < 2 ^ bits := lt_of_lt_of_le hx hNle
    have hzbits : (a ^ (2 ^ i) * x) % N < 2 ^ bits :=
      lt_of_lt_of_le (Nat.mod_lt _ hN0) hNle
    have hAncPos : 0 < ancBig w bits numWin cm := by
      have := ancBig_pad w bits numWin cm; omega
    have hCanPos : 0 < 2 * w + 2 * bits + 3 := by omega
    -- the wide and canonical input encodings of `x` agree (anc-irrelevance).
    have h_in : encodeDataZeroAnc bits (ancBig w bits numWin cm) x
        = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x :=
      encodeDataZeroAnc_anc_irrel hxbits hAncPos hCanPos
    -- the wide and canonical output encodings of the residue agree.
    have h_out : encodeDataZeroAnc bits (2 * w + 2 * bits + 3) ((a ^ (2 ^ i) * x) % N)
        = encodeDataZeroAnc bits (ancBig w bits numWin cm) ((a ^ (2 ^ i) * x) % N) :=
      encodeDataZeroAnc_anc_irrel hzbits hCanPos hAncPos
    -- transfer the canonical residue identity.
    show EGate.applyNat (egRfree w bits numWin cm N a (unmulConcrete w bits numWin a) i)
        (encodeDataZeroAnc bits (ancBig w bits numWin cm) x)
      = encodeDataZeroAnc bits (ancBig w bits numWin cm) ((a ^ (2 ^ i) * x) % N)
    rw [h_in,
        egRfree_matchesResidue_unconditional w bits numWin cm N a ainv0
          hw hbits hb1 hN1 hN2 hcm h_inv0 |>.block_matches_residue i x hx,
        h_out]

/-! ## §4. The measured witness — bound family PINNED to `egRfree` by the residue. -/

/-- **★ THE WITNESS — `egate_matches_rev` PROVEN for the concrete `egRfree` family ★.**
    A `MeasuredEqualsReversibleOnEncoded` at the wide ancilla `ancBig` whose measured
    family is the concrete reversible `egRfree … unmulConcrete` (containing the literal
    `multiplyAddAt`) and whose reversible family is the PADDED verified windowed mod-N
    multiplier.  `egate_matches_rev` is PROVEN via
    `egate_matches_rev_of_modExpAtResidue_pad ∘ egRfree_residue_ancBig` — i.e. from the
    §3 residue identity, not a trivial wrapping. -/
def egRfree_measuredEqRev
    (w bits numWin cm N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hcm : cm ≤ bits)
    (h_inv0 : a * ainv0 % N = 1) :
    MeasuredEqualsReversibleOnEncoded a N bits (ancBig w bits numWin cm)
      (fun i => egRfree w bits numWin cm N a (unmulConcrete w bits numWin a) i)
      (fun _ x => encodeDataZeroAnc bits (ancBig w bits numWin cm) x) where
  rev := paddedRevFamily_verifiedModMulFamily w bits numWin N a ainv0
    hw hbits hb1 hN1 hN2 h_inv0 (ancBig_pad w bits numWin cm)
  eg_wellTyped := fun i =>
    egRfree_wellTyped w bits numWin cm N a hw hbits hb1 hcm i
  egate_matches_rev :=
    egate_matches_rev_of_modExpAtResidue_pad w bits numWin N a ainv0
      hw hbits hb1 hN1 hN2 h_inv0 (ancBig_pad w bits numWin cm)
      (fun i => egRfree w bits numWin cm N a (unmulConcrete w bits numWin a) i)
      (egRfree_residue_ancBig w bits numWin cm N a ainv0 hw hbits hb1 hN1 hN2 hcm h_inv0)

/-! ## §5. THE HEADLINE — the Shor bound riding the concrete reversible `egRfree`. -/

/-- **★ HEADLINE — the end-to-end Shor success bound on the concrete reversible
    `egRfree … unmulConcrete` ★.**  The Shor success probability of the PADDED
    verified reversible family that the concrete `egRfree … unmulConcrete`
    (literally containing the measured count gate `multiplyAddAt`) PROVABLY acts as
    on the encoded subspace attains `≥ κ/(log₂N)⁴` — UNCONDITIONALLY (only the
    standard sizing + a base inverse + a `ShorSetting`).

    `egate_matches_rev` is PROVEN from the §3 residue identity (the residue read-out
    is genuinely the canonical residue), so the bound is PINNED to `egRfree`.  HONEST
    SCOPE: the bound rides `.rev.family` (the padded reversible family egRfree
    matches); `multiplyAddAt` is literally present in `egRfree` but functionally
    decorative — the in-place residue work is the reused verified
    `windowedModNMulInPlace` (G8). -/
theorem egRfree_shor_succeeds
    (w bits numWin cm N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hcm : cm ≤ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (ancBig w bits numWin cm)
        (egRfree_measuredEqRev w bits numWin cm N a ainv0
          hw hbits hb1 hN1 hN2 hcm h_inv0).rev.family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  countOptimal_shor_succeeds_constrained
    (w := w) (numWin := numWin) (q_start := 1 + 2 * w) (Tfam := fun _ _ _ => 0)
    hw (by omega)
    (egRfree_measuredEqRev w bits numWin cm N a ainv0 hw hbits hb1 hN1 hN2 hcm h_inv0)
    r m h_setting

/-! ## §6. THE CAPSTONE — Shor success ∧ the honest Toffoli-count decomposition. -/

/-- **The honest T-count of the 7-gate `egRfree`** (mirrors `eg_tcount` for the
    `eg` 9-gate, dropping the T-free R copy/clear that `egRfree` omits):

      tcount(egRfree unmul) = tcount(multiplyAddAt) + 2·tcount(divModNAt)
                              + tcount(unmul) + tcount(inPlaceMulDataAt).

    G1/G7 (adapter + reverse) are T-free; G5 = reverse G3 has `tcount G3`
    (`tcount_reverse`); G2 = `multiplyAddAt`; G8 = X ; inPlaceMul ; X. -/
theorem egRfree_tcount (w bits numWin cm N a : Nat) (unmul : Nat → Gate) (i : Nat) :
    EGate.tcount (egRfree w bits numWin cm N a unmul i)
      = EGate.tcount (multiplyAddAt w bits bits (tableFam w bits a) 1 i numWin)
        + 2 * Gate.tcount (divModNAt w bits numWin cm N 1)
        + Gate.tcount (unmul i)
        + Gate.tcount (inPlaceMulDataAt w bits N numWin (a ^ (2 ^ i)) (modInv N (a ^ (2 ^ i)))) := by
  show Gate.tcount (egG1 w bits i) + EGate.tcount (egG2 w bits numWin a i)
        + Gate.tcount (egG3 w bits numWin cm N)
        + Gate.tcount (egG5 w bits numWin cm N)
        + Gate.tcount (unmul i)
        + Gate.tcount (egG7 w bits i)
        + Gate.tcount (egG8 w bits numWin N a i) = _
  have hG1 : Gate.tcount (egG1 w bits i) = 0 := ge2021_adaptIn_tfree w bits 1 i
  have hG5 : Gate.tcount (egG5 w bits numWin cm N)
      = Gate.tcount (divModNAt w bits numWin cm N 1) := by
    show Gate.tcount (Gate.reverse (egG3 w bits numWin cm N)) = _
    rw [tcount_reverse]; rfl
  have hG7 : Gate.tcount (egG7 w bits i) = 0 := by
    show Gate.tcount (Gate.reverse (egG1 w bits i)) = 0
    rw [tcount_reverse]; exact hG1
  have hG3 : Gate.tcount (egG3 w bits numWin cm N)
      = Gate.tcount (divModNAt w bits numWin cm N 1) := rfl
  have hG8 : Gate.tcount (egG8 w bits numWin N a i)
      = Gate.tcount (inPlaceMulDataAt w bits N numWin (a ^ (2 ^ i)) (modInv N (a ^ (2 ^ i)))) := by
    show Gate.tcount (Gate.X bits)
        + Gate.tcount (inPlaceMulDataAt w bits N numWin (a ^ (2 ^ i)) (modInv N (a ^ (2 ^ i))))
        + Gate.tcount (Gate.X bits) = _
    simp [Gate.tcount]
  have hG2 : EGate.tcount (egG2 w bits numWin a i)
      = EGate.tcount (multiplyAddAt w bits bits (tableFam w bits a) 1 i numWin) := rfl
  rw [hG1, hG2, hG3, hG5, hG7, hG8]
  ring

/-- **★ CAPSTONE — Shor success ∧ the honest count decomposition, ONE gate ★.**
    On the IDENTICAL concrete reversible gate `egRfree … unmulConcrete` (per QPE
    iterate `i`):

    (i) the Shor success bound `≥ κ/(log₂N)⁴` holds for the padded verified
        reversible family it PROVABLY acts as on the encoded subspace — PINNED to
        `egRfree` by the §3 residue identity (`egate_matches_rev` PROVEN); and

    (ii) the HONEST T-count decomposition

           tcount(egRfree…) = tcount(multiplyAddAt) + 2·tcount(divModNAt)
                              + tcount(unmulConcrete) + tcount(inPlaceMulDataAt),

         with `multiplyAddAt` the LITERAL measured count gate (G2) and
         `tcount(unmulConcrete) = tcount(radd)` (the reversible reconstruction's
         inverse, `reverse`-invariant); G1/G7 (adapter + reverse) T-free.

    Both faces ride the SAME syntactic object: the measured count gate is literally
    present, its measured Toffoli figure flows through the count decomposition, and
    the bound rides the reversible family `egRfree` matches.  This is the honest
    end-to-end assembly atop the unconditional residue identity. -/
theorem egRfree_shor_AND_count
    (w bits numWin cm N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hcm : cm ≤ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (ancBig w bits numWin cm)
        (egRfree_measuredEqRev w bits numWin cm N a ainv0
          hw hbits hb1 hN1 hN2 hcm h_inv0).rev.family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4
    ∧ ∀ i, EGate.tcount (egRfree w bits numWin cm N a (unmulConcrete w bits numWin a) i)
        = EGate.tcount (multiplyAddAt w bits bits (tableFam w bits a) 1 i numWin)
          + 2 * Gate.tcount (divModNAt w bits numWin cm N 1)
          + Gate.tcount (radd w bits numWin a i)
          + Gate.tcount (inPlaceMulDataAt w bits N numWin (a ^ (2 ^ i))
              (modInv N (a ^ (2 ^ i)))) :=
  ⟨egRfree_shor_succeeds w bits numWin cm N a ainv0 r m
      hw hbits hb1 hN1 hN2 hcm h_inv0 h_setting,
   fun i => by
     -- the honest count: `egRfree`'s tcount via `egRfree_tcount`, then
     -- `tcount(unmulConcrete) = tcount(radd)`.
     rw [egRfree_tcount w bits numWin cm N a (unmulConcrete w bits numWin a) i,
         unmulConcrete_tcount w bits numWin a i]⟩

end

end FormalRV.Audit.GidneyEkera2021.ModExpAtReductionBound
