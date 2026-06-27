/-
  Audit · Gidney–Ekerå 2021 · A CONCRETE REVERSIBLE `unmul` DISCHARGING
  `UnmulSpecRfree`, AND AN UNCONDITIONAL `block_matches_residue_direct`.
  ════════════════════════════════════════════════════════════════════════════
  GOAL.  The R-free residue discharge `block_matches_residue_direct`
  (`ModExpAtReductionDirect`) is parametric in a reversible multiply-UNcompute
  family `unmul : Nat → Gate`, constrained by the single named obligation

      UnmulSpecRfree w bits numWin N a unmul := ∀ i x, x < N →
        Gate.applyNat (unmul i) (s2State w bits numWin a i x)
          = Gate.applyNat (egG1 w bits i)
              (encodeDataZeroAnc bits (2*w+2*bits+3) x)

  where `s2State = applyNat (egG2 = multiplyAddAt …) (egG1-state)` is the post-
  count-gate state.  This module CONSTRUCTS a concrete reversible `unmul` and
  derives the UNCONDITIONAL residue equation.

  DESIGN (the measured count gate's reversible inverse, Bennett style).
  `multiplyAddAt = seqAll (laAt …)` and
  `laAt = babbushLookupAddAt = (unaryQROMAt ; cuccaro) ; mzList(addend)`
  (MeasUncomputeAt.lean).  It is MEASURED only via:
    • the internal per-level `EGate.mz (ancBase + d)` in `unaryQROMAt`, and
    • the final `mzList` clearing the addend register.
  Each `mz` clears a qubit that — at the point it fires — holds a value that a
  reversible CCX/uncompute would ALSO clear to 0.  So we build a fully-reversible
  pure `Gate` counterpart:

    • `unaryQROMAtRev` — `unaryQROMAt` with every `EGate.mz (ancBase + d)`
      replaced by the reversible `Gate.CCX ctrl (addrBase + d) (ancBase + d)`
      (which clears `ancBase + d = ctrl ∧ addr_d` to 0).  A PURE `Gate`.
    • `laAtRev` / `multiplyAddAtRev` — the windowed reversible multiply-add:
      `(unaryQROMAtRev ; cuccaro) ; Gate.reverse unaryQROMAtRev` per window
      (the Bennett uncompute replaces the measured `mzList`).
    • `radd i` = the placed reversible multiply-add at the same stacked layout.

  Then `unmulConcrete i := Gate.reverse (radd i)` and, via the key bridge
  `radd_agrees : applyNat (radd i) (egG1-state x) = s2State … i x`,

    applyNat (unmulConcrete i) (s2State)
      = applyNat (reverse (radd i)) (applyNat (radd i) (egG1-state x))
      = egG1-state x                                  (applyNat_reverse_cancel)

  i.e. `UnmulSpecRfree` holds.  Instantiating `block_matches_residue_direct`
  yields the UNCONDITIONAL `block_matches_residue_direct_unconditional` and the
  packaged `ModExpAtEncodedMatchesResidue` instance.

  STATUS — FULLY UNCONDITIONAL.  Every step is proved:
    • `unaryQROMAtRev_agrees`        (the reversible/measured QROM read agree),
    • `babbushLookupAddAtRev_agrees` (per-window reversible/measured lookup-add),
    • `multiplyAddAtRev_agrees_fold` (the windowed fold),
    • `radd_agrees`                  (`radd` realises `s2State`),
    • `radd_wellTyped`,
    • `unmulConcrete_spec`           (discharges `UnmulSpecRfree`, NO hypothesis),
    • `block_matches_residue_direct_unconditional` (residue eqn, NO `unmul` hyp),
    • `egRfree_matchesResidue_unconditional`       (packaged instance).
  There is NO abstract `unmul` parameter and NO `UnmulSpecRfree` hypothesis left.

  Kernel-clean: no `sorry`, no `native_decide`; axioms ⊆ {propext,
  Classical.choice, Quot.sound}.  ADDITIVE: no existing file weakened.
-/
import FormalRV.Audit.GidneyEkera2021.ModExpAtReductionDirect

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace FormalRV.Audit.GidneyEkera2021.ModExpAtUnmul

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasUncomputeAt
open FormalRV.Shor.WindowedComposed (seqAll)
open FormalRV.Shor.WindowedComposedAt
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.GidneyInPlace.GateReversible (Gate.reverse applyNat_reverse_cancel)
open FormalRV.Audit.GidneyEkera2021.ShorComposed (CountGateMulInput countOptimal_multiplyAdd_value)
open FormalRV.Audit.GidneyEkera2021.ModExpAtReductionDirect

/-! ## §1. The reversible mirror of `unaryQROMAt`.

`unaryQROMAt pos W T addrBase ancBase d ctrl base` (MeasUncomputeAt.lean:71) has
the recursive shape, at depth `d+1`:

    CCX ctrl addr_d anc_d ;                 -- anc ← ctrl ∧ addr_d
    QROM(base + 2^d) [ctrl := anc_d] ;      -- bit_d = 1 half
    CX ctrl anc_d ;                         -- anc ← ctrl ∧ ¬addr_d
    QROM(base)      [ctrl := anc_d] ;       -- bit_d = 0 half
    CX ctrl anc_d ;                         -- restore anc ← ctrl ∧ addr_d
    mz anc_d                                -- MEASURE-clear anc_d

At the `mz`, `anc_d = ctrl ∧ addr_d`.  We replace `mz anc_d` by the reversible
`CCX ctrl addr_d anc_d`, which XORs `anc_d` with `ctrl ∧ addr_d` again — clearing
it to `false` — IDENTICALLY to the measurement, but reversibly. -/

/-- **Reversible mirror of `unaryQROMAt`** — a pure `Gate` (no `EGate.mz`).
    Every measured `EGate.mz (ancBase + d)` is replaced by the reversible
    `Gate.CCX ctrl (addrBase + d) (ancBase + d)`, which clears the level-`d`
    ancilla (holding `ctrl ∧ addr_d` at that point) back to `false`. -/
def unaryQROMAtRev (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) (addrBase ancBase : Nat) :
    Nat → Nat → Nat → Gate
  | 0,     ctrl, base =>
      cx_gates_from_indices ctrl (wordCnotsAt pos W (T base))
  | d + 1, ctrl, base =>
      Gate.seq (Gate.seq (Gate.seq (Gate.seq (Gate.seq
        (Gate.CCX ctrl (addrBase + d) (ancBase + d))                                  -- anc ← ctrl∧bit_d
        (unaryQROMAtRev pos W T addrBase ancBase d (ancBase + d) (base + 2 ^ d)))     -- bit_d = 1 half
        (Gate.CX ctrl (ancBase + d)))                                                 -- anc ← ctrl∧¬bit_d
        (unaryQROMAtRev pos W T addrBase ancBase d (ancBase + d) base))               -- bit_d = 0 half
        (Gate.CX ctrl (ancBase + d)))                                                 -- restore anc
        (Gate.CCX ctrl (addrBase + d) (ancBase + d))                                  -- reversible-uncompute anc

/-- The reversible mirror is T-free EXACTLY when `unaryQROMAt` is (the leaf CNOTs
    are Clifford; the per-level CCX-uncompute adds `7` per level beyond the
    measured version, accounted honestly).  We record its raw T-count: `2^{d+1}−1`
    Toffolis from the read tree plus one CCX per level for the uncompute. -/
theorem tcount_unaryQROMAtRev (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase : Nat) :
    ∀ (d ctrl base : Nat),
      Gate.tcount (unaryQROMAtRev pos W T addrBase ancBase d ctrl base)
        = 7 * (2 ^ (d + 1) - 2)
  | 0, ctrl, base => by
      simp [unaryQROMAtRev, tcount_cx_gates_zero]
  | d + 1, ctrl, base => by
      simp only [unaryQROMAtRev, Gate.tcount,
                 tcount_unaryQROMAtRev pos W T addrBase ancBase d]
      have h2d : 2 ≤ 2 ^ (d + 1) := by
        have : (1:Nat) ≤ 2 ^ d := Nat.one_le_two_pow
        have : 2 ^ (d+1) = 2 * 2 ^ d := by ring
        omega
      have hpow : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by ring
      omega

/-! ### Well-typedness of the reversible mirror.

`unaryQROMAtRev` is well-typed at `dim` provided: `ctrl < dim`; every address bit
`addrBase + i` (`i ≤ d`), every ancilla `ancBase + i` (`i < d` for the recursion,
and the level ancilla `ancBase + d`), and every word target `pos j` (`j < W`) is
`< dim`; and the control/target distinctness for the three generators holds.  We
package the index-range + distinctness as hypotheses (the placed instance below
discharges them from the concrete layout). -/

/-- Index/​distinctness side-conditions for `unaryQROMAtRev`'s well-typedness at a
    given control `ctrl` and depth `d`.  Mirrors the layout disjointness that the
    measured tree's lemmas consume. -/
structure QROMRevWT (pos : Nat → Nat) (W addrBase ancBase d ctrl dim : Nat) : Prop where
  ctrl_lt   : ctrl < dim
  addr_lt   : ∀ i, i < d → addrBase + i < dim
  anc_lt    : ∀ i, i < d → ancBase + i < dim
  word_lt   : ∀ j, j < W → pos j < dim
  ctrl_addr : ∀ i, i < d → ctrl ≠ addrBase + i
  ctrl_anc  : ∀ i, i < d → ctrl ≠ ancBase + i
  addr_anc  : ∀ i i', i < d → i' < d → addrBase + i ≠ ancBase + i'
  addr_word : ∀ i j, i < d → j < W → addrBase + i ≠ pos j
  anc_word  : ∀ i j, i < d → j < W → ancBase + i ≠ pos j
  ctrl_word : ∀ j, j < W → ctrl ≠ pos j

/-- A CNOT layer `cx_gates_from_indices c xs` is well-typed when the control `c`
    and every target are in range and `c` is distinct from every target.
    (Local copy to avoid an import dependency on `SplitPhaseFixup`.) -/
theorem cxGates_wellTyped_local (dim c : Nat) (xs : List Nat)
    (hdim : 0 < dim) (hc : c < dim) (hxs : ∀ t ∈ xs, t < dim ∧ c ≠ t) :
    Gate.WellTyped dim (cx_gates_from_indices c xs) := by
  induction xs with
  | nil => exact hdim
  | cons t rest ih =>
      obtain ⟨ht, hct⟩ := hxs t (List.mem_cons_self ..)
      exact ⟨ih (fun u hu => hxs u (List.mem_cons_of_mem t hu)), hc, ht, hct⟩

/-- **`unaryQROMAtRev` is well-typed** under `QROMRevWT`.  Mirrors
    `MeasuredBabbushRead.unaryQROMPos_wellTypedAt` for the reversible mirror: the
    leaf is a CNOT layer (`cxGates_wellTyped_local`); each level adds the
    `CCX/CX/CCX` generators whose in-range + distinctness obligations are read off
    `QROMRevWT`. -/
theorem unaryQROMAtRev_wellTyped (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase dim : Nat) (hdim : 0 < dim) :
    ∀ (d ctrl base : Nat), QROMRevWT pos W addrBase ancBase d ctrl dim →
      Gate.WellTyped dim (unaryQROMAtRev pos W T addrBase ancBase d ctrl base)
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
      -- the `QROMRevWT` for the two depth-`d` sub-calls (control `ancBase + d`)
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
      · exact unaryQROMAtRev_wellTyped pos W T addrBase ancBase dim hdim d (ancBase + d)
          (base + 2 ^ d) Hrec
      · exact ⟨H.ctrl_lt, hcd_lt, hctrl_cd⟩
      · exact unaryQROMAtRev_wellTyped pos W T addrBase ancBase dim hdim d (ancBase + d)
          base Hrec
      · exact ⟨H.ctrl_lt, hcd_lt, hctrl_cd⟩
      · exact ⟨H.ctrl_lt, had_lt, hcd_lt, hctrl_ad, hctrl_cd, had_cd⟩

/-! ## §2. The reversible mirror AGREES with the measured `unaryQROMAt` on
clean-ancilla inputs.

The two circuits share an identical prefix at every level; they differ only in the
final per-level step (`mz (ancBase + d)` vs `CCX ctrl (addrBase + d) (ancBase + d)`).
At the moment that step fires the level ancilla holds `ctrl ∧ addr_d`, so BOTH clear
it to `false`.  Hence the FULL outputs coincide on any state whose ancillas
`ancBase + i` (`i < d`) start clean (the invariant the windowed fold maintains). -/

/-- **THE AGREEMENT LEMMA.**  On a state with clean tree-ancillas, with the tree's
    registers pairwise disjoint (ctrl off addr/anc/word; addr off anc; addr/anc off
    word), the reversible mirror `unaryQROMAtRev` has the SAME `Gate.applyNat`
    action as the measured `unaryQROMAt`'s `EGate.applyNat`. -/
theorem unaryQROMAtRev_agrees (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase : Nat) :
    ∀ (d ctrl base : Nat) (f : Nat → Bool),
      (∀ i, i < d → ctrl ≠ ancBase + i) →
      (∀ i, i < d → ctrl ≠ addrBase + i) →
      (∀ i i', i < d → i' < d → addrBase + i ≠ ancBase + i') →
      (∀ j, j < W → ctrl ≠ pos j) →
      (∀ i j, i < d → j < W → addrBase + i ≠ pos j) →
      (∀ i j, i < d → j < W → ancBase + i ≠ pos j) →
      (∀ i, i < d → f (ancBase + i) = false) →
      Gate.applyNat (unaryQROMAtRev pos W T addrBase ancBase d ctrl base) f
        = EGate.applyNat (unaryQROMAt pos W T addrBase ancBase d ctrl base) f := by
  intro d
  induction d with
  | zero =>
      intro ctrl base f _ _ _ _ _ _ _
      rfl
  | succ d ih =>
      intro ctrl base f h_ctrl_anc h_ctrl_addr h_addr_anc h_ctrl_word h_addr_word
        h_anc_word h_clean
      have hlt := Nat.lt_succ_self d
      -- shrunk hypotheses for the depth-`d` sub-calls (control `ancBase + d`)
      have H_ctrl_anc' : ∀ i, i < d → ancBase + d ≠ ancBase + i := fun i hi => by omega
      have H_ctrl_addr' : ∀ i, i < d → ancBase + d ≠ addrBase + i :=
        fun i hi => Ne.symm (h_addr_anc i d (Nat.lt_succ_of_lt hi) hlt)
      have H_addr_anc' : ∀ i i', i < d → i' < d → addrBase + i ≠ ancBase + i' :=
        fun i i' hi hi' => h_addr_anc i i' (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hi')
      have H_ctrl_word' : ∀ j, j < W → ancBase + d ≠ pos j := fun j hj => h_anc_word d j hlt hj
      have H_addr_word' : ∀ i j, i < d → j < W → addrBase + i ≠ pos j :=
        fun i j hi hj => h_addr_word i j (Nat.lt_succ_of_lt hi) hj
      have H_anc_word' : ∀ i j, i < d → j < W → ancBase + i ≠ pos j :=
        fun i j hi hj => h_anc_word i j (Nat.lt_succ_of_lt hi) hj
      -- the loaded state s1 = CCX ctrl addr_d anc_d f keeps the i<d ancillas clean
      set s1 := Gate.applyNat (Gate.CCX ctrl (addrBase + d) (ancBase + d)) f with hs1
      have hs1_clean : ∀ i, i < d → s1 (ancBase + i) = false := by
        intro i hi
        rw [hs1, Gate.applyNat_CCX, update_neq _ _ _ _ (by omega)]
        exact h_clean i (Nat.lt_succ_of_lt hi)
      -- IH on the first (bit_d = 1) sub-call, on the loaded state s1
      have ih1 : Gate.applyNat (unaryQROMAtRev pos W T addrBase ancBase d (ancBase + d) (base + 2 ^ d)) s1
          = (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) (base + 2 ^ d)).applyNat s1 :=
        ih (ancBase + d) (base + 2 ^ d) s1 H_ctrl_anc' H_ctrl_addr' H_addr_anc'
          H_ctrl_word' H_addr_word' H_anc_word' hs1_clean
      -- the MEASURED prefix state s2m = QROMmeas(base+2^d) s1; via ih1, s2r = s2m
      set s2m := (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) (base + 2 ^ d)).applyNat s1
        with hs2m
      -- s3 = CX ctrl anc_d s2m keeps the i<d ancillas clean
      set s3 := Gate.applyNat (Gate.CX ctrl (ancBase + d)) s2m with hs3
      have hs2m_clean : ∀ i, i < d → s2m (ancBase + i) = false := by
        intro i hi
        rw [hs2m]
        exact unaryQROMAt_anc_cleared pos W T addrBase ancBase d (ancBase + d) (base + 2 ^ d) s1 i hi
      have hs3_clean : ∀ i, i < d → s3 (ancBase + i) = false := by
        intro i hi
        rw [hs3, Gate.applyNat_CX, update_neq _ _ _ _ (by omega)]
        exact hs2m_clean i hi
      -- IH on the second (bit_d = 0) sub-call, on s3
      have ih2 : Gate.applyNat (unaryQROMAtRev pos W T addrBase ancBase d (ancBase + d) base) s3
          = (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) base).applyNat s3 :=
        ih (ancBase + d) base s3 H_ctrl_anc' H_ctrl_addr' H_addr_anc'
          H_ctrl_word' H_addr_word' H_anc_word' hs3_clean
      simp only [unaryQROMAtRev, unaryQROMAt, Gate.applyNat_seq, EGate.applyNat]
      -- collapse the reversible prefix to the measured prefix `s3`:
      -- innermost CCX..f = s1, then QROMrev(base+2^d) s1 = s2m (ih1), CX → s3.
      rw [show Gate.applyNat (Gate.CCX ctrl (addrBase + d) (ancBase + d)) f = s1 from rfl]
      rw [ih1]
      rw [show (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) (base + 2 ^ d)).applyNat s1
            = s2m from rfl]
      -- both branches now read `Gate.applyNat (CX ctrl anc_d) s2m = s3`
      rw [show Gate.applyNat (Gate.CX ctrl (ancBase + d)) s2m = s3 from rfl]
      rw [ih2]
      -- now both sides share the common state s5 = CX ctrl anc_d (QROMmeas(base) s3);
      -- LHS finishes with reversible CCX, RHS with update ... false.
      set s4 := (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) base).applyNat s3 with hs4
      set s5 := Gate.applyNat (Gate.CX ctrl (ancBase + d)) s4 with hs5
      -- Frame facts: ctrl and addr_d survive a measured sub-call (off word + i<d ancillas).
      have frame_ctrl : ∀ (b : Nat) (s : Nat → Bool),
          (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) b).applyNat s ctrl = s ctrl :=
        fun b s => unaryQROMAt_frame pos W T addrBase ancBase d (ancBase + d) b s ctrl
          (fun j hj => h_ctrl_word j hj) (fun i hi => h_ctrl_anc i (Nat.lt_succ_of_lt hi))
      have frame_addrd : ∀ (b : Nat) (s : Nat → Bool),
          (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) b).applyNat s (addrBase + d)
            = s (addrBase + d) :=
        fun b s => unaryQROMAt_frame pos W T addrBase ancBase d (ancBase + d) b s (addrBase + d)
          (fun j hj => h_addr_word d j hlt hj)
          (fun i hi => h_addr_anc d i hlt (Nat.lt_succ_of_lt hi))
      have frame_ancd : ∀ (b : Nat) (s : Nat → Bool),
          (unaryQROMAt pos W T addrBase ancBase d (ancBase + d) b).applyNat s (ancBase + d)
            = s (ancBase + d) :=
        fun b s => unaryQROMAt_frame pos W T addrBase ancBase d (ancBase + d) b s (ancBase + d)
          (fun j hj => h_anc_word d j hlt hj) (fun i hi => by omega)
      -- values of s1 at ctrl / addr_d / anc_d
      have hs1_ctrl : s1 ctrl = f ctrl := by
        rw [hs1, Gate.applyNat_CCX, update_neq _ _ _ _ (h_ctrl_anc d hlt)]
      have hs1_addrd : s1 (addrBase + d) = f (addrBase + d) := by
        rw [hs1, Gate.applyNat_CCX, update_neq _ _ _ _ (h_addr_anc d d hlt hlt)]
      have hs1_ancd : s1 (ancBase + d) = (f ctrl && f (addrBase + d)) := by
        rw [hs1, Gate.applyNat_CCX, update_eq, h_clean d hlt, Bool.false_xor]
      -- ctrl / addr_d / anc_d at s2m = QROMmeas(base+2^d) s1
      have hs2m_ctrl : s2m ctrl = f ctrl := by
        rw [hs2m, frame_ctrl, hs1_ctrl]
      have hs2m_addrd : s2m (addrBase + d) = f (addrBase + d) := by
        rw [hs2m, frame_addrd, hs1_addrd]
      have hs2m_ancd : s2m (ancBase + d) = (f ctrl && f (addrBase + d)) := by
        rw [hs2m, frame_ancd, hs1_ancd]
      -- ctrl / addr_d / anc_d at s3 = CX ctrl anc_d s2m
      have hs3_ctrl : s3 ctrl = f ctrl := by
        rw [hs3, Gate.applyNat_CX, update_neq _ _ _ _ (h_ctrl_anc d hlt), hs2m_ctrl]
      have hs3_addrd : s3 (addrBase + d) = f (addrBase + d) := by
        rw [hs3, Gate.applyNat_CX, update_neq _ _ _ _ (h_addr_anc d d hlt hlt), hs2m_addrd]
      have hs3_ancd : s3 (ancBase + d) = (f ctrl && !(f (addrBase + d))) := by
        rw [hs3, Gate.applyNat_CX, update_eq, hs2m_ancd, hs2m_ctrl]
        cases f ctrl <;> cases f (addrBase + d) <;> rfl
      -- carry to s4, then s5
      have hs4_ctrl : s4 ctrl = f ctrl := by rw [hs4, frame_ctrl, hs3_ctrl]
      have hs4_addrd : s4 (addrBase + d) = f (addrBase + d) := by rw [hs4, frame_addrd, hs3_addrd]
      have hs4_ancd : s4 (ancBase + d) = (f ctrl && !(f (addrBase + d))) := by
        rw [hs4, frame_ancd, hs3_ancd]
      have hs5_ctrl : s5 ctrl = f ctrl := by
        rw [hs5, Gate.applyNat_CX, update_neq _ _ _ _ (h_ctrl_anc d hlt), hs4_ctrl]
      have hs5_addrd : s5 (addrBase + d) = f (addrBase + d) := by
        rw [hs5, Gate.applyNat_CX, update_neq _ _ _ _ (h_addr_anc d d hlt hlt), hs4_addrd]
      have hs5_ancd : s5 (ancBase + d) = (f ctrl && f (addrBase + d)) := by
        rw [hs5, Gate.applyNat_CX, update_eq, hs4_ancd, hs4_ctrl]
        cases f ctrl <;> cases f (addrBase + d) <;> rfl
      -- final: CCX clears anc_d (= ctrl ∧ addr_d) to false, leaving everything else.
      show Gate.applyNat (Gate.CCX ctrl (addrBase + d) (ancBase + d)) s5
          = Function.update s5 (ancBase + d) false
      rw [Gate.applyNat_CCX]
      have hval : (s5 (ancBase + d) ^^ s5 ctrl && s5 (addrBase + d)) = false := by
        rw [hs5_ancd, hs5_ctrl, hs5_addrd]
        cases f ctrl <;> cases f (addrBase + d) <;> rfl
      rw [hval]
      funext p
      by_cases hp : p = ancBase + d
      · subst hp; rw [update_eq, Function.update_self]
      · rw [update_neq _ _ _ _ hp, Function.update_of_ne hp]

/-! ## §3. The reversible per-window lookup-add and the placed `radd`.

`babbushLookupAddAt = (unaryQROMAt ; cuccaro) ; mzList(addend)` clears the addend
register by MEASUREMENT.  The reversible counterpart `babbushLookupAddAtRev` does a
Bennett uncompute instead: a SECOND `unaryQROMAtRev` read.  After the adder the
addend register STILL holds `T[addr]` (`cuccaroAdder.addendRestored`) and the
address register is intact (Cuccaro frames it — it sits off the accumulator block),
so the second read XORs `T[addr]` into the addend AGAIN, clearing it to 0 —
reversibly and with the SAME net effect as the measurement.  Everything else (the
accumulator sum, the addresses, the now-clean AND-ancillas) coincides, so
`babbushLookupAddAtRev` agrees with `babbushLookupAddAt` on the clean inputs the
windowed fold supplies. -/

/-- **The reversible per-window lookup-add** — a pure `Gate`.  Reads `T[addr]` into
    the addend (`unaryQROMAtRev`), adds it onto the accumulator (`cuccaro`), then
    Bennett-uncomputes the addend with a SECOND reversible read. -/
def babbushLookupAddAtRev (w W : Nat) (T : Nat → Nat) (bits addrBase ancBase q_start : Nat) :
    Gate :=
  Gate.seq (Gate.seq
    (unaryQROMAtRev (addendIdx q_start) W T addrBase ancBase w 0 0)
    (cuccaro_n_bit_adder_full bits q_start))
    (unaryQROMAtRev (addendIdx q_start) W T addrBase ancBase w 0 0)

/-- One window's reversible measured lookup-add on the SHARED accumulator at
    `q_start`, mirroring `WindowedComposedAt.laAt`. -/
def laAtRev (w W bits : Nat) (Tfam : Nat → Nat → Nat → Nat) (q_start m k : Nat) : Gate :=
  babbushLookupAddAtRev w W (Tfam m k) bits
    (addrBaseOf w bits q_start k) (ancBaseOf w bits q_start k) q_start

/-- Sequence a list of `Gate`s left-to-right (identity seed) — the `Gate`-level
    analogue of `WindowedComposed.seqAll`. -/
def seqAllG (gs : List Gate) : Gate := gs.foldl Gate.seq Gate.I

/-- Peel the last step of a `seqAllG`-fold over `List.range (n+1)` (Gate-level
    analogue of `applyNat_seqAll_range_succ`). -/
theorem applyNat_seqAllG_range_succ (step : Nat → Gate) (n : Nat) (g0 : Nat → Bool) :
    Gate.applyNat (seqAllG ((List.range (n + 1)).map step)) g0
      = Gate.applyNat (step n)
          (Gate.applyNat (seqAllG ((List.range n).map step)) g0) := by
  unfold seqAllG
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
  rfl

/-- **The reversible multiply-add** = `numWin` shared-accumulator reversible
    lookup-adds, mirroring `WindowedComposedAt.multiplyAddAt`. -/
def multiplyAddAtRev (w W bits : Nat) (Tfam : Nat → Nat → Nat → Nat) (q_start m numWin : Nat) :
    Gate :=
  seqAllG ((List.range numWin).map (laAtRev w W bits Tfam q_start m))

/-- **`radd i`** — the placed reversible multiply-add at the SAME stacked layout as
    `egG2 = multiplyAddAt w bits bits (tableFam w bits a) 1 i numWin`. -/
def radd (w bits numWin a i : Nat) : Gate :=
  multiplyAddAtRev w bits bits (tableFam w bits a) 1 i numWin

/-! ### Well-typedness of the reversible circuit. -/

/-- `seqAllG` is well-typed when every element is. -/
theorem seqAllG_foldl_wellTyped (dim : Nat) :
    ∀ (gs : List Gate) (seed : Gate),
      Gate.WellTyped dim seed → (∀ g ∈ gs, Gate.WellTyped dim g) →
      Gate.WellTyped dim (gs.foldl Gate.seq seed)
  | [], seed, hseed, _ => hseed
  | g :: rest, seed, hseed, h =>
      seqAllG_foldl_wellTyped dim rest (Gate.seq seed g)
        ⟨hseed, h g (List.mem_cons_self ..)⟩
        (fun x hx => h x (List.mem_cons_of_mem g hx))

theorem seqAllG_wellTyped (dim : Nat) (h0 : 0 < dim) (gs : List Gate)
    (h : ∀ g ∈ gs, Gate.WellTyped dim g) :
    Gate.WellTyped dim (seqAllG gs) :=
  seqAllG_foldl_wellTyped dim gs Gate.I h0 h

/-- `babbushLookupAddAtRev` is well-typed at `dim` when the window's QROM registers
    fit (via `QROMRevWT`) and the accumulator block fits (`q_start + 2·bits + 1 ≤
    dim`). -/
theorem babbushLookupAddAtRev_wellTyped (w W : Nat) (T : Nat → Nat)
    (bits addrBase ancBase q_start dim : Nat) (hdim : 0 < dim)
    (hQ : QROMRevWT (addendIdx q_start) W addrBase ancBase w 0 dim)
    (hacc : q_start + 2 * bits + 1 ≤ dim) :
    Gate.WellTyped dim (babbushLookupAddAtRev w W T bits addrBase ancBase q_start) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact unaryQROMAtRev_wellTyped (addendIdx q_start) W T addrBase ancBase dim hdim w 0 0 hQ
  · exact cuccaro_n_bit_adder_full_wellTyped bits q_start dim hacc
  · exact unaryQROMAtRev_wellTyped (addendIdx q_start) W T addrBase ancBase dim hdim w 0 0 hQ

/-- The dimension covering the whole stacked region of `radd`'s windows: the
    accumulator block `[1, 1+2·bits+1)` plus `numWin` per-window address/ancilla
    registers (`stride 2·w`).  Matches `multiplyAddAt`'s `M3` frame boundary. -/
def dimRadd (w bits numWin : Nat) : Nat := 1 + 2 * bits + 1 + numWin * (2 * w)

/-- `QROMRevWT` holds for window `k` of `radd` at `dimRadd`. -/
theorem radd_window_QROMRevWT (w bits numWin : Nat) (hw : 0 < w)
    (k : Nat) (hk : k < numWin) :
    QROMRevWT (addendIdx 1) bits
      (addrBaseOf w bits 1 k) (ancBaseOf w bits 1 k) w 0 (dimRadd w bits numWin) := by
  have hkstep : k * (2 * w) + 2 * w ≤ numWin * (2 * w) :=
    le_trans (le_of_eq (by ring)) (Nat.mul_le_mul_right (2 * w) (by omega : k + 1 ≤ numWin))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold dimRadd; omega
  · intro i hi; unfold dimRadd addrBaseOf; omega
  · intro i hi; unfold dimRadd ancBaseOf addrBaseOf; omega
  · intro j hj; unfold dimRadd addendIdx; omega
  · intro i hi; unfold addrBaseOf; omega
  · intro i hi; unfold ancBaseOf addrBaseOf; omega
  · intro i i' hi hi'; unfold ancBaseOf addrBaseOf; omega
  · intro i j hi hj; unfold addrBaseOf addendIdx; omega
  · intro i j hi hj; unfold ancBaseOf addrBaseOf addendIdx; omega
  · intro j hj; unfold addendIdx; omega

/-- **`radd i` is well-typed** at `dimRadd`. -/
theorem radd_wellTyped (w bits numWin a i : Nat) (hw : 0 < w) (hbits : 1 ≤ bits) :
    Gate.WellTyped (dimRadd w bits numWin) (radd w bits numWin a i) := by
  unfold radd multiplyAddAtRev
  apply seqAllG_wellTyped (dimRadd w bits numWin) (by unfold dimRadd; omega)
  intro g hg
  simp only [List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  unfold laAtRev
  exact babbushLookupAddAtRev_wellTyped w bits (tableFam w bits a i k) bits
    (addrBaseOf w bits 1 k) (ancBaseOf w bits 1 k) 1 (dimRadd w bits numWin)
    (by unfold dimRadd; omega)
    (radd_window_QROMRevWT w bits numWin hw k hk)
    (by unfold dimRadd; omega)

/-! ### Per-window agreement: `babbushLookupAddAtRev` matches the measured
`babbushLookupAddAt` on clean inputs.

The shared prefix `(read ; adder)` coincides because the two reads agree
(`unaryQROMAtRev_agrees`).  The final step differs — Bennett reversible read vs
measured `mzList` — but BOTH clear the addend to 0 and frame everything else: after
the adder the addend still holds `T[addr]` (`addendRestored`), the addresses
survive (Cuccaro frame), and the AND-ancillas are clean, so the second reversible
read XORs `T[addr]` back to 0, exactly as `mzList` does. -/

theorem babbushLookupAddAtRev_agrees
    (w W bits : Nat) (T : Nat → Nat) (addrBase ancBase q_start : Nat)
    (hW : W ≤ bits) (h_addr_pos : 0 < addrBase) (h_anc_pos : 0 < ancBase)
    (h_anc_addr : ∀ i i', i < w → i' < w → ancBase + i ≠ addrBase + i')
    (h_anc_blk : ∀ i, i < w →
      ¬ (q_start ≤ ancBase + i ∧ ancBase + i ≤ q_start + 2 * bits))
    (h_addr_blk : ∀ i, i < w →
      ¬ (q_start ≤ addrBase + i ∧ addrBase + i ≤ q_start + 2 * bits))
    (f : Nat → Bool) (hf : CleanInputModFree w W bits addrBase ancBase q_start T f) :
    Gate.applyNat (babbushLookupAddAtRev w W T bits addrBase ancBase q_start) f
      = EGate.applyNat (babbushLookupAddAt w W T bits addrBase ancBase q_start) f := by
  obtain ⟨hctrl, hanc, hcarry, haddend, hTlt⟩ := hf
  have hq_pos : 0 < q_start := by
    rcases Nat.eq_zero_or_pos q_start with h | h
    · rw [h] at hcarry; rw [hcarry] at hctrl; exact absurd hctrl (by simp)
    · exact h
  set pos := addendIdx q_start with hpos
  -- positional facts
  have hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k := by
    intro j k _ _ h; simp only [hpos, addendIdx] at h; omega
  -- disjointness for the QROM agreement (ctrl = 0, depth w)
  have h0_anc : ∀ i, i < w → (0 : Nat) ≠ ancBase + i := by
    intro i hi; omega
  have h0_addr : ∀ i, i < w → (0 : Nat) ≠ addrBase + i := by
    intro i hi; omega
  have haddr_anc : ∀ i i', i < w → i' < w → addrBase + i ≠ ancBase + i' :=
    fun i i' hi hi' => Ne.symm (h_anc_addr i' i hi' hi)
  have h0_word : ∀ j, j < W → (0 : Nat) ≠ pos j := by
    intro j hj; simp only [hpos, addendIdx]; omega
  have haddr_word : ∀ i j, i < w → j < W → addrBase + i ≠ pos j := by
    intro i j hi hj; have := h_addr_blk i hi; simp only [hpos, addendIdx]; omega
  have hanc_word : ∀ i j, i < w → j < W → ancBase + i ≠ pos j := by
    intro i j hi hj; have := h_anc_blk i hi; simp only [hpos, addendIdx]; omega
  -- the agreement applies to the FIRST read on `f`
  have agree1 : Gate.applyNat (unaryQROMAtRev pos W T addrBase ancBase w 0 0) f
      = EGate.applyNat (unaryQROMAt pos W T addrBase ancBase w 0 0) f :=
    unaryQROMAtRev_agrees pos W T addrBase ancBase w 0 0 f h0_anc h0_addr haddr_anc
      h0_word haddr_word hanc_word hanc
  -- common states
  set u := EGate.applyNat (unaryQROMAt pos W T addrBase ancBase w 0 0) f with hu
  set v := Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) u with hv
  -- the address decode after the read is unchanged (read frames addr register)
  have hu_addr : decodeReg (fun i => addrBase + i) w u
      = decodeReg (fun i => addrBase + i) w f :=
    decodeReg_ext _ _ _ _ (fun i hi => by
      rw [hu, unaryQROMAt_frame pos W T addrBase ancBase w 0 0 f (addrBase + i)
            (fun j hj => haddr_word i j hi hj)
            (fun i' hi' => Ne.symm (h_anc_addr i' i hi' hi))])
  -- ctrl preserved by read
  have hu_ctrl : u 0 = true := by
    rw [hu, unaryQROMAt_frame pos W T addrBase ancBase w 0 0 f 0 h0_word h0_anc, hctrl]
  -- read writes T[addr] onto the (clean) addend
  have hu_addend : ∀ j, j < W → u (pos j) = (T (decodeReg (fun i => addrBase + i) w f)).testBit j := by
    intro j hj
    have hsel := unaryQROMAt_selects_word pos W T addrBase ancBase hpos_inj w 0 0 f
      (fun i j hi hj => hanc_word i j hi hj)
      (fun i i' hi hi' => h_anc_addr i i' hi hi')
      (fun i j hi hj => haddr_word i j hi hj) h0_word h0_anc hanc j hj
    have hAj : f (pos j) = false := by simp only [hpos, addendIdx]; exact haddend j (by omega)
    rw [hu]
    simpa [hctrl, hAj] using hsel
  -- read clears (leaves clean) its AND-ancillas
  have hu_anc : ∀ i, i < w → u (ancBase + i) = false :=
    fun i hi => by rw [hu]; exact unaryQROMAt_anc_cleared pos W T addrBase ancBase w 0 0 f i hi
  -- carry-in clean after read
  have hu_carry : u q_start = false := by
    rw [hu, unaryQROMAt_frame pos W T addrBase ancBase w 0 0 f q_start
          (fun j hj => by simp only [hpos, addendIdx]; omega)
          (fun i hi => by have := h_anc_blk i hi; omega), hcarry]
  -- cuccaro ancClean on u (carry-in clean)
  have hanc_clean : cuccaroAdder.ancClean u bits q_start := by
    show u q_start = false; exact hu_carry
  -- v facts: addend restored to T[addr], addr/ctrl/anc framed off the adder block
  have hv_addend : ∀ j, j < W → v (pos j) = (T (decodeReg (fun i => addrBase + i) w f)).testBit j := by
    intro j hj
    have hr := cuccaroAdder.addendRestored bits q_start u hanc_clean j (by omega)
    have hidx : cuccaroAdder.addendIdx q_start j = pos j := rfl
    rw [hidx] at hr
    rw [hv]; show Gate.applyNat (cuccaroAdder.circuit bits q_start) u (pos j) = _
    rw [hr]; exact hu_addend j hj
  have hv_anc : ∀ i, i < w → v (ancBase + i) = false := by
    intro i hi
    have hframe := cuccaroAdder.frame bits q_start u (ancBase + i)
      (by show ¬ (q_start ≤ ancBase + i ∧ ancBase + i < q_start + (2 * bits + 1))
          have := h_anc_blk i hi; omega)
    rw [hv]; show Gate.applyNat (cuccaroAdder.circuit bits q_start) u (ancBase + i) = false
    rw [hframe]; exact hu_anc i hi
  -- the second reversible read, via agreement on the clean `v`, equals the measured read
  have agree2 : Gate.applyNat (unaryQROMAtRev pos W T addrBase ancBase w 0 0) v
      = EGate.applyNat (unaryQROMAt pos W T addrBase ancBase w 0 0) v :=
    unaryQROMAtRev_agrees pos W T addrBase ancBase w 0 0 v h0_anc h0_addr haddr_anc
      h0_word haddr_word hanc_word hv_anc
  -- addr decode after the adder is unchanged (adder frames the address register)
  have hv_addr : decodeReg (fun i => addrBase + i) w v
      = decodeReg (fun i => addrBase + i) w f := by
    rw [← hu_addr]
    refine decodeReg_ext _ _ _ _ (fun i hi => ?_)
    have hframe := cuccaroAdder.frame bits q_start u (addrBase + i)
      (by show ¬ (q_start ≤ addrBase + i ∧ addrBase + i < q_start + (2 * bits + 1))
          have := h_addr_blk i hi; omega)
    rw [hv]; show Gate.applyNat (cuccaroAdder.circuit bits q_start) u (addrBase + i) = _
    rw [hframe]
  -- ctrl preserved by the adder (0 is off the adder block since q_start > 0)
  have hv_ctrl : v 0 = true := by
    have hframe := cuccaroAdder.frame bits q_start u 0
      (by show ¬ (q_start ≤ 0 ∧ 0 < q_start + (2 * bits + 1)); omega)
    rw [hv]; show Gate.applyNat (cuccaroAdder.circuit bits q_start) u 0 = true
    rw [hframe]; exact hu_ctrl
  -- FINAL: both circuits clear the addend and frame the rest; agree as functions.
  show Gate.applyNat (Gate.seq (Gate.seq
      (unaryQROMAtRev pos W T addrBase ancBase w 0 0)
      (cuccaro_n_bit_adder_full bits q_start))
      (unaryQROMAtRev pos W T addrBase ancBase w 0 0)) f
    = EGate.applyNat (EGate.seq (EGate.seq
      (unaryQROMAt pos W T addrBase ancBase w 0 0)
      (EGate.base (cuccaro_n_bit_adder_full bits q_start)))
      (mzList ((List.range W).map pos))) f
  simp only [Gate.applyNat_seq, EGate.applyNat]
  rw [agree1, ← hu, ← hv, agree2]
  -- now: applyNat (unaryQROMAt) v = applyNat (mzList (addend)) v
  funext p
  by_cases hpos_word : ∃ j, j < W ∧ p = pos j
  · obtain ⟨j, hj, rfl⟩ := hpos_word
    -- addend wire: measured mzList → false; reversible read XORs T[addr] back → false
    rw [applyNat_mzList_clears _ _ (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)]
    have hsel := unaryQROMAt_selects_word pos W T addrBase ancBase hpos_inj w 0 0 v
      (fun i j hi hj => hanc_word i j hi hj)
      (fun i i' hi hi' => h_anc_addr i i' hi hi')
      (fun i j hi hj => haddr_word i j hi hj) h0_word h0_anc hv_anc j hj
    rw [hsel, hv_ctrl, hv_addr, hv_addend j hj]
    simp
  · push Not at hpos_word
    by_cases hp_anc : ∃ i, i < w ∧ p = ancBase + i
    · obtain ⟨i, hi, rfl⟩ := hp_anc
      -- AND-ancilla: measured mzList preserves (= v anc = false); read clears to false
      rw [applyNat_mzList_preserves _ _
            (by simp only [List.mem_map, List.mem_range]; rintro ⟨j, hj, hjeq⟩
                exact hanc_word i j hi hj hjeq.symm),
          unaryQROMAt_anc_cleared pos W T addrBase ancBase w 0 0 v i hi, hv_anc i hi]
    · push Not at hp_anc
      -- elsewhere: both frame to v p
      rw [applyNat_mzList_preserves _ _
            (by simp only [List.mem_map, List.mem_range]; rintro ⟨j, hj, hjeq⟩
                exact hpos_word j hj hjeq.symm),
          unaryQROMAt_frame pos W T addrBase ancBase w 0 0 v p
            (fun j hj => fun h => hpos_word j hj h)
            (fun i hi => fun h => hp_anc i hi h)]

/-! ### The windowed fold: `multiplyAddAtRev` agrees with the measured
`multiplyAddAt` on a `CountGateMulInput`.

By induction on the number of consumed windows.  At each step the running MEASURED
state is `CleanInputModFree` for window `n` (read off `multiplyAddAt_fold`'s carried
invariants), so the per-window agreement `babbushLookupAddAtRev_agrees` applies; the
IH gives that the reversible and measured running states coincide, so the next
window's reversible step matches its measured step. -/

open FormalRV.Shor.WindowedArith (window) in
theorem multiplyAddAtRev_agrees_fold
    (w bits a numWin y m q_start : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (hw : 0 < w) (hq : 0 < q_start)
    (hT : ∀ k v, Tfam m k v = (a * (2 ^ w) ^ k * v) % 2 ^ bits)
    (hy : y < (2 ^ w) ^ numWin)
    (g0 : Nat → Bool) (hg0 : CountGateMulInput w bits numWin y q_start g0) :
    ∀ n, n ≤ numWin →
      Gate.applyNat (seqAllG ((List.range n).map (laAtRev w bits bits Tfam q_start m))) g0
        = EGate.applyNat (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0 := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n ≤ numWin := by omega
    have hnW : n < numWin := by omega
    -- the measured fold's depth-`n` invariants (for the just-about-to-run window `n`)
    have hfold := multiplyAddAt_fold w bits a numWin y m q_start Tfam hw hq hT g0
      hg0.ctrl0 hg0.carry0 hg0.aug0 hg0.addend0 hg0.anc0 hg0.addr0 n hn'
    obtain ⟨_hV, hC, hCar, hAdd, hAnc, hAddr⟩ := hfold
    -- the measured depth-`n` state and the window-`n` gates
    set gm := EGate.applyNat (seqAll ((List.range n).map (laAt w bits bits Tfam q_start m))) g0
      with hgm
    -- peel the last reversible/measured window via the succ lemmas
    rw [applyNat_seqAllG_range_succ, applyNat_seqAll_range_succ, ih hn', ← hgm]
    -- now both reduce to applying window `n`'s step to the COMMON state `gm`
    -- the measured window `n` address = window w y n
    have haddr_n : decodeReg (fun i => addrBaseOf w bits q_start n + i) w gm = window w y n :=
      hAddr n (le_refl n) hnW
    -- the per-window CleanInputModFree at the measured depth-`n` state
    have hclean : CleanInputModFree w bits bits
        (addrBaseOf w bits q_start n) (ancBaseOf w bits q_start n) q_start (Tfam m n) gm := by
      refine ⟨hC, fun i hi => hAnc n (le_refl n) hnW i hi, hCar, hAdd, ?_⟩
      rw [haddr_n, hT n (window w y n)]
      exact Nat.mod_lt _ (Nat.two_pow_pos bits)
    -- window `n`'s reversible step agrees with its measured step on `gm`
    show Gate.applyNat (laAtRev w bits bits Tfam q_start m n) gm
      = EGate.applyNat (laAt w bits bits Tfam q_start m n) gm
    unfold laAtRev laAt
    exact babbushLookupAddAtRev_agrees w bits bits (Tfam m n)
      (addrBaseOf w bits q_start n) (ancBaseOf w bits q_start n) q_start
      (le_refl bits)
      (by unfold addrBaseOf; omega)
      (by unfold ancBaseOf addrBaseOf; omega)
      (fun i i' hi hi' => by unfold ancBaseOf addrBaseOf; omega)
      (fun i hi => by unfold ancBaseOf addrBaseOf; omega)
      (fun i hi => by unfold addrBaseOf; omega)
      gm hclean

/-- **★ `radd_agrees` — the reversible reconstruction computes `s2State`. ★**  The
    placed reversible `radd i` has the SAME `applyNat` action on the clean scattered
    `egG1`-state as the MEASURED count gate `egG2 = multiplyAddAt`, for every
    iterate `i` and `x < N`.  PROVED: the per-window agreement
    `babbushLookupAddAtRev_agrees` (built on the reversible-QROM agreement
    `unaryQROMAtRev_agrees`) folded across all `numWin` windows
    (`multiplyAddAtRev_agrees_fold`), instantiated at the `CountGateMulInput` that
    `egG1` produces (`s1_countGateMulInput`). -/
theorem radd_agrees
    (w bits numWin N a : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (i x : Nat) (hx : x < N) :
    Gate.applyNat (radd w bits numWin a i)
        (Gate.applyNat (egG1 w bits i)
          (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x))
      = s2State w bits numWin a i x := by
  set g0 := Gate.applyNat (egG1 w bits i)
    (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) with hg0def
  have hg0 : CountGateMulInput w bits numWin x 1 g0 :=
    s1_countGateMulInput w bits numWin N a hw hbits hN2 i x hx
  have hxbits : x < 2 ^ bits := lt_of_lt_of_le hx (by omega)
  have hxnw : x < (2 ^ w) ^ numWin := by
    rw [pow_w_numWin w bits numWin hbits]; exact hxbits
  -- both sides are the same windowed fold; `radd` = seqAllG (laAtRev), `egG2` = seqAll (laAt)
  show Gate.applyNat (multiplyAddAtRev w bits bits (tableFam w bits a) 1 i numWin) g0
    = EGate.applyNat (egG2 w bits numWin a i) g0
  show Gate.applyNat
      (seqAllG ((List.range numWin).map (laAtRev w bits bits (tableFam w bits a) 1 i))) g0
    = EGate.applyNat
      (seqAll ((List.range numWin).map (laAt w bits bits (tableFam w bits a) 1 i))) g0
  exact multiplyAddAtRev_agrees_fold w bits (a ^ (2 ^ i)) numWin x i 1 (tableFam w bits a)
    hw (by omega) (fun k v => tableFam_spec w bits a i k v) hxnw g0 hg0 numWin (le_refl numWin)

/-! ## §4. The concrete `unmul` and the UNCONDITIONAL residue discharge.

`radd` is a fully-REVERSIBLE pure `Gate` (no `EGate.mz`) whose `applyNat` on the
clean scattered `egG1`-state computes the SAME post-state as the MEASURED count
gate `egG2 = multiplyAddAt` (it realises `s2State`) — this is `radd_agrees`, PROVED
above by folding the per-window agreement (built on `unaryQROMAtRev_agrees`).
Therefore `unmulConcrete := Gate.reverse radd` discharges `UnmulSpecRfree`
(reverse-cancel), and the residue equation follows UNCONDITIONALLY (no abstract
`unmul` parameter, no extra hypothesis) by instantiating
`block_matches_residue_direct`. -/

/-- **The concrete reversible multiply-UNcompute** = the inverse circuit of the
    reversible reconstruction `radd`. -/
def unmulConcrete (w bits numWin a : Nat) : Nat → Gate :=
  fun i => Gate.reverse (radd w bits numWin a i)

/-- **★ `unmulConcrete` DISCHARGES `UnmulSpecRfree` — UNCONDITIONALLY. ★**
    `unmul i = reverse (radd i)` and `radd i` is well-typed, so by
    `applyNat_reverse_cancel`, applying it to `radd i`'s output `s2State`
    (= `radd_agrees`) returns `radd i`'s input — the scattered `egG1`-state —
    exactly as `UnmulSpecRfree` demands. -/
theorem unmulConcrete_spec (w bits numWin N a : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits) (hN2 : 2 * N ≤ 2 ^ bits) :
    UnmulSpecRfree w bits numWin N a (unmulConcrete w bits numWin a) := by
  intro i x hx
  show Gate.applyNat (Gate.reverse (radd w bits numWin a i)) (s2State w bits numWin a i x)
    = Gate.applyNat (egG1 w bits i) (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)
  rw [← radd_agrees w bits numWin N a hw hbits hN2 i x hx]
  exact applyNat_reverse_cancel (radd w bits numWin a i) (dimRadd w bits numWin)
    (radd_wellTyped w bits numWin a i hw hb1)
    (Gate.applyNat (egG1 w bits i) (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x))

/-- **★ THE UNCONDITIONAL RESIDUE DISCHARGE (R-free). ★**  Instantiating
    `block_matches_residue_direct` at the CONCRETE reversible `unmul := unmulConcrete`
    (whose spec `unmulConcrete_spec` is PROVED), the concrete `egRfree` — which
    literally contains `multiplyAddAt` — realises the residue equation on the
    canonical zero-ancilla encoding, with NO `unmul` hypothesis at all. -/
theorem block_matches_residue_direct_unconditional
    (w bits numWin cm N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hcm : cm ≤ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (i x : Nat) (hx : x < N) :
    EGate.applyNat (egRfree w bits numWin cm N a (unmulConcrete w bits numWin a) i)
        (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)
      = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) ((a ^ (2 ^ i) * x) % N) :=
  block_matches_residue_direct w bits numWin cm N a ainv0 (unmulConcrete w bits numWin a)
    hw hbits hb1 hN1 hN2 hcm h_inv0
    (unmulConcrete_spec w bits numWin N a hw hbits hb1 hN2) i x hx

/-- **★ PACKAGED UNCONDITIONAL `ModExpAtEncodedMatchesResidue` ★** for the concrete
    reversible `eg i := egRfree … (unmulConcrete …) i`.  The measured count-bearing
    `multiplyAddAt` is literally present (`G2`); the multiply-UNcompute is the
    concrete reversible `unmulConcrete` (NO abstract parameter, NO extra
    hypothesis). -/
theorem egRfree_matchesResidue_unconditional
    (w bits numWin cm N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hcm : cm ≤ bits)
    (h_inv0 : a * ainv0 % N = 1) :
    ShorComposedFinal.ModExpAtEncodedMatchesResidue a N bits (2 * w + 2 * bits + 3)
      (fun i => egRfree w bits numWin cm N a (unmulConcrete w bits numWin a) i)
      (fun _ x => encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) where
  block_matches_residue := fun i x hx =>
    block_matches_residue_direct_unconditional w bits numWin cm N a ainv0
      hw hbits hb1 hN1 hN2 hcm h_inv0 i x hx

/-- **The honest count of the unconditional reversible reconstruction.**  The
    Bennett-reversible `unmulConcrete` (= `reverse radd`) is NOT T-free: its T-count
    equals `radd`'s (reverse preserves T-count).  The packaged `egRfree`'s T-count
    therefore decomposes as `multiplyAddAt` (G2, the literal count gate) +
    `2·divModNAt` (G3/G5) + `radd` (the reversible reconstruction = G6) +
    `inPlaceMulDataAt` (G8); G1/G7 are T-free.  We record the `reverse`-invariance
    of `unmulConcrete`'s T-count, the load-bearing honest fact. -/
theorem unmulConcrete_tcount (w bits numWin a i : Nat) :
    Gate.tcount (unmulConcrete w bits numWin a i)
      = Gate.tcount (radd w bits numWin a i) := by
  show Gate.tcount (Gate.reverse (radd w bits numWin a i)) = _
  exact tcount_reverse (radd w bits numWin a i)

end FormalRV.Audit.GidneyEkera2021.ModExpAtUnmul
