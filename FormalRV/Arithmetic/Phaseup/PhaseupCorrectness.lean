/-
  FormalRV.Arithmetic.Phaseup.PhaseupCorrectness
  ────────────────────────────────────────────────
  CORRECTNESS for the reusable phaseup gadget: the diagonal phase action and the
  end-to-end measured-uncompute channel behaviour.  Every proof here REUSES the
  verified `splitPhaseLookup` machinery in `FormalRV.Shor.SplitPhaseFixup` — NO
  phase semantics is re-derived; this file only surfaces the load-bearing
  `splitPhaseLookup_diagonal` under the gadget's public name.

  ## What "correct" means for a phase gadget

  Phaseup is a DIAGONAL operator at the amplitude / `BaseUCom` layer — it does NOT
  flip any Boolean wire (so there is no `applyNat` statement to make).  Its
  contract is the phase it stamps on each basis state:

      `uc_eval (phaseup …) * |f⟩ = (−1)^(ctrl ∧ F(addr)) • |f⟩`,

  exactly when the AND-ladder and one-hot ancillas are clean (the gadget's own
  operating frame — surfaced HONESTLY as the hypotheses `hand`, `hhot`).  This is
  `splitPhaseLookup_diagonal`, re-exported here verbatim.

  ## The required clean-ancilla hypotheses (honest)

  No address-driven phase circuit on this wire layout can act diagonally on a
  state whose AND-ladder ancillas are DIRTY (see `PhaseLookupFixup`'s module note:
  the abstract `hP` is strictly stronger than any real ancilla-using circuit can
  satisfy).  So `phaseup_diagonal` carries:
    * `hand : ∀ i < w, f (ulookup_and_idx i) = false`   — AND-ladder clean,
    * `hhot : ∀ h < 2^w1, f (base + h) = false`          — one-hot ancillas clean.
  These are exactly the conditions the channel corollary's `SplitGoodState`
  bundles; they are met by every lookup-computed family the uncompute consumes.

  Refs: Gidney 2025 (phaseup); proof reuse from `Shor.SplitPhaseFixup`.
-/
import FormalRV.Arithmetic.Phaseup.PhaseupDef

namespace FormalRV.Arithmetic.Phaseup

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.Framework.BaseCom
open FormalRV.BQAlgo
open FormalRV.Shor.MeasuredLookupUncompute
open FormalRV.Shor.PhaseLookupFixup
open FormalRV.Shor.SplitPhaseFixup
open Matrix

noncomputable section

/-! ## §1. The diagonal phase action (decoder form). -/

/-- **★ HEADLINE — phaseup applies the table-indexed phase.**  On EVERY basis
    state `f` whose AND-ladder and one-hot ancillas are clean (ctrl and address
    arbitrary), the phaseup gadget is DIAGONAL with phase `(−1)^(ctrl ∧ F(addr))`,
    where `addr = decAddr (w1 + w2) f` is the value held by the address wires.

    Reuses `splitPhaseLookup_diagonal` verbatim; the clean-ancilla hypotheses
    `hand`/`hhot` are surfaced honestly (no address-driven phase circuit acts
    diagonally on a ladder-dirty state). -/
theorem phaseup_diagonal (dim w1 w2 base : Nat) (F : Nat → Bool) (f : Nat → Bool)
    (hbase : 2 * (w1 + w2) < base) (hdim : base + 2 ^ w1 ≤ dim)
    (hand : ∀ i, i < w1 + w2 → f (ulookup_and_idx i) = false)
    (hhot : ∀ h, h < 2 ^ w1 → f (base + h) = false) :
    uc_eval (phaseup dim F w1 w2 base) * f_to_vec dim f
      = (if f ulookup_ctrl_idx && F (decAddr (w1 + w2) f) then (-1 : ℂ) else 1)
          • f_to_vec dim f :=
  splitPhaseLookup_diagonal dim w1 w2 base F f hbase hdim hand hhot

/-- **HEADLINE (address form)** — the query-state shape: ctrl set, the address
    wires holding the bits of `v < 2^(w1+w2)`, ladders and one-hot ancillas clean
    ⟹ phaseup applies exactly the single table phase `(−1)^(F v)`. -/
theorem phaseup_diagonal_addr (dim w1 w2 base : Nat) (F : Nat → Bool)
    (v : Nat) (f : Nat → Bool)
    (hbase : 2 * (w1 + w2) < base) (hdim : base + 2 ^ w1 ≤ dim)
    (hv : v < 2 ^ (w1 + w2))
    (hctrl : f ulookup_ctrl_idx = true)
    (haddr : ∀ i, i < w1 + w2 → f (ulookup_address_idx i) = v.testBit i)
    (hand : ∀ i, i < w1 + w2 → f (ulookup_and_idx i) = false)
    (hhot : ∀ h, h < 2 ^ w1 → f (base + h) = false) :
    uc_eval (phaseup dim F w1 w2 base) * f_to_vec dim f
      = (if F v then (-1 : ℂ) else 1) • f_to_vec dim f :=
  splitPhaseLookup_diagonal_addr dim w1 w2 base F v f hbase hdim hv hctrl haddr
    hand hhot

/-- The UNSPLIT phaseup has the SAME diagonal phase action (decoder form) — the
    object `phaseupFull` is verified to apply `(−1)^(ctrl ∧ F(addr))` too; it just
    costs the full table read.  (Reuses `phaseLookup_diagonal`.) -/
theorem phaseupFull_diagonal (dim w : Nat) (F : Nat → Bool) (f : Nat → Bool)
    (hdim : 2 * w < dim)
    (hand : ∀ i, i < w → f (ulookup_and_idx i) = false) :
    uc_eval (phaseupFull dim w F) * f_to_vec dim f
      = (if f ulookup_ctrl_idx && F (decAddr w f) then (-1 : ℂ) else 1)
          • f_to_vec dim f :=
  phaseLookup_diagonal dim w F f hdim hand

/-! ## §2. The end-to-end measured-uncompute channel corollary.

The phaseup gadget's faithful END-TO-END behaviour: used as the per-bit fixup of
Gidney's measurement-based lookup-uncompute, it perfectly uncomputes the QROM
word register at the √-cost.  This is `measWordUncompute_splitPhaseLookup`,
re-exported under the gadget's name — the channel-layer correctness, on the
`SplitGoodState` family (ctrl set, ladders + one-hot ancillas clean). -/

/-- **★ END-TO-END (channel) HEADLINE** — phaseup as the per-bit fixup of the
    measured lookup-uncompute is the PERFECT uncompute on every lookup-computed
    family (ctrl set, ladders + one-hot ancillas clean, word bit `j` holding
    `T[addr].bit j` on the support): coefficients intact, all `W` word bits
    released as `|0…0⟩`, no second lookup — at the Gidney–Ekerå √-cost.

    Re-exports `measWordUncompute_splitPhaseLookup` verbatim with
    `P j := phaseup dim (fun v => (T v).testBit j) w1 w2 base`. -/
theorem measWordUncompute_phaseup {dim : Nat} {ι : Type*}
    (w1 w2 base W : Nat) (pos : Nat → Nat) (T : Nat → Nat)
    (hbase : 2 * (w1 + w2) < base)
    (hdim : base + 2 ^ w1 ≤ dim)
    (hpos : ∀ j, j < W → pos j < dim)
    (hpos_high : ∀ j, j < W → base + 2 ^ w1 ≤ pos j)
    (hinj : ∀ j, j < W → ∀ k, k < W → j ≠ k → pos j ≠ pos k)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool)
    (hgood : ∀ i ∈ s, SplitGoodState w1 w2 base (g i))
    (hword : ∀ i ∈ s, ∀ j, j < W →
        g i (pos j) = (T (decAddr (w1 + w2) (g i))).testBit j) :
    c_eval (measWordUncompute dim pos
        (fun j => phaseup dim (fun v => (T v).testBit j) w1 w2 base) W)
        ((∑ i ∈ s, α i • f_to_vec dim (g i))
          * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
      = (∑ i ∈ s, α i • f_to_vec dim (clearWord pos W (g i)))
          * (∑ i ∈ s, α i • f_to_vec dim (clearWord pos W (g i)))ᴴ :=
  measWordUncompute_splitPhaseLookup w1 w2 base W pos T hbase hdim hpos hpos_high
    hinj s α g hgood hword

end -- noncomputable section

end FormalRV.Arithmetic.Phaseup
