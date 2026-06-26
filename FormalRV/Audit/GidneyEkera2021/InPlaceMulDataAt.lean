/-
  Audit · Gidney–Ekerå 2021 · THE DATA-BAND IN-PLACE MODULAR-MULTIPLY GATE
  `inPlaceMulDataAt`  (relabel route — works for ANY `numWin`)
  ════════════════════════════════════════════════════════════════════════════
  GOAL.  A verified reversible IN-PLACE modular multiply `x ↦ (c·x) % N` on the
  canonical BIG-ENDIAN DATA BAND `[0, bits)` of an `encodeDataZeroAnc`-style
  state, for ANY `numWin` — with NO `numWin ≤ 2` (`hsep : bits ≤ 1 + 2·w`)
  restriction.

  WHY THE TRANSCODE ROUTE NEEDS `hsep`.  `InPlaceMulData.lean` BRIDGES the
  big-endian band `[0,bits)` into `windowedModNMulInPlace`'s native
  `ModNMulReady` Cuccaro layout (control `0`, Cuccaro block `[1+2w, 1+2w+2bits+1)`,
  y-register `[yBase, yBase+bits)`, flag `yBase+bits`, with
  `yBase = 1+2w+(2·bits+1)`).  Because the band `[0,bits)` overlaps the Cuccaro
  block `[1+2w, …)` on `[1+2w, bits)`, "band holds `x`" and "block clean" are only
  simultaneously satisfiable when `bits ≤ 1+2w`, i.e. `numWin ≤ 2`.

  HOW THE RELABEL ROUTE REMOVES IT.  We do NOT move bits with a SWAP cascade.
  Instead we CONJUGATE `windowedModNMulInPlace` by a fixed wire RELABEL
  `σ = layoutMul` (via `BQAlgo.relabelGate` + the transport `applyNat_relabelGate`)
  that:
    • sends each native VALUE wire `yBase + i` (LSB-first, carrying `y.testBit i`)
      to the big-endian DATA wire `bits-1-i ∈ [0,bits)`
      (`encodeDataZeroAnc bits anc x (bits-1-i) = x.testBit i`), and
    • sends EVERY OTHER native wire `p` (control, Cuccaro block, flag) UP to the
      FRESH scratch region `scratchBase + p` with `scratchBase := bits`.
  Data images live in `[0, bits)`; non-data images live in `[bits, …)`; the two
  families are disjoint, so `σ` is injective.  The whole `ModNMulReady` scratch
  (control / block / flag) then sits at positions `≥ bits`, DISJOINT from the data
  band `[0,bits)` — NO overlap, NO `hsep`.

  This reuses `windowedModNMulInPlace_correct` VERBATIM, at ANY `numWin`.

  DELIVERABLES (mirroring `DivModNAt.lean`).
    • `layoutMul`            — the value→data, rest→fresh-scratch relabel;
        injective; image-range lemma (data in `[0,bits)`, scratch `≥ bits`).
    • `inPlaceMulDataAt`     — `relabelGate layoutMul (windowedModNMulInPlace …)`.
    • `inPlaceMulDataAt_apply` — on `f` with the data band `[0,bits)` encoding `x`
        (big-endian `encodeDataZeroAnc`, `x < N`) and the fresh scratch region
        clean: after the gate the data band encodes `(c·x)%N` in the SAME
        convention, the scratch is restored clean, off-band/off-scratch FRAMED.
        NO `numWin` restriction.
    • `inPlaceMulDataAt_wellTyped` — `WellTyped Dmul`, `Dmul := scratchBase + native`.
    • `inPlaceMulDataAt_tcount`    — `= tcount (windowedModNMulInPlace …)`
        (relabel is wire-only).

  Kernel-clean: no `sorry`, no `native_decide`; axioms ⊆
  `{propext, Classical.choice, Quot.sound}`.  ADDITIVE.
-/
import FormalRV.Audit.GidneyEkera2021.TranscodeBand
import FormalRV.Arithmetic.Windowed.WindowedModNInPlace
import FormalRV.Arithmetic.Adder.ContiguousTransport

namespace FormalRV.Audit.GidneyEkera2021.InPlaceMulDataAt

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open VerifiedShor.Windowed (nat_to_funbool_eq_testBit)

/-! ## §0. Positions and the layout permutation `layoutMul`.

`windowedModNMulInPlace`'s native `ModNMulReady` layout:
  • control     : `ulookup_ctrl_idx = 0`                         (must be SET)
  • carry-in    : `1 + 2·w`                                      (clean)
  • augend      : `1 + 2·w + 2·i + 1`   (`i < bits`)             (clean)
  • addend      : `1 + 2·w + 2·i + 2`   (`i < bits`)             (clean)
  • VALUE band  : `yBase + i`           (`i < bits`)  carries `y.testBit i`
  • flag        : `yBase + numWin·w`    (= `yBase + bits`)       (clean)
where `yBase = 1 + 2·w + (2·bits+1)` and (under `numWin·w = bits`) the native
dimension is `yBase + bits + 1`.

`layoutMul` sends VALUE wire `yBase + i` to data wire `bits-1-i ∈ [0,bits)`, and
EVERY other native wire `p` to `scratchBase + p` with `scratchBase := bits`. -/

/-- The y-register base of the `ModNMulReady` layout (= `1+2w+cuccaroAdder.span bits`). -/
def yBase (w bits : Nat) : Nat := 1 + 2 * w + (2 * bits + 1)

/-- Fresh scratch base: the first position at-or-above the big-endian data band
    `[0, bits)`.  We pick the minimal `scratchBase = bits`, so the entire
    `ModNMulReady` scratch (control / Cuccaro block / flag) lands at positions
    `≥ bits`, disjoint from the data band. -/
def scratchBase (bits : Nat) : Nat := bits

/-- The VALUE-wire predicate of `windowedModNMulInPlace`'s native layout: the
    contiguous y-register range `[yBase, yBase + bits)`.  (Wire `yBase + i`,
    `i < bits`, carries `y.testBit i`.) -/
def isValWire (w bits p : Nat) : Prop := yBase w bits ≤ p ∧ p < yBase w bits + bits

instance (w bits p : Nat) : Decidable (isValWire w bits p) := by
  unfold isValWire; infer_instance

/-- The layout permutation.  The native VALUE wire `yBase + i` goes to the
    big-endian data wire `bits-1-i`; every other native wire `p` goes up to
    `scratchBase + p` (fresh scratch at/above the data band). -/
def layoutMul (w bits : Nat) : Nat → Nat := fun p =>
  if isValWire w bits p then bits - 1 - (p - yBase w bits)
  else scratchBase bits + p

/-! ## §1. Injectivity of `layoutMul`. -/

/-- `layoutMul` is injective: value images live in `[0, bits)` (below
    `scratchBase = bits`), non-value images are `scratchBase + p ≥ bits`. -/
theorem layoutMul_injective (w bits : Nat) :
    Function.Injective (layoutMul w bits) := by
  intro a b hab
  unfold layoutMul at hab
  by_cases ha : isValWire w bits a <;> by_cases hb : isValWire w bits b
  · rw [if_pos ha, if_pos hb] at hab
    obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
    unfold yBase at ha1 ha2 hb1 hb2 hab; omega
  · rw [if_pos ha, if_neg hb] at hab
    obtain ⟨ha1, ha2⟩ := ha
    unfold yBase at ha1 ha2 hab; unfold scratchBase at hab; omega
  · rw [if_neg ha, if_pos hb] at hab
    obtain ⟨hb1, hb2⟩ := hb
    unfold yBase at hb1 hb2 hab; unfold scratchBase at hab; omega
  · rw [if_neg ha, if_neg hb] at hab; unfold scratchBase at hab; omega

/-! ## §2. Image equations for the named native-wire families. -/

/-- VALUE wire `yBase + i` (`i < bits`) maps to the big-endian data wire
    `bits-1-i ∈ [0, bits)`. -/
theorem layoutMul_val (w bits i : Nat) (hi : i < bits) :
    layoutMul w bits (yBase w bits + i) = bits - 1 - i := by
  unfold layoutMul
  have h : isValWire w bits (yBase w bits + i) := ⟨by omega, by omega⟩
  rw [if_pos h, Nat.add_sub_cancel_left]

/-- Control wire `ulookup_ctrl_idx = 0` maps to `scratchBase + 0 = bits`. -/
theorem layoutMul_ctrl (w bits : Nat) :
    layoutMul w bits ulookup_ctrl_idx = scratchBase bits := by
  unfold layoutMul isValWire ulookup_ctrl_idx yBase
  rw [if_neg (by omega), Nat.add_zero]

/-- Any NON-value native wire `p` (control, Cuccaro block, flag, …) maps to
    `scratchBase + p`. -/
theorem layoutMul_nonval (w bits p : Nat) (hp : ¬ isValWire w bits p) :
    layoutMul w bits p = scratchBase bits + p := by
  unfold layoutMul; rw [if_neg hp]

/-- **Image containment.**  Every `σ`-image lies in `[0, bits) ∪ [bits, ∞)`:
    value images are `bits-1-i < bits`; non-value images are
    `scratchBase + p = bits + p ≥ bits`.  (Data band below scratch.) -/
theorem layoutMul_image_range (w bits p : Nat) :
    layoutMul w bits p < bits ∨ bits ≤ layoutMul w bits p := by
  unfold layoutMul
  by_cases h : isValWire w bits p
  · left; rw [if_pos h]; obtain ⟨h1, h2⟩ := h; unfold yBase at h1 h2; omega
  · right; rw [if_neg h]; unfold scratchBase; omega

/-! ## §3. Generic relabel helpers (local copies; tiny + self-contained).

These mirror the `DivModNAt.lean` helpers (`tcount_relabelGate`,
`wellTyped_relabelGate_src`, `applyNat_relabelGate_frame`).  Kept local to avoid
importing the divider tree. -/

/-- `tcount` is invariant under relabel (relabel changes only wire indices). -/
theorem tcount_relabelGate (σ : Nat → Nat) (g : Gate) :
    Gate.tcount (relabelGate σ g) = Gate.tcount g := by
  induction g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ ih₁ ih₂ => simp only [relabelGate, Gate.tcount, ih₁, ih₂]

/-- **Relabel preserves well-typedness (source-dimension form).**  If `g` is
    WellTyped at the SOURCE dimension `d0`, `σ` is injective, and `σ` maps the
    source wires `[0, d0)` into the TARGET `[0, dim)`, then `relabelGate σ g` is
    WellTyped at `dim`. -/
theorem wellTyped_relabelGate_src (σ : Nat → Nat) (hσ : Function.Injective σ)
    (d0 dim : Nat) (hmap : ∀ x, x < d0 → σ x < dim) :
    ∀ g, Gate.WellTyped d0 g → Gate.WellTyped dim (relabelGate σ g)
  | Gate.I,         hg => Nat.lt_of_le_of_lt (Nat.zero_le _) (hmap 0 hg)
  | Gate.X q,       hg => hmap q hg
  | Gate.CX c t,    hg => ⟨hmap c hg.1, hmap t hg.2.1, fun h => hg.2.2 (hσ h)⟩
  | Gate.CCX a b c, hg =>
      ⟨hmap a hg.1, hmap b hg.2.1, hmap c hg.2.2.1,
        fun h => hg.2.2.2.1 (hσ h), fun h => hg.2.2.2.2.1 (hσ h),
        fun h => hg.2.2.2.2.2 (hσ h)⟩
  | Gate.seq g₁ g₂, hg =>
      ⟨wellTyped_relabelGate_src σ hσ d0 dim hmap g₁ hg.1,
        wellTyped_relabelGate_src σ hσ d0 dim hmap g₂ hg.2⟩

/-- **Relabel frame.**  If `p` is not the `σ`-image of any wire, the relabeled
    gate fixes `p`.  Proved by structural induction on `g`. -/
theorem applyNat_relabelGate_frame (σ : Nat → Nat) :
    ∀ (g : Gate) (f : Nat → Bool) (p : Nat), (∀ q, σ q ≠ p) →
      Gate.applyNat (relabelGate σ g) f p = f p := by
  intro g
  induction g with
  | I => intro f p _; rfl
  | X q =>
      intro f p hp
      show update f (σ q) (!f (σ q)) p = f p
      exact update_neq f (σ q) p _ (hp q).symm
  | CX c t =>
      intro f p hp
      show update f (σ t) (xor (f (σ t)) (f (σ c))) p = f p
      exact update_neq f (σ t) p _ (hp t).symm
  | CCX a b c =>
      intro f p hp
      show update f (σ c) (xor (f (σ c)) (f (σ a) && f (σ b))) p = f p
      exact update_neq f (σ c) p _ (hp c).symm
  | seq g₁ g₂ ih₁ ih₂ =>
      intro f p hp
      show Gate.applyNat (relabelGate σ g₂) (Gate.applyNat (relabelGate σ g₁) f) p = f p
      rw [ih₂ (Gate.applyNat (relabelGate σ g₁) f) p hp, ih₁ f p hp]

/-! ## §4. The placed gate, its dimension, well-typedness and T-count. -/

/-- Native register dimension of `windowedModNMulInPlace` (flag at `yBase + bits`
    inclusive, under `numWin·w = bits`). -/
def dimNative (w bits : Nat) : Nat := yBase w bits + bits + 1

/-- Total placed dimension: `scratchBase + native`.  Every native wire maps below
    this (data images `< bits ≤` this; non-data images `scratchBase + p` with
    `p < dimNative`). -/
def Dmul (w bits : Nat) : Nat := scratchBase bits + dimNative w bits

/-- **The placed in-place modular-multiply gate.**  `windowedModNMulInPlace`
    conjugated by the layout permutation `layoutMul`. -/
def inPlaceMulDataAt (w bits N numWin c cinv : Nat) : Gate :=
  relabelGate (layoutMul w bits) (windowedModNMulInPlace w bits c cinv N numWin)

/-- **Honest Toffoli count.**  `inPlaceMulDataAt` has exactly the same T-count as
    the native `windowedModNMulInPlace` (relabel is wire-only). -/
theorem inPlaceMulDataAt_tcount (w bits N numWin c cinv : Nat) :
    Gate.tcount (inPlaceMulDataAt w bits N numWin c cinv)
      = Gate.tcount (windowedModNMulInPlace w bits c cinv N numWin) := by
  unfold inPlaceMulDataAt; exact tcount_relabelGate _ _

/-- **Well-typed.**  `inPlaceMulDataAt` is well-typed at `Dmul`: the native
    `windowedModNMulInPlace` is well-typed at `dimNative`, and `layoutMul` maps
    every source wire `< dimNative` into `[0, Dmul)` (value wires below `bits`,
    non-value wires `< scratchBase + dimNative`). -/
theorem inPlaceMulDataAt_wellTyped (w bits N numWin c cinv : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) :
    Gate.WellTyped (Dmul w bits) (inPlaceMulDataAt w bits N numWin c cinv) := by
  unfold inPlaceMulDataAt Dmul
  refine wellTyped_relabelGate_src (layoutMul w bits)
    (layoutMul_injective w bits)
    (dimNative w bits)
    (scratchBase bits + dimNative w bits)
    (fun x hx => ?_)
    (windowedModNMulInPlace w bits c cinv N numWin)
    ?_
  · -- σ maps each source wire x < dimNative into [0, scratchBase + dimNative).
    unfold layoutMul
    by_cases h : isValWire w bits x
    · rw [if_pos h]; obtain ⟨h1, h2⟩ := h
      unfold scratchBase dimNative yBase at hx ⊢; omega
    · rw [if_neg h]; unfold scratchBase dimNative yBase at hx ⊢; omega
  · -- native well-typedness of windowedModNMulInPlace at dimNative.
    have hd : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dimNative w bits := by
      unfold dimNative yBase; omega
    exact FormalRV.BQAlgo.WindowedModNShor.windowedModNMulGate_wellTyped
      w bits N numWin c cinv (dimNative w bits) hw hbits hd

/-! ## §5. The data-band cleanliness contract and the pull-back of `ModNMulReady`.

`DataMulReady w bits anc x f` is the input/output contract for `inPlaceMulDataAt`:
  • the big-endian data band `[0,bits)` carries `x` (`encodeDataZeroAnc` order), and
  • the fresh scratch region is clean: `f scratchBase = true` (the control image)
    and `f (scratchBase + p) = false` for every NON-value native wire `p ≠ 0`
    (control / Cuccaro block / flag images, AND every out-of-range image).
This is EXACTLY the σ-pull-back of `ModNMulReady` (cf. `DivModNAt.pullback_DivState`):
each field below is one `ModNMulReady` conjunct transported by §2's image equations. -/

/-- Local accessor: `mulInputOf cuccaroAdder` reads bit `i` of `v` at the
    y-register wire `yBase + i`.  (The original is private in
    `WindowedModNInPlace`; restated via the public `mulInputOf_eq_encodeReg`
    + `encodeReg_at`.) -/
theorem mulInputOf_cuc_y_bit_local (w bits numWin v i : Nat)
    (hi : i < numWin * w) :
    mulInputOf cuccaroAdder w bits numWin v (1 + 2 * w + (2 * bits + 1) + i)
      = v.testBit i := by
  rw [mulInputOf_eq_encodeReg cuccaroAdder w bits numWin v _
        (by unfold ulookup_ctrl_idx; omega)]
  exact encodeReg_at _ _ _ i hi

/-- The input/output contract on the data band.  (`anc` is the canonical encoding
    ancilla count of `encodeDataZeroAnc`; it is inert here.) -/
def DataMulReady (w bits anc x : Nat) (f : Nat → Bool) : Prop :=
  -- data band `[0,bits)` = `x`, big-endian `encodeDataZeroAnc` convention.
  (∀ j, j < bits → f j = encodeDataZeroAnc bits anc x j)
  -- control image set.
  ∧ f (scratchBase bits) = true
  -- scratch region clean (every non-value native image except the control).
  ∧ (∀ p, p ≠ ulookup_ctrl_idx → ¬ isValWire w bits p →
        f (scratchBase bits + p) = false)

/-- The pull-back state `f ∘ σ` satisfies `ModNMulReady w bits numWin x` whenever
    `f` satisfies `DataMulReady`.  This is the bridge into
    `windowedModNMulInPlace_correct`.  PROOF: every `ModNMulReady` conjunct is a
    `DataMulReady` field transported by the §2 image equations; `mulInputOf`'s
    value is `x.testBit i` on value wires (`mulInputOf_cuc_y_bit`) and `false`
    elsewhere (low/high `encodeReg`), matching `DataMulReady`'s clean fields. -/
theorem pullback_ModNMulReady
    (w bits numWin anc x : Nat) (f : Nat → Bool)
    (hbits : 0 < bits) (hbw : numWin * w = bits) (hxbits : x < 2 ^ bits)
    (hf : DataMulReady w bits anc x f) :
    ModNMulReady w bits numWin x (fun p => f (layoutMul w bits p)) := by
  obtain ⟨h_data, h_ctrl, h_clean⟩ := hf
  -- The value-band readout: σ-pulled value wire `yBase + i` reads `x.testBit i`.
  have h_y : ∀ i, i < bits →
      f (layoutMul w bits (yBase w bits + i)) = x.testBit i := by
    intro i hi
    rw [layoutMul_val w bits i hi]
    -- `f (bits-1-i) = encodeDataZeroAnc … (bits-1-i) = nat_to_funbool bits x (bits-1-i)
    --              = x.testBit (bits-1-(bits-1-i)) = x.testBit i`.
    rw [h_data _ (by omega), encodeDataZeroAnc_data hxbits (by omega),
        nat_to_funbool_eq_testBit]
    congr 1; omega
  -- `mulInputOf` is `false` at any NON-control NON-value native wire.
  have h_mul_false : ∀ p, p ≠ ulookup_ctrl_idx → ¬ isValWire w bits p →
      mulInputOf cuccaroAdder w bits numWin x p = false := by
    intro p hp0 hpv
    by_cases hplow : p < 1 + 2 * w + (2 * bits + 1)
    · -- low: below the y-register base `yBase = 1+2w+span bits`.
      exact mulInputOf_low cuccaroAdder w bits numWin x p hp0 (by
        show p < 1 + 2 * w + cuccaroAdder.span bits
        show p < 1 + 2 * w + (2 * bits + 1); exact hplow)
    · -- high: `p ≥ yBase` and not a value wire ⟹ `p ≥ yBase + bits`.
      have hphigh : 1 + 2 * w + (2 * bits + 1) + bits ≤ p := by
        unfold isValWire yBase at hpv; omega
      have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
      rw [mulInputOf_eq_encodeReg cuccaroAdder w bits numWin x p hp0,
          hspan, encodeReg_high _ _ _ _ (by rw [hbw]; omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (F) frame: off-block, off-flag → `mulInputOf cuccaroAdder x p`.
    intro p hpb hpf
    by_cases hpv : isValWire w bits p
    · -- value wire `yBase + i`: reads `x.testBit i = mulInputOf … (yBase+i)`.
      obtain ⟨h1, h2⟩ := hpv
      obtain ⟨i, hi, rfl⟩ : ∃ i, i < bits ∧ p = yBase w bits + i :=
        ⟨p - yBase w bits, by unfold yBase at h1 h2 ⊢; omega,
          by unfold yBase at h1 ⊢; omega⟩
      show f (layoutMul w bits (yBase w bits + i))
        = mulInputOf cuccaroAdder w bits numWin x (yBase w bits + i)
      rw [h_y i hi]
      have hpos : yBase w bits + i = 1 + 2 * w + (2 * bits + 1) + i := rfl
      rw [hpos]
      exact (mulInputOf_cuc_y_bit_local w bits numWin x i (by omega)).symm
    · -- non-value: control or clean scratch image, matching `mulInputOf = …`.
      show f (layoutMul w bits p) = mulInputOf cuccaroAdder w bits numWin x p
      by_cases hp0 : p = ulookup_ctrl_idx
      · subst hp0
        rw [layoutMul_ctrl, h_ctrl, mulInputOf_ctrl]
      · rw [layoutMul_nonval w bits p hpv, h_clean p hp0 hpv,
            h_mul_false p hp0 hpv]
  · -- (D) addend register `1+2w+2i+2` clean.
    intro i hi
    have hpv : ¬ isValWire w bits (1 + 2 * w + 2 * i + 2) := by
      unfold isValWire yBase; omega
    show f (layoutMul w bits (1 + 2 * w + 2 * i + 2)) = false
    rw [layoutMul_nonval w bits _ hpv]
    exact h_clean _ (by unfold ulookup_ctrl_idx; omega) hpv
  · -- (C) carry-in `1+2w` clean.
    have hpv : ¬ isValWire w bits (1 + 2 * w) := by unfold isValWire yBase; omega
    show f (layoutMul w bits (1 + 2 * w)) = false
    rw [layoutMul_nonval w bits _ hpv]
    exact h_clean _ (by unfold ulookup_ctrl_idx; omega) hpv
  · -- (G) flag `yBase + numWin·w` clean.
    have hpv : ¬ isValWire w bits (1 + 2 * w + (2 * bits + 1) + numWin * w) := by
      unfold isValWire yBase; rw [hbw]; omega
    show f (layoutMul w bits (1 + 2 * w + (2 * bits + 1) + numWin * w)) = false
    rw [layoutMul_nonval w bits _ hpv]
    exact h_clean _ (by unfold ulookup_ctrl_idx; omega) hpv
  · -- (V) augend register `1+2w+2i+1` clean.
    intro i hi
    have hpv : ¬ isValWire w bits (1 + 2 * w + 2 * i + 1) := by
      unfold isValWire yBase; omega
    show f (layoutMul w bits (1 + 2 * w + 2 * i + 1)) = false
    rw [layoutMul_nonval w bits _ hpv]
    exact h_clean _ (by unfold ulookup_ctrl_idx; omega) hpv

/-! ## §6. HEADLINE — the placed in-place modular multiply on the data band. -/

/-- **★ `inPlaceMulDataAt_apply` — placed in-place modular multiply, ANY `numWin`. ★**
    On `f` whose big-endian data band `[0,bits)` encodes `x` (`encodeDataZeroAnc`
    convention, `DataMulReady`, `x < N`) with the fresh scratch region clean, and
    `c` invertible mod `N` (`cinv < N`, `c·cinv ≡ 1`), `0 < N`, `2·N ≤ 2^bits`,
    `0 < w`, `numWin·w = bits` — running `inPlaceMulDataAt`:

      • the DATA band `[0,bits)` encodes `(c·x) % N` in the SAME `encodeDataZeroAnc`
        big-endian convention;
      • the fresh scratch region is restored clean (control still set, every other
        non-value scratch image `false`);
      • positions OUTSIDE `[0,bits) ∪ scratch-region` are FRAMED (untouched).

    PROOF.  Pull the `ModNMulReady` predicate back through `σ = layoutMul`
    (`pullback_ModNMulReady`), apply `windowedModNMulInPlace_correct` to get
    `ModNMulReady ((c·x)%N)` of `f ∘ σ`-image, then push each output field
    forward via `applyNat_relabelGate` + the §2 image equations; the frame uses
    the relabel frame (§3) + image containment (§2).  NO `numWin` restriction. -/
theorem inPlaceMulDataAt_apply
    (w bits N numWin c cinv anc x : Nat) (f : Nat → Bool)
    (hw : 0 < w) (hbits : 0 < bits) (hbw : numWin * w = bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hx : x < N) (hcinv : cinv < N) (hinv : c * cinv % N = 1)
    (hf : DataMulReady w bits anc x f) :
    -- DATA band encodes (c·x)%N, SAME big-endian convention.
    (∀ j, j < bits →
        Gate.applyNat (inPlaceMulDataAt w bits N numWin c cinv) f j
          = encodeDataZeroAnc bits anc ((c * x) % N) j)
    -- scratch restored clean: control still set …
    ∧ Gate.applyNat (inPlaceMulDataAt w bits N numWin c cinv) f (scratchBase bits)
        = true
    -- … and every other non-value scratch image false.
    ∧ (∀ p, p ≠ ulookup_ctrl_idx → ¬ isValWire w bits p →
        Gate.applyNat (inPlaceMulDataAt w bits N numWin c cinv) f
          (scratchBase bits + p) = false)
    -- FRAME: positions off the data band and off the scratch region untouched.
    ∧ (∀ q, ¬ (∃ j, j < bits ∧ q = j) → ¬ (∃ p, q = scratchBase bits + p) →
        Gate.applyNat (inPlaceMulDataAt w bits N numWin c cinv) f q = f q)
    -- WELL-TYPED.
    ∧ Gate.WellTyped (Dmul w bits) (inPlaceMulDataAt w bits N numWin c cinv) := by
  set σ := layoutMul w bits with hσdef
  have hσinj : Function.Injective σ := layoutMul_injective w bits
  have hN_le : N ≤ 2 ^ bits := by omega
  have hxbits : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN_le
  have hcxlt : (c * x) % N < N := Nat.mod_lt _ hN_pos
  have hcxbits : (c * x) % N < 2 ^ bits := Nat.lt_of_lt_of_le hcxlt hN_le
  -- Pull `ModNMulReady x` back through σ.
  have hDS : ModNMulReady w bits numWin x (fun p => f (σ p)) :=
    pullback_ModNMulReady w bits numWin anc x f hbits hbw hxbits hf
  -- Apply the native correctness: `ModNMulReady ((c·x)%N)` of the native output.
  have hout :
      ModNMulReady w bits numWin ((c * x) % N)
        (Gate.applyNat (windowedModNMulInPlace w bits c cinv N numWin)
          (fun p => f (σ p))) :=
    windowedModNMulInPlace_correct w bits c cinv N numWin x hw hbw hN_pos hN2
      hx hcinv hinv _ hDS
  obtain ⟨houtF, houtD, houtC, houtG, houtV⟩ := hout
  -- The relabel transport: applyNat (inPlaceMulDataAt) f (σ p)
  --   = applyNat (windowedModNMulInPlace) (f∘σ) p.
  have htrans : ∀ p, Gate.applyNat (inPlaceMulDataAt w bits N numWin c cinv) f (σ p)
      = Gate.applyNat (windowedModNMulInPlace w bits c cinv N numWin)
          (fun q => f (σ q)) p := by
    intro p
    show Gate.applyNat (relabelGate σ (windowedModNMulInPlace w bits c cinv N numWin))
        f (σ p) = _
    exact applyNat_relabelGate σ hσinj
      (windowedModNMulInPlace w bits c cinv N numWin) f p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- DATA band → `(c·x)%N` big-endian.
    intro j hj
    -- data wire `j` is the σ-image of value wire `yBase + (bits-1-j)`.
    have hidx : bits - 1 - j < bits := by omega
    have heq : j = σ (yBase w bits + (bits - 1 - j)) := by
      rw [hσdef, layoutMul_val w bits (bits - 1 - j) hidx]; omega
    conv_lhs => rw [heq]
    rw [htrans (yBase w bits + (bits - 1 - j))]
    -- read the value wire from `houtF` (frame conjunct of the native output).
    have hpb : ¬ inBlock (1 + 2 * w) (2 * bits + 1) (yBase w bits + (bits - 1 - j)) := by
      unfold inBlock yBase; omega
    have hpf : yBase w bits + (bits - 1 - j) ≠ 1 + 2 * w + (2 * bits + 1) + numWin * w := by
      unfold yBase; rw [hbw]; omega
    rw [houtF _ hpb hpf]
    have hpos : yBase w bits + (bits - 1 - j)
        = 1 + 2 * w + (2 * bits + 1) + (bits - 1 - j) := rfl
    rw [hpos, mulInputOf_cuc_y_bit_local w bits numWin ((c * x) % N) (bits - 1 - j)
          (by rw [hbw]; omega)]
    -- `(c·x%N).testBit (bits-1-j) = encodeDataZeroAnc bits anc ((c·x)%N) j`.
    rw [encodeDataZeroAnc_data hcxbits hj, nat_to_funbool_eq_testBit]
  · -- control image still set.
    have heq : scratchBase bits = σ ulookup_ctrl_idx := by
      rw [hσdef, layoutMul_ctrl]
    rw [heq, htrans ulookup_ctrl_idx]
    -- the native control is `mulInputOf … ctrl = true` (frame conjunct).
    have hpb : ¬ inBlock (1 + 2 * w) (2 * bits + 1) ulookup_ctrl_idx := by
      unfold inBlock ulookup_ctrl_idx; omega
    have hpf : (ulookup_ctrl_idx : Nat) ≠ 1 + 2 * w + (2 * bits + 1) + numWin * w := by
      unfold ulookup_ctrl_idx; omega
    rw [houtF _ hpb hpf, mulInputOf_ctrl]
  · -- every other non-value scratch image false.
    intro p hp0 hpv
    have heq : scratchBase bits + p = σ p := by
      rw [hσdef, layoutMul_nonval w bits p hpv]
    rw [heq, htrans p]
    -- the native wire `p` (control excluded) is clean.  Case on its role.
    by_cases hpb : inBlock (1 + 2 * w) (2 * bits + 1) p
    · -- inside the Cuccaro block: carry / augend / addend (all clean).
      obtain ⟨hlo, hhi⟩ := hpb
      by_cases hpcarry : p = 1 + 2 * w
      · subst hpcarry; exact houtC
      · -- `p = 1+2w+r`, `1 ≤ r ≤ 2bits`: odd→augend, even→addend.
        obtain ⟨r, hr1, hr2, rfl⟩ : ∃ r, 1 ≤ r ∧ r ≤ 2 * bits ∧ p = 1 + 2 * w + r :=
          ⟨p - (1 + 2 * w), by omega, by omega, by omega⟩
        rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
        · have hkr : k - 1 < bits := by omega
          have hpe : 1 + 2 * w + r = 1 + 2 * w + 2 * (k - 1) + 2 := by omega
          rw [hpe]; exact houtD (k - 1) hkr
        · have hkr : k < bits := by omega
          have hpe : 1 + 2 * w + r = 1 + 2 * w + 2 * k + 1 := by omega
          rw [hpe]; exact houtV k hkr
    · -- off-block, off-control, off-value: flag, or out-of-range — `mulInputOf = false`.
      by_cases hpflag : p = 1 + 2 * w + (2 * bits + 1) + numWin * w
      · subst hpflag; exact houtG
      · rw [houtF p hpb hpflag]
        -- `mulInputOf … p = false` (low or high, since p ≠ ctrl, p not a value wire).
        by_cases hplow : p < 1 + 2 * w + (2 * bits + 1)
        · exact mulInputOf_low cuccaroAdder w bits numWin ((c * x) % N) p hp0 (by
            show p < 1 + 2 * w + cuccaroAdder.span bits
            show p < 1 + 2 * w + (2 * bits + 1); exact hplow)
        · have hphigh : 1 + 2 * w + (2 * bits + 1) + bits ≤ p := by
            unfold isValWire yBase at hpv; omega
          have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
          rw [mulInputOf_eq_encodeReg cuccaroAdder w bits numWin ((c * x) % N) p hp0,
              hspan, encodeReg_high _ _ _ _ (by rw [hbw]; omega)]
  · -- FRAME: positions off the data band and off the scratch region are not σ-images.
    intro q hqdata hqscr
    apply applyNat_relabelGate_frame σ
      (windowedModNMulInPlace w bits c cinv N numWin) f q
    intro p hp
    -- `hp : σ p = q`; σ p is either a value image (< bits, a data wire) or scratch.
    rw [hσdef] at hp
    have himg := layoutMul_image_range w bits p
    rcases himg with hlt | hge
    · -- layoutMul p < bits ⟹ `q = layoutMul p` is a data wire, contra `hqdata`.
      exact hqdata ⟨q, by rw [← hp]; exact hlt, rfl⟩
    · -- layoutMul p ≥ bits ⟹ `q = scratchBase + (q - bits)`, contra `hqscr`.
      refine hqscr ⟨q - scratchBase bits, ?_⟩
      unfold scratchBase; omega
  · exact inPlaceMulDataAt_wellTyped w bits N numWin c cinv hw hbw

end FormalRV.Audit.GidneyEkera2021.InPlaceMulDataAt
