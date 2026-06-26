/-
  Audit · Gidney–Ekerå 2021 · THE REDUCTION-BAND DIVMOD-BY-N GATE `divModNAt`
  ════════════════════════════════════════════════════════════════════════════
  GOAL.  A verified reversible mod-N REDUCTION gate placed at `modExpAt`'s
  ACCUMULATOR band, for the GE2021 reduction read-out.

  CONTEXT.  The count-optimal `multiplyAddAt` leaves the UN-reduced product
  `v = a^(2^i)·x < 2^bits` (no-wrap) in the interleaved accumulator band at
  positions `q_start + 2·i + 1` (`i < bits`), reading
  `decodeReg (fun i => q_start + 2·i + 1) bits`
  (= `cuccaro_target_val bits q_start`, via
  `ModExpAtFullOutput.decodeReg_eq_cuccaro_target_val`).  We need a gate that
  reduces `v ↦ v % N` THERE, leaving the quotient `⌊v/N⌋` in a FRESH scratch
  region disjoint from everything else.

  STRATEGY.  The verified divider `E2RunwayDivider.divModN` already does the long
  division, but in its NATIVE layout (`q_start = 0`):
    • carry-in        : wire `0`                          (transient)
    • DATA/REMAINDER  : wire `2·i + 1`   (`i < bits`)      (input v, output v%N)
    • READ band       : wire `2·i + 2`   (`i < bits`)      (transient workspace)
    • FLAG            : wire `flagW bits = 2·bits + 1`     (transient)
    • QUOTIENT band   : wire `qBase bits + k = 2·bits+2+k` (`k < cm`)  (output ⌊v/N⌋)
  Total native dim `dimDiv bits cm = 2·bits + 2 + cm`.

  We CONJUGATE `divModN` by a layout permutation `σ = layoutAt` (an index relabel /
  swap cascade, via `BQAlgo.relabelGate` + the transport `applyNat_relabelGate`)
  that:
    • sends each native DATA wire `2·i + 1` to the accumulator band position
      `q_start + (2·i + 1)` (= `q_start + 2·i + 1`, matching `multiplyAddAt`);
    • sends EVERY OTHER native wire `p` (carry / read / flag / quotient) up to
      `S + p`, where the fresh scratch base
        `S := q_start + 2·bits + 1 + numWin·(2·w)`
      sits ABOVE the whole stacked address/anc region.
  Since data images live in `[q_start, q_start + 2·bits + 1) ⊆ [0, S)` and the
  non-data images live in `[S, …)`, the two image families are disjoint, so `σ`
  is injective.  The quotient/flag/read/carry scratch then lands at
  `S + {0, 2·i+2, 2·bits+1, 2·bits+2+k}`, all `≥ S`, DISJOINT from:
    (a) `[0, bits)`                                (encodeDataZeroAnc band),
    (b) `[q_start, q_start + 2·bits + 1)`          (accumulator block),
    (c) `[q_start + 2·bits + 1, S)`                (stacked address/anc region),
  exactly as the brief requires.

  TOTAL DIMENSION (chosen freely — the Shor bound is anc-indifferent):
    `dimDivAt := S + dimDiv bits cm
              = q_start + 2·bits+1 + numWin·(2·w) + (2·bits + 2 + cm)`.

  DELIVERABLES.
    • `divModNAt`            — the relabeled divider gate.
    • `divModNAt_decode`     — on `f` with the accumulator band decoding to
        `v = z + j·N` and the fresh scratch clean: after the gate the accumulator
        band decodes to `v % N = z`, the quotient band to `⌊v/N⌋ = j`, the working
        scratch is transient-clean, and `[0, q_start)` (incl. `[0, bits)`) and the
        stacked address/anc region `[q_start+2·bits+1, S)` are UNTOUCHED (frame).
    • `divModNAt_wellTyped`  — `Gate.WellTyped dimDivAt divModNAt`.
    • `divModNAt_tcount`     — the honest Toffoli count (= `tcount (divModN …)`),
        for the count decomposition.

  Kernel-clean: no `sorry`, no `native_decide`; axioms ⊆
  `{propext, Classical.choice, Quot.sound}`.  ADDITIVE.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider
import FormalRV.Arithmetic.Adder.ContiguousTransport
import FormalRV.Audit.GidneyEkera2021.ModExpAtFullOutput

namespace FormalRV.Audit.GidneyEkera2021.DivModNAt

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider
open FormalRV.Audit.GidneyEkera2021.ModExpAtFullOutput (decodeReg_eq_cuccaro_target_val)

/-! ## §0. The layout permutation `layoutAt`. -/

/-- Fresh scratch base: the first position at-or-above the whole stacked region
    `[q_start + 2·bits + 1, q_start + 2·bits + 1 + numWin·(2·w))`. -/
def scratchBase (w bits numWin q_start : Nat) : Nat :=
  q_start + 2 * bits + 1 + numWin * (2 * w)

/-- The data-wire predicate of `divModN`'s native layout: odd index below
    `2·bits + 1`, i.e. one of the target-register wires `2·i + 1` (`i < bits`). -/
def isDataWire (bits p : Nat) : Prop := p % 2 = 1 ∧ p < 2 * bits + 1

instance (bits p : Nat) : Decidable (isDataWire bits p) := by
  unfold isDataWire; infer_instance

/-- The layout permutation.  Native DATA wires `2·i + 1` go to the accumulator
    band `q_start + (2·i + 1)`; every other native wire `p` goes up to `S + p`
    (fresh scratch above the stacked region). -/
def layoutAt (w bits numWin q_start : Nat) : Nat → Nat := fun p =>
  if isDataWire bits p then q_start + p
  else scratchBase w bits numWin q_start + p

/-! ## §1. Injectivity of `layoutAt`. -/

/-- `layoutAt` is injective whenever the fresh scratch base is at or above the
    accumulator block (so data images `< S ≤` non-data images). -/
theorem layoutAt_injective (w bits numWin q_start : Nat)
    (hS : q_start + 2 * bits + 1 ≤ scratchBase w bits numWin q_start) :
    Function.Injective (layoutAt w bits numWin q_start) := by
  intro a b hab
  unfold layoutAt at hab
  by_cases ha : isDataWire bits a <;> by_cases hb : isDataWire bits b
  · rw [if_pos ha, if_pos hb] at hab; omega
  · rw [if_pos ha, if_neg hb] at hab
    obtain ⟨_, ha2⟩ := ha; omega
  · rw [if_neg ha, if_pos hb] at hab
    obtain ⟨_, hb2⟩ := hb; omega
  · rw [if_neg ha, if_neg hb] at hab; omega

/-! ## §2. Image equations for the named wire families. -/

/-- Data wire `2·i + 1` (`i < bits`) maps to the accumulator band `q_start+2·i+1`. -/
theorem layoutAt_data (w bits numWin q_start i : Nat) (hi : i < bits) :
    layoutAt w bits numWin q_start (2 * i + 1) = q_start + 2 * i + 1 := by
  unfold layoutAt isDataWire
  have h : (2 * i + 1) % 2 = 1 ∧ 2 * i + 1 < 2 * bits + 1 := by omega
  rw [if_pos h]; omega

/-- Carry-in wire `0` maps to `S + 0 = S`. -/
theorem layoutAt_cin (w bits numWin q_start : Nat) :
    layoutAt w bits numWin q_start 0 = scratchBase w bits numWin q_start := by
  unfold layoutAt isDataWire
  rw [if_neg (by omega), Nat.add_zero]

/-- Read wire `2·i + 2` (`i < bits`) maps to `S + (2·i + 2)`. -/
theorem layoutAt_read (w bits numWin q_start i : Nat) :
    layoutAt w bits numWin q_start (2 * i + 2)
      = scratchBase w bits numWin q_start + (2 * i + 2) := by
  unfold layoutAt isDataWire
  rw [if_neg (by omega)]

/-- Flag wire `flagW bits = 2·bits + 1` maps to `S + flagW bits`. -/
theorem layoutAt_flag (w bits numWin q_start : Nat) :
    layoutAt w bits numWin q_start (flagW bits)
      = scratchBase w bits numWin q_start + flagW bits := by
  unfold layoutAt isDataWire flagW
  rw [if_neg (by omega)]

/-- Quotient wire `qBase bits + k` maps to `S + (qBase bits + k)`. -/
theorem layoutAt_qbit (w bits numWin q_start k : Nat) :
    layoutAt w bits numWin q_start (qBase bits + k)
      = scratchBase w bits numWin q_start + (qBase bits + k) := by
  unfold layoutAt isDataWire qBase
  rw [if_neg (by omega)]

/-- **Image containment.**  Every `σ`-image lies in
    `[q_start, q_start + 2·bits + 1) ∪ [S, ∞)`: data images are
    `q_start + p` with `p < 2·bits+1`; non-data images are `S + p ≥ S`. -/
theorem layoutAt_image_range (w bits numWin q_start p : Nat) :
    (q_start ≤ layoutAt w bits numWin q_start p
       ∧ layoutAt w bits numWin q_start p < q_start + 2 * bits + 1)
    ∨ scratchBase w bits numWin q_start ≤ layoutAt w bits numWin q_start p := by
  unfold layoutAt
  by_cases h : isDataWire bits p
  · left; rw [if_pos h]; obtain ⟨_, h2⟩ := h; omega
  · right; rw [if_neg h]; unfold scratchBase; omega

/-! ## §3. The gate, its dimension, well-typedness and T-count. -/

/-- Total register dimension for the placed divider (chosen freely; the Shor
    bound is anc-indifferent).  `S + dimDiv bits cm`. -/
def dimDivAt (w bits numWin cm q_start : Nat) : Nat :=
  scratchBase w bits numWin q_start + dimDiv bits cm

/-- **The placed divmod gate.**  `divModN bits cm N` conjugated by the layout
    permutation `layoutAt`. -/
def divModNAt (w bits numWin cm N q_start : Nat) : Gate :=
  relabelGate (layoutAt w bits numWin q_start) (divModN bits cm N)

/-- `tcount` is invariant under relabel (relabel changes only wire indices). -/
theorem tcount_relabelGate (σ : Nat → Nat) (g : Gate) :
    Gate.tcount (relabelGate σ g) = Gate.tcount g := by
  induction g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ ih₁ ih₂ => simp only [relabelGate, Gate.tcount, ih₁, ih₂]

/-- **Honest Toffoli count.**  `divModNAt` has exactly the same T-count as the
    native divider `divModN bits cm N` (relabel is wire-only, so identical
    Toffoli structure — the count decomposition reuses `divModN`'s count). -/
theorem divModNAt_tcount (w bits numWin cm N q_start : Nat) :
    Gate.tcount (divModNAt w bits numWin cm N q_start)
      = Gate.tcount (divModN bits cm N) := by
  unfold divModNAt; exact tcount_relabelGate _ _

/-- **Relabel preserves well-typedness (source-dimension form).**  If `g` is
    WellTyped at the SOURCE dimension `d0`, `σ` is injective, and `σ` maps the
    source wires `[0, d0)` into the TARGET `[0, dim)`, then `relabelGate σ g` is
    WellTyped at `dim`.  Unlike `BQAlgo.wellTyped_relabelGate` (which needs `σ`
    to map `[0,dim)` into itself), this keys the `hmap` requirement to the wires
    `g` actually contains (all `< d0`), so a relabel that scatters into a much
    larger `dim` is fine. -/
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

/-- **Well-typed.**  `divModNAt` is well-typed at `dimDivAt`: `divModN` is
    well-typed at the SOURCE dimension `dimDiv bits cm`, and `layoutAt` maps every
    source wire `< dimDiv bits cm` into `[0, dimDivAt)` (data wires below `S`,
    non-data wires `< S + dimDiv`). -/
theorem divModNAt_wellTyped (w bits numWin cm N q_start : Nat)
    (hbits : 1 ≤ bits) (hcm : cm ≤ bits)
    (hS : q_start + 2 * bits + 1 ≤ scratchBase w bits numWin q_start) :
    Gate.WellTyped (dimDivAt w bits numWin cm q_start)
      (divModNAt w bits numWin cm N q_start) := by
  unfold divModNAt dimDivAt
  refine wellTyped_relabelGate_src (layoutAt w bits numWin q_start)
    (layoutAt_injective w bits numWin q_start hS)
    (dimDiv bits cm)
    (scratchBase w bits numWin q_start + dimDiv bits cm)
    (fun x hx => ?_)
    (divModN bits cm N)
    (divModN_wellTyped bits cm N hbits hcm)
  -- σ maps each source wire x < dimDiv into [0, S + dimDiv).
  unfold layoutAt
  by_cases h : isDataWire bits x
  · rw [if_pos h]
    obtain ⟨_, h2⟩ := h
    unfold scratchBase dimDiv at hx ⊢; omega
  · rw [if_neg h]; omega

/-! ## §3b. A relabel frame lemma: positions off `σ`'s image are untouched. -/

/-- **Relabel frame.**  If `p` is not the `σ`-image of any wire, then the relabeled
    gate fixes `p`.  (`relabelGate σ g` only ever writes to `σ`-images; the carried
    quantifier `∀ q, σ q ≠ p` survives every constructor.)  Proved by structural
    induction on `g`. -/
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

/-! ## §4. The DECODE specification.

  The proof routes everything through `E2RunwayDivider.divModN_decode_gen`, which
  is stated on the native layout via the `DivState` predicate (constraining ONLY
  the named native wires).  We feed it the pull-back state `g := f ∘ σ`; each
  `DivState` field is exactly one of our placed-wire preconditions transported by
  the image equations of §2.  The relabel transport `applyNat_relabelGate` then
  pushes the native output back to the placed wires, and the relabel frame
  (§3b + image containment §2) handles the untouched regions. -/

/-- The pull-back state `f ∘ σ` satisfies `DivState bits cm N v` whenever the
    accumulator band of `f` holds `v` and the fresh scratch is clean.  This is the
    bridge into `divModN_decode_gen` (no full-function `encDiv` equality needed —
    `DivState` constrains only the divider's wires). -/
theorem pullback_DivState
    (w bits numWin cm N q_start v : Nat) (f : Nat → Bool)
    (hbudget : N * 2 ^ cm ≤ 2 ^ bits) (hcm : cm ≤ bits) (hN : 0 < N)
    (hv : v < N * 2 ^ cm)
    (h_data : ∀ i, i < bits → f (q_start + 2 * i + 1) = v.testBit i)
    (h_cin : f (scratchBase w bits numWin q_start) = false)
    (h_read : ∀ i, i < bits →
        f (scratchBase w bits numWin q_start + (2 * i + 2)) = false)
    (h_flag : f (scratchBase w bits numWin q_start + flagW bits) = false)
    (h_quot : ∀ k, k < cm →
        f (scratchBase w bits numWin q_start + (qBase bits + k)) = false) :
    DivState bits cm N v (fun p => f (layoutAt w bits numWin q_start p)) := by
  refine
    { hr := hv, hbudget := hbudget, hcm := hcm, hN := hN
      h_cin := ?_, h_flag := ?_, h_tgt := ?_, h_read := ?_, h_quot := ?_ }
  · show f (layoutAt w bits numWin q_start 0) = false
    rw [layoutAt_cin]; exact h_cin
  · show f (layoutAt w bits numWin q_start (flagW bits)) = false
    rw [layoutAt_flag]; exact h_flag
  · intro i hi
    show f (layoutAt w bits numWin q_start (0 + 2 * i + 1)) = v.testBit i
    have h2 : (0 : Nat) + 2 * i + 1 = 2 * i + 1 := by omega
    rw [h2, layoutAt_data w bits numWin q_start i hi]
    exact h_data i hi
  · intro i hi
    show f (layoutAt w bits numWin q_start (0 + 2 * i + 2)) = false
    have h2 : (0 : Nat) + 2 * i + 2 = 2 * i + 2 := by omega
    rw [h2, layoutAt_read w bits numWin q_start i]; exact h_read i hi
  · intro k hk
    show f (layoutAt w bits numWin q_start (qBase bits + k)) = false
    rw [layoutAt_qbit w bits numWin q_start k]; exact h_quot k hk

/-- **★ `divModNAt_decode` — the placed reversible DIVMOD-by-N decode. ★**
    On a state `f` whose accumulator band `q_start + 2·i + 1` decodes to
    `v = z + j·N` (`z < N`, `j < 2^cm`, budget `2^cm·N ≤ 2^bits`) and whose FRESH
    scratch (carry `S`, read `S + 2·i+2`, flag `S + flagW`, quotient `S + qBase+k`)
    is clean, running `divModNAt`:

      • the ACCUMULATOR band decodes to `v % N = z` (remainder in place);
      • the QUOTIENT band wire `S + qBase bits + k` holds bit `k` of `v / N = j`;
      • the WORKING SCRATCH (carry / read band / flag) returns clean
        (transient-clean);
      • positions in `[0, q_start)` (incl. the `encodeDataZeroAnc` band `[0, bits)`)
        and the stacked address/anc region `[q_start + 2·bits + 1, S)` are UNTOUCHED.

    The total dimension is `dimDivAt = S + dimDiv bits cm` (chosen freely; the Shor
    bound is anc-indifferent). -/
theorem divModNAt_decode
    (w bits numWin cm N q_start z j : Nat) (f : Nat → Bool)
    (hbits : 1 ≤ bits) (hN : 0 < N) (hcm : cm ≤ bits)
    (hbudget : 2 ^ cm * N ≤ 2 ^ bits)
    (hz : z < N) (hj : j < 2 ^ cm)
    (hS : q_start + 2 * bits + 1 ≤ scratchBase w bits numWin q_start)
    (h_data : ∀ i, i < bits → f (q_start + 2 * i + 1) = (z + j * N).testBit i)
    (h_cin : f (scratchBase w bits numWin q_start) = false)
    (h_read : ∀ i, i < bits →
        f (scratchBase w bits numWin q_start + (2 * i + 2)) = false)
    (h_flag : f (scratchBase w bits numWin q_start + flagW bits) = false)
    (h_quot : ∀ k, k < cm →
        f (scratchBase w bits numWin q_start + (qBase bits + k)) = false) :
    -- REMAINDER in place: accumulator band decodes to v % N = z.
    decodeReg (fun i => q_start + 2 * i + 1) bits
        (Gate.applyNat (divModNAt w bits numWin cm N q_start) f) = z
    -- QUOTIENT band: bit k of v / N = j, on the fresh quotient wires.
    ∧ (∀ k, k < cm →
        Gate.applyNat (divModNAt w bits numWin cm N q_start) f
          (scratchBase w bits numWin q_start + (qBase bits + k)) = j.testBit k)
    -- WORKING SCRATCH transient-clean: carry, read band, flag restored to false.
    ∧ Gate.applyNat (divModNAt w bits numWin cm N q_start) f
        (scratchBase w bits numWin q_start) = false
    ∧ (∀ i, i < bits →
        Gate.applyNat (divModNAt w bits numWin cm N q_start) f
          (scratchBase w bits numWin q_start + (2 * i + 2)) = false)
    ∧ Gate.applyNat (divModNAt w bits numWin cm N q_start) f
        (scratchBase w bits numWin q_start + flagW bits) = false
    -- FRAME: everything below q_start (incl. [0,bits)) and the stacked
    -- address/anc region [q_start+2·bits+1, S) is untouched.
    ∧ (∀ p, (p < q_start ∨ (q_start + 2 * bits + 1 ≤ p ∧
              p < scratchBase w bits numWin q_start)) →
        Gate.applyNat (divModNAt w bits numWin cm N q_start) f p = f p)
    -- WELL-TYPED.
    ∧ Gate.WellTyped (dimDivAt w bits numWin cm q_start)
        (divModNAt w bits numWin cm N q_start) := by
  set σ := layoutAt w bits numWin q_start with hσdef
  set S := scratchBase w bits numWin q_start with hSdef
  set v := z + j * N with hv
  have hσinj : Function.Injective σ := layoutAt_injective w bits numWin q_start hS
  have hbud' : N * 2 ^ cm ≤ 2 ^ bits := by rw [Nat.mul_comm]; exact hbudget
  have hv_lt : v < N * 2 ^ cm := by
    rw [hv]
    calc z + j * N < N + j * N := by omega
      _ = (j + 1) * N := by ring
      _ ≤ 2 ^ cm * N := Nat.mul_le_mul_right _ (by omega)
      _ = N * 2 ^ cm := by ring
  have hDS : DivState bits cm N v (fun p => f (σ p)) :=
    pullback_DivState w bits numWin cm N q_start v f hbud' hcm hN hv_lt
      h_data h_cin h_read h_flag h_quot
  obtain ⟨hg_tgt, hg_quot, hg_cin, hg_flag, hg_read⟩ :=
    divModN_decode_gen cm bits N v (fun p => f (σ p)) hDS
  obtain ⟨hjdiv, hzmod⟩ := divModN_arith N z j hN hz
  rw [← hv] at hjdiv hzmod
  -- The relabel transport: applyNat divModNAt f (σ p) = applyNat (divModN) (f∘σ) p.
  have htrans : ∀ p, Gate.applyNat (divModNAt w bits numWin cm N q_start) f (σ p)
      = Gate.applyNat (divModN bits cm N) (fun p => f (σ p)) p := by
    intro p
    show Gate.applyNat (relabelGate σ (divModN bits cm N)) f (σ p) = _
    exact applyNat_relabelGate σ hσinj (divModN bits cm N) f p
  have hz_bits : z < 2 ^ bits := by
    have hNle : N ≤ 2 ^ bits :=
      le_trans (Nat.le_mul_of_pos_right N (by positivity : 0 < 2 ^ cm)) hbud'
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- REMAINDER band → v % N = z.
    rw [decodeReg_eq_cuccaro_target_val]
    rw [cuccaro_target_val_eq_sum_when_bits_match bits q_start (v % N) _ (fun i hi => ?_)]
    · rw [hzmod]; exact Nat.mod_eq_of_lt hz_bits
    · have heq : q_start + 2 * i + 1 = σ (2 * i + 1) := by
        rw [hσdef, layoutAt_data w bits numWin q_start i hi]
      rw [heq, htrans (2 * i + 1)]
      have h2 : (2 : Nat) * i + 1 = 0 + 2 * i + 1 := by omega
      rw [h2]; exact hg_tgt i hi
  · -- QUOTIENT band → bit k of v/N = j.
    intro k hk
    have heq : S + (qBase bits + k) = σ (qBase bits + k) := by
      rw [hσdef, layoutAt_qbit w bits numWin q_start k]
    rw [heq, htrans (qBase bits + k), hg_quot k hk, hjdiv]
  · -- carry scratch clean.
    have heq : S = σ 0 := by rw [hσdef, layoutAt_cin]
    rw [heq, htrans 0]; exact hg_cin
  · -- read band clean.
    intro i hi
    have heq : S + (2 * i + 2) = σ (2 * i + 2) := by
      rw [hσdef, layoutAt_read w bits numWin q_start i]
    rw [heq, htrans (2 * i + 2)]
    have h2 : (2 : Nat) * i + 2 = 0 + 2 * i + 2 := by omega
    rw [h2]; exact hg_read i hi
  · -- flag clean.
    have heq : S + flagW bits = σ (flagW bits) := by
      rw [hσdef, layoutAt_flag w bits numWin q_start]
    rw [heq, htrans (flagW bits)]; exact hg_flag
  · -- FRAME: positions below q_start and in the stacked region are not σ-images.
    intro p hp
    apply applyNat_relabelGate_frame σ (divModN bits cm N) f p
    intro q hq
    -- σ q lies in [q_start, q_start+2bits+1) ∪ [S, ∞); p lies below q_start or in
    -- [q_start+2bits+1, S); contradiction.
    have himg := layoutAt_image_range w bits numWin q_start q
    rw [← hσdef] at himg
    rcases himg with ⟨hlo, hhi⟩ | hge <;> rcases hp with hp1 | ⟨hp2a, hp2b⟩ <;> omega
  · exact divModNAt_wellTyped w bits numWin cm N q_start hbits hcm hS

end FormalRV.Audit.GidneyEkera2021.DivModNAt
