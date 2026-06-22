/-
  FormalRV.Arithmetic.Adder.ContiguousTransport
  ──────────────────────────────────────────────
  TRANSPORT INVESTIGATION (per Shor/GidneyInPlace/GIDNEY_INPLACE_DESIGN.md §5).

  QUESTION: can the verified INTERLEAVED Cuccaro adder correctness be transported
  by a fixed qubit PERMUTATION into a CONTIGUOUS-accumulator layout
    - augend / accumulator : q + i   (contiguous)
    - addend / control     : separate contiguous block
  reusing the verified ripple-carry arithmetic rather than re-proving it?

  ANSWER: YES.  `Gate.applyNat` is built from point `update`s, so a generic
  index-RELABEL `relabelGate σ` (generalizing `GateShift.shiftBy`, which is the
  special case `σ = (· + s)`) transports the Boolean semantics for any INJECTIVE σ:

      applyNat (relabelGate σ g) f (σ p)  =  applyNat g (f ∘ σ) p.

  De-interleaving is exactly such an injective relabel.  We
    §1  define the generic relabel + prove the transport;
    §2  define the de-interleaving map, prove its value equations, that it is
        injective, and that the augend / addend image blocks do not overlap;
    §3  DERIVE a transported `sumCorrect` for the contiguous layout directly from
        `cuccaroAdder.sumCorrect` — no new ripple-carry proof.

  SCOPE: this is the upstream dependency named in the design doc.  It does NOT
  build the two-register product-add wrapper and does NOT touch the Shor scaffold.
-/
import FormalRV.Arithmetic.Adder.Cuccaro
import FormalRV.Arithmetic.Adder.TwoBaseBoundedAdder

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## §1. Generic index-relabel transport (generalizes `GateShift.shiftBy`). -/

/-- Relabel every qubit index of a gate through `σ`.
    `GateShift.shiftBy s = relabelGate (· + s)`. -/
def relabelGate (σ : Nat → Nat) : Gate → Gate
  | Gate.I          => Gate.I
  | Gate.X q        => Gate.X (σ q)
  | Gate.CX c t     => Gate.CX (σ c) (σ t)
  | Gate.CCX a b c  => Gate.CCX (σ a) (σ b) (σ c)
  | Gate.seq g₁ g₂  => Gate.seq (relabelGate σ g₁) (relabelGate σ g₂)

/-- **The relabel transport.**  For an INJECTIVE `σ`, the relabeled gate acts on
    the image positions exactly as the original gate acts on the state pulled
    back along `σ`.  Proved by the same structural induction as
    `GateShift.applyNat_shiftBy`. -/
theorem applyNat_relabelGate (σ : Nat → Nat) (hσ : Function.Injective σ) (g : Gate) :
    ∀ (f : Nat → Bool) (p : Nat),
      Gate.applyNat (relabelGate σ g) f (σ p)
        = Gate.applyNat g (fun q => f (σ q)) p := by
  induction g with
  | I => intro f p; rfl
  | X q =>
    intro f p
    show update f (σ q) (!f (σ q)) (σ p)
        = update (fun q => f (σ q)) q (!f (σ q)) p
    unfold update
    by_cases h : p = q
    · subst h; simp
    · rw [if_neg (fun hc => h (hσ hc)), if_neg h]
  | CX c t =>
    intro f p
    show update f (σ t) (xor (f (σ t)) (f (σ c))) (σ p)
        = update (fun q => f (σ q)) t (xor (f (σ t)) (f (σ c))) p
    unfold update
    by_cases h : p = t
    · subst h; simp
    · rw [if_neg (fun hc => h (hσ hc)), if_neg h]
  | CCX a b c =>
    intro f p
    show update f (σ c) (xor (f (σ c)) (f (σ a) && f (σ b))) (σ p)
        = update (fun q => f (σ q)) c (xor (f (σ c)) (f (σ a) && f (σ b))) p
    unfold update
    by_cases h : p = c
    · subst h; simp
    · rw [if_neg (fun hc => h (hσ hc)), if_neg h]
  | seq g₁ g₂ ih₁ ih₂ =>
    intro f p
    show Gate.applyNat (relabelGate σ g₂) (Gate.applyNat (relabelGate σ g₁) f) (σ p)
        = Gate.applyNat g₂ (Gate.applyNat g₁ (fun q => f (σ q))) p
    rw [ih₂ (Gate.applyNat (relabelGate σ g₁) f) p]
    have hstep : (fun q => Gate.applyNat (relabelGate σ g₁) f (σ q))
        = Gate.applyNat g₁ (fun q => f (σ q)) := by
      funext q; exact ih₁ f q
    rw [hstep]

/-- `decodeReg` commutes with pulling the index function through `σ`:
    reading at `σ ∘ idx` over a state `g` is reading at `idx` over `g ∘ σ`. -/
theorem decodeReg_comp_index (σ idx : Nat → Nat) (n : Nat) (g : Nat → Bool) :
    decodeReg (fun i => σ (idx i)) n g = decodeReg idx n (fun p => g (σ p)) := rfl

/-- `decodeReg` depends only on the read-out VALUES: two (index, state) pairs that
    yield the same bit at every position `i < n` decode to the same number.  This
    is the join of `decodeReg_ext` (state) and an index change. -/
theorem decodeReg_congr (idx₁ idx₂ : Nat → Nat) (n : Nat) (H₁ H₂ : Nat → Bool)
    (h : ∀ i, i < n → H₁ (idx₁ i) = H₂ (idx₂ i)) :
    decodeReg idx₁ n H₁ = decodeReg idx₂ n H₂ := by
  unfold decodeReg
  have key : ∀ (m : Nat) (init : Nat), m ≤ n →
      (List.range m).foldl (fun acc i => acc + if H₁ (idx₁ i) then 2 ^ i else 0) init
        = (List.range m).foldl (fun acc i => acc + if H₂ (idx₂ i) then 2 ^ i else 0) init := by
    intro m
    induction m with
    | zero => intro init _; simp
    | succ k ih =>
        intro init hk
        rw [List.range_succ, List.foldl_append, List.foldl_append, ih init (by omega)]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [h k (by omega)]
  exact key n 0 (le_refl n)

/-! ## §2. The de-interleaving permutation. -/

/-- De-interleaving map `σ` for width `n`, base `q`, on the block `[q, q + 2n + 1)`:
      carry-in `q`        ↦ `q + 2n`            (top of the block);
      augend bit `i`  (`q + 2i + 1`) ↦ `q + i`        (contiguous accumulator);
      addend bit `i`  (`q + 2i + 2`) ↦ `q + n + i`    (separate contiguous block).
    Identity outside the block. -/
def deinterleave (n q : Nat) : Nat → Nat := fun p =>
  if p ≤ q then (if p = q then q + 2 * n else p)
  else if p < q + 2 * n + 1 then
    (if (p - q) % 2 = 1 then q + (p - q) / 2 else q + n + (p - q) / 2 - 1)
  else p

/-- Inverse map `ρ` (contiguous → interleaved), division-free; serves as a left
    inverse of `deinterleave` to witness injectivity. -/
def reinterleave (n q : Nat) : Nat → Nat := fun r =>
  if r < q then r
  else if r = q + 2 * n then q
  else if r < q + n then q + 2 * (r - q) + 1
  else if r < q + 2 * n then q + 2 * (r - q - n) + 2
  else r

@[simp] theorem deinterleave_carry (n q : Nat) :
    deinterleave n q q = q + 2 * n := by
  unfold deinterleave; simp

theorem deinterleave_augend (n q i : Nat) (hi : i < n) :
    deinterleave n q (q + 2 * i + 1) = q + i := by
  unfold deinterleave
  have h1 : ¬ (q + 2 * i + 1 ≤ q) := by omega
  have h2 : q + 2 * i + 1 < q + 2 * n + 1 := by omega
  have h3 : (q + 2 * i + 1 - q) % 2 = 1 := by omega
  rw [if_neg h1, if_pos h2, if_pos h3]
  omega

theorem deinterleave_addend (n q i : Nat) (hi : i < n) :
    deinterleave n q (q + 2 * i + 2) = q + n + i := by
  unfold deinterleave
  have h1 : ¬ (q + 2 * i + 2 ≤ q) := by omega
  have h2 : q + 2 * i + 2 < q + 2 * n + 1 := by omega
  have h3 : ¬ ((q + 2 * i + 2 - q) % 2 = 1) := by omega
  rw [if_neg h1, if_pos h2, if_neg h3]
  omega

/-- `reinterleave` is a left inverse of `deinterleave`, hence the latter is
    injective (a genuine permutation of `Nat`). -/
theorem reinterleave_leftInverse (n q : Nat) :
    Function.LeftInverse (reinterleave n q) (deinterleave n q) := by
  intro p
  unfold deinterleave reinterleave
  split_ifs <;> omega

theorem deinterleave_injective (n q : Nat) : Function.Injective (deinterleave n q) :=
  (reinterleave_leftInverse n q).injective

/-- **Non-overlap of the image blocks.**  The augend image `[q, q+n)`, the addend
    image `[q+n, q+2n)`, and the carry image `{q+2n}` are pairwise disjoint, so a
    bit string written across the contiguous layout decodes faithfully. -/
theorem deinterleave_blocks_disjoint (n q i j : Nat) (hi : i < n) (hj : j < n) :
    deinterleave n q (q + 2 * i + 1) ≠ deinterleave n q (q + 2 * j + 2)
    ∧ deinterleave n q (q + 2 * i + 1) ≠ deinterleave n q q
    ∧ deinterleave n q (q + 2 * j + 2) ≠ deinterleave n q q := by
  rw [deinterleave_augend n q i hi, deinterleave_addend n q j hj, deinterleave_carry]
  omega

/-! ## §3. The transported `sumCorrect` (contiguous layout). -/

/-- The contiguous-layout circuit: the verified Cuccaro adder, relabeled. -/
def contiguousAdderCircuit (n q : Nat) : Gate :=
  relabelGate (deinterleave n q) (cuccaro_n_bit_adder_full n q)

/-- **HEADLINE (deliverable 4): transported `sumCorrect`.**
    In the CONTIGUOUS layout — accumulator bit `i` at `q + i`, addend bit `i` at
    `q + n + i`, carry-in (clean) at `q + 2n` — the relabeled Cuccaro circuit
    computes `accumulator ← (accumulator + addend) mod 2^n` in place.  Derived
    entirely from `cuccaroAdder.sumCorrect`; NO ripple-carry re-proof. -/
theorem contiguous_sumCorrect (n q : Nat) (f : Nat → Bool)
    (hclean : f (q + 2 * n) = false) :
    decodeReg (fun i => q + i) n (Gate.applyNat (contiguousAdderCircuit n q) f)
      = (decodeReg (fun i => q + i) n f + decodeReg (fun i => q + n + i) n f) % 2 ^ n := by
  have hσ : Function.Injective (deinterleave n q) := deinterleave_injective n q
  -- Pull the relabeled output back along σ: it is the Cuccaro output on `f ∘ σ`.
  have htrans : ∀ p, Gate.applyNat (contiguousAdderCircuit n q) f (deinterleave n q p)
      = Gate.applyNat (cuccaro_n_bit_adder_full n q)
          (fun q' => f (deinterleave n q q')) p := fun p =>
    applyNat_relabelGate (deinterleave n q) hσ (cuccaro_n_bit_adder_full n q) f p
  -- `ancClean` for `f ∘ σ`: the Cuccaro carry-in at `q` is `f (σ q) = f (q+2n) = false`.
  have hcleanσ : cuccaroAdder.ancClean (fun q' => f (deinterleave n q q')) n q := by
    show (fun q' => f (deinterleave n q q')) q = false
    show f (deinterleave n q q) = false
    rw [deinterleave_carry]; exact hclean
  -- The already-verified Cuccaro `sumCorrect`, instantiated on `f ∘ σ`.
  have hsum := cuccaroAdder.sumCorrect n q (fun q' => f (deinterleave n q q')) hcleanσ
  -- Reindex each of the three `decodeReg`s from the contiguous layout to the
  -- interleaved Cuccaro layout (valid for `i < n` via the value equations).
  rw [decodeReg_congr (fun i => q + i) (fun i => q + 2 * i + 1) n
        (Gate.applyNat (contiguousAdderCircuit n q) f)
        (Gate.applyNat (cuccaro_n_bit_adder_full n q) (fun q' => f (deinterleave n q q')))
        (fun i hi => by
          show Gate.applyNat (contiguousAdderCircuit n q) f (q + i) = _
          rw [← deinterleave_augend n q i hi]; exact htrans (q + 2 * i + 1))]
  rw [decodeReg_congr (fun i => q + i) (fun i => q + 2 * i + 1) n f
        (fun q' => f (deinterleave n q q'))
        (fun i hi => by
          show f (q + i) = f (deinterleave n q (q + 2 * i + 1))
          rw [deinterleave_augend n q i hi])]
  rw [decodeReg_congr (fun i => q + n + i) (fun i => q + 2 * i + 2) n f
        (fun q' => f (deinterleave n q q'))
        (fun i hi => by
          show f (q + n + i) = f (deinterleave n q (q + 2 * i + 2))
          rw [deinterleave_addend n q i hi])]
  -- The goal is now exactly `hsum` (cuccaroAdder projections are defeq).
  exact hsum

/-! ## §4. The remaining correctness obligations also transport.

The arithmetic content of EVERY `Adder.correct`/`wellTyped`/`frame` obligation
transports through the same relabel, with no new ripple-carry reasoning.  We
prove them as standalone facts about `contiguousAdderCircuit`. -/

/-- Outside the block `σ` is the identity. -/
theorem deinterleave_outside (n q p : Nat) (h : p < q ∨ q + 2 * n + 1 ≤ p) :
    deinterleave n q p = p := by
  rcases h with h | h <;> · unfold deinterleave; split_ifs <;> omega

/-- `σ` maps the block `[0, q+2n+1)` into itself (used for well-typedness). -/
theorem deinterleave_maps_lt (n q x : Nat) (hx : x < q + 2 * n + 1) :
    deinterleave n q x < q + 2 * n + 1 := by
  unfold deinterleave; split_ifs <;> omega

/-- **Relabel preserves well-typedness** for an injective `σ` that maps `[0,dim)`
    into `[0,dim)` (the `≠` side-conditions survive because `σ` is injective). -/
theorem wellTyped_relabelGate (σ : Nat → Nat) (hσ : Function.Injective σ) (dim : Nat)
    (hmap : ∀ x, x < dim → σ x < dim) :
    ∀ g, Gate.WellTyped dim g → Gate.WellTyped dim (relabelGate σ g)
  | Gate.I,        hg => hg
  | Gate.X q,      hg => hmap q hg
  | Gate.CX c t,   hg => ⟨hmap c hg.1, hmap t hg.2.1, fun h => hg.2.2 (hσ h)⟩
  | Gate.CCX a b c, hg =>
      ⟨hmap a hg.1, hmap b hg.2.1, hmap c hg.2.2.1,
        fun h => hg.2.2.2.1 (hσ h), fun h => hg.2.2.2.2.1 (hσ h),
        fun h => hg.2.2.2.2.2 (hσ h)⟩
  | Gate.seq g₁ g₂, hg =>
      ⟨wellTyped_relabelGate σ hσ dim hmap g₁ hg.1,
        wellTyped_relabelGate σ hσ dim hmap g₂ hg.2⟩

/-- Transported `addendRestored`: the addend register (contiguous block at
    `q+n+i`) is returned bit-for-bit. -/
theorem contiguous_addendRestored (n q : Nat) (f : Nat → Bool) (i : Nat) (hi : i < n) :
    Gate.applyNat (contiguousAdderCircuit n q) f (q + n + i) = f (q + n + i) := by
  have hσ := deinterleave_injective n q
  have htrans := applyNat_relabelGate (deinterleave n q) hσ
    (cuccaro_n_bit_adder_full n q) f (q + 2 * i + 2)
  rw [deinterleave_addend n q i hi] at htrans
  show Gate.applyNat (relabelGate (deinterleave n q) (cuccaro_n_bit_adder_full n q))
      f (q + n + i) = _
  rw [htrans, (cuccaro_n_bit_adder_full_correct n q
        (fun q' => f (deinterleave n q q'))).2.2 i hi]
  show f (deinterleave n q (q + 2 * i + 2)) = f (q + n + i)
  rw [deinterleave_addend n q i hi]

/-- Transported `ancRestored`: the carry-in (at `q+2n`) is returned clean. -/
theorem contiguous_ancRestored (n q : Nat) (f : Nat → Bool) (hclean : f (q + 2 * n) = false) :
    Gate.applyNat (contiguousAdderCircuit n q) f (q + 2 * n) = false := by
  have hσ := deinterleave_injective n q
  have htrans := applyNat_relabelGate (deinterleave n q) hσ
    (cuccaro_n_bit_adder_full n q) f q
  rw [deinterleave_carry] at htrans
  show Gate.applyNat (relabelGate (deinterleave n q) (cuccaro_n_bit_adder_full n q))
      f (q + 2 * n) = false
  rw [htrans, (cuccaro_n_bit_adder_full_correct n q (fun q' => f (deinterleave n q q'))).1]
  show f (deinterleave n q q) = false
  rw [deinterleave_carry]; exact hclean

/-- Transported `frame`: anything outside the block `[q, q+2n+1)` is untouched. -/
theorem contiguous_frame (n q : Nat) (f : Nat → Bool) (p : Nat)
    (hp : ¬ inBlock q (2 * n + 1) p) :
    Gate.applyNat (contiguousAdderCircuit n q) f p = f p := by
  have hσ := deinterleave_injective n q
  have hdisj : p < q ∨ q + 2 * n + 1 ≤ p := by unfold inBlock at hp; omega
  have hout : deinterleave n q p = p := deinterleave_outside n q p hdisj
  have htrans := applyNat_relabelGate (deinterleave n q) hσ
    (cuccaro_n_bit_adder_full n q) f p
  rw [hout] at htrans
  show Gate.applyNat (relabelGate (deinterleave n q) (cuccaro_n_bit_adder_full n q)) f p = f p
  rw [htrans]
  have hframe : Gate.applyNat (cuccaro_n_bit_adder_full n q)
      (fun q' => f (deinterleave n q q')) p = (fun q' => f (deinterleave n q q')) p := by
    rcases hdisj with hlo | hhi
    · exact cuccaro_n_bit_adder_full_frame_below n q _ p hlo
    · exact cuccaro_n_bit_adder_full_frame_above n q _ p (by omega)
  rw [hframe]
  show f (deinterleave n q p) = f p
  rw [hout]

/-- Transported `wellTyped`: the contiguous circuit is well-typed at `q + 2n + 1`. -/
theorem contiguous_wellTyped (n q : Nat) :
    Gate.WellTyped (q + (2 * n + 1)) (contiguousAdderCircuit n q) := by
  unfold contiguousAdderCircuit
  refine wellTyped_relabelGate (deinterleave n q) (deinterleave_injective n q) _
    (fun x hx => ?_) _ (cuccaro_n_bit_adder_full_wellTyped n q (q + (2 * n + 1)) (by omega))
  have := deinterleave_maps_lt n q x (by omega)
  omega

/-! ### Layout bookkeeping that DOES transport, and the one field that does not.

The contiguous layout is: accumulator bit `i` at `q+i`, addend bit `i` at
`q+n+i`, clean carry-in at `q+2n`.  The in-block / injectivity facts hold for the
indices actually used (`i, j < n`): -/

theorem contiguous_augendIdx_inBlock (n q i : Nat) (hi : i < n) :
    inBlock q (2 * n + 1) (q + i) := by unfold inBlock; omega

theorem contiguous_addendIdx_inBlock (n q i : Nat) (hi : i < n) :
    inBlock q (2 * n + 1) (q + n + i) := by unfold inBlock; omega

theorem contiguous_addendIdx_inj (n q i j : Nat) (h : q + n + i = q + n + j) : i = j := by omega

/-- Augend (`q+i`) and addend (`q+n+i`) are disjoint **for every augend index in
    use** (`i < n`, any `j`): `q+i < q+n ≤ q+n+j`.  This is all any consumer needs. -/
theorem contiguous_augend_addend_disjoint (n q i j : Nat) (hi : i < n) :
    q + i ≠ q + n + j := by omega

/-- **The one obligation that does NOT transport unchanged.**  `Adder`'s field
    `augend_addend_disjoint : ∀ q i j, augendIdx q i ≠ addendIdx q j` is quantified
    over ALL `i j`.  Cuccaro/Gidney satisfy it unboundedly via their stride-≥2
    parity (`q+2i+1 ≠ q+2j+2`).  A unit-stride contiguous augend cannot: at
    `i = n + j` we get `q + i = q + n + j`.  Witness that the unbounded statement
    is genuinely FALSE for this layout (so a literal drop-in `Adder` instance is
    impossible without bounding the quantifier — which every call site already
    respects, since they invoke the field only at `i, j < bits`). -/
theorem contiguous_augend_addend_NOT_globally_disjoint (n q : Nat) :
    ¬ (∀ i j, q + i ≠ q + n + j) := by
  intro h; exact h n 0 (by omega)

/-! ## §5. Packaging: the contiguous PACKED layout as a `TwoBaseBoundedAdder`.

The two-base, width-aware interface (`Adder/TwoBaseBoundedAdder.lean`) is what the
contiguous layout fits.  This is the *packed* specialization: accumulator base
`accBase = q`, addend base `addBase = q + n` (so `valid := addBase = accBase + n`).
Every obligation is discharged by a transported lemma from §3–§4; bounded
disjointness consumes `contiguous_augend_addend_disjoint` (`i < n`).  A genuine
interface instance — drop-in for any consumer written against `TwoBaseBoundedAdder`
— with NO informal "the call sites are bounded" hand-waving and NO change to `Adder`.

(The general two-base case, with the addend block at an arbitrary independent base,
is supported by the *interface*; this instance pins the packed `addBase = accBase+n`
choice that the §1–§4 relabel transport built. A different `valid` + relocation
permutation would give other base layouts.) -/

/-- **The contiguous-accumulator Cuccaro adder, packed, as a `TwoBaseBoundedAdder`.**
    Accumulator bit `i` at `accBase + i`, addend bit `i` at `addBase + i` with
    `addBase = accBase + n`, clean carry-in at `accBase + 2n`. -/
def contiguousPackedAdder : TwoBaseBoundedAdder where
  span     := fun n _ _ => 2 * n + 1
  accIdx   := fun _ accBase i => accBase + i
  addIdx   := fun _ addBase i => addBase + i
  valid    := fun n accBase addBase => addBase = accBase + n
  ancClean := fun f n accBase _ => f (accBase + 2 * n) = false
  circuit  := fun n accBase _ => contiguousAdderCircuit n accBase
  sumCorrect := by
    intro n accBase addBase f hv hclean; subst hv
    exact contiguous_sumCorrect n accBase f hclean
  addendRestored := by
    intro n accBase addBase f hv hclean i hi; subst hv
    exact contiguous_addendRestored n accBase f i hi
  ancRestored := by
    intro n accBase addBase f hv hclean; subst hv
    exact contiguous_ancRestored n accBase f hclean
  frame := by
    intro n accBase addBase f p _ hp
    exact contiguous_frame n accBase f p hp
  wellTyped := by
    intro n accBase addBase _
    exact contiguous_wellTyped n accBase
  accIdx_inBlock := fun n accBase _ i _ hi => contiguous_augendIdx_inBlock n accBase i hi
  addIdx_inBlock := by
    intro n accBase addBase i hv hi; subst hv
    exact contiguous_addendIdx_inBlock n accBase i hi
  addIdx_inj := fun n addBase i j h => by omega
  acc_add_disjoint := by
    intro n accBase addBase i j hv hi _; subst hv
    exact contiguous_augend_addend_disjoint n accBase i j hi
  ancClean_ext := by
    intro n accBase addBase f g hv hagree hclean; subst hv
    show g (accBase + 2 * n) = false
    have hp : inBlock accBase (2 * n + 1) (accBase + 2 * n) := by unfold inBlock; omega
    have hne : ∀ i, i < n →
        accBase + 2 * n ≠ accBase + i ∧ accBase + 2 * n ≠ accBase + n + i := fun i hi => by omega
    rw [← hagree (accBase + 2 * n) hp hne]
    exact hclean

/-! ### Smoke: both interfaces are non-vacuously usable.

`valid` is inhabited and `sumCorrect` fires — for the packed contiguous instance
(`valid` discharged by `rfl`, `addBase = q + n`), and for a single-base Cuccaro
`Adder` coerced in via `toTwoBaseBounded` (the diagonal `addBase = q`). -/

example (n q : Nat) (f : Nat → Bool) (hclean : f (q + 2 * n) = false) :
    decodeReg (contiguousPackedAdder.accIdx n q) n
        (Gate.applyNat (contiguousPackedAdder.circuit n q (q + n)) f)
      = (decodeReg (contiguousPackedAdder.accIdx n q) n f
          + decodeReg (contiguousPackedAdder.addIdx n (q + n)) n f) % 2 ^ n :=
  contiguousPackedAdder.sumCorrect n q (q + n) f rfl hclean

example (n q : Nat) (f : Nat → Bool) (hclean : cuccaroAdder.ancClean f n q) :
    decodeReg (cuccaroAdder.toTwoBaseBounded.accIdx n q) n
        (Gate.applyNat (cuccaroAdder.toTwoBaseBounded.circuit n q q) f)
      = (decodeReg (cuccaroAdder.toTwoBaseBounded.accIdx n q) n f
          + decodeReg (cuccaroAdder.toTwoBaseBounded.addIdx n q) n f) % 2 ^ n :=
  cuccaroAdder.toTwoBaseBounded.sumCorrect n q q f rfl hclean

end FormalRV.BQAlgo
