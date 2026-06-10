/-
  FormalRV.Arithmetic.Windowed.WindowedInPlace — the IN-PLACE windowed
  multiplier and its pass-composition (the structural core of windowed modexp).

  Replays the Gidney `modMultInPlace` algorithm (OOPmul(a) ; SWAP ; OOPmul(−a⁻¹),
  `ModularAdder/Gidney/Def.lean`) at the WINDOWED level, with mod-2^bits
  arithmetic and an arbitrary `Adder` backend:

  * **Stage 1 — generalized pass.**  `windowedMulCircuitOf` run from ANY state
    satisfying the window-step invariant with partial sum `acc₀` (not just the
    clean `mulInputOf` with `acc₀ = 0`) leaves `(acc₀ + a·y) mod 2^bits` in the
    accumulator (`stepInv_full_pass`, `windowedMulCircuitOf_correct_acc`); the
    concrete nonzero-accumulator input `mulInputAccOf` instantiates it.
  * **Stage 2 — the acc↔y swap.**  `accYSwap A w bits`, three interleaved
    CX cascades between the accumulator (`A.augendIdx`) and the y-register,
    exchanges the two registers and frames everything else (`accYSwap_apply`),
    by the generic cascade engine of `WindowedCopySemantics`.
  * **Stage 3 — in-place multiply.**  For `a` invertible mod 2^bits
    (`a·ainv ≡ 1`), `windowedMulInPlace = pass(a) ; swap ; pass(2^bits − ainv)`
    maps the `MulReady`-shaped state with y-register `y` to the `MulReady`
    state with y-register `(a·y) mod 2^bits` — accumulator and ancillas
    restored CLEAN (`windowedMulInPlace_correct`).  The cancellation
    `(y + (2^bits − ainv)·(a·y mod 2^bits)) ≡ 0` is `mod_inv_cancel_identity`.
  * **Stage 4 — pass-composition.**  `windowedMulInPlaceSeq`, the k-fold
    in-place multiply by constants `aₖ`, computes `y ← (Π aₖ)·y mod 2^bits`
    (`windowedMulInPlaceSeq_correct`); the modular-exponentiation instance
    `windowedExpInPlace` with CLASSICAL exponent windows
    `aₖ = g^((2^wE)^k · windowₖ(e))` computes `y ← g^e·y mod 2^bits`
    (`windowedExpInPlace_correct`).  The quantum-selected version (windows
    read from an exponent register via `expWindowPassOf`) is the documented
    next step, NOT attempted here.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Windowed.WindowedCircuitCorrect
import FormalRV.Arithmetic.ModularAdder.Gidney.ControlledPipeline

namespace FormalRV.Shor.WindowedCircuit

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §1. Register-decode bit lemmas: reading individual bits back out. -/

/-- `decodeReg` peels its top bit (weight `2^n` at `idx n`). -/
theorem decodeReg_succ_eq (idx : Nat → Nat) (n : Nat) (f : Nat → Bool) :
    decodeReg idx (n + 1) f
      = decodeReg idx n f + (if f (idx n) then 2 ^ n else 0) := by
  unfold decodeReg
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]

/-- A `n`-bit register decode is `< 2^n`. -/
theorem decodeReg_lt_two_pow (idx : Nat → Nat) (n : Nat) (f : Nat → Bool) :
    decodeReg idx n f < 2 ^ n := by
  induction n with
  | zero => simp [decodeReg]
  | succ k ih =>
    rw [decodeReg_succ_eq]
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    by_cases hb : f (idx k)
    · rw [if_pos hb]; omega
    · rw [if_neg hb]; omega

/-- **Decode determines the bits.**  Bit `i` of `decodeReg idx n f` is exactly
    the state bit at `idx i` — the converse of `decodeReg_eq_mod_of_testBit`,
    by uniqueness of binary digits.  (No injectivity of `idx` needed: the
    decode SUM indexes over `i`, reading `f (idx i)` once per `i`.) -/
theorem decodeReg_testBit (idx : Nat → Nat) (n : Nat) (f : Nat → Bool)
    (i : Nat) (hi : i < n) :
    (decodeReg idx n f).testBit i = f (idx i) := by
  induction n with
  | zero => omega
  | succ k ih =>
    have hlt : decodeReg idx k f < 2 ^ k := decodeReg_lt_two_pow idx k f
    rw [decodeReg_succ_eq]
    by_cases hik : i = k
    · subst hik
      by_cases hb : f (idx i)
      · rw [if_pos hb, Nat.add_comm, Nat.testBit_two_pow_add_eq,
            Nat.testBit_lt_two_pow hlt, hb]
        rfl
      · rw [if_neg hb, Nat.add_zero, Nat.testBit_lt_two_pow hlt]
        cases hh : f (idx i)
        · rfl
        · exact absurd hh hb
    · have hik' : i < k := by omega
      by_cases hb : f (idx k)
      · rw [if_pos hb, Nat.add_comm, Nat.testBit_two_pow_add_gt hik', ih hik']
      · rw [if_neg hb, Nat.add_zero, ih hik']

/-- `encodeReg` at an in-range offset reads bit `i`. -/
theorem encodeReg_at (base len x i : Nat) (hi : i < len) :
    encodeReg base len x (base + i) = x.testBit i := by
  unfold encodeReg
  rw [if_pos ⟨by omega, by omega⟩]
  congr 1
  omega

/-- `encodeReg` above the register reads `false`. -/
theorem encodeReg_high (base len x p : Nat) (hp : base + len ≤ p) :
    encodeReg base len x p = false := by
  unfold encodeReg
  rw [if_neg (by omega)]

/-! ## §2. Writing a register: `writeReg` and the nonzero-accumulator input. -/

/-- Overwrite the `n`-bit register at positions `idx 0 … idx (n−1)` with the
    binary digits of `v` (bit `i` at `idx i`). -/
def writeReg (idx : Nat → Nat) (n v : Nat) (f : Nat → Bool) : Nat → Bool :=
  (List.range n).foldl (fun g i => update g (idx i) (v.testBit i)) f

/-- `writeReg` frame: positions off the register are untouched. -/
theorem writeReg_frame (idx : Nat → Nat) (n v : Nat) (f : Nat → Bool) (p : Nat)
    (hp : ∀ i, i < n → p ≠ idx i) :
    writeReg idx n v f p = f p := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold writeReg
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [update_neq _ _ _ _ (hp k (Nat.lt_succ_self k))]
    exact ih (fun i hi => hp i (Nat.lt_succ_of_lt hi))

/-- `writeReg` writes: with pairwise-distinct positions, position `idx i`
    ends as bit `i` of `v`. -/
theorem writeReg_at (idx : Nat → Nat) (n v : Nat) (f : Nat → Bool)
    (hinj : ∀ i j, i < n → j < n → idx i = idx j → i = j)
    (i : Nat) (hi : i < n) :
    writeReg idx n v f (idx i) = v.testBit i := by
  induction n with
  | zero => omega
  | succ k ih =>
    unfold writeReg
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hik : i = k
    · subst hik
      rw [update_eq]
    · have hi' : i < k := by omega
      rw [update_neq _ _ _ _
            (fun heq => hik (hinj i k (by omega) (by omega) heq))]
      exact ih (fun a b ha hb => hinj a b (by omega) (by omega)) hi'

/-- **The nonzero-accumulator input**: `mulInputOf` with `acc₀` additionally
    encoded at the accumulator (augend) positions of adder `A`. -/
def mulInputAccOf (A : Adder) (w bits numWin acc₀ y : Nat) : Nat → Bool :=
  writeReg (A.augendIdx (1 + 2 * w)) bits acc₀ (mulInputOf A w bits numWin y)

/-! ## §3. Stage 1 — the generalized pass (nonzero initial accumulator).

The existing `stepInv_step` is start-value-agnostic (it advances `StepInv`
from ANY partial sum `s`), so the generalization only needs a new INIT (the
invariant at partial sum `acc₀`) and a replayed fold. -/

/-- **Invariant initialization at `acc₀`.**  `mulInputAccOf` satisfies the
    window-step invariant with partial sum `acc₀` (accumulator positions must
    be pairwise distinct so the written digits read back). -/
theorem stepInv_init_acc (A : Adder) (w bits numWin acc₀ y : Nat)
    (hinj : ∀ i j, i < bits → j < bits →
      A.augendIdx (1 + 2 * w) i = A.augendIdx (1 + 2 * w) j → i = j)
    (hclean : A.ancClean (mulInputAccOf A w bits numWin acc₀ y) bits (1 + 2 * w)) :
    StepInv A w bits numWin y acc₀ (mulInputAccOf A w bits numWin acc₀ y) := by
  unfold mulInputAccOf
  refine ⟨?_, ?_, hclean, ?_⟩
  · -- (F): off-block positions are untouched by the accumulator write.
    intro p hp
    exact writeReg_frame _ _ _ _ _
      (fun i hi heq => hp (heq ▸ A.augendIdx_inBlock bits (1 + 2 * w) i hi))
  · -- (D): the addend register is clean (augend and addend never collide).
    intro i hi
    rw [writeReg_frame _ _ _ _ _
          (fun k hk => Ne.symm (A.augend_addend_disjoint (1 + 2 * w) k i))]
    have hblk := A.addendIdx_inBlock bits (1 + 2 * w) i hi
    unfold inBlock at hblk
    exact mulInputOf_low A w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega) (by omega)
  · -- (V): the accumulator decodes to `acc₀ % 2^bits`.
    exact decodeReg_eq_mod_of_testBit _ bits acc₀ _
      (fun i hi => writeReg_at _ bits acc₀ _ hinj i hi)

/-- **The generalized fold.**  From ANY state `f` satisfying the invariant with
    partial sum `acc₀`, running the first `n ≤ numWin` window-steps yields the
    invariant with partial sum `acc₀ + Σ_{k<n} a·(2^w)^k·windowₖ(y)`.
    (Reuses the existing start-value-agnostic `stepInv_step` verbatim.) -/
theorem stepInv_fold_acc (A : Adder) (w bits a numWin y acc₀ : Nat) (hw : 0 < w)
    (f : Nat → Bool) (hf : StepInv A w bits numWin y acc₀ f) :
    ∀ n, n ≤ numWin →
      StepInv A w bits numWin y
        (acc₀ + ∑ k ∈ Finset.range n, a * (2 ^ w) ^ k * WindowedArith.window w y k)
        (Gate.applyNat
          (windowedMulOf A w bits a bits (1 + 2 * w) (1 + 2 * w + A.span bits) n)
          f) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Finset.sum_range_zero, Nat.add_zero]
    show StepInv A w bits numWin y acc₀ (Gate.applyNat Gate.I f)
    rw [Gate.applyNat_I]
    exact hf
  | succ n ih =>
    intro hn
    have hsplit : windowedMulOf A w bits a bits (1 + 2 * w)
          (1 + 2 * w + A.span bits) (n + 1)
        = Gate.seq
            (windowedMulOf A w bits a bits (1 + 2 * w)
              (1 + 2 * w + A.span bits) n)
            (windowStepOf A w bits a bits (1 + 2 * w)
              (1 + 2 * w + A.span bits) n) := by
      unfold windowedMulOf
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq, Finset.sum_range_succ, ← Nat.add_assoc]
    exact stepInv_step A w bits a numWin y hw n (by omega) _ _ (ih (by omega))

/-- **The full generalized pass, invariant form.**  One complete
    `windowedMulCircuitOf` run from an invariant state with partial sum `acc₀`
    re-establishes the invariant with partial sum `acc₀ + a·y` — the form the
    in-place composition consumes. -/
theorem stepInv_full_pass (A : Adder) (w bits a numWin y acc₀ : Nat)
    (hw : 0 < w) (hy : y < 2 ^ (w * numWin)) (f : Nat → Bool)
    (hf : StepInv A w bits numWin y acc₀ f) :
    StepInv A w bits numWin y (acc₀ + a * y)
      (Gate.applyNat (windowedMulCircuitOf A w bits a numWin) f) := by
  have hfold := stepInv_fold_acc A w bits a numWin y acc₀ hw f hf numWin le_rfl
  have hy' : y < (2 ^ w) ^ numWin := by rw [← pow_mul]; exact hy
  have hsum : (∑ k ∈ Finset.range numWin,
        a * (2 ^ w) ^ k * WindowedArith.window w y k) = a * y := by
    rw [WindowedArith.windowed_mul w numWin a y hy']
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hsum] at hfold
  exact hfold

/-- **Stage 1 HEADLINE — generalized-pass VALUE theorem.**  For ANY adder `A`,
    the windowed multiplier run from an invariant state whose accumulator
    holds partial sum `acc₀` leaves `(acc₀ + a·y) mod 2^bits` in the
    accumulator. -/
theorem windowedMulCircuitOf_correct_acc (A : Adder) (w bits a numWin y acc₀ : Nat)
    (hw : 0 < w) (hy : y < 2 ^ (w * numWin)) (f : Nat → Bool)
    (hf : StepInv A w bits numWin y acc₀ f) :
    decodeAccOf A (Gate.applyNat (windowedMulCircuitOf A w bits a numWin) f)
        (1 + 2 * w) bits
      = (acc₀ + a * y) % 2 ^ bits := by
  show decodeReg (A.augendIdx (1 + 2 * w)) bits
      (Gate.applyNat (windowedMulCircuitOf A w bits a numWin) f)
    = (acc₀ + a * y) % 2 ^ bits
  exact (stepInv_full_pass A w bits a numWin y acc₀ hw hy f hf).2.2.2

/-- **Stage 1, concrete input.**  On `mulInputAccOf` (ctrl set, `y` in the
    y-register, `acc₀` in the accumulator, everything else clean), the pass
    leaves `(acc₀ + a·y) mod 2^bits` in the accumulator. -/
theorem mulInputAccOf_correct (A : Adder) (w bits a numWin acc₀ y : Nat)
    (hw : 0 < w) (hy : y < 2 ^ (w * numWin))
    (hinj : ∀ i j, i < bits → j < bits →
      A.augendIdx (1 + 2 * w) i = A.augendIdx (1 + 2 * w) j → i = j)
    (hclean : A.ancClean (mulInputAccOf A w bits numWin acc₀ y) bits (1 + 2 * w)) :
    decodeAccOf A (Gate.applyNat (windowedMulCircuitOf A w bits a numWin)
        (mulInputAccOf A w bits numWin acc₀ y)) (1 + 2 * w) bits
      = (acc₀ + a * y) % 2 ^ bits :=
  windowedMulCircuitOf_correct_acc A w bits a numWin y acc₀ hw hy _
    (stepInv_init_acc A w bits numWin acc₀ y hinj hclean)

/-! ## §4. Stage 2 — the accumulator ↔ y-register swap.

Three interleaved full-register CX cascades (the register-level 3-CX SWAP):
`CX(acc→y) ; CX(y→acc) ; CX(acc→y)` per bit, with all semantics inherited from
the generic cascade engine `applyNat_cx_cascade_at/_frame`. -/

/-- A parallel CX cascade `CX (ctrl 0) (tgt 0) ; … ; CX (ctrl (n−1)) (tgt (n−1))`
    (the foldl shape of the generic cascade engine). -/
def cxCascade (ctrl tgt : Nat → Nat) (n : Nat) : Gate :=
  (List.range n).foldl (fun g i => Gate.seq g (Gate.CX (ctrl i) (tgt i))) Gate.I

/-- **The acc↔y swap** over adder `A`: a 3-cascade transposition between
    accumulator bit `A.augendIdx (1+2w) i` and y-register bit
    `(1+2w + A.span bits) + i`, for `i < bits`. -/
def accYSwap (A : Adder) (w bits : Nat) : Gate :=
  Gate.seq
    (Gate.seq
      (cxCascade (A.augendIdx (1 + 2 * w))
        (fun i => 1 + 2 * w + A.span bits + i) bits)
      (cxCascade (fun i => 1 + 2 * w + A.span bits + i)
        (A.augendIdx (1 + 2 * w)) bits))
    (cxCascade (A.augendIdx (1 + 2 * w))
      (fun i => 1 + 2 * w + A.span bits + i) bits)

/-- **`accYSwap` post-state**: the accumulator and the (low `bits` of the)
    y-register are exchanged, and every other wire is untouched.
    Needs only the accumulator positions pairwise distinct (`hinj`) — their
    disjointness from the y-wires is the interface fact `augendIdx_inBlock`. -/
theorem accYSwap_apply (A : Adder) (w bits : Nat) (g : Nat → Bool)
    (hinj : ∀ i j, i < bits → j < bits →
      A.augendIdx (1 + 2 * w) i = A.augendIdx (1 + 2 * w) j → i = j) :
    (∀ i, i < bits →
        Gate.applyNat (accYSwap A w bits) g (A.augendIdx (1 + 2 * w) i)
          = g (1 + 2 * w + A.span bits + i))
    ∧ (∀ i, i < bits →
        Gate.applyNat (accYSwap A w bits) g (1 + 2 * w + A.span bits + i)
          = g (A.augendIdx (1 + 2 * w) i))
    ∧ (∀ p, (∀ i, i < bits →
          p ≠ A.augendIdx (1 + 2 * w) i ∧ p ≠ 1 + 2 * w + A.span bits + i) →
        Gate.applyNat (accYSwap A w bits) g p = g p) := by
  -- Standing zone facts: the accumulator sits strictly below the y-register.
  have haug_lt : ∀ k, k < bits →
      A.augendIdx (1 + 2 * w) k < 1 + 2 * w + A.span bits := by
    intro k hk
    have hblk := A.augendIdx_inBlock bits (1 + 2 * w) k hk
    unfold inBlock at hblk
    omega
  have haug_ne_y : ∀ i k, i < bits → k < bits →
      A.augendIdx (1 + 2 * w) i ≠ 1 + 2 * w + A.span bits + k := by
    intro i k hi _
    have := haug_lt i hi
    omega
  have hy_ne_aug : ∀ i k, i < bits → k < bits →
      1 + 2 * w + A.span bits + i ≠ A.augendIdx (1 + 2 * w) k := by
    intro i k _ hk
    have := haug_lt k hk
    omega
  have hy_inj : ∀ i k, i < bits → k < bits → i ≠ k →
      1 + 2 * w + A.span bits + i ≠ 1 + 2 * w + A.span bits + k := by
    intro i k _ _ hne
    omega
  have haug_inj : ∀ i k, i < bits → k < bits → i ≠ k →
      A.augendIdx (1 + 2 * w) i ≠ A.augendIdx (1 + 2 * w) k :=
    fun i k hi hk hne heq => hne (hinj i k hi hk heq)
  -- Expose the three cascades.
  unfold accYSwap
  simp only [Gate.applyNat_seq]
  set g1 : Nat → Bool := Gate.applyNat
    (cxCascade (A.augendIdx (1 + 2 * w))
      (fun i => 1 + 2 * w + A.span bits + i) bits) g with hg1def
  set g2 : Nat → Bool := Gate.applyNat
    (cxCascade (fun i => 1 + 2 * w + A.span bits + i)
      (A.augendIdx (1 + 2 * w)) bits) g1 with hg2def
  -- Cascade 1 (acc → y): each y-wire XORs in its accumulator bit.
  have hg1_at : ∀ k, k < bits →
      g1 (1 + 2 * w + A.span bits + k)
        = xor (g (1 + 2 * w + A.span bits + k)) (g (A.augendIdx (1 + 2 * w) k)) := by
    intro k hk
    rw [hg1def]
    unfold cxCascade
    exact applyNat_cx_cascade_at (A.augendIdx (1 + 2 * w))
      (fun i => 1 + 2 * w + A.span bits + i) g bits hy_inj haug_ne_y k hk
  have hg1_frame : ∀ p, (∀ k, k < bits → p ≠ 1 + 2 * w + A.span bits + k) →
      g1 p = g p := by
    intro p hp
    rw [hg1def]
    unfold cxCascade
    exact applyNat_cx_cascade_frame (A.augendIdx (1 + 2 * w))
      (fun i => 1 + 2 * w + A.span bits + i) g bits p hp
  -- Cascade 2 (y → acc): each accumulator wire XORs in the UPDATED y-bit.
  have hg2_at : ∀ k, k < bits →
      g2 (A.augendIdx (1 + 2 * w) k)
        = xor (g1 (A.augendIdx (1 + 2 * w) k)) (g1 (1 + 2 * w + A.span bits + k)) := by
    intro k hk
    rw [hg2def]
    unfold cxCascade
    exact applyNat_cx_cascade_at (fun i => 1 + 2 * w + A.span bits + i)
      (A.augendIdx (1 + 2 * w)) g1 bits haug_inj hy_ne_aug k hk
  have hg2_frame : ∀ p, (∀ k, k < bits → p ≠ A.augendIdx (1 + 2 * w) k) →
      g2 p = g1 p := by
    intro p hp
    rw [hg2def]
    unfold cxCascade
    exact applyNat_cx_cascade_frame (fun i => 1 + 2 * w + A.span bits + i)
      (A.augendIdx (1 + 2 * w)) g1 bits p hp
  -- Cascade 3 (acc → y): each y-wire XORs in the UPDATED accumulator bit.
  have hg3_at : ∀ k, k < bits →
      Gate.applyNat (cxCascade (A.augendIdx (1 + 2 * w))
          (fun i => 1 + 2 * w + A.span bits + i) bits) g2
          (1 + 2 * w + A.span bits + k)
        = xor (g2 (1 + 2 * w + A.span bits + k)) (g2 (A.augendIdx (1 + 2 * w) k)) := by
    intro k hk
    unfold cxCascade
    exact applyNat_cx_cascade_at (A.augendIdx (1 + 2 * w))
      (fun i => 1 + 2 * w + A.span bits + i) g2 bits hy_inj haug_ne_y k hk
  have hg3_frame : ∀ p, (∀ k, k < bits → p ≠ 1 + 2 * w + A.span bits + k) →
      Gate.applyNat (cxCascade (A.augendIdx (1 + 2 * w))
          (fun i => 1 + 2 * w + A.span bits + i) bits) g2 p = g2 p := by
    intro p hp
    unfold cxCascade
    exact applyNat_cx_cascade_frame (A.augendIdx (1 + 2 * w))
      (fun i => 1 + 2 * w + A.span bits + i) g2 bits p hp
  refine ⟨?_, ?_, ?_⟩
  · -- The accumulator wire ends holding the ORIGINAL y-bit.
    intro i hi
    rw [hg3_frame _ (fun k hk => haug_ne_y i k hi hk),
        hg2_at i hi,
        hg1_frame _ (fun k hk => haug_ne_y i k hi hk),
        hg1_at i hi]
    cases g (A.augendIdx (1 + 2 * w) i) <;>
      cases g (1 + 2 * w + A.span bits + i) <;> rfl
  · -- The y-wire ends holding the ORIGINAL accumulator bit.
    intro i hi
    rw [hg3_at i hi,
        hg2_frame _ (fun k hk => hy_ne_aug i k hi hk),
        hg2_at i hi,
        hg1_frame _ (fun k hk => haug_ne_y i k hi hk),
        hg1_at i hi]
    cases g (A.augendIdx (1 + 2 * w) i) <;>
      cases g (1 + 2 * w + A.span bits + i) <;> rfl
  · -- Everything else is framed by all three cascades.
    intro p hp
    rw [hg3_frame _ (fun k hk => (hp k hk).2),
        hg2_frame _ (fun k hk => (hp k hk).1),
        hg1_frame _ (fun k hk => (hp k hk).2)]

/-! ## §5. The composable I/O shape: `MulReady`.

The state shape that the in-place multiplier both CONSUMES and PRODUCES:
off the adder block the state IS `mulInputOf` (ctrl set, lookup zone clean,
`y` encoded in the y-register), and inside the block the addend register,
the accumulator, and the adder ancillas are all clean.  Because the output
shape equals the input shape (with the new y-value), in-place multiplies
compose by induction — this is why Stage 3 proves full state restoration,
not just a decode. -/

/-- The in-place multiplier's input/output contract: a `mulInputOf`-shaped
    state with y-register value `y` and a CLEAN block. -/
def MulReady (A : Adder) (w bits numWin y : Nat) (f : Nat → Bool) : Prop :=
  (∀ p, ¬ inBlock (1 + 2 * w) (A.span bits) p →
      f p = mulInputOf A w bits numWin y p)
  ∧ (∀ i, i < bits → f (A.addendIdx (1 + 2 * w) i) = false)
  ∧ A.ancClean f bits (1 + 2 * w)
  ∧ (∀ i, i < bits → f (A.augendIdx (1 + 2 * w) i) = false)

/-- A `MulReady` state satisfies the window-step invariant with partial sum 0
    (a bitwise-clean accumulator decodes to 0). -/
theorem MulReady.toStepInv {A : Adder} {w bits numWin y : Nat} {f : Nat → Bool}
    (h : MulReady A w bits numWin y f) : StepInv A w bits numWin y 0 f :=
  ⟨h.1, h.2.1, h.2.2.1,
    by rw [decodeReg_eq_zero _ bits f h.2.2.2, Nat.zero_mod]⟩

/-- The clean input `mulInputOf` is `MulReady` (given the adder's abstract
    ancilla-cleanliness, discharged concretely per instance). -/
theorem mulReady_mulInputOf (A : Adder) (w bits numWin y : Nat)
    (hclean : A.ancClean (mulInputOf A w bits numWin y) bits (1 + 2 * w)) :
    MulReady A w bits numWin y (mulInputOf A w bits numWin y) := by
  refine ⟨fun p _ => rfl, ?_, hclean, ?_⟩
  · intro i hi
    have hblk := A.addendIdx_inBlock bits (1 + 2 * w) i hi
    unfold inBlock at hblk
    exact mulInputOf_low A w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega) (by omega)
  · intro i hi
    have hblk := A.augendIdx_inBlock bits (1 + 2 * w) i hi
    unfold inBlock at hblk
    exact mulInputOf_low A w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega) (by omega)

/-! ## §6. Stage 3 — the in-place windowed multiplier.

The Gidney `modMultInPlace` algorithm at the windowed level, mod `2^bits`:

    pass(a) ; acc↔y swap ; pass(2^bits − ainv)

On a `MulReady` state with y-value `y`:  pass 1 puts `a·y mod 2^bits` in the
accumulator; the swap moves it into the y-register (leaving `y` in the
accumulator); pass 2 — the STAGE-1 GENERALIZED pass, initial accumulator `y`,
multiplier register `a·y mod 2^bits` — adds `(2^bits − ainv)·(a·y)`, and
`y·(1 − ainv·a) ≡ 0 (mod 2^bits)` clears the accumulator. -/

/-- **The in-place windowed multiplier** by an (odd, hence invertible
    mod `2^bits`) constant `a` with inverse `ainv`. -/
def windowedMulInPlace (A : Adder) (w bits a ainv numWin : Nat) : Gate :=
  Gate.seq
    (Gate.seq (windowedMulCircuitOf A w bits a numWin) (accYSwap A w bits))
    (windowedMulCircuitOf A w bits (2 ^ bits - ainv) numWin)

/-- **Stage 3 HEADLINE — in-place windowed multiplication, full state
    restoration.**  For ANY adder `A` whose accumulator positions are pairwise
    distinct, with `numWin·w = bits` (the y-register exactly matches the
    accumulator width) and `a·ainv ≡ 1 (mod 2^bits)`: the in-place multiplier
    maps any `MulReady` state with y-value `y < 2^bits` to the `MulReady`
    state with y-value `(a·y) mod 2^bits` — accumulator, addend register, and
    ancillas all returned CLEAN, everything off the y-register restored.  The
    output shape equals the input shape, so in-place multiplies compose. -/
theorem windowedMulInPlace_correct (A : Adder) (w bits a ainv numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hy : y < 2 ^ bits)
    (hainv : ainv < 2 ^ bits) (hinv : a * ainv % 2 ^ bits = 1)
    (hinj : ∀ i j, i < bits → j < bits →
      A.augendIdx (1 + 2 * w) i = A.augendIdx (1 + 2 * w) j → i = j)
    (f : Nat → Bool) (hf : MulReady A w bits numWin y f) :
    MulReady A w bits numWin (a * y % 2 ^ bits)
      (Gate.applyNat (windowedMulInPlace A w bits a ainv numWin) f) := by
  have hpow : (2 : Nat) ^ (w * numWin) = 2 ^ bits := by
    rw [Nat.mul_comm w numWin, hbits]
  -- Standing zone facts.
  have hadd_lt : ∀ i, i < bits →
      A.addendIdx (1 + 2 * w) i < 1 + 2 * w + A.span bits := by
    intro i hi
    have hblk := A.addendIdx_inBlock bits (1 + 2 * w) i hi
    unfold inBlock at hblk
    omega
  have hy_off : ∀ i : Nat,
      ¬ inBlock (1 + 2 * w) (A.span bits) (1 + 2 * w + A.span bits + i) := by
    intro i
    unfold inBlock
    omega
  -- Expose the three stages.
  unfold windowedMulInPlace
  simp only [Gate.applyNat_seq]
  set s1 : Nat → Bool :=
    Gate.applyNat (windowedMulCircuitOf A w bits a numWin) f with hs1def
  set s2 : Nat → Bool := Gate.applyNat (accYSwap A w bits) s1 with hs2def
  -- ── Pass 1: accumulator ← a·y mod 2^bits ──────────────────────────────
  have hy1 : y < 2 ^ (w * numWin) := by rw [hpow]; exact hy
  have h1 := stepInv_full_pass A w bits a numWin y 0 hw hy1 f hf.toStepInv
  rw [Nat.zero_add] at h1
  obtain ⟨h1F, h1D, h1C, h1V⟩ := h1
  rw [← hs1def] at h1F h1D h1C h1V
  -- Bitwise content after pass 1: the accumulator holds the digits of
  -- a·y mod 2^bits, the y-register still holds the digits of y.
  have h1aug : ∀ i, i < bits →
      s1 (A.augendIdx (1 + 2 * w) i) = (a * y % 2 ^ bits).testBit i := by
    intro i hi
    rw [← decodeReg_testBit (A.augendIdx (1 + 2 * w)) bits s1 i hi, h1V]
  have h1y : ∀ i, i < bits →
      s1 (1 + 2 * w + A.span bits + i) = y.testBit i := by
    intro i hi
    rw [h1F _ (hy_off i),
        mulInputOf_eq_encodeReg A w bits numWin y _
          (by unfold ulookup_ctrl_idx; omega),
        encodeReg_at _ _ _ i (by omega)]
  -- ── The swap: accumulator ↔ y-register ────────────────────────────────
  obtain ⟨hsw_acc, hsw_y, hsw_fr⟩ := accYSwap_apply A w bits s1 hinj
  rw [← hs2def] at hsw_acc hsw_y hsw_fr
  -- s2 is a window-step-invariant state for the SECOND pass: y-register
  -- value a·y mod 2^bits, partial sum (initial accumulator) y.
  have h2 : StepInv A w bits numWin (a * y % 2 ^ bits) y s2 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (F): off-block, s2 IS the fresh input with y-value a·y mod 2^bits.
      intro p hp
      by_cases hpy : ∃ i, i < bits ∧ p = 1 + 2 * w + A.span bits + i
      · obtain ⟨i, hi, rfl⟩ := hpy
        rw [hsw_y i hi, h1aug i hi,
            mulInputOf_eq_encodeReg A w bits numWin _ _
              (by unfold ulookup_ctrl_idx; omega),
            encodeReg_at _ _ _ i (by omega)]
      · push Not at hpy
        have hpa : ∀ i, i < bits → p ≠ A.augendIdx (1 + 2 * w) i :=
          fun i hi heq => hp (heq ▸ A.augendIdx_inBlock bits (1 + 2 * w) i hi)
        rw [hsw_fr p (fun i hi => ⟨hpa i hi, hpy i hi⟩), h1F p hp]
        by_cases hpc : p = ulookup_ctrl_idx
        · rw [hpc, mulInputOf_ctrl, mulInputOf_ctrl]
        · unfold inBlock at hp
          push Not at hp
          by_cases hplow : p < 1 + 2 * w + A.span bits
          · have hlow : p < 1 + 2 * w := by
              by_contra hcon
              have := hp (by omega)
              omega
            rw [mulInputOf_low A w bits numWin y p hpc (by omega),
                mulInputOf_low A w bits numWin _ p hpc (by omega)]
          · have hphigh : 1 + 2 * w + A.span bits + bits ≤ p := by
              by_contra hcon
              exact hpy (p - (1 + 2 * w + A.span bits)) (by omega) (by omega)
            rw [mulInputOf_eq_encodeReg A w bits numWin y p hpc,
                mulInputOf_eq_encodeReg A w bits numWin _ p hpc,
                encodeReg_high _ _ _ _ (by omega),
                encodeReg_high _ _ _ _ (by omega)]
    · -- (D): the addend register is untouched by the swap.
      intro i hi
      rw [hsw_fr _ (fun k hk =>
            ⟨Ne.symm (A.augend_addend_disjoint (1 + 2 * w) k i),
             by have := hadd_lt i hi; omega⟩)]
      exact h1D i hi
    · -- (C): the swap only touches data wires, so cleanliness transfers.
      refine A.ancClean_ext bits (1 + 2 * w) s1 s2 ?_ h1C
      intro p hin hoff
      exact (hsw_fr p (fun k hk =>
        ⟨(hoff k hk).1, by unfold inBlock at hin; omega⟩)).symm
    · -- (V): the accumulator now holds the digits of y.
      exact decodeReg_eq_mod_of_testBit _ bits y s2
        (fun i hi => by rw [hsw_acc i hi, h1y i hi])
  -- ── Pass 2: accumulator ← y + (2^bits − ainv)·(a·y mod 2^bits) ≡ 0 ────
  have hy2 : a * y % 2 ^ bits < 2 ^ (w * numWin) := by
    rw [hpow]
    exact Nat.mod_lt _ (Nat.two_pow_pos bits)
  set s3 : Nat → Bool :=
    Gate.applyNat (windowedMulCircuitOf A w bits (2 ^ bits - ainv) numWin) s2
    with hs3def
  have h3 := stepInv_full_pass A w bits (2 ^ bits - ainv) numWin
    (a * y % 2 ^ bits) y hw hy2 s2 h2
  obtain ⟨h3F, h3D, h3C, h3V⟩ := h3
  rw [← hs3def] at h3F h3D h3C h3V
  -- The modular-inverse cancellation clears the accumulator.
  have hzero : (y + (2 ^ bits - ainv) * (a * y % 2 ^ bits)) % 2 ^ bits = 0 :=
    mod_inv_cancel_identity a ainv (2 ^ bits) y (Nat.two_pow_pos bits)
      hy hainv hinv
  rw [hzero] at h3V
  refine ⟨h3F, h3D, h3C, ?_⟩
  intro i hi
  rw [← decodeReg_testBit (A.augendIdx (1 + 2 * w)) bits s3 i hi, h3V,
      Nat.zero_testBit]

/-! ## §7. Stage 4 — pass-composition: the in-place product chain.

Because Stage 3 returns the state to the `MulReady` shape, in-place multiplies
compose by induction: `k` of them compute `y ← (Π aₖ)·y mod 2^bits`.  The
modular-exponentiation instance takes `aₖ := g^((2^wE)^k · windowₖ(e))` for a
CLASSICAL exponent `e`; then `Π aₖ = g^e` by the windowed digit expansion. -/

/-- The `n`-fold in-place multiply by the constants `as 0, …, as (n−1)`
    (with inverses `ainvs k`). -/
def windowedMulInPlaceSeq (A : Adder) (w bits numWin : Nat)
    (as ainvs : Nat → Nat) (n : Nat) : Gate :=
  (List.range n).foldl
    (fun g k => Gate.seq g (windowedMulInPlace A w bits (as k) (ainvs k) numWin))
    Gate.I

/-- **Stage 4 HEADLINE — the in-place product chain.**  `n` in-place windowed
    multiplies by invertible constants `as k` compute
    `y ← (Π_{k<n} as k)·y mod 2^bits`, returning to the `MulReady` shape
    (clean accumulator/ancillas) after EVERY round — the composition is by
    induction on `n`, using Stage 3's full state restoration. -/
theorem windowedMulInPlaceSeq_correct (A : Adder) (w bits numWin : Nat)
    (as ainvs : Nat → Nat) (y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hy : y < 2 ^ bits)
    (hinj : ∀ i j, i < bits → j < bits →
      A.augendIdx (1 + 2 * w) i = A.augendIdx (1 + 2 * w) j → i = j)
    (f : Nat → Bool) (hf : MulReady A w bits numWin y f) :
    ∀ n, (∀ k, k < n → ainvs k < 2 ^ bits ∧ as k * ainvs k % 2 ^ bits = 1) →
      MulReady A w bits numWin ((∏ k ∈ Finset.range n, as k) * y % 2 ^ bits)
        (Gate.applyNat (windowedMulInPlaceSeq A w bits numWin as ainvs n) f) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Finset.prod_range_zero, Nat.one_mul, Nat.mod_eq_of_lt hy]
    show MulReady A w bits numWin y (Gate.applyNat Gate.I f)
    rw [Gate.applyNat_I]
    exact hf
  | succ n ih =>
    intro hpairs
    have hsplit : windowedMulInPlaceSeq A w bits numWin as ainvs (n + 1)
        = Gate.seq (windowedMulInPlaceSeq A w bits numWin as ainvs n)
            (windowedMulInPlace A w bits (as n) (ainvs n) numWin) := by
      unfold windowedMulInPlaceSeq
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq]
    -- After `n` rounds: a `MulReady` state with y-value (Π_{k<n} as k)·y.
    have ihn := ih (fun k hk => hpairs k (by omega))
    have hyn : (∏ k ∈ Finset.range n, as k) * y % 2 ^ bits < 2 ^ bits :=
      Nat.mod_lt _ (Nat.two_pow_pos bits)
    -- Round n+1: one more in-place multiply, by Stage 3.
    have hstep := windowedMulInPlace_correct A w bits (as n) (ainvs n) numWin
      ((∏ k ∈ Finset.range n, as k) * y % 2 ^ bits) hw hbits hyn
      (hpairs n (by omega)).1 (hpairs n (by omega)).2 hinj _ ihn
    -- Fold the new factor into the running product.
    have hval : as n * ((∏ k ∈ Finset.range n, as k) * y % 2 ^ bits) % 2 ^ bits
        = (∏ k ∈ Finset.range (n + 1), as k) * y % 2 ^ bits := by
      rw [Finset.prod_range_succ, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
          show as n * ((∏ k ∈ Finset.range n, as k) * y)
              = (∏ k ∈ Finset.range n, as k) * as n * y from by ring]
    rw [← hval]
    exact hstep

/-- **The in-place windowed modular exponentiation, CLASSICAL exponent.**
    One in-place multiply per exponent window `k < nE`, by the constant
    `g^((2^wE)^k · windowₖ(e))` (the `k`-th windowed factor of `g^e`).
    The quantum-selected version — windows READ from an exponent register via
    `expWindowPassOf`-style selection — is the documented next step. -/
def windowedExpInPlace (A : Adder) (w bits numWin wE nE g e : Nat)
    (ainvs : Nat → Nat) : Gate :=
  windowedMulInPlaceSeq A w bits numWin
    (fun k => g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k)) ainvs nE

/-- **Stage 4 instance — in-place windowed MODEXP value theorem (classical
    exponent).**  For `e < (2^wE)^nE`, the chain of per-window in-place
    multiplies computes `y ← g^e·y mod 2^bits`: the windowed factors multiply
    out to `g^e` by the base-`2^wE` digit expansion of `e`. -/
theorem windowedExpInPlace_correct (A : Adder)
    (w bits numWin wE nE g e y : Nat) (ainvs : Nat → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hy : y < 2 ^ bits)
    (he : e < (2 ^ wE) ^ nE)
    (hpairs : ∀ k, k < nE → ainvs k < 2 ^ bits ∧
      g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k) * ainvs k % 2 ^ bits = 1)
    (hinj : ∀ i j, i < bits → j < bits →
      A.augendIdx (1 + 2 * w) i = A.augendIdx (1 + 2 * w) j → i = j)
    (f : Nat → Bool) (hf : MulReady A w bits numWin y f) :
    MulReady A w bits numWin (g ^ e * y % 2 ^ bits)
      (Gate.applyNat (windowedExpInPlace A w bits numWin wE nE g e ainvs) f) := by
  have h := windowedMulInPlaceSeq_correct A w bits numWin
    (fun k => g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k)) ainvs y
    hw hbits hy hinj f hf nE hpairs
  -- Σ_{k<nE} (2^wE)^k · windowₖ(e) = e — the windowed digit expansion.
  have hexp : (∑ k ∈ Finset.range nE,
        (2 ^ wE) ^ k * WindowedArith.window wE e k) = e := by
    have hm := (WindowedArith.windowed_mul wE nE 1 e he).symm
    simp only [Nat.one_mul] at hm
    calc (∑ k ∈ Finset.range nE, (2 ^ wE) ^ k * WindowedArith.window wE e k)
        = ∑ k ∈ Finset.range nE, WindowedArith.window wE e k * (2 ^ wE) ^ k :=
          Finset.sum_congr rfl (fun k _ => Nat.mul_comm _ _)
      _ = e := hm
  -- Π_{k<nE} g^((2^wE)^k · windowₖ(e)) = g^e.
  have hprod : (∏ k ∈ Finset.range nE,
        g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k)) = g ^ e := by
    rw [Finset.prod_pow_eq_pow_sum, hexp]
  rw [← hprod]
  exact h

/-! ## §8. Decode-form value corollary and concrete adder instances. -/

/-- **Stage 3, decode form.**  After the in-place multiply, the y-register
    itself decodes to `(a·y) mod 2^bits` (the accumulator is clean by
    `windowedMulInPlace_correct`). -/
theorem windowedMulInPlace_value (A : Adder) (w bits a ainv numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hy : y < 2 ^ bits)
    (hainv : ainv < 2 ^ bits) (hinv : a * ainv % 2 ^ bits = 1)
    (hinj : ∀ i j, i < bits → j < bits →
      A.augendIdx (1 + 2 * w) i = A.augendIdx (1 + 2 * w) j → i = j)
    (f : Nat → Bool) (hf : MulReady A w bits numWin y f) :
    decodeReg (fun i => 1 + 2 * w + A.span bits + i) bits
        (Gate.applyNat (windowedMulInPlace A w bits a ainv numWin) f)
      = a * y % 2 ^ bits := by
  obtain ⟨hF, -, -, -⟩ := windowedMulInPlace_correct A w bits a ainv numWin y
    hw hbits hy hainv hinv hinj f hf
  have hbit : ∀ i, i < bits →
      Gate.applyNat (windowedMulInPlace A w bits a ainv numWin) f
          (1 + 2 * w + A.span bits + i)
        = (a * y % 2 ^ bits).testBit i := by
    intro i hi
    rw [hF _ (by unfold inBlock; omega),
        mulInputOf_eq_encodeReg A w bits numWin _ _
          (by unfold ulookup_ctrl_idx; omega),
        encodeReg_at _ _ _ i (by omega)]
  rw [decodeReg_eq_mod_of_testBit _ bits (a * y % 2 ^ bits) _ hbit, Nat.mod_mod]

/-- Cuccaro accumulator positions `q + 2i + 1` are pairwise distinct. -/
theorem cuccaroAdder_augendIdx_inj (q i j : Nat)
    (h : cuccaroAdder.augendIdx q i = cuccaroAdder.augendIdx q j) : i = j := by
  have h' : q + 2 * i + 1 = q + 2 * j + 1 := h
  omega

/-- Gidney accumulator positions `q + 3i + 1` are pairwise distinct. -/
theorem gidneyAdder_augendIdx_inj (q i j : Nat)
    (h : gidneyAdder.augendIdx q i = gidneyAdder.augendIdx q j) : i = j := by
  have h' : q + 3 * i + 1 = q + 3 * j + 1 := h
  omega

/-- **Cuccaro instance, state form.**  On the clean encoded input, the
    Cuccaro-backed in-place multiplier produces the `MulReady` state with
    y-value `(a·y) mod 2^bits` (its `ancClean` — the carry-in at the block
    base — is discharged concretely). -/
theorem windowedMulInPlace_correct_cuccaro (w bits a ainv numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hy : y < 2 ^ bits)
    (hainv : ainv < 2 ^ bits) (hinv : a * ainv % 2 ^ bits = 1) :
    MulReady cuccaroAdder w bits numWin (a * y % 2 ^ bits)
      (Gate.applyNat (windowedMulInPlace cuccaroAdder w bits a ainv numWin)
        (mulInputOf cuccaroAdder w bits numWin y)) := by
  refine windowedMulInPlace_correct cuccaroAdder w bits a ainv numWin y hw hbits
    hy hainv hinv (fun i j _ _ h => cuccaroAdder_augendIdx_inj (1 + 2 * w) i j h)
    _ (mulReady_mulInputOf cuccaroAdder w bits numWin y ?_)
  show mulInputOf cuccaroAdder w bits numWin y (1 + 2 * w) = false
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  exact mulInputOf_low cuccaroAdder w bits numWin y _
    (by unfold ulookup_ctrl_idx; omega) (by omega)

/-- **Cuccaro instance, value form.**  The y-register of the output decodes to
    `(a·y) mod 2^bits`, and the accumulator is returned clean. -/
theorem windowedMulInPlace_value_cuccaro (w bits a ainv numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hy : y < 2 ^ bits)
    (hainv : ainv < 2 ^ bits) (hinv : a * ainv % 2 ^ bits = 1) :
    decodeReg (fun i => 1 + 2 * w + cuccaroAdder.span bits + i) bits
        (Gate.applyNat (windowedMulInPlace cuccaroAdder w bits a ainv numWin)
          (mulInputOf cuccaroAdder w bits numWin y))
      = a * y % 2 ^ bits := by
  refine windowedMulInPlace_value cuccaroAdder w bits a ainv numWin y hw hbits
    hy hainv hinv (fun i j _ _ h => cuccaroAdder_augendIdx_inj (1 + 2 * w) i j h)
    _ (mulReady_mulInputOf cuccaroAdder w bits numWin y ?_)
  show mulInputOf cuccaroAdder w bits numWin y (1 + 2 * w) = false
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  exact mulInputOf_low cuccaroAdder w bits numWin y _
    (by unfold ulookup_ctrl_idx; omega) (by omega)

/-- **Gidney instance, state form.**  Same, over the Gidney patched ripple
    adder (its `ancClean` — every carry wire `q + 3i + 2` — is discharged
    concretely). -/
theorem windowedMulInPlace_correct_gidney (w bits a ainv numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hy : y < 2 ^ bits)
    (hainv : ainv < 2 ^ bits) (hinv : a * ainv % 2 ^ bits = 1) :
    MulReady gidneyAdder w bits numWin (a * y % 2 ^ bits)
      (Gate.applyNat (windowedMulInPlace gidneyAdder w bits a ainv numWin)
        (mulInputOf gidneyAdder w bits numWin y)) := by
  refine windowedMulInPlace_correct gidneyAdder w bits a ainv numWin y hw hbits
    hy hainv hinv (fun i j _ _ h => gidneyAdder_augendIdx_inj (1 + 2 * w) i j h)
    _ (mulReady_mulInputOf gidneyAdder w bits numWin y ?_)
  show ∀ i, i < bits →
    mulInputOf gidneyAdder w bits numWin y (1 + 2 * w + 3 * i + 2) = false
  intro i hi
  have hspan : gidneyAdder.span bits = 3 * bits + 2 := rfl
  exact mulInputOf_low gidneyAdder w bits numWin y _
    (by unfold ulookup_ctrl_idx; omega) (by omega)

/-- **Cuccaro modexp instance.**  The full in-place windowed modular
    exponentiation by a classical exponent, over the Cuccaro adder, run on the
    clean encoded input with `y` in the y-register: the output is the
    `MulReady` state with y-value `g^e·y mod 2^bits`. -/
theorem windowedExpInPlace_correct_cuccaro (w bits numWin wE nE g e y : Nat)
    (ainvs : Nat → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hy : y < 2 ^ bits)
    (he : e < (2 ^ wE) ^ nE)
    (hpairs : ∀ k, k < nE → ainvs k < 2 ^ bits ∧
      g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k) * ainvs k % 2 ^ bits = 1) :
    MulReady cuccaroAdder w bits numWin (g ^ e * y % 2 ^ bits)
      (Gate.applyNat
        (windowedExpInPlace cuccaroAdder w bits numWin wE nE g e ainvs)
        (mulInputOf cuccaroAdder w bits numWin y)) := by
  refine windowedExpInPlace_correct cuccaroAdder w bits numWin wE nE g e y ainvs
    hw hbits hy he hpairs
    (fun i j _ _ h => cuccaroAdder_augendIdx_inj (1 + 2 * w) i j h)
    _ (mulReady_mulInputOf cuccaroAdder w bits numWin y ?_)
  show mulInputOf cuccaroAdder w bits numWin y (1 + 2 * w) = false
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  exact mulInputOf_low cuccaroAdder w bits numWin y _
    (by unfold ulookup_ctrl_idx; omega) (by omega)

/-! ## Named next-stage obligation (NOT attempted here).

**Quantum-selected exponent windows.**  `windowedExpInPlace` takes the
exponent windows CLASSICALLY (`aₖ = g^((2^wE)^k·windowₖ(e))` for a fixed `e`).
The full `WindowedExpCorrect` requires the QUANTUM version: each window value
is read from an exponent REGISTER (an `expWindowPassOf`-style lookup selecting
the multiplication constant per window), so that the circuit acts correctly on
every basis state `|e⟩` simultaneously.  That needs (i) a lookup layer
selecting among the `2^wE` constants `g^((2^wE)^k·v)` and their inverses, and
(ii) a frame argument that the exponent register is preserved through each
in-place round — both are layered ON TOP of the `MulReady`-composition proved
here, which is exactly the per-basis-state engine that proof will fold. -/

end FormalRV.Shor.WindowedCircuit
