/-
  FormalRV.Arithmetic.Windowed.WindowedModNInPlace — the IN-PLACE mod-N
  windowed multiplier: `y ← (a·y) mod N` with FULL state restoration.

  Replays the in-place algorithm of `WindowedInPlace.lean`
  (`pass(a) ; acc↔y swap ; pass(−a⁻¹)`) over the PER-WINDOW mod-N multiplier
  of `WindowedModN.lean` (each window does `acc ← (acc + T_j[v]) mod N`), so
  the in-place product is `(a·y) mod N` — the mod-N entry point the Shor
  weld (`EncodeRoundTripModMul.gate c`) consumes.

  * **Stage 1 — generalized pass.**  `windowedModNMulCircuit` run from ANY
    state satisfying the mod-N window-step invariant with partial sum
    `acc₀ < N` (not just the clean input with `acc₀ = 0`) leaves
    `(acc₀ + a·y) mod N` in the accumulator (`modNStepInv_full_pass`,
    `windowedModNMulCircuit_correct_acc`).  The existing `modNStepInv_step`
    is already start-value-agnostic, so this is a new init + replayed fold.
  * **Stage 2 — the swap.**  `accYSwap cuccaroAdder w bits` is reused as-is:
    the mod-N layout is the product-adder layout plus ONE flag qubit at
    `yBase + numWin·w`, which is outside both swap zones (the accumulator
    sits below `yBase`; the swapped y-wires are `yBase + i`, `i < bits`).
  * **Stage 3 — HEADLINE.**  For `a` invertible mod `N` (`a·ainv ≡ 1`),
    `windowedModNMulInPlace = modNpass(a) ; swap ; modNpass(N − ainv)` maps
    the `ModNMulReady`-shaped state with y-register `y < N` to the
    `ModNMulReady` state with y-register `(a·y) mod N` — accumulator, addend
    register, carry-in AND the comparison flag all returned CLEAN
    (`windowedModNMulInPlace_correct`).  The cancellation
    `(y + (N − ainv)·(a·y mod N)) ≡ 0 (mod N)` is `mod_inv_cancel_identity`
    (already general-modulus).  `y < N` is required: after the swap the
    MULTIPLIER register holds `(a·y) mod N < N` and the accumulator holds
    `y`, which must be a valid mod-N partial sum.
  * **Stage 4 — pass-composition.**  `windowedModNMulInPlaceSeq`, the k-fold
    in-place mod-N multiply, computes `y ← (Π aₖ)·y mod N`
    (`windowedModNMulInPlaceSeq_correct`); the squared-power instance
    `windowedModNMulGate (a^(2^k) mod N) (ainv^(2^k) mod N)` realizes
    `y ← a^(2^k)·y mod N` (`windowedModNMulGate_squaredPower`) — the exact
    per-iterate gate family the Shor weld needs.
  * **Counts.**  Two mod-N passes plus a T-free swap:
    `tcount = 2·numWin·(56·w·2^w + 56·bits)`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Windowed.WindowedModN
import FormalRV.Arithmetic.Windowed.WindowedInPlace

namespace FormalRV.Shor.WindowedCircuit

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §1. Cuccaro-layout bridges (definitional).

The mod-N file works at LITERAL Cuccaro positions (`1+2w+2i+1`,
`1+2w+(2·bits+1)+i`), while the adder-generic swap and `mulInputOf` speak
`cuccaroAdder.augendIdx` / `cuccaroAdder.span`.  These are definitionally
equal; the bridges below restate the generic facts in literal form so `rw`
and `omega` operate on one shape. -/

/-- `mulInputOf cuccaroAdder` off the control qubit, literal-base form. -/
private theorem mulInputOf_cuccaro_encodeReg (w bits numWin v p : Nat)
    (hp : p ≠ ulookup_ctrl_idx) :
    mulInputOf cuccaroAdder w bits numWin v p
      = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) v p :=
  mulInputOf_eq_encodeReg cuccaroAdder w bits numWin v p hp

/-- `mulInputOf cuccaroAdder` reads bit `i` of `v` at y-wire `yBase + i`. -/
private theorem mulInputOf_cuccaro_y_bit (w bits numWin v i : Nat)
    (hi : i < numWin * w) :
    mulInputOf cuccaroAdder w bits numWin v (1 + 2 * w + (2 * bits + 1) + i)
      = v.testBit i := by
  rw [mulInputOf_cuccaro_encodeReg w bits numWin v _
        (by unfold ulookup_ctrl_idx; omega)]
  exact encodeReg_at _ _ _ i hi

/-! ## §2. Stage 1 — the generalized mod-N pass (nonzero initial accumulator).

`modNStepInv_step` is start-value-agnostic (it advances `ModNStepInv` from
ANY partial sum `s < N`), so the generalization only needs the fold replayed
from an arbitrary invariant state with `acc₀ < N`. -/

/-- **The generalized mod-N fold.**  From ANY state `f` satisfying the mod-N
    invariant with partial sum `acc₀ < N`, running the first `n ≤ numWin`
    mod-N window steps yields the invariant with partial sum
    `windowedLookupFold a N w (window w y) n acc₀`. -/
theorem modNStepInv_fold_acc (w bits a N numWin y acc₀ : Nat) (hw : 0 < w)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hacc : acc₀ < N)
    (f : Nat → Bool) (hf : ModNStepInv w bits numWin y acc₀ f) :
    ∀ n, n ≤ numWin →
      ModNStepInv w bits numWin y
        (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) n acc₀)
        (Gate.applyNat
          (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n) f) := by
  intro n
  induction n with
  | zero =>
    intro _
    show ModNStepInv w bits numWin y acc₀ (Gate.applyNat Gate.I f)
    rw [Gate.applyNat_I]
    exact hf
  | succ n ih =>
    intro hn
    have hsplit : windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) (n + 1)
        = Gate.seq
            (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
            (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n) := by
      unfold windowedModNMul
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq]
    have hfold_lt : WindowedArith.windowedLookupFold a N w
        (WindowedArith.window w y) n acc₀ < N := by
      cases n with
      | zero => exact hacc
      | succ m => exact Nat.mod_lt _ hN_pos
    exact modNStepInv_step w bits a N numWin y hw hN_pos hN2 n (by omega) _
      hfold_lt _ (ih (by omega))

/-- **The full generalized mod-N pass, invariant form.**  One complete
    `windowedModNMulCircuit` run from an invariant state with partial sum
    `acc₀ < N` re-establishes the invariant with partial sum
    `(acc₀ + a·y) mod N` — the form the in-place composition consumes. -/
theorem modNStepInv_full_pass (w bits a N numWin y acc₀ : Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hacc : acc₀ < N) (hy : y < 2 ^ (w * numWin))
    (f : Nat → Bool) (hf : ModNStepInv w bits numWin y acc₀ f) :
    ModNStepInv w bits numWin y ((acc₀ + a * y) % N)
      (Gate.applyNat (windowedModNMulCircuit w bits a N numWin) f) := by
  have hy' : y < (2 ^ w) ^ numWin := by
    rw [← pow_mul]
    exact hy
  have h := modNStepInv_fold_acc w bits a N numWin y acc₀ hw hN_pos hN2 hacc
    f hf numWin le_rfl
  rw [WindowedArith.windowedLookupFold_modProductAdd a N w numWin y acc₀
        hacc hy'] at h
  unfold windowedModNMulCircuit
  exact h

/-- **Stage 1 HEADLINE — generalized mod-N pass VALUE theorem.**  The
    per-window mod-N multiplier run from an invariant state whose accumulator
    holds partial sum `acc₀ < N` leaves `(acc₀ + a·y) mod N` in the
    accumulator. -/
theorem windowedModNMulCircuit_correct_acc (w bits a N numWin y acc₀ : Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hacc : acc₀ < N) (hy : y < 2 ^ (w * numWin))
    (f : Nat → Bool) (hf : ModNStepInv w bits numWin y acc₀ f) :
    decodeAccOf cuccaroAdder
        (Gate.applyNat (windowedModNMulCircuit w bits a N numWin) f)
        (1 + 2 * w) bits
      = (acc₀ + a * y) % N := by
  have hN_le : N ≤ 2 ^ bits := by omega
  have h := (modNStepInv_full_pass w bits a N numWin y acc₀ hw hN_pos hN2
    hacc hy f hf).2.2.2.2
  show decodeReg (cuccaroAdder.augendIdx (1 + 2 * w)) bits
      (Gate.applyNat (windowedModNMulCircuit w bits a N numWin) f)
    = (acc₀ + a * y) % N
  rw [decodeReg_eq_mod_of_testBit (cuccaroAdder.augendIdx (1 + 2 * w)) bits
        ((acc₀ + a * y) % N) _ (fun i hi => h i hi)]
  exact Nat.mod_eq_of_lt
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN_le)

/-! ## §3. The composable I/O shape: `ModNMulReady`.

The state shape the in-place mod-N multiplier both CONSUMES and PRODUCES
(the mod-N mirror of `MulReady`): off the Cuccaro block and the flag the
state IS `mulInputOf cuccaroAdder` (ctrl set, lookup zone clean, `y` in the
y-register), and the addend register, carry-in, comparison flag and
accumulator are all clean.  Output shape = input shape (with the new
y-value), so in-place mod-N multiplies compose. -/

/-- The in-place mod-N multiplier's input/output contract: a
    `mulInputOf cuccaroAdder`-shaped state with y-register value `y` and a
    CLEAN block (addend, carry-in, flag, accumulator). -/
def ModNMulReady (w bits numWin y : Nat) (f : Nat → Bool) : Prop :=
  (∀ p, ¬ inBlock (1 + 2 * w) (2 * bits + 1) p →
      p ≠ 1 + 2 * w + (2 * bits + 1) + numWin * w →
      f p = mulInputOf cuccaroAdder w bits numWin y p)
  ∧ (∀ i, i < bits → f (1 + 2 * w + 2 * i + 2) = false)
  ∧ f (1 + 2 * w) = false
  ∧ f (1 + 2 * w + (2 * bits + 1) + numWin * w) = false
  ∧ (∀ i, i < bits → f (1 + 2 * w + 2 * i + 1) = false)

/-- A `ModNMulReady` state satisfies the mod-N window-step invariant with
    partial sum 0. -/
theorem ModNMulReady.toStepInv {w bits numWin y : Nat} {f : Nat → Bool}
    (h : ModNMulReady w bits numWin y f) : ModNStepInv w bits numWin y 0 f :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    fun i hi => by rw [h.2.2.2.2 i hi, Nat.zero_testBit]⟩

/-- The clean encoded input is `ModNMulReady`. -/
theorem modNMulReady_mulInputOf (w bits numWin y : Nat) :
    ModNMulReady w bits numWin y (mulInputOf cuccaroAdder w bits numWin y) := by
  obtain ⟨hF, hD, hC, hG, hV⟩ := modNStepInv_init w bits numWin y
  exact ⟨hF, hD, hC, hG, fun i hi => by rw [hV i hi, Nat.zero_testBit]⟩

/-! ## §4. Stage 3 — HEADLINE: the in-place mod-N windowed multiplier.

    modNpass(a) ; acc↔y swap ; modNpass(N − ainv)

On a `ModNMulReady` state with y-value `y < N`:  pass 1 puts `(a·y) mod N`
in the accumulator (flag self-uncomputed); the swap moves it into the
y-register (leaving `y` in the accumulator — a valid mod-N partial sum since
`y < N`); pass 2 — the STAGE-1 GENERALIZED pass, initial accumulator `y`,
multiplier register `(a·y) mod N` — adds `(N − ainv)·((a·y) mod N)`, and
`y·(1 − ainv·a) ≡ 0 (mod N)` clears the accumulator. -/

/-- **The in-place mod-N windowed multiplier** by a constant `a` invertible
    mod `N` with inverse `ainv < N`. -/
def windowedModNMulInPlace (w bits a ainv N numWin : Nat) : Gate :=
  Gate.seq
    (Gate.seq (windowedModNMulCircuit w bits a N numWin)
      (accYSwap cuccaroAdder w bits))
    (windowedModNMulCircuit w bits (N - ainv) N numWin)

/-- **Stage 3 HEADLINE — in-place mod-N windowed multiplication, full state
    restoration.**  With `numWin·w = bits` (the y-register exactly matches
    the accumulator width), `0 < N`, `2·N ≤ 2^bits`, and `a·ainv ≡ 1 (mod N)`:
    the in-place mod-N multiplier maps any `ModNMulReady` state with y-value
    `y < N` to the `ModNMulReady` state with y-value `(a·y) mod N` —
    accumulator, addend register, carry-in AND comparison flag all returned
    CLEAN, everything off the y-register restored.  Output shape = input
    shape, so in-place mod-N multiplies compose: this is the Shor-weld entry
    point `y ← (a·y) mod N`. -/
theorem windowedModNMulInPlace_correct (w bits a ainv N numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < N) (hainv : ainv < N) (hinv : a * ainv % N = 1)
    (f : Nat → Bool) (hf : ModNMulReady w bits numWin y f) :
    ModNMulReady w bits numWin (a * y % N)
      (Gate.applyNat (windowedModNMulInPlace w bits a ainv N numWin) f) := by
  have hN_le : N ≤ 2 ^ bits := by omega
  have hpow : (2 : Nat) ^ (w * numWin) = 2 ^ bits := by
    rw [Nat.mul_comm w numWin, hbits]
  have hy1 : y < 2 ^ (w * numWin) := by
    rw [hpow]
    exact Nat.lt_of_lt_of_le hy hN_le
  have hay_lt : a * y % N < N := Nat.mod_lt _ hN_pos
  have hay_bits : a * y % N < 2 ^ (w * numWin) := by
    rw [hpow]
    exact Nat.lt_of_lt_of_le hay_lt hN_le
  -- Expose the three stages.
  unfold windowedModNMulInPlace
  simp only [Gate.applyNat_seq]
  set s1 : Nat → Bool :=
    Gate.applyNat (windowedModNMulCircuit w bits a N numWin) f with hs1def
  set s2 : Nat → Bool := Gate.applyNat (accYSwap cuccaroAdder w bits) s1
    with hs2def
  -- ── Pass 1: accumulator ← (a·y) mod N, flag self-uncomputed ────────────
  have h1 := modNStepInv_full_pass w bits a N numWin y 0 hw hN_pos hN2 hN_pos
    hy1 f hf.toStepInv
  rw [Nat.zero_add] at h1
  obtain ⟨h1F, h1D, h1C, h1G, h1V⟩ := h1
  rw [← hs1def] at h1F h1D h1C h1G h1V
  -- The y-register still holds the digits of `y` after pass 1.
  have h1y : ∀ i, i < bits → s1 (1 + 2 * w + (2 * bits + 1) + i) = y.testBit i := by
    intro i hi
    rw [h1F _ (by unfold inBlock; omega) (by omega)]
    exact mulInputOf_cuccaro_y_bit w bits numWin y i (by omega)
  -- ── The swap: accumulator ↔ y-register (flag untouched) ────────────────
  obtain ⟨hsw_acc, hsw_y, hsw_fr⟩ := accYSwap_apply cuccaroAdder w bits s1
    (fun i j _ _ h => cuccaroAdder_augendIdx_inj (1 + 2 * w) i j h)
  rw [← hs2def] at hsw_acc hsw_y hsw_fr
  -- Literal-position forms of the swap facts (definitional bridges).
  have hsw_acc' : ∀ i, i < bits →
      s2 (1 + 2 * w + 2 * i + 1) = s1 (1 + 2 * w + (2 * bits + 1) + i) :=
    fun i hi => hsw_acc i hi
  have hsw_y' : ∀ i, i < bits →
      s2 (1 + 2 * w + (2 * bits + 1) + i) = s1 (1 + 2 * w + 2 * i + 1) :=
    fun i hi => hsw_y i hi
  have hsw_fr' : ∀ p, (∀ i, i < bits →
      p ≠ 1 + 2 * w + 2 * i + 1 ∧ p ≠ 1 + 2 * w + (2 * bits + 1) + i) →
      s2 p = s1 p :=
    fun p hp => hsw_fr p (fun i hi => hp i hi)
  -- s2 is a mod-N invariant state for the SECOND pass: y-register value
  -- (a·y) mod N, partial sum (initial accumulator) y < N.
  have h2F : ∀ p, ¬ inBlock (1 + 2 * w) (2 * bits + 1) p →
      p ≠ 1 + 2 * w + (2 * bits + 1) + numWin * w →
      s2 p = mulInputOf cuccaroAdder w bits numWin (a * y % N) p := by
    intro p hpb hpf
    by_cases hpy : ∃ i, i < bits ∧ p = 1 + 2 * w + (2 * bits + 1) + i
    · obtain ⟨i, hi, rfl⟩ := hpy
      rw [hsw_y' i hi, h1V i hi,
          mulInputOf_cuccaro_y_bit w bits numWin (a * y % N) i (by omega)]
    · push Not at hpy
      have hp_out : p < 1 + 2 * w ∨ 1 + 2 * w + 2 * bits + 1 ≤ p := by
        unfold inBlock at hpb
        omega
      rw [hsw_fr' p (fun i hi => ⟨by omega, hpy i hi⟩), h1F p hpb hpf]
      by_cases hpc : p = ulookup_ctrl_idx
      · rw [hpc, mulInputOf_ctrl, mulInputOf_ctrl]
      · rcases hp_out with hlow | hhigh
        · rw [mulInputOf_low cuccaroAdder w bits numWin y p hpc (by omega),
              mulInputOf_low cuccaroAdder w bits numWin _ p hpc (by omega)]
        · have hphigh : 1 + 2 * w + (2 * bits + 1) + bits ≤ p := by
            by_contra hcon
            exact hpy (p - (1 + 2 * w + (2 * bits + 1))) (by omega) (by omega)
          rw [mulInputOf_cuccaro_encodeReg w bits numWin y p hpc,
              mulInputOf_cuccaro_encodeReg w bits numWin _ p hpc,
              encodeReg_high _ _ _ _ (by omega),
              encodeReg_high _ _ _ _ (by omega)]
  have h2D : ∀ i, i < bits → s2 (1 + 2 * w + 2 * i + 2) = false := by
    intro i hi
    rw [hsw_fr' _ (fun k hk => ⟨by omega, by omega⟩)]
    exact h1D i hi
  have h2C : s2 (1 + 2 * w) = false := by
    rw [hsw_fr' _ (fun k hk => ⟨by omega, by omega⟩)]
    exact h1C
  have h2G : s2 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hsw_fr' _ (fun k hk => ⟨by omega, by omega⟩)]
    exact h1G
  have h2V : ∀ i, i < bits → s2 (1 + 2 * w + 2 * i + 1) = y.testBit i := by
    intro i hi
    rw [hsw_acc' i hi]
    exact h1y i hi
  -- ── Pass 2: accumulator ← (y + (N − ainv)·((a·y) mod N)) mod N = 0 ─────
  have h3 := modNStepInv_full_pass w bits (N - ainv) N numWin (a * y % N) y
    hw hN_pos hN2 hy hay_bits s2 ⟨h2F, h2D, h2C, h2G, h2V⟩
  rw [mod_inv_cancel_identity a ainv N y hN_pos hy hainv hinv] at h3
  obtain ⟨h3F, h3D, h3C, h3G, h3V⟩ := h3
  exact ⟨h3F, h3D, h3C, h3G, fun i hi => by rw [h3V i hi, Nat.zero_testBit]⟩

/-- **Stage 3, decode form.**  After the in-place mod-N multiply, the
    y-register itself decodes to `(a·y) mod N` (the block is clean by
    `windowedModNMulInPlace_correct`). -/
theorem windowedModNMulInPlace_value (w bits a ainv N numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < N) (hainv : ainv < N) (hinv : a * ainv % N = 1)
    (f : Nat → Bool) (hf : ModNMulReady w bits numWin y f) :
    decodeReg (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits
        (Gate.applyNat (windowedModNMulInPlace w bits a ainv N numWin) f)
      = a * y % N := by
  have hN_le : N ≤ 2 ^ bits := by omega
  obtain ⟨hF, -, -, -, -⟩ := windowedModNMulInPlace_correct w bits a ainv N
    numWin y hw hbits hN_pos hN2 hy hainv hinv f hf
  have hbit : ∀ i, i < bits →
      Gate.applyNat (windowedModNMulInPlace w bits a ainv N numWin) f
          (1 + 2 * w + (2 * bits + 1) + i)
        = (a * y % N).testBit i := by
    intro i hi
    rw [hF _ (by unfold inBlock; omega) (by omega)]
    exact mulInputOf_cuccaro_y_bit w bits numWin (a * y % N) i (by omega)
  rw [decodeReg_eq_mod_of_testBit _ bits (a * y % N) _ (fun i hi => hbit i hi)]
  exact Nat.mod_eq_of_lt
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN_le)

/-- **Stage 3, clean-input instance.**  On the clean encoded input the
    in-place mod-N multiplier produces the `ModNMulReady` state with
    y-value `(a·y) mod N`. -/
theorem windowedModNMulInPlace_correct_clean (w bits a ainv N numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < N) (hainv : ainv < N) (hinv : a * ainv % N = 1) :
    ModNMulReady w bits numWin (a * y % N)
      (Gate.applyNat (windowedModNMulInPlace w bits a ainv N numWin)
        (mulInputOf cuccaroAdder w bits numWin y)) :=
  windowedModNMulInPlace_correct w bits a ainv N numWin y hw hbits hN_pos hN2
    hy hainv hinv _ (modNMulReady_mulInputOf w bits numWin y)

/-! ## §5. Stage 4 — pass-composition and the Shor-weld gate family.

Because Stage 3 returns the state to the `ModNMulReady` shape, in-place
mod-N multiplies compose by induction: `k` of them compute
`y ← (Π aₖ)·y mod N`.  The squared-power instance `aₖ = a^(2^k) mod N` is
the per-QPE-iterate gate family the Shor weld
(`EncodeRoundTripModMul.gate c` at `c = a^(2^i)`) consumes. -/

/-- Inverses lift to powers: `(a^k mod N)·(ainv^k mod N) ≡ 1 (mod N)`.
    (Local copy of `ModExp.mul_pow_mod_one`, kept private to avoid the
    cross-tree import.) -/
private theorem pow_inv_mod_one (a ainv N k : Nat) (hN1 : 1 < N)
    (hinv : a * ainv % N = 1) :
    (a ^ k % N) * (ainv ^ k % N) % N = 1 := by
  rw [← Nat.mul_mod, ← mul_pow, Nat.pow_mod, hinv]
  simp [Nat.mod_eq_of_lt hN1]

/-- The `n`-fold in-place mod-N multiply by the constants `as 0, …, as (n−1)`
    (with inverses `ainvs k`). -/
def windowedModNMulInPlaceSeq (w bits N numWin : Nat)
    (as ainvs : Nat → Nat) (n : Nat) : Gate :=
  (List.range n).foldl
    (fun g k =>
      Gate.seq g (windowedModNMulInPlace w bits (as k) (ainvs k) N numWin))
    Gate.I

/-- **Stage 4 HEADLINE — the in-place mod-N product chain.**  `n` in-place
    mod-N multiplies by invertible constants `as k` compute
    `y ← (Π_{k<n} as k)·y mod N`, returning to the `ModNMulReady` shape
    (clean accumulator/addend/carry/flag) after EVERY round. -/
theorem windowedModNMulInPlaceSeq_correct (w bits N numWin : Nat)
    (as ainvs : Nat → Nat) (y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hy : y < N)
    (f : Nat → Bool) (hf : ModNMulReady w bits numWin y f) :
    ∀ n, (∀ k, k < n → ainvs k < N ∧ as k * ainvs k % N = 1) →
      ModNMulReady w bits numWin ((∏ k ∈ Finset.range n, as k) * y % N)
        (Gate.applyNat (windowedModNMulInPlaceSeq w bits N numWin as ainvs n)
          f) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Finset.prod_range_zero, Nat.one_mul, Nat.mod_eq_of_lt hy]
    show ModNMulReady w bits numWin y (Gate.applyNat Gate.I f)
    rw [Gate.applyNat_I]
    exact hf
  | succ n ih =>
    intro hpairs
    have hsplit : windowedModNMulInPlaceSeq w bits N numWin as ainvs (n + 1)
        = Gate.seq (windowedModNMulInPlaceSeq w bits N numWin as ainvs n)
            (windowedModNMulInPlace w bits (as n) (ainvs n) N numWin) := by
      unfold windowedModNMulInPlaceSeq
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq]
    -- After `n` rounds: a `ModNMulReady` state with y-value (Π_{k<n} as k)·y.
    have ihn := ih (fun k hk => hpairs k (by omega))
    have hyn : (∏ k ∈ Finset.range n, as k) * y % N < N :=
      Nat.mod_lt _ hN_pos
    -- Round n+1: one more in-place mod-N multiply, by Stage 3.
    have hstep := windowedModNMulInPlace_correct w bits (as n) (ainvs n) N
      numWin ((∏ k ∈ Finset.range n, as k) * y % N) hw hbits hN_pos hN2 hyn
      (hpairs n (by omega)).1 (hpairs n (by omega)).2 _ ihn
    -- Fold the new factor into the running product.
    have hval : as n * ((∏ k ∈ Finset.range n, as k) * y % N) % N
        = (∏ k ∈ Finset.range (n + 1), as k) * y % N := by
      rw [Finset.prod_range_succ, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
          show as n * ((∏ k ∈ Finset.range n, as k) * y)
              = (∏ k ∈ Finset.range n, as k) * as n * y from by ring]
    rw [← hval]
    exact hstep

/-- **The Shor-weld gate**: in-place multiply-by-`c` mod `N` at window size
    `w` (`cinv` the mod-N inverse of `c`).  Thin wrapper so the weld
    (`EncodeRoundTripModMul.gate`) can take `fun c => windowedModNMulGate
    w bits N numWin c (cinv c)` directly. -/
def windowedModNMulGate (w bits N numWin c cinv : Nat) : Gate :=
  windowedModNMulInPlace w bits c cinv N numWin

/-- The weld gate realizes `y ← (c·y) mod N` with full state restoration. -/
theorem windowedModNMulGate_correct (w bits N numWin c cinv y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < N) (hcinv : cinv < N) (hinv : c * cinv % N = 1)
    (f : Nat → Bool) (hf : ModNMulReady w bits numWin y f) :
    ModNMulReady w bits numWin (c * y % N)
      (Gate.applyNat (windowedModNMulGate w bits N numWin c cinv) f) :=
  windowedModNMulInPlace_correct w bits c cinv N numWin y hw hbits hN_pos hN2
    hy hcinv hinv f hf

/-- **The squared-power gate family** — QPE iterate `k` of Shor:
    `windowedModNMulGate` at `c = a^(2^k) mod N`, `cinv = ainv^(2^k) mod N`
    realizes `y ← a^(2^k)·y mod N` (the raw-constant value the weld's
    round-trip at `c = a^(2^k)` requires), needing only the BASE inverse
    `a·ainv ≡ 1 (mod N)`. -/
theorem windowedModNMulGate_squaredPower (w bits N numWin a ainv k y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < N) (hinv : a * ainv % N = 1)
    (f : Nat → Bool) (hf : ModNMulReady w bits numWin y f) :
    ModNMulReady w bits numWin (a ^ 2 ^ k * y % N)
      (Gate.applyNat
        (windowedModNMulGate w bits N numWin (a ^ 2 ^ k % N)
          (ainv ^ 2 ^ k % N)) f) := by
  have hN_pos : 0 < N := by omega
  have hval : a ^ 2 ^ k * y % N = a ^ 2 ^ k % N * y % N := by
    conv_lhs => rw [Nat.mul_mod, Nat.mod_eq_of_lt hy]
  rw [hval]
  exact windowedModNMulGate_correct w bits N numWin (a ^ 2 ^ k % N)
    (ainv ^ 2 ^ k % N) y hw hbits hN_pos hN2 hy (Nat.mod_lt _ hN_pos)
    (pow_inv_mod_one a ainv N (2 ^ k) hN1 hinv) f hf

/-! ## §6. Toffoli/T-counts (kernel-clean, exact).

The swap is T-free (three CX cascades), so the in-place mod-N multiply costs
exactly two mod-N passes: `2·numWin·(56·w·2^w + 56·bits)` T. -/

private theorem tcount_cxCascade (ctrl tgt : Nat → Nat) (n : Nat) :
    tcount (cxCascade ctrl tgt n) = 0 := by
  rw [cxCascade, tcount_foldl_seq_const
        (fun i => Gate.CX (ctrl i) (tgt i)) 0 (fun _ => rfl)]
  simp [tcount]

/-- The acc↔y swap is Toffoli-free. -/
theorem tcount_accYSwap (A : Adder) (w bits : Nat) :
    tcount (accYSwap A w bits) = 0 := by
  show tcount (cxCascade (A.augendIdx (1 + 2 * w))
        (fun i => 1 + 2 * w + A.span bits + i) bits)
      + tcount (cxCascade (fun i => 1 + 2 * w + A.span bits + i)
        (A.augendIdx (1 + 2 * w)) bits)
      + tcount (cxCascade (A.augendIdx (1 + 2 * w))
        (fun i => 1 + 2 * w + A.span bits + i) bits) = 0
  rw [tcount_cxCascade, tcount_cxCascade]

/-- **In-place mod-N multiply T-count**: two mod-N passes plus the T-free
    swap, `2·numWin·(56·w·2^w + 56·bits)`. -/
theorem tcount_windowedModNMulInPlace (w bits a ainv N numWin : Nat) :
    tcount (windowedModNMulInPlace w bits a ainv N numWin)
      = 2 * (numWin * (56 * w * 2 ^ w + 56 * bits)) := by
  show tcount (windowedModNMulCircuit w bits a N numWin)
      + tcount (accYSwap cuccaroAdder w bits)
      + tcount (windowedModNMulCircuit w bits (N - ainv) N numWin)
      = 2 * (numWin * (56 * w * 2 ^ w + 56 * bits))
  rw [tcount_windowedModNMulCircuit, tcount_accYSwap,
      tcount_windowedModNMulCircuit]
  ring

/-- The weld gate's T-count (same circuit, weld-facing name). -/
theorem tcount_windowedModNMulGate (w bits N numWin c cinv : Nat) :
    tcount (windowedModNMulGate w bits N numWin c cinv)
      = 2 * (numWin * (56 * w * 2 ^ w + 56 * bits)) :=
  tcount_windowedModNMulInPlace w bits c cinv N numWin

/-- **The k-fold chain T-count**: `n` in-place mod-N multiplies,
    `n · 2·numWin·(56·w·2^w + 56·bits)`. -/
theorem tcount_windowedModNMulInPlaceSeq (w bits N numWin : Nat)
    (as ainvs : Nat → Nat) (n : Nat) :
    tcount (windowedModNMulInPlaceSeq w bits N numWin as ainvs n)
      = n * (2 * (numWin * (56 * w * 2 ^ w + 56 * bits))) := by
  rw [windowedModNMulInPlaceSeq,
      tcount_foldl_seq_const
        (fun k => windowedModNMulInPlace w bits (as k) (ainvs k) N numWin)
        (2 * (numWin * (56 * w * 2 ^ w + 56 * bits)))
        (fun k => tcount_windowedModNMulInPlace w bits (as k) (ainvs k) N
          numWin)]
  simp [tcount, List.length_range]

end FormalRV.Shor.WindowedCircuit
