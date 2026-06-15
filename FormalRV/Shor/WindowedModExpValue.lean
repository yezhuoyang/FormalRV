/-
  FormalRV.Shor.WindowedModExpValue — the SINGLE end-to-end VALUE theorem for
  windowed modular exponentiation: ONE verified circuit object whose semantics
  is `result = a^e mod N` (classical exponent), composing the proven windowed
  in-place mod-N machinery.

  ## What this file delivers (the audit cites ONE theorem)

  `windowedModNExpInPlace` is the k-fold in-place chain over
  `windowedModNMulInPlace` (`Arithmetic/Windowed/WindowedModNInPlace`) with the
  per-exponent-window constants

      aₖ = a ^ (windowₖ(e) · (2^wE)^k)  mod N

  the squared-power factors of `a^e` over the base-`2^wE` digit expansion of a
  CLASSICAL exponent `e`.  On a `ModNMulReady` state with y-value `y < N` it
  computes (HEADLINE `windowedModNExpInPlace_correct`):

      y ← (a^e · y) mod N      — full state restoration, mod N (not mod 2^bits)

  and, instantiated from the clean encoded input with `y = 1`
  (`windowedModNExp_value`):

      result-register decodes to  a^e mod N      — THE modexp value.

  This is the mod-N analogue of `WindowedInPlace.windowedExpInPlace_correct`
  (which is honestly mod `2^bits`); here the modulus is the true `N`, via the
  per-window mod-N multiplier of `WindowedModN`/`WindowedModNInPlace`.

  ## Scope (read carefully)

  * **mod N**, not mod `2^bits` — the true modular-exponentiation value.
  * **CLASSICAL exponent** `e` (a fixed `Nat`).  The QUANTUM-selected exponent
    (windows read from an exponent register, the per-basis-state engine QPE
    consumes) is the documented next step `WindowedExpInPlaceQ` (proven there
    for mod `2^bits`); it is NOT re-derived mod N here.
  * **standalone** in-place chain (single accumulator/y-register), not the
    `EncodeRoundTripModMul` family object.

  ## Relation to the Shor-bound object

  The family-level Shor success bound lives in
  `Shor.WindowedModNShor.windowedModNMul_shor_correct`, built from the SAME
  `windowedModNMulInPlace` gate via `windowedModNMultiplier`'s
  `VerifiedModMulFamily` (QPE iterate `i` multiplies by `a^(2^i) mod N`,
  `windowedModNMulGate_squaredPower`).  THIS file instead composes that gate
  CLASSICALLY into a single `a^e mod N` value — the standalone arithmetic
  statement "the windowed modexp computes the right value", complementary to
  the per-iterate family object the bound consumes.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Windowed.WindowedModNInPlace

namespace FormalRV.Shor.WindowedModExpValue

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit

/-! ## §1. The classical-exponent windowing constants.

`a^e mod N` factors over the base-`2^wE` digit expansion of `e` into the
per-exponent-window squared-power factors `a^(windowₖ(e)·(2^wE)^k)` (the
multiplicative analogue `WindowedArith.windowed_exp`).  We pre-reduce each
factor mod `N` so the constants land directly in the `windowed_exp_modProduct`
shape, and pair each with the matching reduced inverse power. -/

/-- The `k`-th per-exponent-window multiplier of `a^e`, reduced mod `N`:
    `a^(windowₖ(e)·(2^wE)^k) mod N`. -/
def expConst (a N wE e k : Nat) : Nat :=
  a ^ (WindowedArith.window wE e k * (2 ^ wE) ^ k) % N

/-- The matching reduced inverse: `ainv^(windowₖ(e)·(2^wE)^k) mod N`. -/
def expConstInv (ainv N wE e k : Nat) : Nat :=
  ainv ^ (WindowedArith.window wE e k * (2 ^ wE) ^ k) % N

/-- **Inverse pairing of the windowing constants.**  Given a base inverse
    `a·ainv ≡ 1 (mod N)`, the reduced factor `expConst` and its reduced inverse
    `expConstInv` are mod-`N` inverses at EVERY window — the per-round
    invertibility witness `windowedModNMulInPlaceSeq_correct` needs. -/
theorem expConst_inv_pairing (a ainv N wE e k : Nat) (hN1 : 1 < N)
    (hinv : a * ainv % N = 1) :
    expConst a N wE e k * expConstInv ainv N wE e k % N = 1 := by
  unfold expConst expConstInv
  rw [← Nat.mul_mod, ← mul_pow, Nat.pow_mod, hinv, one_pow,
      Nat.one_mod_eq_one.mpr (by omega : N ≠ 1)]

/-! ## §2. The product collapse: the windowing constants multiply to `a^e mod N`.

The chain of `nE` in-place multiplies multiplies `y` by `∏ₖ expConstₖ` mod `N`;
this product collapses to `a^e mod N` by the multiplicative windowed expansion
`WindowedArith.windowed_exp_modProduct`. -/

/-- **Product collapse.**  For `e < (2^wE)^nE`, multiplying `y` by the product
    of all per-window constants `expConst a N wE e k` mod `N` equals
    multiplying by `a^e` mod `N`. -/
theorem expConst_prod_collapse (a N wE e nE y : Nat)
    (he : e < (2 ^ wE) ^ nE) :
    (∏ k ∈ Finset.range nE, expConst a N wE e k) * y % N = a ^ e * y % N := by
  -- Pull `y` out of the mod, collapse the product to `a^e mod N`, push `y` back.
  rw [Nat.mul_mod, Nat.mul_mod (a ^ e)]
  congr 1
  congr 1
  -- (∏ expConst) % N = a^e % N : exactly windowed_exp_modProduct after unfolding.
  show (∏ k ∈ Finset.range nE,
      a ^ (WindowedArith.window wE e k * (2 ^ wE) ^ k) % N) % N = a ^ e % N
  exact WindowedArith.windowed_exp_modProduct wE nE a N e he

/-! ## §3. THE HEADLINE: in-place windowed modular exponentiation, mod N.

`windowedModNExpInPlace` is the `nE`-fold in-place mod-N multiply by the
per-exponent-window constants `expConst a N wE e k`, returning to the
`ModNMulReady` shape after every round (Stage-4 composition of
`WindowedModNInPlace`).  Its value is `y ← (a^e · y) mod N`. -/

/-- **The in-place windowed modular exponentiation, CLASSICAL exponent.**
    One in-place mod-N multiply per exponent window `k < nE`, by the constant
    `expConst a N wE e k = a^(windowₖ(e)·(2^wE)^k) mod N`. -/
def windowedModNExpInPlace (w bits numWin N wE nE a ainv e : Nat) : Gate :=
  windowedModNMulInPlaceSeq w bits N numWin
    (expConst a N wE e) (expConstInv ainv N wE e) nE

/-- **THE END-TO-END VALUE THEOREM — windowed modular exponentiation mod N
    (classical exponent).**  For `e < (2^wE)^nE`, the per-window in-place
    mod-N multiply chain maps any `ModNMulReady` state with y-value `y < N`
    to the `ModNMulReady` state with y-value `(a^e · y) mod N`: full state
    restoration (accumulator, addend, carry-in, comparison flag all clean),
    the windowing constants multiplied out to `a^e` by the base-`2^wE` digit
    expansion of `e`, all reduced mod the TRUE modulus `N`.

    This is the mod-N analogue of
    `WindowedInPlace.windowedExpInPlace_correct` (which computes mod `2^bits`).
    The composition reuses `ModNMulReady` restoration (`windowedModNMulInPlace`
    returns to the ready shape after each multiply) and the product collapse
    `∏ a^(windowₖ(e)·(2^wE)^k) ≡ a^e (mod N)`. -/
theorem windowedModNExpInPlace_correct (w bits numWin N wE nE a ainv e y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hy : y < N)
    (he : e < (2 ^ wE) ^ nE) (hinv : a * ainv % N = 1)
    (f : Nat → Bool) (hf : ModNMulReady w bits numWin y f) :
    ModNMulReady w bits numWin (a ^ e * y % N)
      (Gate.applyNat (windowedModNExpInPlace w bits numWin N wE nE a ainv e) f) := by
  have hN_pos : 0 < N := by omega
  -- The proven chain: y ← (∏ₖ expConstₖ)·y mod N, ModNMulReady throughout.
  have h := windowedModNMulInPlaceSeq_correct w bits N numWin
    (expConst a N wE e) (expConstInv ainv N wE e) y hw hbits hN_pos hN2 hy f hf nE
    (fun k _ => ⟨Nat.mod_lt _ hN_pos, expConst_inv_pairing a ainv N wE e k hN1 hinv⟩)
  -- Collapse the product of windowing constants to a^e mod N.
  rw [expConst_prod_collapse a N wE e nE y he] at h
  exact h

/-! ## §4. Decode-form value corollary: the result register holds `a^e mod N`.

A `ModNMulReady` state with y-value `v < N` has its y-register decode to `v`
(the block is clean, so off-block the state IS `mulInputOf` encoding `v`).
Reading this off the output of the modexp chain from the clean encoded input
with `y = 1` gives the standalone modexp value `a^e mod N`. -/

/-- The y-register of any `ModNMulReady` state decodes to its y-value `v`
    (given `v < N ≤ 2^bits`, so `v` fits). -/
theorem modNMulReady_decode (w bits numWin v N : Nat) (f : Nat → Bool)
    (hbits : numWin * w = bits) (hN_le : N ≤ 2 ^ bits) (hv : v < N)
    (hf : ModNMulReady w bits numWin v f) :
    decodeReg (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits f = v := by
  obtain ⟨hF, -, -, -, -⟩ := hf
  have hbit : ∀ i, i < bits →
      f (1 + 2 * w + (2 * bits + 1) + i) = v.testBit i := by
    intro i hi
    rw [hF _ (by unfold inBlock; omega) (by omega),
        mulInputOf_eq_encodeReg cuccaroAdder w bits numWin v _
          (by unfold ulookup_ctrl_idx; omega)]
    show encodeReg (1 + 2 * w + cuccaroAdder.span bits) (numWin * w) v _ = _
    rw [show cuccaroAdder.span bits = 2 * bits + 1 from rfl]
    exact encodeReg_at _ _ _ i (by omega)
  rw [decodeReg_eq_mod_of_testBit _ bits v _ (fun i hi => hbit i hi)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hv hN_le)

/-- **THE STANDALONE MODEXP VALUE — `result = a^e mod N`.**  Run on the clean
    encoded input with `y = 1`, the in-place windowed modular-exponentiation
    chain leaves `a^e mod N` in the y-(result-)register, with all ancillas
    returned clean.  This is the single end-to-end value object the audit can
    cite for "the windowed modexp arithmetic computes the right value", mod the
    TRUE modulus `N`. -/
theorem windowedModNExp_value (w bits numWin N wE nE a ainv e : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (he : e < (2 ^ wE) ^ nE) (hinv : a * ainv % N = 1) :
    decodeReg (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits
        (Gate.applyNat (windowedModNExpInPlace w bits numWin N wE nE a ainv e)
          (mulInputOf cuccaroAdder w bits numWin 1))
      = a ^ e % N := by
  have hN_pos : 0 < N := by omega
  have hN_le : N ≤ 2 ^ bits := by omega
  -- The chain on the clean `y = 1` input lands `a^e · 1 mod N = a^e mod N`.
  have h := windowedModNExpInPlace_correct w bits numWin N wE nE a ainv e 1
    hw hbits hN1 hN2 hN1 he hinv _ (modNMulReady_mulInputOf w bits numWin 1)
  rw [Nat.mul_one] at h
  -- Read the value off the (clean) result register.
  have hval_lt : a ^ e % N < N := Nat.mod_lt _ hN_pos
  exact modNMulReady_decode w bits numWin (a ^ e % N) N _ hbits hN_le hval_lt h

end FormalRV.Shor.WindowedModExpValue
