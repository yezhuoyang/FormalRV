/-
  FormalRV.BQAlgo.ModularAdder — first building block of the
  modular-addition layer, built on top of the patched Gidney adder
  primitive proved in `BQAlgo/RippleCarryAdder.lean`.

  This module's deliverables this iteration:
  1. Boolean-level specs for modular addition.
  2. A clean wrapper proving the patched Gidney adder implements
     `(x + c) mod 2^bits` on the target register.

  The general modular-add-constant `(x + c) mod N` for arbitrary N
  is NOT yet implemented — it requires comparator/subtractor/
  conditional-add infrastructure that doesn't exist in the project
  yet (grep for `compare`, `subtract`, `less`, `flag`, `overflow`,
  `conditional`, `controlled` in `BQAlgo/*` returns no matches).

  See the "Modular reduction by arbitrary N — missing pieces"
  section below for the precise list of primitives that the next
  tick needs to add.
-/
import FormalRV.Arithmetic.RippleCarryAdder
import Mathlib.Data.Nat.Bitwise

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Boolean-level specifications -/

/-- Spec for modular addition by a constant under arbitrary modulus `N`. -/
def modAddConstSpec (N c x : Nat) : Nat := (x + c) % N

/-- Spec specialized to `N = 2^bits` (the case the patched Gidney
adder implements natively without any extra circuitry). -/
def addConstPow2Spec (bits c x : Nat) : Nat := (x + c) % 2^bits

/-! ## Power-of-2 modular adder (the easy case)

The patched Gidney adder implements `(a + b) mod 2^bits` in the
target register when applied to `adder_input_F bits a b`.  With
`a = c` (constant in the read register) and `b = x` (data in the
target register), the output target register decodes to
`(x + c) mod 2^bits`.

This is just a renaming wrapper around
`gidney_adder_patched_target_decode` (in `RippleCarryAdder.lean`),
exposed under a name the modular-multiplication layer can call
directly. -/

/-- **The patched Gidney adder implements `(x + c) mod 2^bits`.**
With the constant `c` placed in the read register and the data `x`
placed in the target register, applying the patched full faithful
no-measurement Gidney adder writes `(x + c) mod 2^bits` into the
target register. -/
theorem patched_adder_add_const_pow2
    (bits c x : Nat) (hbits : 2 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits) :
    gidney_target_val bits
      (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
        (adder_input_F bits c x))
    = addConstPow2Spec bits c x := by
  unfold addConstPow2Spec
  rw [Nat.add_comm x c]
  exact gidney_adder_patched_target_decode bits c x hbits hc hx

/-- **Bundled `(x + c) mod 2^bits` primitive.**  Combines the
power-of-2 modular-addition spec, the patched-adder WellTyped, the
read-register preservation (constant `c` survives), and the carry
clearing (workspace zeroed) — the single theorem a modular-
multiplication layer should call when adding a constant modulo
`2^bits`. -/
theorem patched_adder_add_const_pow2_bundled
    (bits c x : Nat) (hbits : 2 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits) :
    Gate.WellTyped (adder_n_qubits bits)
      (gidney_adder_full_faithful_no_measurement_patched bits)
    ∧ gidney_target_val bits
        (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits c x))
      = addConstPow2Spec bits c x
    ∧ (∀ i, i < bits →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits c x) (read_idx i) = c.testBit i)
    ∧ (∀ i, i < bits →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits c x) (carry_idx i) = false) := by
  obtain ⟨hwt, _, hr, hc_clear⟩ :=
    gidney_adder_patched_primitive bits c x hbits hc hx
  exact ⟨hwt, patched_adder_add_const_pow2 bits c x hbits hc hx, hr, hc_clear⟩

/-! ## Modular reduction by arbitrary N — missing pieces

To implement `(x + c) mod N` for general `N` (the actual modular
adder needed by modular multiplication), the standard construction
requires:

1. **Constant addition over `n+1` bits** (room for carry-out).  Use
   `gidney_adder_full_faithful_no_measurement_patched (bits + 1)` to
   compute `t := x + c` with a "free" overflow bit in the target.

2. **Constant subtraction**: a gate `sub_const_gate N` that computes
   `t := t - N` in two's complement, leaving an overflow/underflow
   flag in a dedicated ancilla bit.  Missing.

3. **Comparator / sign-bit extraction**: detect whether `t ≥ N` by
   checking the borrow-out of step 2.  Missing.

4. **Controlled add-back of `N`**: a CCX-controlled version of step 1
   that re-adds `N` when the sign bit indicates underflow.  Missing.

5. **Uncompute the comparison flag** by re-comparing `t` against `N`
   (or by some other reversible-flag-clearing scheme).  Missing.

None of these primitives currently exist in `BQAlgo/*`.  Building
each one is itself a multi-step task analogous to the patched-Gidney-
adder work just completed.  Estimated scope: ~3-5 ticks of
infrastructure work (one tick each per missing primitive plus one
tick to compose them).

The next concrete sub-target is `sub_const_gate` — the reversible
constant-subtraction gate.  The simplest construction reuses the
patched Gidney adder via `x - N = x + (2^bits - N)`, treating the
subtraction as addition of the two's-complement representation of
`-N` (mod `2^bits`).  That reduces the problem to:

  given the patched adder for `(x + c') mod 2^bits` (where `c' = 2^bits - N`),
  prove that the result satisfies the borrow-flag interpretation that
  comparator + conditional add-back will need.

This is a clean follow-up tick.

The `patched_adder_add_const_pow2_bundled` primitive above is the
key building block — every subsequent step reuses it. -/

/-! ## Wraparound subtract-constant primitive

The simplest reversible subtraction: compute `x + (2^bits - N) mod 2^bits`
by feeding the constant `2^bits - N` into the read register of the
patched Gidney adder.  This is reversible (just the adder), takes
no extra ancillas, and lays the foundation for the comparator
(`x < N` iff this subtraction underflows).

**Semantic caveat**: Lean's `Nat` subtraction saturates at zero, so
the canonical spec is stated as `(x + (2^bits - N)) % 2^bits`, NOT
`(x - N) % 2^bits` (which would silently truncate the underflow
case `x < N` to zero rather than wrapping).  Split-case lemmas
below recover the two natural arithmetic specializations under the
appropriate side conditions. -/

/-- Wraparound spec for subtraction by `N` modulo `2^bits`. -/
def subConstPow2Spec (bits N x : Nat) : Nat := (x + (2^bits - N)) % 2^bits

/-- **The patched Gidney adder with `read = 2^bits - N` implements
the wraparound subtraction**.  For `0 < N ≤ 2^bits` and `x < 2^bits`,
applying the patched adder to `adder_input_F bits (2^bits - N) x`
decodes the target register to `(x + (2^bits - N)) mod 2^bits`. -/
theorem patched_adder_sub_const_pow2
    (bits N x : Nat) (hbits : 2 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    gidney_target_val bits
      (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
        (adder_input_F bits (2^bits - N) x))
    = subConstPow2Spec bits N x := by
  unfold subConstPow2Spec
  have h_c : 2^bits - N < 2^bits := by
    have h2pos : 0 < 2^bits := Nat.two_pow_pos bits
    omega
  exact patched_adder_add_const_pow2 bits (2^bits - N) x hbits h_c hx

/-! ## Arithmetic split-case lemmas

These recover the two natural arithmetic specializations of
`subConstPow2Spec`:

* When `N ≤ x` (no underflow), the wraparound result equals the
  ordinary Nat subtraction `x - N`.
* When `x < N` (underflow), the wraparound result equals
  `x + 2^bits - N` (a value in `[2^bits - N, 2^bits - 1]`).

Together they characterize the subtraction modulo `2^bits` without
ever using saturated Nat subtraction. -/

/-- No-underflow case: `N ≤ x` ⇒ `subConstPow2Spec bits N x = x - N`. -/
theorem subConstPow2Spec_of_le
    (bits N x : Nat) (hN : N ≤ 2^bits) (hx : x < 2^bits) (hle : N ≤ x) :
    subConstPow2Spec bits N x = x - N := by
  unfold subConstPow2Spec
  have h_eq : x + (2^bits - N) = (x - N) + 2^bits := by omega
  rw [h_eq, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- Underflow case: `x < N` ⇒ `subConstPow2Spec bits N x = x + 2^bits - N`. -/
theorem subConstPow2Spec_of_lt
    (bits N x : Nat) (hN : N ≤ 2^bits) (hx_lt : x < N) :
    subConstPow2Spec bits N x = x + 2^bits - N := by
  unfold subConstPow2Spec
  have h2pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_lt : x + (2^bits - N) < 2^bits := by omega
  rw [Nat.mod_eq_of_lt h_lt]
  omega

/-! ## Underflow/borrow flag — missing infrastructure

The natural way to detect underflow (i.e., whether `x < N` at the
input) is to expose a "borrow flag" bit in the output.  In a
standard reversible subtractor this is the carry-out of the
high bit, which would naturally live at position `carry_idx bits`
(= `3*bits + 2`) — but `gidney_adder_full_faithful_no_measurement_patched bits`
operates on `adder_n_qubits bits = 3*bits + 2` qubits, indexed
`0..3*bits + 1`, and **does not include** position `carry_idx bits`.
Additionally, the patch's carry-clearing zeroes all carries that
ARE in range, removing the candidate flag from the in-range carries
as well.

To extract the borrow flag we need ONE of:

1. **Widen the adder** to `bits + 1` bits.  The high bit of the
   wider target register would directly encode the borrow (and the
   spec becomes `(x + (2^bits - N))` without the mod — the high bit
   is the wraparound indicator).  Requires re-instantiating the
   patched-adder primitive at width `bits + 1`, with the "extra"
   read bit forced to zero.  Two of the existing free qubit slots
   (positions `3*bits, 3*bits + 1`) already provide r[bits] and
   t[bits], so this only requires extending the adder definition,
   not allocating more qubits.

2. **Add a separate comparison circuit**: after the subtraction,
   compare `target` to `x` (or equivalently check the high bit of
   `target` under a specific encoding).  This introduces a new gate
   primitive — at minimum a controlled-CX cascade that XORs an
   ancilla flag based on the comparison result.  Then the flag
   needs to be reversibly uncomputed before reuse.

3. **Hand-craft a borrow-flag-aware variant** of the Gidney adder
   itself, where one of the existing ancillas is repurposed as the
   borrow output rather than being cleared by the patch.  Departs
   from the proved patched-adder primitive.

The cleanest path (lowest risk, maximum reuse) is **option 1**: a
`(bits+1)`-bit version of the patched-adder primitive applied to a
zero-padded input.  The borrow is then literally `target_val
(bits+1) (...) ≥ 2^bits`, or equivalently the function
`gidney_target_val_high_bit (bits+1) (...)`.

This is the next concrete sub-target for the modular-addition layer.
For this iteration, the wraparound subtraction primitive
(`patched_adder_sub_const_pow2` + split-case lemmas) is complete
under the existing infrastructure. -/

/-! ## Widened subtraction with borrow flag extraction

The "underflow flag" / "comparison flag" / "borrow bit" is the
canonical missing piece between wraparound subtraction and the full
modular adder.  Following the path noted above, we instantiate the
patched Gidney adder at width `bits + 1` and prove that the high
target bit (bit at position `bits`) is exactly the comparison flag
`decide (x < N)`. -/

/-- Wraparound-subtraction spec at widened bit-count `bits + 1`. -/
def subConstPow2WideSpec (bits N x : Nat) : Nat :=
  (x + (2^(bits + 1) - N)) % 2^(bits + 1)

/-- Arithmetic high-bit lemma, no-underflow case: when `N ≤ x` the
widened result equals `x - N`, which fits in `bits` bits, so bit
`bits` is `false`. -/
theorem subConstPow2WideSpec_high_bit_of_le
    (bits N x : Nat) (hN : N ≤ 2^bits) (hx : x < 2^bits) (hle : N ≤ x) :
    (subConstPow2WideSpec bits N x).testBit bits = false := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_eq : subConstPow2WideSpec bits N x = x - N := by
    unfold subConstPow2WideSpec
    have h_eq2 : x + (2^(bits + 1) - N) = (x - N) + 2^(bits + 1) := by omega
    rw [h_eq2, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h_eq]
  exact Nat.testBit_lt_two_pow (by omega)

/-- Arithmetic high-bit lemma, underflow case: when `x < N ≤ 2^bits`
the widened result lies in `[2^bits, 2^(bits+1))`, so bit `bits` is `true`. -/
theorem subConstPow2WideSpec_high_bit_of_lt
    (bits N x : Nat) (hN : N ≤ 2^bits) (hx_lt : x < N) :
    (subConstPow2WideSpec bits N x).testBit bits = true := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_2pos : 0 < 2^(bits + 1) := Nat.two_pow_pos (bits + 1)
  have h_eq : subConstPow2WideSpec bits N x = x + 2^(bits+1) - N := by
    unfold subConstPow2WideSpec
    have h_lt : x + (2^(bits+1) - N) < 2^(bits+1) := by omega
    rw [Nat.mod_eq_of_lt h_lt]
    omega
  rw [h_eq]
  have h_lo : 2^bits ≤ x + 2^(bits+1) - N := by omega
  have h_hi : x + 2^(bits+1) - N < 2^(bits + 1) := by omega
  exact Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h_lo h_hi

/-- **Main high-bit theorem**: bit `bits` of the widened-subtraction
result is exactly the comparison flag `decide (x < N)`. -/
theorem subConstPow2WideSpec_high_bit
    (bits N x : Nat) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    (subConstPow2WideSpec bits N x).testBit bits = decide (x < N) := by
  by_cases h : x < N
  · rw [decide_eq_true h]
    exact subConstPow2WideSpec_high_bit_of_lt bits N x hN h
  · rw [decide_eq_false (by omega)]
    exact subConstPow2WideSpec_high_bit_of_le bits N x hN hx (by omega)

/-- **Gate-level underflow flag theorem** (Deliverable C).
Instantiating the patched Gidney adder at width `bits + 1` with
`read = 2^(bits + 1) - N`, the target bit at position `bits` is
exactly `decide (x < N)`. -/
theorem patched_adder_sub_const_underflow_flag
    (bits N x : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.applyNat
      (gidney_adder_full_faithful_no_measurement_patched (bits + 1))
      (adder_input_F (bits + 1) (2^(bits + 1) - N) x)
      (target_idx bits)
    = decide (x < N) := by
  have h_hb : 2 ≤ bits + 1 := by omega
  have h_2pos : 0 < 2^(bits + 1) := Nat.two_pow_pos (bits + 1)
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_a : 2^(bits + 1) - N < 2^(bits + 1) := by omega
  have h_b : x < 2^(bits + 1) := by omega
  obtain ⟨_, ht, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                          (bits + 1) (2^(bits + 1) - N) x h_hb h_a h_b
  have h := ht bits (by omega)
  rw [h]
  -- Goal: ((2^(bits+1) - N) + x).testBit bits = decide (x < N)
  have h_mod_eq : (((2^(bits+1) - N) + x) % 2^(bits+1)).testBit bits
                  = ((2^(bits+1) - N) + x).testBit bits := by
    rw [Nat.testBit_mod_two_pow]
    simp [show bits < bits + 1 from by omega]
  rw [← h_mod_eq]
  -- Now: testBit bits of the modded value
  rw [show (((2^(bits+1) - N) + x) % 2^(bits+1))
        = subConstPow2WideSpec bits N x from by
        unfold subConstPow2WideSpec; congr 1; omega]
  exact subConstPow2WideSpec_high_bit bits N x hN hx

/-- **Helper**: bit `i` of `y + 2^n` equals bit `i` of `y` when `i < n`
(adding a power of 2 at position `n` doesn't affect lower bits). -/
private theorem testBit_add_two_pow_below
    (y i n : Nat) (h : i < n) :
    (y + 2^n).testBit i = y.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  congr 1
  have h_pow : (2:Nat)^n = 2^i * 2^(n - i) := by
    rw [← pow_add]; congr 1; omega
  rw [h_pow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i)]
  have h_ni : 0 < n - i := by omega
  have h_2pow_even : (2:Nat)^(n - i) % 2 = 0 := by
    have h_split : n - i = (n - i - 1) + 1 := by omega
    rw [h_split, pow_succ]
    exact Nat.mul_mod_left (2^(n - i - 1)) 2
  rw [Nat.add_mod, h_2pow_even, Nat.add_zero, Nat.mod_mod]

/-- **Gate-level low-bits theorem** (Deliverable D).  At the widened
adder, the lower `bits` target positions decode to the bits of
`subConstPow2Spec bits N x` — i.e., they hold the wraparound
subtraction value (mod `2^bits`) just as the narrow adder would. -/
theorem patched_adder_sub_const_low_bits
    (bits N x i : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < 2^bits) (hi : i < bits) :
    Gate.applyNat
      (gidney_adder_full_faithful_no_measurement_patched (bits + 1))
      (adder_input_F (bits + 1) (2^(bits + 1) - N) x)
      (target_idx i)
    = (subConstPow2Spec bits N x).testBit i := by
  have h_hb : 2 ≤ bits + 1 := by omega
  have h_2pos : 0 < 2^(bits + 1) := Nat.two_pow_pos (bits + 1)
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_a : 2^(bits + 1) - N < 2^(bits + 1) := by omega
  have h_b : x < 2^(bits + 1) := by omega
  obtain ⟨_, ht, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                          (bits + 1) (2^(bits + 1) - N) x h_hb h_a h_b
  have h := ht i (by omega)
  rw [h]
  unfold subConstPow2Spec
  rw [Nat.testBit_mod_two_pow]
  simp [show i < bits from hi]
  have h_rearrange : (2^(bits+1) - N) + x = (x + (2^bits - N)) + 2^bits := by omega
  rw [h_rearrange]
  exact testBit_add_two_pow_below _ i bits hi

/-! ## Conditional add-back primitive (masked-register preparation)

Following from the underflow/comparison flag (`patched_adder_sub_const_underflow_flag`),
the next step in the standard modular-addition pipeline is a
conditional add-back of `N` whenever the comparison flag indicates
underflow.

Naive controlled-adder approaches require controlled-CCX gates not
present in the Gate IR (which has only `X / CX / CCX / seq`).  We
avoid this by using **masked-register preparation**: prepare the
adder's read register with the bits `flag ∧ N.testBit i` (computed
in-place via a single CX per nonzero N-bit), then run the ordinary
patched Gidney adder, then un-prepare (the cascade is its own
inverse since CX is involutive).

The flag qubit lives at index `flagIdx`, required to be disjoint
from the adder's working register (`adder_n_qubits bits ≤ flagIdx`).
This places the flag above the natural adder range and avoids
collisions with read / target / carry positions.

### Deliverable A — `prepareMaskedConstRead`

Cascade of CXs from `flagIdx` into each `read_idx k` (for `k < bits`)
guarded by whether `N.testBit k` is set. -/

/-- Prepare the read register by XORing each `read_idx k` (for `k < bits`)
with `flag ∧ N.testBit k`, where the flag bit lives at `flagIdx`.
Implemented as a CX cascade conditioned on the bit pattern of `N`. -/
def prepareMaskedConstRead : Nat → Nat → Nat → Gate
  | 0,     _, _       => Gate.I
  | k + 1, N, flagIdx =>
      Gate.seq (prepareMaskedConstRead k N flagIdx)
               (if N.testBit k then Gate.CX flagIdx (read_idx k) else Gate.I)

/-! ### Deliverable B — preservation / read-idx action lemmas -/

/-- Outside the read register's `[0, bits)` window, `prepareMaskedConstRead`
acts as the identity (in particular: target, carry, and `flagIdx` are
preserved). -/
theorem prepareMaskedConstRead_preserves_outside
    (bits N flagIdx : Nat) (f : Nat → Bool) (p : Nat)
    (h : ∀ i, i < bits → p ≠ read_idx i) :
    Gate.applyNat (prepareMaskedConstRead bits N flagIdx) f p = f p := by
  induction bits with
  | zero => rfl
  | succ k ih =>
      have ih_inst : Gate.applyNat (prepareMaskedConstRead k N flagIdx) f p = f p := by
        apply ih; intro i hi; exact h i (by omega)
      have h_p_rk : p ≠ read_idx k := h k (by omega)
      show Gate.applyNat (if N.testBit k = true then Gate.CX flagIdx (read_idx k) else Gate.I)
            (Gate.applyNat (prepareMaskedConstRead k N flagIdx) f) p = f p
      split
      · simp only [Gate.applyNat_CX]
        rw [update_neq _ _ _ _ h_p_rk]
        exact ih_inst
      · exact ih_inst

/-- At `read_idx j` (for `j < bits`), `prepareMaskedConstRead` XORs the
existing value with `f flagIdx && N.testBit j` — i.e. it conditionally
flips the read bit based on the flag and the constant pattern. -/
theorem prepareMaskedConstRead_at_read_idx
    (bits N flagIdx : Nat) (f : Nat → Bool) (j : Nat) (hj : j < bits)
    (h_flag_disj_read : ∀ i, i < bits → flagIdx ≠ read_idx i) :
    Gate.applyNat (prepareMaskedConstRead bits N flagIdx) f (read_idx j) =
    xor (f (read_idx j)) (f flagIdx && N.testBit j) := by
  induction bits with
  | zero => omega
  | succ k ih =>
      show Gate.applyNat (if N.testBit k = true then Gate.CX flagIdx (read_idx k) else Gate.I)
            (Gate.applyNat (prepareMaskedConstRead k N flagIdx) f) (read_idx j) = _
      by_cases hjk : j < k
      · have h_rk_neq_rj : read_idx j ≠ read_idx k := by unfold read_idx; omega
        split
        · simp only [Gate.applyNat_CX]
          rw [update_neq _ _ _ _ h_rk_neq_rj]
          exact ih hjk (fun i hi => h_flag_disj_read i (by omega))
        · exact ih hjk (fun i hi => h_flag_disj_read i (by omega))
      · have hjeq : j = k := by omega
        rw [hjeq]
        have h_frame_rk : Gate.applyNat (prepareMaskedConstRead k N flagIdx) f (read_idx k)
                         = f (read_idx k) := by
          apply prepareMaskedConstRead_preserves_outside
          intro i hi; unfold read_idx; omega
        have h_frame_flag : Gate.applyNat (prepareMaskedConstRead k N flagIdx) f flagIdx
                           = f flagIdx := by
          apply prepareMaskedConstRead_preserves_outside
          intro i hi; exact h_flag_disj_read i (by omega)
        split
        next h_test =>
          simp only [Gate.applyNat_CX]
          rw [update_eq, h_frame_rk, h_frame_flag, h_test]
          simp [Bool.xor_comm]
        next h_test =>
          have h_test_false : N.testBit k = false := by
            cases hN_t : N.testBit k
            · rfl
            · exact absurd hN_t h_test
          show Gate.applyNat (prepareMaskedConstRead k N flagIdx) f (read_idx k) = _
          rw [h_frame_rk, h_test_false]
          simp

/-! ### Generic frame lemma for well-typed gates

A `Gate.WellTyped dim g` gate commutes with `update _ p v` whenever
`p ≥ dim`.  This lets us slip an "out-of-band" flag bit past any
in-range gate sequence — crucial for the conditional add-back proof. -/

/-- Any `WellTyped dim` gate commutes with `update _ p v` for `p ≥ dim`. -/
theorem applyNat_commute_update_above_dim
    (dim : Nat) (g : Gate) (h_wt : Gate.WellTyped dim g)
    (f : Nat → Bool) (p : Nat) (v : Bool) (h_p : dim ≤ p) :
    Gate.applyNat g (update f p v) = update (Gate.applyNat g f) p v := by
  induction g generalizing f with
  | I => rfl
  | X q =>
      have hq : q < dim := h_wt
      have h_q_p : q ≠ p := by omega
      simp only [Gate.applyNat_X]
      rw [update_neq _ _ _ _ h_q_p]
      exact update_update_comm f p q v _ h_q_p.symm
  | CX c t =>
      obtain ⟨hc, ht, _⟩ := h_wt
      have h_p_c : p ≠ c := by omega
      have h_p_t : p ≠ t := by omega
      exact applyNat_CX_commute_update_disjoint c t f p v h_p_c h_p_t
  | CCX a b c =>
      obtain ⟨ha, hb, hc, _, _, _⟩ := h_wt
      have h_p_a : p ≠ a := by omega
      have h_p_b : p ≠ b := by omega
      have h_p_c : p ≠ c := by omega
      exact applyNat_CCX_commute_update_disjoint a b c f p v h_p_a h_p_b h_p_c
  | seq g₁ g₂ ih₁ ih₂ =>
      obtain ⟨hwt₁, hwt₂⟩ := h_wt
      apply applyNat_seq_commute_update _ _ _ _ _ (ih₁ hwt₁) (ih₂ hwt₂)

/-! ### `adder_input_F` evaluation helpers -/

private theorem adder_input_F_at_read_idx_eq
    (n a b j : Nat) (hj : j < n) :
    adder_input_F n a b (read_idx j) = a.testBit j := by
  unfold adder_input_F
  have h_mod : (read_idx j) % 3 = 0 := by unfold read_idx; omega
  have h_div : (read_idx j) / 3 = j := by unfold read_idx; omega
  rw [h_mod, h_div]
  simp [hj]

private theorem adder_input_F_eq_outside_read_in_range
    (n a b k : Nat) (h : ∀ j, j < n → k ≠ read_idx j) :
    adder_input_F n a b k = adder_input_F n 0 b k := by
  unfold adder_input_F
  rcases h_mod : k % 3 with _ | _ | _
  · have h_k_eq : k = read_idx (k / 3) := by unfold read_idx; omega
    by_cases hkn : k / 3 < n
    · exfalso; apply h (k / 3) hkn; exact h_k_eq
    · simp [hkn]
  · rfl
  · rfl

/-- **Key intermediate theorem.**  Applying `prepareMaskedConstRead` to
`update (adder_input_F bits 0 x) flagIdx flag` yields
`update (adder_input_F bits (if flag then N else 0) x) flagIdx flag` —
i.e. the read register has been re-loaded with the **conditionally
masked** constant `flag ∧ N`. -/
theorem prepareMaskedConstRead_yields_input_F
    (bits N flagIdx x : Nat) (flag : Bool)
    (h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j) :
    Gate.applyNat (prepareMaskedConstRead bits N flagIdx)
      (update (adder_input_F bits 0 x) flagIdx flag)
    = update (adder_input_F bits (if flag then N else 0) x) flagIdx flag := by
  funext k
  by_cases h_k_flag : k = flagIdx
  · rw [h_k_flag]
    rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ flagIdx h_disj]
    rw [update_eq, update_eq]
  · by_cases h_k_read : ∃ j, j < bits ∧ k = read_idx j
    · obtain ⟨j, hj, h_kj⟩ := h_k_read
      rw [h_kj]
      rw [h_kj] at h_k_flag
      have h_rj_ne_flag : read_idx j ≠ flagIdx := h_k_flag
      rw [prepareMaskedConstRead_at_read_idx bits N flagIdx _ j hj h_disj]
      rw [update_neq _ _ _ _ h_rj_ne_flag, update_eq, update_neq _ _ _ _ h_rj_ne_flag]
      rw [adder_input_F_at_read_idx_eq bits 0 x j hj]
      rw [Nat.zero_testBit, Bool.false_xor]
      rw [adder_input_F_at_read_idx_eq bits _ x j hj]
      cases flag with
      | true => simp
      | false => simp [Nat.zero_testBit]
    · have h_k_read' : ∀ j, j < bits → k ≠ read_idx j := by
        intro j hj h_eq; exact h_k_read ⟨j, hj, h_eq⟩
      rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ k h_k_read']
      rw [update_neq _ _ _ _ h_k_flag, update_neq _ _ _ _ h_k_flag]
      rw [adder_input_F_eq_outside_read_in_range bits 0 x k h_k_read',
          ← adder_input_F_eq_outside_read_in_range bits (if flag then N else 0) x k h_k_read']

/-! ### Deliverable C — `conditionalAddConstGate` -/

/-- Conditional add-back gate: prepare the read register with the
masked constant `flag ∧ N`, run the patched Gidney adder, un-prepare
the read register.  The result computes
`target := (x + (if flag then N else 0)) mod 2^bits` without using
any controlled-CCX (CCCX) gate. -/
def conditionalAddConstGate (bits N flagIdx : Nat) : Gate :=
  Gate.seq (prepareMaskedConstRead bits N flagIdx)
    (Gate.seq (gidney_adder_full_faithful_no_measurement_patched bits)
      (prepareMaskedConstRead bits N flagIdx))

/-! ### Deliverable D — target decode theorem

The headline correctness theorem of this iteration. -/

/-- **Conditional add-back target decode.**  Applied to
`update (adder_input_F bits 0 x) flagIdx flag` (read register zero,
target register `x`, carry register zero, flag at `flagIdx`), the
`conditionalAddConstGate` produces target register equal to
`(x + (if flag then N else 0)) mod 2^bits`. -/
theorem conditionalAddConstGate_target_decode
    (bits N flagIdx x : Nat) (flag : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (h_flag : adder_n_qubits bits ≤ flagIdx) :
    gidney_target_val bits
      (Gate.applyNat (conditionalAddConstGate bits N flagIdx)
        (update (adder_input_F bits 0 x) flagIdx flag))
    = (x + (if flag then N else 0)) % 2^bits := by
  have h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j := by
    intro j hj
    unfold adder_n_qubits read_idx at *
    omega
  have h_disj_t : ∀ j, j < bits → flagIdx ≠ target_idx j := by
    intro j hj
    unfold adder_n_qubits target_idx at *
    omega
  have h_c_lt : (if flag then N else 0) < 2^bits := by
    cases flag with
    | true => exact hN
    | false => exact Nat.two_pow_pos bits
  unfold conditionalAddConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareMaskedConstRead_yields_input_F bits N flagIdx x flag h_disj]
  have h_wt : Gate.WellTyped (adder_n_qubits bits)
              (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  rw [applyNat_commute_update_above_dim (adder_n_qubits bits) _ h_wt _ _ _ h_flag]
  apply gidney_target_val_eq_sum_when_bits_match bits (x + (if flag then N else 0))
  intro i hi
  have h_target_neq_read : ∀ j, j < bits → target_idx i ≠ read_idx j := by
    intro j _; unfold target_idx read_idx; omega
  rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ (target_idx i) h_target_neq_read]
  have h_target_ne_flag : target_idx i ≠ flagIdx := (h_disj_t i hi).symm
  rw [update_neq _ _ _ _ h_target_ne_flag]
  obtain ⟨_, h_target, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                              bits (if flag then N else 0) x hbits h_c_lt hx
  rw [h_target i hi, Nat.add_comm]

/-! ### Frame / restoration / WellTyped deliverables

Five additional theorems that promote `conditionalAddConstGate` from a
"target-only" primitive to a fully reusable building block: read
register restored to zero, carry register cleared, flag preserved,
gate WellTyped in an enlarged dimension, and a bundled `_clean` form. -/

/-- **WellTyped monotonicity**: `WellTyped` is preserved under dimension
enlargement.  Generic helper, applies to any `Gate`. -/
theorem Gate.WellTyped.mono {dim dim' : Nat} {g : Gate}
    (h : Gate.WellTyped dim g) (h_le : dim ≤ dim') :
    Gate.WellTyped dim' g := by
  induction g with
  | I =>
      show 0 < dim'
      have : 0 < dim := h; omega
  | X q =>
      show q < dim'
      have : q < dim := h; omega
  | CX a b =>
      obtain ⟨_, _, hab⟩ := h
      exact ⟨by omega, by omega, hab⟩
  | CCX a b c =>
      obtain ⟨_, _, _, hab, hac, hbc⟩ := h
      exact ⟨by omega, by omega, by omega, hab, hac, hbc⟩
  | seq g₁ g₂ ih₁ ih₂ =>
      obtain ⟨hwt₁, hwt₂⟩ := h
      exact ⟨ih₁ hwt₁, ih₂ hwt₂⟩

/-- `prepareMaskedConstRead` is `WellTyped` in dimension `flagIdx + 1`
whenever the flag is placed above the adder's working register. -/
theorem prepareMaskedConstRead_wellTyped
    (bits N flagIdx : Nat) (h_flag : adder_n_qubits bits ≤ flagIdx) :
    Gate.WellTyped (flagIdx + 1) (prepareMaskedConstRead bits N flagIdx) := by
  induction bits with
  | zero =>
      show 0 < flagIdx + 1; omega
  | succ k ih =>
      show Gate.WellTyped (flagIdx + 1) _
      have h_flag_k : adder_n_qubits k ≤ flagIdx := by
        unfold adder_n_qubits at *; omega
      refine ⟨ih h_flag_k, ?_⟩
      by_cases h_test : N.testBit k
      · simp [h_test]
        unfold adder_n_qubits read_idx at *
        exact ⟨by omega, by omega, by omega⟩
      · simp [h_test]
        show 0 < flagIdx + 1; omega

/-- **Deliverable A — read register restored.**  After the full
conditional add-back, every in-range read position is back to zero
(the read register served only as a scratch space during the
underlying adder). -/
theorem conditionalAddConstGate_read_restored
    (bits N x flagIdx : Nat) (flag : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    ∀ i, i < bits →
      Gate.applyNat (conditionalAddConstGate bits N flagIdx)
        (update (adder_input_F bits 0 x) flagIdx flag) (read_idx i)
      = false := by
  intro i hi
  have h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j := by
    intro j hj
    unfold adder_n_qubits read_idx at *; omega
  have h_c_lt : (if flag then N else 0) < 2^bits := by
    cases flag with
    | true => exact hN
    | false => exact Nat.two_pow_pos bits
  unfold conditionalAddConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareMaskedConstRead_yields_input_F bits N flagIdx x flag h_disj]
  have h_wt : Gate.WellTyped (adder_n_qubits bits)
              (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  rw [applyNat_commute_update_above_dim (adder_n_qubits bits) _ h_wt _ _ _ hflagIdx]
  rw [prepareMaskedConstRead_at_read_idx bits N flagIdx _ i hi h_disj]
  have h_read_ne_flag : read_idx i ≠ flagIdx := (h_disj i hi).symm
  rw [update_neq _ _ _ _ h_read_ne_flag, update_eq]
  obtain ⟨h_read, _, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                            bits (if flag then N else 0) x hbits h_c_lt hx
  rw [h_read i hi]
  cases flag with
  | true => simp
  | false => simp [Nat.zero_testBit]

/-- **Deliverable B — carry register cleared.**  Every in-range carry
position is `false` after the full conditional add-back (carries are
fully cleared by the inner patched Gidney adder, and the outer prep
cascade touches no carry positions). -/
theorem conditionalAddConstGate_carries_cleared
    (bits N x flagIdx : Nat) (flag : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    ∀ i, i < bits →
      Gate.applyNat (conditionalAddConstGate bits N flagIdx)
        (update (adder_input_F bits 0 x) flagIdx flag) (carry_idx i)
      = false := by
  intro i hi
  have h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j := by
    intro j hj
    unfold adder_n_qubits read_idx at *; omega
  have h_disj_c : ∀ j, j < bits → flagIdx ≠ carry_idx j := by
    intro j hj
    unfold adder_n_qubits carry_idx at *; omega
  have h_c_lt : (if flag then N else 0) < 2^bits := by
    cases flag with
    | true => exact hN
    | false => exact Nat.two_pow_pos bits
  unfold conditionalAddConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareMaskedConstRead_yields_input_F bits N flagIdx x flag h_disj]
  have h_wt : Gate.WellTyped (adder_n_qubits bits)
              (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  rw [applyNat_commute_update_above_dim (adder_n_qubits bits) _ h_wt _ _ _ hflagIdx]
  have h_carry_neq_read : ∀ j, j < bits → carry_idx i ≠ read_idx j := by
    intro j _; unfold carry_idx read_idx; omega
  rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ (carry_idx i)
        h_carry_neq_read]
  have h_carry_ne_flag : carry_idx i ≠ flagIdx := (h_disj_c i hi).symm
  rw [update_neq _ _ _ _ h_carry_ne_flag]
  obtain ⟨_, _, h_carry⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                            bits (if flag then N else 0) x hbits h_c_lt hx
  exact h_carry i hi

/-- **Deliverable C — flag preserved.**  The flag bit at `flagIdx`
survives the full conditional add-back unchanged.  Follows from the
adder commuting past the flag update (by `WellTyped` framing) and
both preps preserving positions outside the read range. -/
theorem conditionalAddConstGate_flag_preserved
    (bits N x flagIdx : Nat) (flag : Bool)
    (hbits : 2 ≤ bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx)
      (update (adder_input_F bits 0 x) flagIdx flag) flagIdx = flag := by
  have h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j := by
    intro j hj
    unfold adder_n_qubits read_idx at *; omega
  unfold conditionalAddConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareMaskedConstRead_yields_input_F bits N flagIdx x flag h_disj]
  have h_wt : Gate.WellTyped (adder_n_qubits bits)
              (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  rw [applyNat_commute_update_above_dim (adder_n_qubits bits) _ h_wt _ _ _ hflagIdx]
  rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ flagIdx h_disj]
  rw [update_eq]

/-- **Deliverable D — `WellTyped` at `flagIdx + 1`.**  The whole
conditional add-back gate is `WellTyped` in the enlarged dimension
that includes the out-of-band flag bit. -/
theorem conditionalAddConstGate_wellTyped
    (bits N flagIdx : Nat) (hbits : 2 ≤ bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    Gate.WellTyped (flagIdx + 1) (conditionalAddConstGate bits N flagIdx) := by
  unfold conditionalAddConstGate
  have h_prep : Gate.WellTyped (flagIdx + 1)
                  (prepareMaskedConstRead bits N flagIdx) :=
    prepareMaskedConstRead_wellTyped bits N flagIdx hflagIdx
  have h_adder_base : Gate.WellTyped (adder_n_qubits bits)
                  (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  have h_adder : Gate.WellTyped (flagIdx + 1)
                  (gidney_adder_full_faithful_no_measurement_patched bits) :=
    Gate.WellTyped.mono h_adder_base (by omega)
  exact ⟨h_prep, ⟨h_adder, h_prep⟩⟩

/-- **Deliverable E — bundled clean primitive.**  The headline
characterisation of `conditionalAddConstGate`: WellTyped, correct
target decode, read register restored, carries cleared, flag
preserved.  This is the one theorem downstream consumers should call. -/
theorem conditionalAddConstGate_clean
    (bits N x flagIdx : Nat) (flag : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    Gate.WellTyped (flagIdx + 1) (conditionalAddConstGate bits N flagIdx)
    ∧ gidney_target_val bits
        (Gate.applyNat (conditionalAddConstGate bits N flagIdx)
          (update (adder_input_F bits 0 x) flagIdx flag))
      = (x + (if flag then N else 0)) % 2^bits
    ∧ (∀ i, i < bits →
        Gate.applyNat (conditionalAddConstGate bits N flagIdx)
          (update (adder_input_F bits 0 x) flagIdx flag) (read_idx i) = false)
    ∧ (∀ i, i < bits →
        Gate.applyNat (conditionalAddConstGate bits N flagIdx)
          (update (adder_input_F bits 0 x) flagIdx flag) (carry_idx i) = false)
    ∧ Gate.applyNat (conditionalAddConstGate bits N flagIdx)
        (update (adder_input_F bits 0 x) flagIdx flag) flagIdx = flag := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact conditionalAddConstGate_wellTyped bits N flagIdx hbits hflagIdx
  · exact conditionalAddConstGate_target_decode bits N flagIdx x flag hbits hN hx hflagIdx
  · exact conditionalAddConstGate_read_restored bits N x flagIdx flag hbits hN hx hflagIdx
  · exact conditionalAddConstGate_carries_cleared bits N x flagIdx flag hbits hN hx hflagIdx
  · exact conditionalAddConstGate_flag_preserved bits N x flagIdx flag hbits hflagIdx

/-! ## Composable constant-add / constant-sub primitives

The conditional add-back gate above is parameterised by an external
`flag` bit.  For full modular-addition composition we also need an
*unconditional* constant-add gate that takes its input as a clean
`adder_input_F bits 0 x` (zero read register, target = `x`) and
produces clean output (target = `(x + c) mod 2^bits`, read register
restored to zero, carries cleared).

These primitives are simpler than the conditional variant — no flag
ancilla, no `WellTyped` enlargement — so they live entirely inside
the natural `adder_n_qubits bits` dimension.

The same prep/unprep idiom is used, but with an X-gate cascade (rather
than CX) since the constant is classically known. -/

/-! ### `prepareConstRead` — unconditional read-register preparation -/

/-- Unconditionally prepare `read_idx k := c.testBit k` for `k < bits`
by applying `X (read_idx k)` whenever `c.testBit k = true`.  When
applied to a zero read register, sets it to the bits of `c`; applied
again (involutive), it clears the read register back to zero. -/
def prepareConstRead : Nat → Nat → Gate
  | 0,     _ => Gate.I
  | k + 1, c => Gate.seq (prepareConstRead k c)
                  (if c.testBit k then Gate.X (read_idx k) else Gate.I)

/-- Outside the read register's `[0, bits)` window, `prepareConstRead`
is the identity (so target, carry, and any extra ancillas are
preserved). -/
theorem prepareConstRead_preserves_outside
    (bits c : Nat) (f : Nat → Bool) (p : Nat)
    (h : ∀ i, i < bits → p ≠ read_idx i) :
    Gate.applyNat (prepareConstRead bits c) f p = f p := by
  induction bits with
  | zero => rfl
  | succ k ih =>
      have ih_inst : Gate.applyNat (prepareConstRead k c) f p = f p := by
        apply ih; intro i hi; exact h i (by omega)
      have h_p_rk : p ≠ read_idx k := h k (by omega)
      show Gate.applyNat (if c.testBit k = true then Gate.X (read_idx k) else Gate.I)
            (Gate.applyNat (prepareConstRead k c) f) p = f p
      split
      · simp only [Gate.applyNat_X]
        rw [update_neq _ _ _ _ h_p_rk]
        exact ih_inst
      · exact ih_inst

/-- At `read_idx j` (for `j < bits`), `prepareConstRead` XORs the value
with `c.testBit j`. -/
theorem prepareConstRead_at_read_idx
    (bits c : Nat) (f : Nat → Bool) (j : Nat) (hj : j < bits) :
    Gate.applyNat (prepareConstRead bits c) f (read_idx j) =
    xor (f (read_idx j)) (c.testBit j) := by
  induction bits with
  | zero => omega
  | succ k ih =>
      show Gate.applyNat (if c.testBit k = true then Gate.X (read_idx k) else Gate.I)
            (Gate.applyNat (prepareConstRead k c) f) (read_idx j) = _
      by_cases hjk : j < k
      · have h_rk_neq_rj : read_idx j ≠ read_idx k := by unfold read_idx; omega
        split
        · simp only [Gate.applyNat_X]
          rw [update_neq _ _ _ _ h_rk_neq_rj]
          exact ih hjk
        · exact ih hjk
      · have hjeq : j = k := by omega
        rw [hjeq]
        have h_frame_rk : Gate.applyNat (prepareConstRead k c) f (read_idx k) = f (read_idx k) := by
          apply prepareConstRead_preserves_outside
          intro i hi; unfold read_idx; omega
        split
        next h_test =>
          simp only [Gate.applyNat_X]
          rw [update_eq, h_frame_rk, h_test]
          simp [Bool.xor_comm]
        next h_test =>
          have h_test_false : c.testBit k = false := by
            cases hN_t : c.testBit k
            · rfl
            · exact absurd hN_t h_test
          show Gate.applyNat (prepareConstRead k c) f (read_idx k) = _
          rw [h_frame_rk, h_test_false]
          simp

/-- `prepareConstRead bits c` applied to `adder_input_F bits 0 x`
produces exactly `adder_input_F bits c x` — i.e., the read register
has been loaded with the bits of `c`. -/
theorem prepareConstRead_yields_input_F
    (bits c x : Nat) :
    Gate.applyNat (prepareConstRead bits c) (adder_input_F bits 0 x)
    = adder_input_F bits c x := by
  funext k
  by_cases h_k_read : ∃ j, j < bits ∧ k = read_idx j
  · obtain ⟨j, hj, h_kj⟩ := h_k_read
    rw [h_kj]
    rw [prepareConstRead_at_read_idx bits c _ j hj]
    rw [adder_input_F_at_read_idx_eq bits 0 x j hj]
    rw [Nat.zero_testBit, Bool.false_xor]
    rw [adder_input_F_at_read_idx_eq bits c x j hj]
  · have h_k_read' : ∀ j, j < bits → k ≠ read_idx j := by
      intro j hj h_eq; exact h_k_read ⟨j, hj, h_eq⟩
    rw [prepareConstRead_preserves_outside bits c _ k h_k_read']
    rw [adder_input_F_eq_outside_read_in_range bits 0 x k h_k_read',
        ← adder_input_F_eq_outside_read_in_range bits c x k h_k_read']

/-- `prepareConstRead bits c` is WellTyped at the adder's natural
dimension `adder_n_qubits bits = 3*bits + 2`. -/
theorem prepareConstRead_wellTyped
    (bits c : Nat) :
    Gate.WellTyped (adder_n_qubits bits) (prepareConstRead bits c) := by
  induction bits with
  | zero =>
      show 0 < adder_n_qubits 0
      unfold adder_n_qubits; omega
  | succ k ih =>
      show Gate.WellTyped (adder_n_qubits (k + 1)) _
      have h_extend : Gate.WellTyped (adder_n_qubits (k + 1)) (prepareConstRead k c) := by
        apply Gate.WellTyped.mono ih
        unfold adder_n_qubits; omega
      refine ⟨h_extend, ?_⟩
      by_cases h_test : c.testBit k
      · simp [h_test]
        show read_idx k < adder_n_qubits (k + 1)
        unfold adder_n_qubits read_idx; omega
      · simp [h_test]
        show 0 < adder_n_qubits (k + 1)
        unfold adder_n_qubits; omega

/-! ### Self-contained `addConstGate` and `subConstGate` -/

/-- Composable constant-add gate: prepare read with `c`, run the
patched Gidney adder, unprepare read.  Takes a clean
`adder_input_F bits 0 x` and produces target = `(x + c) mod 2^bits`,
with read register restored to zero and carries cleared. -/
def addConstGate (bits c : Nat) : Gate :=
  Gate.seq (prepareConstRead bits c)
    (Gate.seq (gidney_adder_full_faithful_no_measurement_patched bits)
      (prepareConstRead bits c))

/-- Composable constant-sub gate, expressed as wraparound addition of
`2^bits - N`.  This implements `(x + (2^bits - N)) mod 2^bits`, which
equals `(x - N) mod 2^bits` over the two's-complement view. -/
def subConstGate (bits N : Nat) : Gate :=
  addConstGate bits (2^bits - N)

/-- **Bundled clean primitive** for `addConstGate`.  Takes a clean
`adder_input_F bits 0 x` and produces:
* WellTyped at the natural dimension `adder_n_qubits bits`;
* target decodes to `(x + c) mod 2^bits`;
* read register restored to zero;
* carries cleared. -/
theorem addConstGate_clean
    (bits c x : Nat) (hbits : 2 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits) :
    Gate.WellTyped (adder_n_qubits bits) (addConstGate bits c)
    ∧ gidney_target_val bits
        (Gate.applyNat (addConstGate bits c) (adder_input_F bits 0 x))
      = (x + c) % 2^bits
    ∧ (∀ i, i < bits →
        Gate.applyNat (addConstGate bits c) (adder_input_F bits 0 x) (read_idx i) = false)
    ∧ (∀ i, i < bits →
        Gate.applyNat (addConstGate bits c) (adder_input_F bits 0 x) (carry_idx i) = false) := by
  have h_prep_wt : Gate.WellTyped (adder_n_qubits bits) (prepareConstRead bits c) :=
    prepareConstRead_wellTyped bits c
  have h_adder_wt : Gate.WellTyped (adder_n_qubits bits)
                    (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  have h_wt : Gate.WellTyped (adder_n_qubits bits) (addConstGate bits c) :=
    ⟨h_prep_wt, ⟨h_adder_wt, h_prep_wt⟩⟩
  obtain ⟨h_read, h_target, h_carry⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                                          bits c x hbits hc hx
  refine ⟨h_wt, ?_, ?_, ?_⟩
  · apply gidney_target_val_eq_sum_when_bits_match bits (x + c)
    intro i hi
    show Gate.applyNat (addConstGate bits c) (adder_input_F bits 0 x) (target_idx i)
       = (x + c).testBit i
    unfold addConstGate
    rw [Gate.applyNat_seq, Gate.applyNat_seq]
    rw [prepareConstRead_yields_input_F bits c x]
    have h_t_neq_read : ∀ j, j < bits → target_idx i ≠ read_idx j := by
      intro j _; unfold target_idx read_idx; omega
    rw [prepareConstRead_preserves_outside bits c _ (target_idx i) h_t_neq_read]
    rw [h_target i hi, Nat.add_comm]
  · intro i hi
    unfold addConstGate
    rw [Gate.applyNat_seq, Gate.applyNat_seq]
    rw [prepareConstRead_yields_input_F bits c x]
    rw [prepareConstRead_at_read_idx bits c _ i hi]
    rw [h_read i hi]
    cases h_test : c.testBit i
    all_goals simp
  · intro i hi
    unfold addConstGate
    rw [Gate.applyNat_seq, Gate.applyNat_seq]
    rw [prepareConstRead_yields_input_F bits c x]
    have h_c_neq_read : ∀ j, j < bits → carry_idx i ≠ read_idx j := by
      intro j _; unfold carry_idx read_idx; omega
    rw [prepareConstRead_preserves_outside bits c _ (carry_idx i) h_c_neq_read]
    exact h_carry i hi

/-- **Bundled clean primitive** for `subConstGate`.  Follows directly
from `addConstGate_clean` with `c = 2^bits - N`. -/
theorem subConstGate_clean
    (bits N x : Nat) (hbits : 2 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.WellTyped (adder_n_qubits bits) (subConstGate bits N)
    ∧ gidney_target_val bits
        (Gate.applyNat (subConstGate bits N) (adder_input_F bits 0 x))
      = subConstPow2Spec bits N x
    ∧ (∀ i, i < bits →
        Gate.applyNat (subConstGate bits N) (adder_input_F bits 0 x) (read_idx i) = false)
    ∧ (∀ i, i < bits →
        Gate.applyNat (subConstGate bits N) (adder_input_F bits 0 x) (carry_idx i) = false) := by
  have h_c_lt : 2^bits - N < 2^bits := by
    have : 0 < 2^bits := Nat.two_pow_pos bits; omega
  unfold subConstGate
  obtain ⟨h_wt, h_target, h_read, h_carry⟩ := addConstGate_clean bits (2^bits - N) x hbits h_c_lt hx
  refine ⟨h_wt, ?_, h_read, h_carry⟩
  rw [h_target]
  rfl

/-! ### Generalized widened underflow / comparison flag for sums `s < 2*N`

After the first add-step of a modular adder, the intermediate sum
`s = x + c` may exceed `2^bits` (it satisfies `s < 2N` only, where
`N ≤ 2^bits`).  We need a generalisation of the existing widened
underflow theorem (`subConstPow2WideSpec_high_bit`) that drops the
`s < 2^bits` assumption in favour of the weaker `s < 2*N`. -/

/-- Generalized no-underflow high-bit lemma.  When `N ≤ s` and
`s < 2*N`, the widened result equals `s - N`, which fits in `bits`
bits, so bit `bits` is `false`.  Drops the `s < 2^bits` assumption
of `subConstPow2WideSpec_high_bit_of_le`. -/
theorem subConstPow2WideSpec_high_bit_bounded_sum_of_le
    (bits N s : Nat) (hN : N ≤ 2^bits) (hle : N ≤ s) (hs : s < 2 * N) :
    (subConstPow2WideSpec bits N s).testBit bits = false := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_eq : subConstPow2WideSpec bits N s = s - N := by
    unfold subConstPow2WideSpec
    have h_eq2 : s + (2^(bits + 1) - N) = (s - N) + 2^(bits + 1) := by omega
    rw [h_eq2, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h_eq]
  exact Nat.testBit_lt_two_pow (by omega)

/-- Generalized underflow high-bit lemma for `s < N` and `N ≤ 2^bits`.
Identical to `subConstPow2WideSpec_high_bit_of_lt`, restated here as a
named entry point for the post-add-step comparison flag. -/
theorem subConstPow2WideSpec_high_bit_bounded_sum_of_lt
    (bits N s : Nat) (hN : N ≤ 2^bits) (hlt : s < N) :
    (subConstPow2WideSpec bits N s).testBit bits = true :=
  subConstPow2WideSpec_high_bit_of_lt bits N s hN hlt

/-- **Generalized main high-bit theorem** for the widened subtraction
under `s < 2*N`.  After the first add-step of the modular-adder
pipeline, the intermediate sum is bounded by `2*N` (not `2^bits`),
yet the widened subtraction's high bit still equals `decide (s < N)`. -/
theorem subConstPow2WideSpec_high_bit_bounded_sum
    (bits N s : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hs : s < 2 * N) :
    (subConstPow2WideSpec bits N s).testBit bits = decide (s < N) := by
  by_cases h : s < N
  · rw [decide_eq_true h]
    exact subConstPow2WideSpec_high_bit_bounded_sum_of_lt bits N s hN h
  · rw [decide_eq_false (by omega)]
    exact subConstPow2WideSpec_high_bit_bounded_sum_of_le bits N s hN (by omega) hs

/-- **Generalized gate-level underflow flag.**  After the first
add-step of a modular adder, the intermediate sum `s` may have
`s ≥ 2^bits` but always satisfies `s < 2*N`.  The widened patched
Gidney adder's target bit at position `bits` is exactly
`decide (s < N)` under this weaker bound. -/
theorem patched_adder_sub_const_underflow_flag_bounded_sum
    (bits N s : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hs : s < 2 * N) :
    Gate.applyNat
      (gidney_adder_full_faithful_no_measurement_patched (bits + 1))
      (adder_input_F (bits + 1) (2^(bits + 1) - N) s)
      (target_idx bits)
    = decide (s < N) := by
  have h_hb : 2 ≤ bits + 1 := by omega
  have h_2pos : 0 < 2^(bits + 1) := Nat.two_pow_pos (bits + 1)
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_a : 2^(bits + 1) - N < 2^(bits + 1) := by omega
  have h_b : s < 2^(bits + 1) := by omega
  obtain ⟨_, ht, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                          (bits + 1) (2^(bits + 1) - N) s h_hb h_a h_b
  have h := ht bits (by omega)
  rw [h]
  have h_mod_eq : (((2^(bits+1) - N) + s) % 2^(bits+1)).testBit bits
                  = ((2^(bits+1) - N) + s).testBit bits := by
    rw [Nat.testBit_mod_two_pow]
    simp [show bits < bits + 1 from by omega]
  rw [← h_mod_eq]
  rw [show (((2^(bits+1) - N) + s) % 2^(bits+1))
        = subConstPow2WideSpec bits N s from by
        unfold subConstPow2WideSpec; congr 1; omega]
  exact subConstPow2WideSpec_high_bit_bounded_sum bits N s hN_pos hN hs

/-! ## Widened modular-addition arithmetic pipeline (width `bits + 1`)

To compute `(x + c) mod N` reversibly when `x, c < N ≤ 2^bits`, we
*cannot* work at width `bits` — the intermediate sum `s = x + c` may
exceed `2^bits`, losing the overflow bit.  The standard widened
pipeline operates at width `bits + 1`:

1. **add** `c`:                    `s = x + c`,  `s < 2N ≤ 2^(bits+1)`.
2. **subtract** `N`:                `y = subConstPow2WideSpec bits N s`.
   Bit `bits` of `y` is the comparison flag `decide (s < N)`.
3. **conditionally add back** `N`:  `z = (y + (if flag then N else 0)) % 2^(bits+1)`.

The arithmetic correctness is `z % 2^bits = (x + c) % N`.  This
section proves that identity at the Nat level, then begins the
gate-level chain via per-step idealized-input theorems. -/

/-! ### Deliverable A — sum bounds -/

/-- After widened add, the sum fits in `bits + 1` bits. -/
theorem modAdd_sum_bound
    (bits N x c : Nat) (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N) :
    x + c < 2^(bits + 1) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  omega

/-- After widened add, the sum is bounded by `2N` (the tighter bound
needed by the generalized underflow theorem). -/
theorem modAdd_sum_lt_twoN
    (N x c : Nat) (hx : x < N) (hc : c < N) :
    x + c < 2 * N := by omega

/-! ### Deliverable B — arithmetic pipeline spec and correctness -/

/-- Arithmetic-level spec for the widened modular-addition pipeline at
width `bits + 1`.  Composes: subtract-`N` after add-`c`, conditionally
add back `N` when the comparison flag indicates underflow. -/
def modAddConstArithmeticSpec (bits N c x : Nat) : Nat :=
  (subConstPow2WideSpec bits N (x + c)
    + (if decide ((x + c) < N) then N else 0)) % 2^(bits + 1)

/-- **Widened modular-add pipeline correctness** (arithmetic level).
For `0 < N ≤ 2^bits` and `x, c < N`, the low `bits` bits of the
widened pipeline result equal `(x + c) mod N`. -/
theorem modAddConstArithmeticSpec_correct
    (bits N c x : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    modAddConstArithmeticSpec bits N c x % 2^bits = (x + c) % N := by
  unfold modAddConstArithmeticSpec
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_2pos : 0 < 2^(bits + 1) := Nat.two_pow_pos (bits + 1)
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_xc_lt_pow : x + c < 2^(bits + 1) := by omega
  by_cases h_flag : x + c < N
  · -- flag = true: subtract underflows, add-back restores `x + c`
    have h_y : subConstPow2WideSpec bits N (x + c) = (x + c) + 2^(bits+1) - N := by
      unfold subConstPow2WideSpec
      have h_lt : (x + c) + (2^(bits+1) - N) < 2^(bits+1) := by omega
      rw [Nat.mod_eq_of_lt h_lt]; omega
    rw [h_y, decide_eq_true h_flag]
    show ((x + c) + 2^(bits+1) - N + N) % 2^(bits+1) % 2^bits = (x + c) % N
    have h_eq : ((x + c) + 2^(bits+1) - N) + N = (x + c) + 2^(bits+1) := by omega
    rw [h_eq, Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (show x + c < 2^(bits+1) by omega)]
    rw [Nat.mod_eq_of_lt (show x + c < 2^bits by omega)]
    exact (Nat.mod_eq_of_lt h_flag).symm
  · -- flag = false: subtract gives `x + c - N`, add-back is zero
    have h_le : N ≤ x + c := by omega
    have h_y : subConstPow2WideSpec bits N (x + c) = (x + c) - N := by
      unfold subConstPow2WideSpec
      have h_eq2 : (x + c) + (2^(bits + 1) - N) = ((x + c) - N) + 2^(bits + 1) := by omega
      rw [h_eq2, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_y, decide_eq_false (by omega)]
    show ((x + c) - N + 0) % 2^(bits+1) % 2^bits = (x + c) % N
    rw [Nat.add_zero]
    have h_sN_lt : (x + c) - N < 2^bits := by omega
    have h_sN_lt' : (x + c) - N < 2^(bits+1) := by omega
    have h_sN_lt_N : (x + c) - N < N := by omega
    rw [Nat.mod_eq_of_lt h_sN_lt', Nat.mod_eq_of_lt h_sN_lt]
    have h_s_mod : (x + c) % N = (x + c) - N := by
      have h_split : x + c = ((x + c) - N) + N := by omega
      conv_lhs => rw [h_split]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt h_sN_lt_N]
    rw [h_s_mod]

/-! ### Deliverable C — low-bit version of the arithmetic correctness -/

/-- Bit-level form of `modAddConstArithmeticSpec_correct`: bit `i` of
the pipeline result (for `i < bits`) equals bit `i` of `(x + c) % N`. -/
theorem modAddConstArithmeticSpec_low_bit_correct
    (bits N c x i : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) (hi : i < bits) :
    (modAddConstArithmeticSpec bits N c x).testBit i
    = ((x + c) % N).testBit i := by
  have h_main : modAddConstArithmeticSpec bits N c x % 2^bits = (x + c) % N :=
    modAddConstArithmeticSpec_correct bits N c x hN_pos hN hx hc
  have h_bit : (modAddConstArithmeticSpec bits N c x % 2^bits).testBit i
              = (modAddConstArithmeticSpec bits N c x).testBit i := by
    rw [Nat.testBit_mod_two_pow]; simp [hi]
  rw [← h_bit, h_main]

/-! ### Deliverable D — per-step gate-level theorems (idealized inputs)

Each gate step in the pipeline is decoded into target-register
semantics, taking the *idealized* `adder_input_F` form as input.
Composition of these into a single gate-level theorem requires
intermediate-state preservation (the gate output of step `k` must be
extensionally equal to the `adder_input_F` form for step `k+1`),
which is the next tick's task and is NOT claimed here. -/

/-- **Step 1 — first add**.  Applied to a clean `adder_input_F (bits+1)
0 x`, `addConstGate (bits+1) c` decodes its target register to
`x + c` (no overflow, since `x + c < 2^(bits+1)`). -/
theorem modAdd_step1_target_decode
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    gidney_target_val (bits+1)
      (Gate.applyNat (addConstGate (bits+1) c) (adder_input_F (bits+1) 0 x))
    = x + c := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have hbits' : 2 ≤ bits + 1 := by omega
  have hc' : c < 2^(bits+1) := by omega
  have hx' : x < 2^(bits+1) := by omega
  obtain ⟨_, h_target, _, _⟩ := addConstGate_clean (bits+1) c x hbits' hc' hx'
  rw [h_target]
  exact Nat.mod_eq_of_lt (by omega)

/-- **Step 2 — subtract `N`, observe comparison flag at `target_idx bits`**.
Applied to an *idealized* `adder_input_F (bits+1) 0 s` (i.e., target
holds `s` and read/carry are zero), `addConstGate (bits+1) (2^(bits+1) - N)`
makes the bit at `target_idx bits` equal `decide (s < N)`. -/
theorem modAdd_step2_flag_at_target_idx_bits
    (bits N s : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hs : s < 2 * N) :
    Gate.applyNat (addConstGate (bits+1) (2^(bits+1) - N))
      (adder_input_F (bits+1) 0 s) (target_idx bits)
    = decide (s < N) := by
  unfold addConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareConstRead_yields_input_F (bits+1) (2^(bits+1)-N) s]
  have h_t_neq_read : ∀ j, j < bits+1 → target_idx bits ≠ read_idx j := by
    intro j _; unfold target_idx read_idx; omega
  rw [prepareConstRead_preserves_outside (bits+1) (2^(bits+1)-N) _
        (target_idx bits) h_t_neq_read]
  exact patched_adder_sub_const_underflow_flag_bounded_sum bits N s hbits hN_pos hN hs

/-- **Step 3 — conditional add-back**.  Applied to the idealized
`update (adder_input_F (bits+1) 0 y) flagIdx flag` (target holds `y`,
read/carry zero, flag bit at out-of-band `flagIdx`), the
`conditionalAddConstGate (bits+1) N flagIdx` decodes target to
`(y + (if flag then N else 0)) mod 2^(bits+1)` — which is exactly the
`modAddConstArithmeticSpec` value when `y = subConstPow2WideSpec bits N s`
and `flag = decide (s < N)`. -/
theorem modAdd_step3_target_decode
    (bits N flagIdx y : Nat) (flag : Bool)
    (hbits : 1 ≤ bits) (hN : N < 2^(bits+1)) (hy : y < 2^(bits+1))
    (hflagIdx : adder_n_qubits (bits+1) ≤ flagIdx) :
    gidney_target_val (bits+1)
      (Gate.applyNat (conditionalAddConstGate (bits+1) N flagIdx)
        (update (adder_input_F (bits+1) 0 y) flagIdx flag))
    = (y + (if flag then N else 0)) % 2^(bits+1) := by
  have hbits' : 2 ≤ bits + 1 := by omega
  exact conditionalAddConstGate_target_decode (bits+1) N flagIdx y flag hbits' hN hy hflagIdx

/-! ## State-normalization for composing the full modular-add gate

The per-step theorems above take *idealised* `adder_input_F` inputs.
For full gate-level composition, we need per-bit / per-position
"normal-form" facts about the output of each step, plus a flag-copy
gate that promotes the comparison flag from the in-band
`target_idx bits` to an out-of-band `flagIdx`.

This section delivers:
* per-bit target correctness for `addConstGate` (Deliverable A);
* weak normal-form (working positions only) for step 1
  (Deliverable B);
* weak normal-form (working positions + flag bit) for step 2
  (Deliverable C);
* flag-copy gate + correctness + frame + WellTyped (Deliverable D).

Full gate-level chain composition (Deliverable E) is *blocked* by the
need to prove the patched Gidney adder is `WellTyped` at the tight
dimension `3 * n` (or equivalent: that the cascade preserves the gap
positions `read_idx n` and `target_idx n` for an `n`-bit adder).  The
existing WellTyped is at `adder_n_qubits n = 3*n + 2`, two positions
too loose to bridge intermediate gate states; see the closing comments
of this section for the precise blocker statement. -/

/-! ### Deliverable A — per-bit target correctness for `addConstGate` -/

/-- Bit-level form of `addConstGate_clean`'s target-decode line:
applied to `adder_input_F bits 0 x`, the gate's value at `target_idx i`
(for `i < bits`) equals bit `i` of `(x + c) % 2^bits`. -/
theorem addConstGate_target_bit
    (bits c x i : Nat) (hbits : 2 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits)
    (hi : i < bits) :
    Gate.applyNat (addConstGate bits c) (adder_input_F bits 0 x) (target_idx i)
    = ((x + c) % 2^bits).testBit i := by
  unfold addConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareConstRead_yields_input_F bits c x]
  have h_t_neq_read : ∀ j, j < bits → target_idx i ≠ read_idx j := by
    intro j _; unfold target_idx read_idx; omega
  rw [prepareConstRead_preserves_outside bits c _ (target_idx i) h_t_neq_read]
  obtain ⟨_, h_target, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                              bits c x hbits hc hx
  rw [h_target i hi]
  rw [Nat.add_comm c x]
  rw [Nat.testBit_mod_two_pow]; simp [hi]

/-- No-overflow corollary for widened addition.  When `x, c < N ≤ 2^bits`,
the widened sum `x + c` fits in `bits + 1` bits, so bit `i` of the
target is `(x + c).testBit i` (no mod needed). -/
theorem addConstGate_target_bit_no_overflow
    (bits N c x i : Nat) (hbits : 1 ≤ bits) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) (hi : i < bits + 1) :
    Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x) (target_idx i)
    = (x + c).testBit i := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_2N_le : 2 * N ≤ 2 * 2^bits := by omega
  have h_xc_lt : x + c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_c_lt : c < 2^(bits+1) := by
    have : c < 2^bits := by omega
    rw [h_pow_succ]; omega
  have h_x_lt : x < 2^(bits+1) := by
    have : x < 2^bits := by omega
    rw [h_pow_succ]; omega
  rw [addConstGate_target_bit (bits+1) c x i hbits' h_c_lt h_x_lt hi]
  rw [Nat.mod_eq_of_lt h_xc_lt]

/-! ### Deliverable B — weak normal-form for step 1 (`addConstGate`)

Working-position state characterization for `addConstGate (bits + 1) c`
applied to a clean `adder_input_F (bits + 1) 0 x`. -/

/-- After step 1, the read register is zero, carries are cleared, and
target bits 0..bits encode `(x + c)` (no overflow under `x, c < N`).
This is the WEAK normal-form: it does NOT claim function equality at
positions outside the working range. -/
theorem addConstGate_modAdd_step1_state_normal
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    (∀ i, i < bits + 1 →
      Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x) (target_idx i)
      = (x + c).testBit i)
    ∧ (∀ i, i < bits + 1 →
      Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x) (read_idx i)
      = false)
    ∧ (∀ i, i < bits + 1 →
      Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x) (carry_idx i)
      = false) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have h_c_lt : c < 2^(bits+1) := by
    have : c < 2^bits := by omega
    rw [h_pow_succ]; omega
  have h_x_lt : x < 2^(bits+1) := by
    have : x < 2^bits := by omega
    rw [h_pow_succ]; omega
  obtain ⟨_, _, h_read, h_carry⟩ := addConstGate_clean (bits+1) c x hbits' h_c_lt h_x_lt
  refine ⟨?_, h_read, h_carry⟩
  intro i hi
  exact addConstGate_target_bit_no_overflow bits N c x i hbits hN hx hc hi

/-! ### Deliverable C — weak normal-form for step 2 (`subConstGate`)

Applied to a clean `adder_input_F (bits + 1) 0 s` (idealised input —
NOT the actual post-step-1 state, but the structurally-clean version),
`subConstGate (bits + 1) N` writes the widened-subtraction bits and
places the comparison flag at `target_idx bits`. -/

/-- Weak normal-form for step 2.  Same caveat as step 1: working
positions only. -/
theorem subConstGate_modAdd_step2_state_normal
    (bits N s : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hs : s < 2 * N) :
    (∀ i, i < bits + 1 →
      Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s) (target_idx i)
      = (subConstPow2WideSpec bits N s).testBit i)
    ∧ Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s) (target_idx bits)
      = decide (s < N)
    ∧ (∀ i, i < bits + 1 →
      Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s) (read_idx i)
      = false)
    ∧ (∀ i, i < bits + 1 →
      Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s) (carry_idx i)
      = false) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have h_s_lt : s < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_c : 2^(bits+1) - N < 2^(bits+1) := by
    have h_pow_pos2 : 0 < 2^(bits+1) := by rw [h_pow_succ]; omega
    omega
  unfold subConstGate
  obtain ⟨_, _, h_read, h_carry⟩ :=
    addConstGate_clean (bits+1) (2^(bits+1) - N) s hbits' h_c h_s_lt
  have h_target_bit : ∀ i, i < bits + 1 →
      Gate.applyNat (addConstGate (bits + 1) (2^(bits+1) - N)) (adder_input_F (bits + 1) 0 s)
        (target_idx i) = (subConstPow2WideSpec bits N s).testBit i := by
    intro i hi
    rw [addConstGate_target_bit (bits+1) (2^(bits+1) - N) s i hbits' h_c h_s_lt hi]
    rfl
  have h_flag :
      Gate.applyNat (addConstGate (bits + 1) (2^(bits+1) - N)) (adder_input_F (bits + 1) 0 s)
        (target_idx bits) = decide (s < N) := by
    rw [h_target_bit bits (by omega)]
    exact subConstPow2WideSpec_high_bit_bounded_sum bits N s hN_pos hN hs
  exact ⟨h_target_bit, h_flag, h_read, h_carry⟩

/-! ### Deliverable D — flag-copy gate

The single `CX (target_idx bits) flagIdx` that moves the comparison
flag from in-band `target_idx bits` to out-of-band `flagIdx`, suitable
as a control for the conditional add-back. -/

/-- Flag-copy gate: a single CX from `target_idx bits` into `flagIdx`. -/
def copyTargetHighBitToFlag (bits flagIdx : Nat) : Gate :=
  Gate.CX (target_idx bits) flagIdx

/-- Correctness: when the flag bit is initially `false`, the gate
sets it to the value of `target_idx bits`. -/
theorem copyTargetHighBitToFlag_correct
    (bits flagIdx : Nat) (f : Nat → Bool) (h_init : f flagIdx = false) :
    Gate.applyNat (copyTargetHighBitToFlag bits flagIdx) f flagIdx
    = f (target_idx bits) := by
  unfold copyTargetHighBitToFlag
  simp only [Gate.applyNat_CX]
  rw [update_eq, h_init]
  simp

/-- Frame: when `flagIdx` is out-of-band (`flagIdx ≥ adder_n_qubits (bits+1)`),
the flag-copy gate preserves all positions strictly inside the
working dimension. -/
theorem copyTargetHighBitToFlag_preserves_working
    (bits flagIdx : Nat) (f : Nat → Bool) (p : Nat)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx)
    (h_p_lt : p < adder_n_qubits (bits + 1)) :
    Gate.applyNat (copyTargetHighBitToFlag bits flagIdx) f p = f p := by
  unfold copyTargetHighBitToFlag
  simp only [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ (by unfold adder_n_qubits at *; omega : p ≠ flagIdx)]

/-- WellTyped at the enlarged dimension `flagIdx + 1`. -/
theorem copyTargetHighBitToFlag_wellTyped
    (bits flagIdx : Nat)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    Gate.WellTyped (flagIdx + 1) (copyTargetHighBitToFlag bits flagIdx) := by
  unfold copyTargetHighBitToFlag
  unfold adder_n_qubits target_idx at *
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ### Deliverable E — STATUS

Composing `addConstGate (bits+1) c → subConstGate (bits+1) N →
copyTargetHighBitToFlag bits flagIdx → conditionalAddConstGate (bits+1) N flagIdx`
into a single `modAddConstGate_dirtyFlag` gate, with the target-decode
theorem `gidney_target_val bits (...) = (x + c) % N`, is BLOCKED on
the following gate-level intermediate-state preservation gap.

**Specific blocker.**  To chain the per-step theorems via the
existing primitive infrastructure, we need the state after step 1 to
be *extensionally equal* to `adder_input_F (bits+1) 0 (x+c)` (so that
the step-2 primitive `subConstGate_clean` / `addConstGate_target_bit`
can be applied).  The WEAK normal-form (Deliverable B) gives equality
at the working positions `read_idx i, target_idx i, carry_idx i` for
`i < bits + 1` — these are positions `0..3*bits + 2`.  But the
ambient dimension `adder_n_qubits (bits + 1) = 3*bits + 5` includes
two *gap* positions `read_idx (bits + 1) = 3*bits + 3` and
`target_idx (bits + 1) = 3*bits + 4` that are touched by neither the
prep cascade nor the (`bits + 1`)-wide patched Gidney adder cascade
(whose maximum touched position is `carry_idx bits = 3*bits + 2`),
but for which we lack a Lean frame lemma.

To close this gap, the next tick needs ONE of:
(a) a frame lemma showing the patched Gidney adder of width `n`
    preserves positions `≥ 3 * n` (which would give the strong
    normal-form `Gate.applyNat (addConstGate (bits+1) c) (adder_input_F
    (bits+1) 0 x) = adder_input_F (bits+1) 0 (x + c)` extensionally);
(b) a re-proof of the patched adder's `WellTyped` at the tight
    dimension `3 * n` (which would yield the same frame via the
    existing `applyNat_commute_update_above_dim`);
(c) a `Gate.applyNat` congruence lemma at a custom dimension matching
    the cascade's actual max-touched position, plus a per-gate
    "doesn't-touch" infrastructure.

The weak normal-forms (Deliverables B and C) together with
`conditionalAddConstGate_clean` are SUFFICIENT to prove Deliverable
E's headline once any of (a)/(b)/(c) closes; the proof skeleton is
the chain `addConstGate_modAdd_step1_state_normal →
(intermediate-state bridge) → subConstGate_modAdd_step2_state_normal →
(intermediate-state bridge) → copyTargetHighBitToFlag_correct →
(intermediate-state bridge) → modAdd_step3_target_decode →
modAddConstArithmeticSpec_low_bit_correct`.

The dirty-flag composite gate is NOT defined or proved in this
commit, to avoid making any unproven claim. -/

/-! ## Tick 1 — Gap-position frame lemmas and strengthened normalization

This section closes the gap blocker by proving:

* Per-step frame lemmas: `bit_step_*_preserves_above` for the first /
  interior / last / *_reverse / *_reverse_patched gates, each with a
  tight position bound derived from the bit index.
* Cascade frame lemmas: `forward_with_propagation`,
  `forward_faithful_full`, `forward_with_propagation_reverse_patched`,
  `forward_faithful_full_reverse_patched`, `final_cx_cascade` — each
  preserves positions above its actual support.
* Full patched-adder frame: positions `≥ 3 * w` preserved.
* `prepareConstRead`, `addConstGate`, `subConstGate` frame lemmas with
  the uniform bound `3 * bits ≤ p`.
* **Strengthened state normalization** lifting the weak normal-form
  theorems to full extensional `Gate.applyNat ... = adder_input_F ...`
  equalities.

These frame lemmas close the gap-position blocker identified in the
previous section. -/

/-! ### Per-step frame lemmas -/

theorem gidney_adder_bit_step_faithful_first_preserves_above
    (f : Nat → Bool) (p : Nat) (hp : 5 ≤ p) :
    Gate.applyNat gidney_adder_bit_step_faithful_first f p = f p := by
  unfold gidney_adder_bit_step_faithful_first
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX]
  have h0 : p ≠ carry_idx 0 := by unfold carry_idx; omega
  have h1 : p ≠ read_idx 1 := by unfold read_idx; omega
  have h2 : p ≠ target_idx 1 := by unfold target_idx; omega
  rw [update_neq _ _ _ _ h2, update_neq _ _ _ _ h1, update_neq _ _ _ _ h0]

theorem gidney_adder_bit_step_faithful_interior_preserves_above
    (i : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * i + 5 ≤ p) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior i) f p = f p := by
  unfold gidney_adder_bit_step_faithful_interior
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX]
  have h_ci : p ≠ carry_idx i := by unfold carry_idx; omega
  have h_ri1 : p ≠ read_idx (i+1) := by unfold read_idx; omega
  have h_ti1 : p ≠ target_idx (i+1) := by unfold target_idx; omega
  rw [update_neq _ _ _ _ h_ti1, update_neq _ _ _ _ h_ri1, update_neq _ _ _ _ h_ci,
      update_neq _ _ _ _ h_ci]

theorem gidney_adder_bit_step_faithful_last_preserves_above
    (i : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * i + 3 ≤ p) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last i) f p = f p := by
  unfold gidney_adder_bit_step_faithful_last
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX]
  have h_ci : p ≠ carry_idx i := by unfold carry_idx; omega
  rw [update_neq _ _ _ _ h_ci, update_neq _ _ _ _ h_ci]

theorem gidney_adder_bit_step_faithful_first_reverse_preserves_above
    (f : Nat → Bool) (p : Nat) (hp : 5 ≤ p) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f p = f p := by
  unfold gidney_adder_bit_step_faithful_first_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX]
  have h0 : p ≠ carry_idx 0 := by unfold carry_idx; omega
  have h1 : p ≠ read_idx 1 := by unfold read_idx; omega
  have h2 : p ≠ target_idx 1 := by unfold target_idx; omega
  rw [update_neq _ _ _ _ h0, update_neq _ _ _ _ h1, update_neq _ _ _ _ h2]

theorem gidney_adder_bit_step_faithful_interior_reverse_preserves_above
    (i : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * i + 5 ≤ p) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f p = f p := by
  unfold gidney_adder_bit_step_faithful_interior_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX]
  have h_ci : p ≠ carry_idx i := by unfold carry_idx; omega
  have h_ri1 : p ≠ read_idx (i+1) := by unfold read_idx; omega
  have h_ti1 : p ≠ target_idx (i+1) := by unfold target_idx; omega
  rw [update_neq _ _ _ _ h_ci, update_neq _ _ _ _ h_ci, update_neq _ _ _ _ h_ri1,
      update_neq _ _ _ _ h_ti1]

theorem gidney_adder_bit_step_faithful_last_reverse_preserves_above
    (i : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * i + 3 ≤ p) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f p = f p := by
  unfold gidney_adder_bit_step_faithful_last_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX]
  have h_ci : p ≠ carry_idx i := by unfold carry_idx; omega
  rw [update_neq _ _ _ _ h_ci, update_neq _ _ _ _ h_ci]

theorem gidney_adder_bit_step_faithful_first_reverse_patched_preserves_above
    (f : Nat → Bool) (p : Nat) (hp : 5 ≤ p) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse_patched f p = f p := by
  unfold gidney_adder_bit_step_faithful_first_reverse_patched
  rw [Gate.applyNat_seq]
  have h0 : p ≠ carry_idx 0 := by unfold carry_idx; omega
  rw [Gate.applyNat_CX, update_neq _ _ _ _ h0]
  exact gidney_adder_bit_step_faithful_first_reverse_preserves_above f p hp

theorem gidney_adder_bit_step_faithful_interior_reverse_patched_preserves_above
    (i : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * i + 5 ≤ p) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched i) f p = f p := by
  unfold gidney_adder_bit_step_faithful_interior_reverse_patched
  rw [Gate.applyNat_seq]
  have h_ci : p ≠ carry_idx i := by unfold carry_idx; omega
  rw [Gate.applyNat_CX, update_neq _ _ _ _ h_ci]
  exact gidney_adder_bit_step_faithful_interior_reverse_preserves_above i f p hp

theorem gidney_adder_bit_step_faithful_last_reverse_patched_preserves_above
    (i : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * i + 3 ≤ p) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched i) f p = f p := by
  unfold gidney_adder_bit_step_faithful_last_reverse_patched
  rw [Gate.applyNat_seq]
  have h_ci : p ≠ carry_idx i := by unfold carry_idx; omega
  rw [Gate.applyNat_CX, update_neq _ _ _ _ h_ci]
  exact gidney_adder_bit_step_faithful_last_reverse_preserves_above i f p hp

/-! ### Cascade frame lemmas -/

/-- `forward_with_propagation k` preserves positions `≥ 3 * k + 2`. -/
theorem gidney_adder_forward_with_propagation_preserves_above
    (k : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * k + 2 ≤ p) :
    Gate.applyNat (gidney_adder_forward_with_propagation k) f p = f p := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      match k with
      | 0 =>
          show Gate.applyNat gidney_adder_bit_step_faithful_first f p = f p
          exact gidney_adder_bit_step_faithful_first_preserves_above f p (by omega)
      | k + 1 =>
          show Gate.applyNat (Gate.seq (gidney_adder_forward_with_propagation (k+1))
                                       (gidney_adder_bit_step_faithful_interior (k+1))) f p = f p
          rw [Gate.applyNat_seq]
          rw [gidney_adder_bit_step_faithful_interior_preserves_above (k+1) _ p (by omega)]
          exact ih _ (by omega)

/-- `forward_with_propagation_reverse_patched k` preserves positions `≥ 3 * k + 2`. -/
theorem gidney_adder_forward_with_propagation_reverse_patched_preserves_above
    (k : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * k + 2 ≤ p) :
    Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched k) f p = f p := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      match k with
      | 0 =>
          show Gate.applyNat gidney_adder_bit_step_faithful_first_reverse_patched f p = f p
          exact gidney_adder_bit_step_faithful_first_reverse_patched_preserves_above f p (by omega)
      | k + 1 =>
          show Gate.applyNat (Gate.seq (gidney_adder_bit_step_faithful_interior_reverse_patched (k+1))
                                       (gidney_adder_forward_with_propagation_reverse_patched (k+1)))
                  f p = f p
          rw [Gate.applyNat_seq]
          rw [ih _ (by omega)]
          exact gidney_adder_bit_step_faithful_interior_reverse_patched_preserves_above
                  (k+1) f p (by omega)

/-- `forward_faithful_full w` preserves positions `≥ 3 * w`. -/
theorem gidney_adder_forward_faithful_full_preserves_above
    (w : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * w ≤ p) :
    Gate.applyNat (gidney_adder_forward_faithful_full w) f p = f p := by
  match w with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
      show Gate.applyNat (Gate.seq (gidney_adder_forward_with_propagation (n+1))
                                   (gidney_adder_bit_step_faithful_last (n+1))) f p = f p
      rw [Gate.applyNat_seq]
      rw [gidney_adder_bit_step_faithful_last_preserves_above (n+1) _ p (by omega)]
      exact gidney_adder_forward_with_propagation_preserves_above (n+1) f p (by omega)

/-- `forward_faithful_full_reverse_patched w` preserves positions `≥ 3 * w`. -/
theorem gidney_adder_forward_faithful_full_reverse_patched_preserves_above
    (w : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * w ≤ p) :
    Gate.applyNat (gidney_adder_forward_faithful_full_reverse_patched w) f p = f p := by
  match w with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
      show Gate.applyNat (Gate.seq (gidney_adder_bit_step_faithful_last_reverse_patched (n+1))
                                   (gidney_adder_forward_with_propagation_reverse_patched (n+1)))
              f p = f p
      rw [Gate.applyNat_seq]
      rw [gidney_adder_forward_with_propagation_reverse_patched_preserves_above
            (n+1) _ p (by omega)]
      exact gidney_adder_bit_step_faithful_last_reverse_patched_preserves_above
              (n+1) f p (by omega)

/-- `final_cx_cascade w` preserves positions `≥ 3 * w`. -/
theorem gidney_final_cx_cascade_preserves_above
    (w : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * w ≤ p) :
    Gate.applyNat (gidney_final_cx_cascade w) f p = f p := by
  induction w generalizing f with
  | zero => rfl
  | succ k ih =>
      show Gate.applyNat (Gate.seq (gidney_final_cx_cascade k)
                                   (Gate.CX (read_idx k) (target_idx k))) f p = f p
      have h_p_rk : p ≠ read_idx k := by unfold read_idx; omega
      have h_p_tk : p ≠ target_idx k := by unfold target_idx; omega
      rw [Gate.applyNat_seq, Gate.applyNat_CX]
      rw [update_neq _ _ _ _ h_p_tk]
      exact ih _ (by omega)

/-! ### Full patched adder frame -/

/-- **Headline frame lemma**: the full patched Gidney adder of width
`w` preserves positions `p ≥ 3 * w`.  This is the tight bound: the
cascade touches positions up to `carry_idx (w-1) = 3w - 1` for `w ≥ 2`. -/
theorem gidney_adder_full_faithful_no_measurement_patched_preserves_above
    (w : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * w ≤ p) :
    Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched w) f p = f p := by
  match w with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
      show Gate.applyNat (Gate.seq
              (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                        (gidney_final_cx_cascade (n + 2)))
              (gidney_adder_forward_faithful_full_reverse_patched (n + 2))) f p = f p
      rw [Gate.applyNat_seq, Gate.applyNat_seq]
      rw [gidney_adder_forward_faithful_full_reverse_patched_preserves_above (n+2) _ p hp]
      rw [gidney_final_cx_cascade_preserves_above (n+2) _ p hp]
      exact gidney_adder_forward_faithful_full_preserves_above (n+2) f p hp

/-! ### `prepareConstRead`, `addConstGate`, `subConstGate` frames -/

/-- `prepareConstRead bits c` preserves positions `≥ 3 * bits`. -/
theorem prepareConstRead_preserves_above
    (bits c : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * bits ≤ p) :
    Gate.applyNat (prepareConstRead bits c) f p = f p := by
  apply prepareConstRead_preserves_outside
  intro i hi; unfold read_idx; omega

/-- **Composable frame**: `addConstGate bits c` preserves positions `≥ 3 * bits`. -/
theorem addConstGate_preserves_above_actual
    (bits c : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * bits ≤ p) :
    Gate.applyNat (addConstGate bits c) f p = f p := by
  unfold addConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareConstRead_preserves_above bits c _ p hp]
  rw [gidney_adder_full_faithful_no_measurement_patched_preserves_above bits _ p hp]
  exact prepareConstRead_preserves_above bits c f p hp

/-- **Composable frame**: `subConstGate bits N` preserves positions `≥ 3 * bits`. -/
theorem subConstGate_preserves_above_actual
    (bits N : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * bits ≤ p) :
    Gate.applyNat (subConstGate bits N) f p = f p :=
  addConstGate_preserves_above_actual bits (2^bits - N) f p hp

/-! ### Gap-position corollaries

For `width = bits + 1`, the two gap positions `read_idx (bits + 1)` and
`target_idx (bits + 1)` are at `3 * (bits + 1)` and `3 * (bits + 1) + 1`
respectively — both `≥ 3 * (bits + 1)`, so both preserved. -/

theorem addConstGate_preserves_gap_read
    (bits c : Nat) (f : Nat → Bool) :
    Gate.applyNat (addConstGate (bits + 1) c) f (read_idx (bits + 1))
      = f (read_idx (bits + 1)) := by
  apply addConstGate_preserves_above_actual
  unfold read_idx; omega

theorem addConstGate_preserves_gap_target
    (bits c : Nat) (f : Nat → Bool) :
    Gate.applyNat (addConstGate (bits + 1) c) f (target_idx (bits + 1))
      = f (target_idx (bits + 1)) := by
  apply addConstGate_preserves_above_actual
  unfold target_idx; omega

theorem subConstGate_preserves_gap_read
    (bits N : Nat) (f : Nat → Bool) :
    Gate.applyNat (subConstGate (bits + 1) N) f (read_idx (bits + 1))
      = f (read_idx (bits + 1)) := by
  apply subConstGate_preserves_above_actual
  unfold read_idx; omega

theorem subConstGate_preserves_gap_target
    (bits N : Nat) (f : Nat → Bool) :
    Gate.applyNat (subConstGate (bits + 1) N) f (target_idx (bits + 1))
      = f (target_idx (bits + 1)) := by
  apply subConstGate_preserves_above_actual
  unfold target_idx; omega

/-! ### Strengthened state normalization (Tick 1 Deliverable C)

With the gap-position frame closed, the per-position state assertions
now extend to FULL extensional equality between the post-gate state
and the canonical `adder_input_F` form of the new value.  This is the
strong normal-form required to chain into the next gate. -/

/-- **Strong normal-form for step 1**: `addConstGate (bits + 1) c`
applied to the clean input `adder_input_F (bits + 1) 0 x` produces a
function extensionally equal to `adder_input_F (bits + 1) 0 (x + c)`.
This supersedes the WEAK `_state_normal` form above. -/
theorem addConstGate_modAdd_step1_state_eq
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x)
    = adder_input_F (bits + 1) 0 (x + c) := by
  funext p
  by_cases hp_high : 3 * (bits + 1) ≤ p
  · rw [addConstGate_preserves_above_actual (bits + 1) c _ p hp_high]
    unfold adder_input_F
    rcases h_mod : p % 3 with _ | _ | _
    · simp [Nat.zero_testBit]
    · have h_div_ge : p / 3 ≥ bits + 1 := by omega
      simp [show ¬ (p / 3 < bits + 1) from by omega]
    · rfl
  · push_neg at hp_high
    obtain ⟨h_target, h_read, h_carry⟩ :=
      addConstGate_modAdd_step1_state_normal bits N c x hbits hN hx hc
    have h_p_div_lt : p / 3 < bits + 1 := by omega
    rcases h_mod : p % 3 with _ | _ | _
    · have h_p_eq : p = read_idx (p / 3) := by unfold read_idx; omega
      rw [h_p_eq, h_read (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (read_idx (p/3)) % 3 = 0 from by unfold read_idx; omega,
          show (read_idx (p/3)) / 3 = p/3 from by unfold read_idx; omega]
      simp [Nat.zero_testBit]
    · have h_p_eq : p = target_idx (p / 3) := by unfold target_idx; omega
      rw [h_p_eq, h_target (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (target_idx (p/3)) % 3 = 1 from by unfold target_idx; omega,
          show (target_idx (p/3)) / 3 = p/3 from by unfold target_idx; omega]
      simp [h_p_div_lt]
    · have h_p_eq : p = carry_idx (p / 3) := by unfold carry_idx; omega
      rw [h_p_eq, h_carry (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (carry_idx (p/3)) % 3 = 2 from by unfold carry_idx; omega]

/-- **Strong normal-form for step 2**: `subConstGate (bits + 1) N`
applied to the clean input `adder_input_F (bits + 1) 0 s` produces a
function extensionally equal to `adder_input_F (bits + 1) 0 y` where
`y := subConstPow2WideSpec bits N s`. -/
theorem subConstGate_modAdd_step2_state_eq
    (bits N s : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hs : s < 2 * N) :
    Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s)
    = adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N s) := by
  funext p
  by_cases hp_high : 3 * (bits + 1) ≤ p
  · rw [subConstGate_preserves_above_actual (bits + 1) N _ p hp_high]
    unfold adder_input_F
    rcases h_mod : p % 3 with _ | _ | _
    · simp [Nat.zero_testBit]
    · have h_div_ge : p / 3 ≥ bits + 1 := by omega
      simp [show ¬ (p / 3 < bits + 1) from by omega]
    · rfl
  · push_neg at hp_high
    obtain ⟨h_target, _, h_read, h_carry⟩ :=
      subConstGate_modAdd_step2_state_normal bits N s hbits hN_pos hN hs
    have h_p_div_lt : p / 3 < bits + 1 := by omega
    rcases h_mod : p % 3 with _ | _ | _
    · have h_p_eq : p = read_idx (p / 3) := by unfold read_idx; omega
      rw [h_p_eq, h_read (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (read_idx (p/3)) % 3 = 0 from by unfold read_idx; omega,
          show (read_idx (p/3)) / 3 = p/3 from by unfold read_idx; omega]
      simp [Nat.zero_testBit]
    · have h_p_eq : p = target_idx (p / 3) := by unfold target_idx; omega
      rw [h_p_eq, h_target (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (target_idx (p/3)) % 3 = 1 from by unfold target_idx; omega,
          show (target_idx (p/3)) / 3 = p/3 from by unfold target_idx; omega]
      simp [h_p_div_lt]
    · have h_p_eq : p = carry_idx (p / 3) := by unfold carry_idx; omega
      rw [h_p_eq, h_carry (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (carry_idx (p/3)) % 3 = 2 from by unfold carry_idx; omega]

/-! ## Tick 2 — Dirty-flag modular add-constant target theorem

With the strong normal-forms `addConstGate_modAdd_step1_state_eq` and
`subConstGate_modAdd_step2_state_eq` in hand, we can now chain the
four-step pipeline and prove decoded target correctness.

Pipeline: `addConstGate (bits+1) c  ;  subConstGate (bits+1) N  ;
copyTargetHighBitToFlag bits flagIdx  ;  conditionalAddConstGate (bits+1) N flagIdx`.

The OUT-OF-BAND flag bit at `flagIdx` is left DIRTY at the value
`decide ((x + c) < N)` — flag uncomputation is the next tick's task. -/

/-- Helper: `adder_input_F w a b` is `false` at any position `≥ 3 * w`
(all working positions are below `3 * w`, and out-of-range bits of `a`
and `b` are zero by the `decide(k/3 < w)` guard). -/
private theorem adder_input_F_at_high
    (w a b k : Nat) (hk : 3 * w ≤ k) :
    adder_input_F w a b k = false := by
  unfold adder_input_F
  rcases h_mod : k % 3 with _ | _ | _
  · have h_div_ge : k / 3 ≥ w := by omega
    simp [show ¬(k/3 < w) from by omega]
  · have h_div_ge : k / 3 ≥ w := by omega
    simp [show ¬(k/3 < w) from by omega]
  · rfl

/-- Bit-level conditional add-back: applied to an
`update (adder_input_F bits 0 y) flagIdx flag` input (target holds `y`,
read/carry zero, flag at `flagIdx ≥ adder_n_qubits bits`), the gate
writes `(y + (if flag then N else 0)).testBit i` at `target_idx i`
for `i < bits`. -/
theorem conditionalAddConstGate_target_bit
    (bits N flagIdx y i : Nat) (flag : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hy : y < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) (hi : i < bits) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx)
      (update (adder_input_F bits 0 y) flagIdx flag) (target_idx i)
    = (y + (if flag then N else 0)).testBit i := by
  have h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j := by
    intro j hj
    unfold adder_n_qubits read_idx at *
    omega
  have h_c_lt : (if flag then N else 0) < 2^bits := by
    cases flag with
    | true => exact hN
    | false => exact Nat.two_pow_pos bits
  unfold conditionalAddConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareMaskedConstRead_yields_input_F bits N flagIdx y flag h_disj]
  have h_wt : Gate.WellTyped (adder_n_qubits bits)
              (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  rw [applyNat_commute_update_above_dim (adder_n_qubits bits) _ h_wt _ _ _ hflagIdx]
  have h_t_neq_read : ∀ j, j < bits → target_idx i ≠ read_idx j := by
    intro j _; unfold target_idx read_idx; omega
  rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ (target_idx i) h_t_neq_read]
  have h_target_ne_flag : target_idx i ≠ flagIdx := by
    intro h_eq
    have h_flag_eq : flagIdx = target_idx i := h_eq.symm
    unfold adder_n_qubits target_idx at *
    omega
  rw [update_neq _ _ _ _ h_target_ne_flag]
  obtain ⟨_, h_target, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                              bits (if flag then N else 0) y hbits h_c_lt hy
  rw [h_target i hi, Nat.add_comm]

/-- The full DIRTY-FLAG modular add-constant gate.  Pipeline:
`addConstGate (bits+1) c  ;  subConstGate (bits+1) N  ;
copyTargetHighBitToFlag bits flagIdx  ;
conditionalAddConstGate (bits+1) N flagIdx`.

The result has the low `bits` target bits encoding `(x + c) mod N`,
but the flag bit at `flagIdx` is LEFT DIRTY at `decide ((x + c) < N)`.
Flag uncomputation is handled in a later tick. -/
def modAddConstGate_dirtyFlag (bits N c flagIdx : Nat) : Gate :=
  Gate.seq (addConstGate (bits + 1) c)
    (Gate.seq (subConstGate (bits + 1) N)
      (Gate.seq (copyTargetHighBitToFlag bits flagIdx)
        (conditionalAddConstGate (bits + 1) N flagIdx)))

/-- **Tick 2 HEADLINE**: the dirty-flag modular add-constant gate
decodes its target register (low `bits` bits) to `(x + c) mod N`. -/
theorem modAddConstGate_dirtyFlag_target_decode
    (bits N c x flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    gidney_target_val bits
      (Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
        (adder_input_F (bits + 1) 0 x))
    = (x + c) % N := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_xc_lt_pow : x + c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hbits' : 2 ≤ bits + 1 := by omega
  have hN_lt : N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_y_lt : subConstPow2WideSpec bits N (x + c) < 2^(bits+1) := by
    unfold subConstPow2WideSpec
    have : 0 < 2^(bits+1) := Nat.two_pow_pos _
    exact Nat.mod_lt _ this
  have h_y_high_bit :
      (subConstPow2WideSpec bits N (x + c)).testBit bits = decide ((x + c) < N) :=
    subConstPow2WideSpec_high_bit_bounded_sum bits N (x+c) hN_pos hN h_xc_lt_2N
  have h_input_at_flag :
      adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)) flagIdx = false := by
    apply adder_input_F_at_high
    unfold adder_n_qubits at hflagIdx; omega
  have h_input_at_tbits :
      adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)) (target_idx bits)
      = (subConstPow2WideSpec bits N (x + c)).testBit bits := by
    unfold adder_input_F
    have h_mod : (target_idx bits) % 3 = 1 := by unfold target_idx; omega
    have h_div : (target_idx bits) / 3 = bits := by unfold target_idx; omega
    rw [h_mod, h_div]
    simp [show bits < bits + 1 from by omega]
  have h_xcN_mod : (x + c) % N % 2^bits = (x + c) % N := by
    have : (x + c) % N < N := Nat.mod_lt _ hN_pos
    exact Nat.mod_eq_of_lt (by omega)
  unfold modAddConstGate_dirtyFlag
  rw [Gate.applyNat_seq, Gate.applyNat_seq, Gate.applyNat_seq]
  rw [addConstGate_modAdd_step1_state_eq bits N c x hbits hN hx hc]
  rw [subConstGate_modAdd_step2_state_eq bits N (x+c) hbits hN_pos hN h_xc_lt_2N]
  show gidney_target_val bits
    (Gate.applyNat (conditionalAddConstGate (bits + 1) N flagIdx)
      (Gate.applyNat (copyTargetHighBitToFlag bits flagIdx)
        (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c))))) = (x + c) % N
  unfold copyTargetHighBitToFlag
  rw [Gate.applyNat_CX]
  rw [h_input_at_flag, h_input_at_tbits, h_y_high_bit, Bool.false_xor]
  rw [← h_xcN_mod]
  apply gidney_target_val_eq_sum_when_bits_match bits ((x + c) % N)
  intro i hi
  rw [conditionalAddConstGate_target_bit (bits + 1) N flagIdx
        (subConstPow2WideSpec bits N (x + c)) i (decide ((x + c) < N))
        hbits' hN_lt h_y_lt hflagIdx (by omega)]
  have h_bridge :
      (subConstPow2WideSpec bits N (x + c) +
        (if (decide ((x + c) < N) = true) then N else 0)).testBit i
      = (modAddConstArithmeticSpec bits N c x).testBit i := by
    unfold modAddConstArithmeticSpec
    rw [Nat.testBit_mod_two_pow]
    simp [show i < bits + 1 from by omega]
  rw [h_bridge]
  exact modAddConstArithmeticSpec_low_bit_correct bits N c x i hN_pos hN hx hc hi

/-! ## Tick 3 — Dirty-flag workspace theorem

Prove workspace properties for `modAddConstGate_dirtyFlag`: WellTyped,
read register restored to zero, carry register cleared, and flag bit
exactly `decide ((x + c) < N)`.  Flag-bit restoration is NOT claimed
here; that is the next tick's task. -/

/-- Intermediate: the state after the first three steps (add ; sub ;
copy-flag) of `modAddConstGate_dirtyFlag` is extensionally equal to
`update (adder_input_F (bits+1) 0 y) flagIdx (decide ((x+c)<N))`,
where `y := subConstPow2WideSpec bits N (x+c)`. -/
theorem modAddConstGate_dirtyFlag_after_three_steps_eq
    (bits N c x flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
      (Gate.seq (subConstGate (bits + 1) N)
        (copyTargetHighBitToFlag bits flagIdx)))
      (adder_input_F (bits + 1) 0 x)
    = update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c))) flagIdx
        (decide ((x + c) < N)) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_y_high_bit :
      (subConstPow2WideSpec bits N (x + c)).testBit bits = decide ((x + c) < N) :=
    subConstPow2WideSpec_high_bit_bounded_sum bits N (x+c) hN_pos hN h_xc_lt_2N
  have h_input_at_flag :
      adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)) flagIdx = false := by
    apply adder_input_F_at_high
    unfold adder_n_qubits at hflagIdx; omega
  have h_input_at_tbits :
      adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)) (target_idx bits)
      = (subConstPow2WideSpec bits N (x + c)).testBit bits := by
    unfold adder_input_F
    have h_mod : (target_idx bits) % 3 = 1 := by unfold target_idx; omega
    have h_div : (target_idx bits) / 3 = bits := by unfold target_idx; omega
    rw [h_mod, h_div]
    simp [show bits < bits + 1 from by omega]
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [addConstGate_modAdd_step1_state_eq bits N c x hbits hN hx hc]
  rw [subConstGate_modAdd_step2_state_eq bits N (x+c) hbits hN_pos hN h_xc_lt_2N]
  unfold copyTargetHighBitToFlag
  rw [Gate.applyNat_CX]
  rw [h_input_at_flag, h_input_at_tbits, h_y_high_bit, Bool.false_xor]

/-- **Tick 3 HEADLINE — dirty-flag workspace theorem**.  The
`modAddConstGate_dirtyFlag` is WellTyped at the enlarged dimension
`flagIdx + 1`, restores the read register to zero, clears the carry
register, and places the comparison flag `decide ((x + c) < N)` at
`flagIdx`.  The flag bit is DIRTY — not restored to false. -/
theorem modAddConstGate_dirtyFlag_workspace
    (bits N c x flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    Gate.WellTyped (flagIdx + 1) (modAddConstGate_dirtyFlag bits N c flagIdx)
    ∧ (∀ i, i < bits + 1 →
        Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
          (adder_input_F (bits + 1) 0 x) (read_idx i) = false)
    ∧ (∀ i, i < bits + 1 →
        Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
          (adder_input_F (bits + 1) 0 x) (carry_idx i) = false)
    ∧ Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
        (adder_input_F (bits + 1) 0 x) flagIdx = decide ((x + c) < N) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have hbits' : 2 ≤ bits + 1 := by omega
  have hN_lt : N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hN_le_succ : N ≤ 2^(bits+1) := by omega
  have h_y_lt : subConstPow2WideSpec bits N (x + c) < 2^(bits+1) := by
    unfold subConstPow2WideSpec
    have : 0 < 2^(bits+1) := Nat.two_pow_pos _
    exact Nat.mod_lt _ this
  have h_c_lt : c < 2^(bits+1) := by
    have : c < 2^bits := by omega
    rw [h_pow_succ]; omega
  have h_x_lt : x < 2^(bits+1) := by
    have : x < 2^bits := by omega
    rw [h_pow_succ]; omega
  have h_flag_succ : adder_n_qubits (bits + 1) ≤ flagIdx + 1 := by omega
  have h_3 := modAddConstGate_dirtyFlag_after_three_steps_eq
                bits N c x flagIdx hbits hN_pos hN hx hc hflagIdx
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- WellTyped at flagIdx + 1
    unfold modAddConstGate_dirtyFlag
    obtain ⟨h_add_wt, _, _, _⟩ := addConstGate_clean (bits+1) c x hbits' h_c_lt h_x_lt
    have h_add_wt' : Gate.WellTyped (flagIdx + 1) (addConstGate (bits + 1) c) :=
      Gate.WellTyped.mono h_add_wt h_flag_succ
    obtain ⟨h_sub_wt, _, _, _⟩ := subConstGate_clean (bits+1) N x hbits' hN_pos hN_le_succ h_x_lt
    have h_sub_wt' : Gate.WellTyped (flagIdx + 1) (subConstGate (bits + 1) N) :=
      Gate.WellTyped.mono h_sub_wt h_flag_succ
    have h_copy_wt : Gate.WellTyped (flagIdx + 1) (copyTargetHighBitToFlag bits flagIdx) :=
      copyTargetHighBitToFlag_wellTyped bits flagIdx hflagIdx
    have h_cond_wt : Gate.WellTyped (flagIdx + 1) (conditionalAddConstGate (bits+1) N flagIdx) :=
      conditionalAddConstGate_wellTyped (bits+1) N flagIdx hbits' hflagIdx
    exact ⟨h_add_wt', h_sub_wt', h_copy_wt, h_cond_wt⟩
  · -- read register restored
    intro i hi
    show Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
          (adder_input_F (bits + 1) 0 x) (read_idx i) = false
    unfold modAddConstGate_dirtyFlag
    rw [show Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
            (Gate.seq (subConstGate (bits + 1) N)
              (Gate.seq (copyTargetHighBitToFlag bits flagIdx)
                (conditionalAddConstGate (bits + 1) N flagIdx))))
            (adder_input_F (bits + 1) 0 x)
          = Gate.applyNat (conditionalAddConstGate (bits + 1) N flagIdx)
              (Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
                  (Gate.seq (subConstGate (bits + 1) N)
                    (copyTargetHighBitToFlag bits flagIdx)))
                (adder_input_F (bits + 1) 0 x)) from rfl]
    rw [h_3]
    exact conditionalAddConstGate_read_restored (bits+1) N
            (subConstPow2WideSpec bits N (x+c)) flagIdx (decide ((x+c)<N))
            hbits' hN_lt h_y_lt hflagIdx i hi
  · -- carry register cleared
    intro i hi
    show Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
          (adder_input_F (bits + 1) 0 x) (carry_idx i) = false
    unfold modAddConstGate_dirtyFlag
    rw [show Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
            (Gate.seq (subConstGate (bits + 1) N)
              (Gate.seq (copyTargetHighBitToFlag bits flagIdx)
                (conditionalAddConstGate (bits + 1) N flagIdx))))
            (adder_input_F (bits + 1) 0 x)
          = Gate.applyNat (conditionalAddConstGate (bits + 1) N flagIdx)
              (Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
                  (Gate.seq (subConstGate (bits + 1) N)
                    (copyTargetHighBitToFlag bits flagIdx)))
                (adder_input_F (bits + 1) 0 x)) from rfl]
    rw [h_3]
    exact conditionalAddConstGate_carries_cleared (bits+1) N
            (subConstPow2WideSpec bits N (x+c)) flagIdx (decide ((x+c)<N))
            hbits' hN_lt h_y_lt hflagIdx i hi
  · -- flag bit value
    show Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
          (adder_input_F (bits + 1) 0 x) flagIdx = decide ((x + c) < N)
    unfold modAddConstGate_dirtyFlag
    rw [show Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
            (Gate.seq (subConstGate (bits + 1) N)
              (Gate.seq (copyTargetHighBitToFlag bits flagIdx)
                (conditionalAddConstGate (bits + 1) N flagIdx))))
            (adder_input_F (bits + 1) 0 x)
          = Gate.applyNat (conditionalAddConstGate (bits + 1) N flagIdx)
              (Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
                  (Gate.seq (subConstGate (bits + 1) N)
                    (copyTargetHighBitToFlag bits flagIdx)))
                (adder_input_F (bits + 1) 0 x)) from rfl]
    rw [h_3]
    exact conditionalAddConstGate_flag_preserved (bits+1) N
            (subConstPow2WideSpec bits N (x+c)) flagIdx (decide ((x+c)<N))
            hbits' hflagIdx

/-! ## Tick 4 — Flag uncomputation design + proof

**Design.**  After `modAddConstGate_dirtyFlag`, target = `m := (x+c) mod N`
and flag = `decide ((x+c) < N)`.  We use the identity
`flag = decide (m ≥ c)` (proved by case analysis on `(x+c)<N`):
* if `(x+c) < N`: `m = x+c`, so `m ≥ c` (since `x ≥ 0`);
* if `(x+c) ≥ N`: `m = x+c-N`, so `m < c` (since `x < N`).

The reversible uncompute is a four-step gate:
1. `subConstGate (bits+1) c` — target → `subConstPow2Spec (bits+1) c m`.
   By `subConstPow2WideSpec_high_bit`, `target_idx bits = decide (m < c)`.
2. `CX (target_idx bits) flagIdx` — XOR-in: flag becomes
   `decide (m ≥ c) XOR decide (m < c) = true`.
3. `X flagIdx` — flag becomes `false`.
4. `addConstGate (bits+1) c` — target restored to `m`.

Read/carry are restored automatically by the add/sub workspace.  This
implementation uses ONLY existing Gate IR primitives (no controlled-CCX). -/

/-! ### Generalized state-eq for add/sub at width `n`

For the uncompute proof we need state-eq under just `c < 2^n, x < 2^n`,
without the modular `x < N, c < N` hypothesis.  Both forms work via the
same per-position case analysis. -/

/-- General state-eq: `addConstGate bits c` applied to a clean input
`adder_input_F bits 0 x` produces `adder_input_F bits 0 ((x + c) % 2^bits)`,
under just `c < 2^bits` and `x < 2^bits`. -/
theorem addConstGate_state_eq_general
    (bits c x : Nat) (hbits : 2 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits) :
    Gate.applyNat (addConstGate bits c) (adder_input_F bits 0 x)
    = adder_input_F bits 0 ((x + c) % 2^bits) := by
  funext p
  by_cases hp_high : 3 * bits ≤ p
  · rw [addConstGate_preserves_above_actual bits c _ p hp_high]
    unfold adder_input_F
    rcases h_mod : p % 3 with _ | _ | _
    · simp [Nat.zero_testBit]
    · have h_div_ge : p / 3 ≥ bits := by omega
      simp [show ¬ (p / 3 < bits) from by omega]
    · rfl
  · push_neg at hp_high
    obtain ⟨_, _, h_read, h_carry⟩ := addConstGate_clean bits c x hbits hc hx
    have h_p_div_lt : p / 3 < bits := by omega
    rcases h_mod : p % 3 with _ | _ | _
    · have h_p_eq : p = read_idx (p / 3) := by unfold read_idx; omega
      rw [h_p_eq, h_read (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (read_idx (p/3)) % 3 = 0 from by unfold read_idx; omega,
          show (read_idx (p/3)) / 3 = p/3 from by unfold read_idx; omega]
      simp [Nat.zero_testBit]
    · have h_p_eq : p = target_idx (p / 3) := by unfold target_idx; omega
      rw [h_p_eq, addConstGate_target_bit bits c x (p/3) hbits hc hx h_p_div_lt]
      unfold adder_input_F
      rw [show (target_idx (p/3)) % 3 = 1 from by unfold target_idx; omega,
          show (target_idx (p/3)) / 3 = p/3 from by unfold target_idx; omega]
      simp [h_p_div_lt]
    · have h_p_eq : p = carry_idx (p / 3) := by unfold carry_idx; omega
      rw [h_p_eq, h_carry (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (carry_idx (p/3)) % 3 = 2 from by unfold carry_idx; omega]

/-- General state-eq for subConstGate.  Follows from
`addConstGate_state_eq_general` via the definition `subConstGate = addConstGate (2^bits - N)`. -/
theorem subConstGate_state_eq_general
    (bits N x : Nat) (hbits : 2 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.applyNat (subConstGate bits N) (adder_input_F bits 0 x)
    = adder_input_F bits 0 (subConstPow2Spec bits N x) := by
  unfold subConstGate
  have hc : 2^bits - N < 2^bits := by
    have : 0 < 2^bits := Nat.two_pow_pos bits
    omega
  rw [addConstGate_state_eq_general bits (2^bits - N) x hbits hc hx]
  rfl

/-! ### Flag-uncompute gate -/

/-- Reversible flag-uncompute gate: `subConstGate c ; CX (target_idx bits) flagIdx ;
X flagIdx ; addConstGate c`.  Restores `flagIdx` to false while leaving the
target, read, and carry registers unchanged. -/
def flagUncomputeGate (bits c flagIdx : Nat) : Gate :=
  Gate.seq (subConstGate (bits + 1) c)
    (Gate.seq (Gate.CX (target_idx bits) flagIdx)
      (Gate.seq (Gate.X flagIdx)
        (addConstGate (bits + 1) c)))

/-- **Tick 4 HEADLINE — flag uncomputation correctness**.  Given a state
of the form `update (adder_input_F (bits+1) 0 m) flagIdx (decide (m ≥ c))`
(target encoding `m < 2^bits`, flag stored at out-of-band `flagIdx`),
the flag-uncompute gate restores the state to a clean
`adder_input_F (bits+1) 0 m` — i.e., flag becomes false, target / read /
carry unchanged. -/
theorem flagUncomputeGate_correct
    (bits c flagIdx m : Nat) (hbits : 1 ≤ bits) (hc_pos : 0 < c)
    (hc : c < 2^bits) (hm : m < 2^bits)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    Gate.applyNat (flagUncomputeGate bits c flagIdx)
      (update (adder_input_F (bits + 1) 0 m) flagIdx (decide (m ≥ c)))
    = adder_input_F (bits + 1) 0 m := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have hc_succ : c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hc_le_succ : c ≤ 2^(bits+1) := by omega
  have hm_succ : m < 2^(bits+1) := by rw [h_pow_succ]; omega
  obtain ⟨h_sub_wt, _, _, _⟩ := subConstGate_clean (bits+1) c c hbits' hc_pos hc_le_succ hc_succ
  have h_flag_eq : decide (m ≥ c) = !decide (m < c) := by
    rcases Nat.lt_or_ge m c with h | h
    · rw [decide_eq_true h, decide_eq_false (Nat.not_le.mpr h)]; rfl
    · rw [decide_eq_false (Nat.not_lt.mpr h), decide_eq_true h]; rfl
  unfold flagUncomputeGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq, Gate.applyNat_seq]
  rw [applyNat_commute_update_above_dim (adder_n_qubits (bits+1))
        (subConstGate (bits+1) c) h_sub_wt _ _ _ hflagIdx]
  rw [subConstGate_state_eq_general (bits+1) c m hbits' hc_pos hc_le_succ hm_succ]
  have h_mp_high :
      (subConstPow2Spec (bits+1) c m).testBit bits = decide (m < c) := by
    show ((m + (2^(bits+1) - c)) % 2^(bits+1)).testBit bits = decide (m < c)
    rw [show ((m + (2^(bits+1) - c)) % 2^(bits+1)) = subConstPow2WideSpec bits c m from by
          unfold subConstPow2WideSpec; rfl]
    exact subConstPow2WideSpec_high_bit bits c m (by omega) hm
  have h_ainput_tbits :
      adder_input_F (bits+1) 0 (subConstPow2Spec (bits+1) c m) (target_idx bits)
      = (subConstPow2Spec (bits+1) c m).testBit bits := by
    unfold adder_input_F
    rw [show (target_idx bits) % 3 = 1 from by unfold target_idx; omega,
        show (target_idx bits) / 3 = bits from by unfold target_idx; omega]
    simp [show bits < bits+1 from by omega]
  have h_flagIdx_ne_tbits : flagIdx ≠ target_idx bits := by
    unfold adder_n_qubits target_idx at *; omega
  have h_tbits_ne_flag : target_idx bits ≠ flagIdx := fun h => h_flagIdx_ne_tbits h.symm
  rw [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ h_tbits_ne_flag, update_eq, h_ainput_tbits, h_mp_high, h_flag_eq]
  have h_xor : ((!decide (m < c) ^^ decide (m < c)) : Bool) = true := by
    generalize decide (m < c) = b
    cases b <;> rfl
  rw [h_xor]
  rw [Gate.applyNat_X, update_eq]
  have h_collapse :
      ∀ (g : Nat → Bool) (v1 v2 v3 : Bool),
        update (update (update g flagIdx v1) flagIdx v2) flagIdx v3 = update g flagIdx v3 := by
    intros g v1 v2 v3
    funext k
    by_cases hk : k = flagIdx
    · subst hk; rw [update_eq, update_eq]
    · rw [update_neq _ _ _ _ hk, update_neq _ _ _ _ hk, update_neq _ _ _ _ hk,
          update_neq _ _ _ _ hk]
  rw [h_collapse]
  have h_input_flag :
      adder_input_F (bits+1) 0 (subConstPow2Spec (bits+1) c m) flagIdx = false := by
    apply adder_input_F_at_high
    unfold adder_n_qubits at hflagIdx; omega
  have h_update_eq :
      update (adder_input_F (bits+1) 0 (subConstPow2Spec (bits+1) c m)) flagIdx false
      = adder_input_F (bits+1) 0 (subConstPow2Spec (bits+1) c m) := by
    funext k
    by_cases hk : k = flagIdx
    · subst hk; rw [update_eq, h_input_flag]
    · rw [update_neq _ _ _ _ hk]
  show Gate.applyNat (addConstGate (bits + 1) c)
        (update (adder_input_F (bits+1) 0 (subConstPow2Spec (bits+1) c m)) flagIdx (!true))
      = adder_input_F (bits+1) 0 m
  rw [Bool.not_true, h_update_eq]
  rw [addConstGate_state_eq_general (bits+1) c (subConstPow2Spec (bits+1) c m) hbits' hc_succ
        (by show subConstPow2Spec (bits+1) c m < 2^(bits+1)
            unfold subConstPow2Spec; exact Nat.mod_lt _ (by rw [h_pow_succ]; omega))]
  congr 1
  show (subConstPow2Spec (bits+1) c m + c) % 2^(bits+1) = m
  unfold subConstPow2Spec
  rw [Nat.mod_add_mod]
  have h_eq : m + (2^(bits+1) - c) + c = m + 2^(bits+1) := by omega
  rw [h_eq, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hm_succ

/-- WellTyped at `flagIdx + 1`.  All four sub-gates are WellTyped at
`adder_n_qubits (bits + 1) ≤ flagIdx + 1`; the CX and X explicitly touch
`flagIdx`. -/
theorem flagUncomputeGate_wellTyped
    (bits c flagIdx : Nat) (hbits : 1 ≤ bits) (hc_pos : 0 < c) (hc : c < 2^bits)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    Gate.WellTyped (flagIdx + 1) (flagUncomputeGate bits c flagIdx) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have hc_succ : c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hc_le_succ : c ≤ 2^(bits+1) := by omega
  have h_flag_succ : adder_n_qubits (bits + 1) ≤ flagIdx + 1 := by omega
  unfold flagUncomputeGate
  obtain ⟨h_sub_wt, _, _, _⟩ := subConstGate_clean (bits+1) c c hbits' hc_pos hc_le_succ hc_succ
  have h_sub_wt' : Gate.WellTyped (flagIdx + 1) (subConstGate (bits + 1) c) :=
    Gate.WellTyped.mono h_sub_wt h_flag_succ
  obtain ⟨h_add_wt, _, _, _⟩ := addConstGate_clean (bits+1) c c hbits' hc_succ hc_succ
  have h_add_wt' : Gate.WellTyped (flagIdx + 1) (addConstGate (bits + 1) c) :=
    Gate.WellTyped.mono h_add_wt h_flag_succ
  have h_cx_wt : Gate.WellTyped (flagIdx + 1) (Gate.CX (target_idx bits) flagIdx) := by
    unfold adder_n_qubits target_idx at *
    refine ⟨?_, ?_, ?_⟩ <;> omega
  have h_x_wt : Gate.WellTyped (flagIdx + 1) (Gate.X flagIdx) := by
    show flagIdx < flagIdx + 1; omega
  exact ⟨h_sub_wt', h_cx_wt, h_x_wt, h_add_wt'⟩

/-! ## Tick 5 — Clean modular add-constant gate

Compose `modAddConstGate_dirtyFlag` with `flagUncomputeGate` to obtain
the *clean* modular add-constant gate `modAddConstGate`, whose output
is extensionally `adder_input_F (bits + 1) 0 ((x + c) mod N)` — i.e.,
target encodes `(x + c) mod N`, ALL workspace restored including the
flag bit.

The internal `flagIdx` is fixed at `adder_n_qubits (bits + 1)` (the
smallest valid out-of-band position).

Restriction: this clean gate requires `0 < c` (since `flagUncomputeGate`
uses `subConstGate (bits + 1) c` which requires `c > 0`).  The `c = 0`
case is degenerate (modular add by 0 = identity) and not handled here. -/

/-- Auxiliary: `modAddConstArithmeticSpec bits N c x < 2^bits` under
modular hypotheses.  Both flag cases produce a value in `[0, N - 1]`,
hence `< 2^bits`. -/
theorem modAddConstArithmeticSpec_lt_pow_bits
    (bits N c x : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N) :
    modAddConstArithmeticSpec bits N c x < 2^bits := by
  unfold modAddConstArithmeticSpec
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_pow_pos2 : 0 < 2^(bits+1) := by rw [h_pow_succ]; omega
  by_cases h_flag : x + c < N
  · have h_y : subConstPow2WideSpec bits N (x + c) = (x + c) + 2^(bits+1) - N := by
      unfold subConstPow2WideSpec
      have h_lt : (x + c) + (2^(bits+1) - N) < 2^(bits+1) := by omega
      rw [Nat.mod_eq_of_lt h_lt]; omega
    rw [h_y, decide_eq_true h_flag]
    show ((x + c) + 2^(bits+1) - N + N) % 2^(bits+1) < 2^bits
    have h_eq : ((x + c) + 2^(bits+1) - N) + N = (x + c) + 2^(bits+1) := by omega
    rw [h_eq, Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (show x + c < 2^(bits+1) by omega)]
    omega
  · have h_le : N ≤ x + c := by omega
    have h_y : subConstPow2WideSpec bits N (x + c) = (x + c) - N := by
      unfold subConstPow2WideSpec
      have h_eq2 : (x + c) + (2^(bits + 1) - N) = ((x + c) - N) + 2^(bits + 1) := by omega
      rw [h_eq2, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_y, decide_eq_false (by omega)]
    show ((x + c) - N + 0) % 2^(bits+1) < 2^bits
    rw [Nat.add_zero]
    have h_sN_lt : (x + c) - N < 2^bits := by omega
    have h_sN_lt' : (x + c) - N < 2^(bits+1) := by omega
    rw [Nat.mod_eq_of_lt h_sN_lt']
    exact h_sN_lt

/-- `modAddConstArithmeticSpec` equals `(x + c) mod N` (the high bit is
zero, so the mod-`2^(bits+1)` mask is the value itself). -/
theorem modAddConstArithmeticSpec_eq_mod
    (bits N c x : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N) :
    modAddConstArithmeticSpec bits N c x = (x + c) % N := by
  have h1 := modAddConstArithmeticSpec_correct bits N c x hN_pos hN hx hc
  have h2 := modAddConstArithmeticSpec_lt_pow_bits bits N c x hN_pos hN hx hc
  rw [Nat.mod_eq_of_lt h2] at h1
  exact h1

/-! ### Frame lemmas for `conditionalAddConstGate` and `modAddConstGate_dirtyFlag` -/

/-- `conditionalAddConstGate bits N flagIdx` preserves positions `≥ 3 * bits`. -/
theorem conditionalAddConstGate_preserves_above_not_flag
    (bits N flagIdx : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * bits ≤ p) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx) f p = f p := by
  unfold conditionalAddConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  have h_p_ne_read : ∀ i, i < bits → p ≠ read_idx i := by
    intro i hi; unfold read_idx; omega
  rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ p h_p_ne_read]
  rw [gidney_adder_full_faithful_no_measurement_patched_preserves_above bits _ p hp]
  exact prepareMaskedConstRead_preserves_outside bits N flagIdx f p h_p_ne_read

/-- `modAddConstGate_dirtyFlag bits N c flagIdx` preserves positions `≥ 3*(bits + 1)`
that are not `flagIdx`. -/
theorem modAddConstGate_dirtyFlag_preserves_above_not_flag
    (bits N c flagIdx : Nat) (f : Nat → Bool) (p : Nat)
    (hp : 3 * (bits + 1) ≤ p) (h_p_ne_flag : p ≠ flagIdx) :
    Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx) f p = f p := by
  unfold modAddConstGate_dirtyFlag
  rw [Gate.applyNat_seq, Gate.applyNat_seq, Gate.applyNat_seq]
  rw [conditionalAddConstGate_preserves_above_not_flag (bits+1) N flagIdx _ p hp]
  unfold copyTargetHighBitToFlag
  rw [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ h_p_ne_flag]
  rw [subConstGate_preserves_above_actual (bits+1) N _ p hp]
  exact addConstGate_preserves_above_actual (bits+1) c f p hp

/-- **Strong state-eq for `modAddConstGate_dirtyFlag`**.  The output is
extensionally equal to the canonical "input form" with target encoding
`(x + c) mod N` and the flag bit at `flagIdx` holding `decide ((x+c)<N)`. -/
theorem modAddConstGate_dirtyFlag_state_eq
    (bits N c x flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
      (adder_input_F (bits + 1) 0 x)
    = update (adder_input_F (bits + 1) 0 ((x + c) % N)) flagIdx (decide ((x + c) < N)) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have hbits' : 2 ≤ bits + 1 := by omega
  have hN_lt : N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_y_lt : subConstPow2WideSpec bits N (x + c) < 2^(bits+1) := by
    unfold subConstPow2WideSpec; exact Nat.mod_lt _ (by rw [h_pow_succ]; omega)
  obtain ⟨_, h_read, h_carry, h_flag⟩ :=
    modAddConstGate_dirtyFlag_workspace bits N c x flagIdx hbits hN_pos hN hx hc hflagIdx
  have h_apply_unfold :
      ∀ (g : Nat → Bool) (p : Nat),
        Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx) g p
        = Gate.applyNat (conditionalAddConstGate (bits + 1) N flagIdx)
            (Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
              (Gate.seq (subConstGate (bits + 1) N)
                (copyTargetHighBitToFlag bits flagIdx))) g) p := by
    intros g p; rfl
  have h_target : ∀ i, i < bits + 1 →
      Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
        (adder_input_F (bits + 1) 0 x) (target_idx i)
      = ((x + c) % N).testBit i := by
    intro i hi
    rw [h_apply_unfold]
    rw [modAddConstGate_dirtyFlag_after_three_steps_eq
          bits N c x flagIdx hbits hN_pos hN hx hc hflagIdx]
    rw [conditionalAddConstGate_target_bit (bits + 1) N flagIdx
          (subConstPow2WideSpec bits N (x + c)) i (decide ((x + c) < N))
          hbits' hN_lt h_y_lt hflagIdx hi]
    have h_bridge :
        (subConstPow2WideSpec bits N (x + c)
          + (if decide ((x + c) < N) = true then N else 0)).testBit i
        = (modAddConstArithmeticSpec bits N c x).testBit i := by
      unfold modAddConstArithmeticSpec
      rw [Nat.testBit_mod_two_pow]; simp [hi]
    rw [h_bridge]
    rw [modAddConstArithmeticSpec_eq_mod bits N c x hN_pos hN hx hc]
  funext p
  by_cases h_p_flag : p = flagIdx
  · subst h_p_flag; rw [h_flag, update_eq]
  · by_cases h_p_high : 3 * (bits + 1) ≤ p
    · rw [modAddConstGate_dirtyFlag_preserves_above_not_flag
            bits N c flagIdx _ p h_p_high h_p_flag]
      rw [update_neq _ _ _ _ h_p_flag]
      unfold adder_input_F
      rcases h_mod : p % 3 with _ | _ | _
      · simp [show ¬(p/3 < bits+1) from by omega]
      · simp [show ¬(p/3 < bits+1) from by omega]
      · rfl
    · push_neg at h_p_high
      have h_p_div_lt : p / 3 < bits + 1 := by omega
      rcases h_mod : p % 3 with _ | _ | _
      · have h_p_eq : p = read_idx (p / 3) := by unfold read_idx; omega
        rw [h_p_eq, h_read (p/3) h_p_div_lt]
        rw [update_neq _ _ _ _ (by rw [← h_p_eq]; exact h_p_flag)]
        unfold adder_input_F
        rw [show (read_idx (p/3)) % 3 = 0 from by unfold read_idx; omega,
            show (read_idx (p/3)) / 3 = p/3 from by unfold read_idx; omega]
        simp [Nat.zero_testBit]
      · have h_p_eq : p = target_idx (p / 3) := by unfold target_idx; omega
        rw [h_p_eq, h_target (p/3) h_p_div_lt]
        rw [update_neq _ _ _ _ (by rw [← h_p_eq]; exact h_p_flag)]
        unfold adder_input_F
        rw [show (target_idx (p/3)) % 3 = 1 from by unfold target_idx; omega,
            show (target_idx (p/3)) / 3 = p/3 from by unfold target_idx; omega]
        simp [h_p_div_lt]
      · have h_p_eq : p = carry_idx (p / 3) := by unfold carry_idx; omega
        rw [h_p_eq, h_carry (p/3) h_p_div_lt]
        rw [update_neq _ _ _ _ (by rw [← h_p_eq]; exact h_p_flag)]
        unfold adder_input_F
        rw [show (carry_idx (p/3)) % 3 = 2 from by unfold carry_idx; omega]

/-- **Clean modular add-constant gate**.  Composition of the dirty-flag
pipeline with the flag-uncompute step.  The internal flag bit lives at
`adder_n_qubits (bits + 1)`. -/
def modAddConstGate (bits N c : Nat) : Gate :=
  Gate.seq (modAddConstGate_dirtyFlag bits N c (adder_n_qubits (bits + 1)))
    (flagUncomputeGate bits c (adder_n_qubits (bits + 1)))

/-- **Tick 5 HEADLINE — clean modular add-constant**.  Applied to
`adder_input_F (bits + 1) 0 x`, the clean modular adder produces
`adder_input_F (bits + 1) 0 ((x + c) mod N)` — full state-eq with
target encoding the modular sum and ALL workspace (read, carry,
internal flag) restored. -/
theorem modAddConstGate_state_eq
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc_pos : 0 < c) (hc : c < N) :
    Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x)
    = adder_input_F (bits + 1) 0 ((x + c) % N) := by
  unfold modAddConstGate
  rw [Gate.applyNat_seq]
  rw [modAddConstGate_dirtyFlag_state_eq bits N c x (adder_n_qubits (bits + 1))
        hbits hN_pos hN hx hc (le_refl _)]
  have h_decide_eq : decide ((x + c) < N) = decide ((x + c) % N ≥ c) := by
    by_cases h : x + c < N
    · have h_mod : (x + c) % N = x + c := Nat.mod_eq_of_lt h
      rw [decide_eq_true h, h_mod]
      rw [decide_eq_true (by omega : x + c ≥ c)]
    · have h_le : N ≤ x + c := by omega
      have h_lt : x + c < 2 * N := by omega
      have h_mod : (x + c) % N = x + c - N := by
        have h_eq : x + c = (x + c - N) + N := by omega
        conv_lhs => rw [h_eq]
        rw [Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [decide_eq_false (by omega), h_mod]
      rw [decide_eq_false (by omega : ¬ x + c - N ≥ c)]
  rw [h_decide_eq]
  have h_xcN_lt_2bits : (x + c) % N < 2^bits := by
    have : (x + c) % N < N := Nat.mod_lt _ hN_pos
    omega
  exact flagUncomputeGate_correct bits c (adder_n_qubits (bits + 1)) ((x + c) % N)
          hbits hc_pos (by omega) h_xcN_lt_2bits (le_refl _)

/-- **Bundled clean theorem** — WellTyped, decoded target, read /
carry / flag all restored.  Derives from `modAddConstGate_state_eq`. -/
theorem modAddConstGate_clean
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc_pos : 0 < c) (hc : c < N) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + 1) (modAddConstGate bits N c)
    ∧ gidney_target_val bits
        (Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x))
      = (x + c) % N
    ∧ (∀ i, i < bits + 1 →
        Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x)
          (read_idx i) = false)
    ∧ (∀ i, i < bits + 1 →
        Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x)
          (carry_idx i) = false)
    ∧ Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x)
        (adder_n_qubits (bits + 1)) = false := by
  have h_state := modAddConstGate_state_eq bits N c x hbits hN_pos hN hx hc_pos hc
  have h_xcN_lt_N : (x + c) % N < N := Nat.mod_lt _ hN_pos
  have h_xcN_lt_2bits : (x + c) % N < 2^bits := by omega
  have h_xcN_mod_2bits : (x + c) % N % 2^bits = (x + c) % N :=
    Nat.mod_eq_of_lt h_xcN_lt_2bits
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- WellTyped: composition
    unfold modAddConstGate
    have h_flag_succ : adder_n_qubits (bits + 1) ≤ adder_n_qubits (bits + 1) := le_refl _
    have h_dirty_wt :
        Gate.WellTyped (adder_n_qubits (bits + 1) + 1)
          (modAddConstGate_dirtyFlag bits N c (adder_n_qubits (bits + 1))) := by
      have := (modAddConstGate_dirtyFlag_workspace bits N c x (adder_n_qubits (bits + 1))
                hbits hN_pos hN hx hc h_flag_succ).1
      exact this
    have h_unc_wt :
        Gate.WellTyped (adder_n_qubits (bits + 1) + 1)
          (flagUncomputeGate bits c (adder_n_qubits (bits + 1))) :=
      flagUncomputeGate_wellTyped bits c (adder_n_qubits (bits + 1)) hbits hc_pos
        (by omega) h_flag_succ
    exact ⟨h_dirty_wt, h_unc_wt⟩
  · -- target decode
    rw [h_state]
    rw [← h_xcN_mod_2bits]
    apply gidney_target_val_eq_sum_when_bits_match bits ((x + c) % N)
    intro i hi
    unfold adder_input_F
    rw [show (target_idx i) % 3 = 1 from by unfold target_idx; omega,
        show (target_idx i) / 3 = i from by unfold target_idx; omega]
    simp only [show decide (i < bits + 1) = true from decide_eq_true (by omega),
               Bool.true_and]
    rw [h_xcN_mod_2bits]
  · -- read restored
    intro i hi
    rw [h_state]
    unfold adder_input_F
    rw [show (read_idx i) % 3 = 0 from by unfold read_idx; omega,
        show (read_idx i) / 3 = i from by unfold read_idx; omega]
    simp [Nat.zero_testBit]
  · -- carries cleared
    intro i hi
    rw [h_state]
    unfold adder_input_F
    rw [show (carry_idx i) % 3 = 2 from by unfold carry_idx; omega]
  · -- flag restored to false
    rw [h_state]
    apply adder_input_F_at_high
    unfold adder_n_qubits; omega

/-! ## Tick 6 — Controlled modular add-constant (skeleton + WellTyped)

For modular multiplication we need a *controlled* version of
`modAddConstGate`: `if control then add c mod N else identity`.

**Design.**  Replace each `addConstGate` / `subConstGate` step in the
`modAddConstGate` pipeline by `conditionalAddConstGate` controlled by
the external `controlIdx`.  Replace the internal `CX (target_idx bits)
flagIdx` flag-copy by `CCX (controlIdx, target_idx bits, flagIdx)`,
and `X flagIdx` by `CX (controlIdx, flagIdx)`.

This uses only Gate IR primitives X / CX / CCX — no controlled-CCX
(CCCX) needed.  The "step 4" (`conditionalAddConstGate N flagIdx`) is
*unchanged*: when `control = false`, the controlled flag-copy at step 3
never fires, so `flagIdx = 0`, and the conditional add-back is itself
identity in that branch.

The correctness theorem follows by case-splitting on the value of
`controlIdx`: for `false`, each step is identity on the working
register; for `true`, each step matches the corresponding step in
`modAddConstGate`.  Proof is deferred to the next sub-tick.

This commit delivers: gate definition + WellTyped (the rest of the
proof requires a per-step "identity-when-control-false" lemma and a
"matches-modAddConstGate-when-control-true" lemma). -/

/-- Controlled modular add-constant gate.  Eight-step pipeline:
controlled add `c` ; controlled sub `N` ; controlled flag-copy ;
flag-controlled add-back `N` ; controlled sub `c` ; controlled
flag-copy ; controlled X flag ; controlled add `c`. -/
def controlledModAddConstGate (bits N c controlIdx flagIdx : Nat) : Gate :=
  Gate.seq (conditionalAddConstGate (bits + 1) c controlIdx)
    (Gate.seq (conditionalAddConstGate (bits + 1) (2^(bits + 1) - N) controlIdx)
      (Gate.seq (Gate.CCX controlIdx (target_idx bits) flagIdx)
        (Gate.seq (conditionalAddConstGate (bits + 1) N flagIdx)
          (Gate.seq (conditionalAddConstGate (bits + 1) (2^(bits + 1) - c) controlIdx)
            (Gate.seq (Gate.CCX controlIdx (target_idx bits) flagIdx)
              (Gate.seq (Gate.CX controlIdx flagIdx)
                (conditionalAddConstGate (bits + 1) c controlIdx)))))))

/-- `controlledModAddConstGate` is `WellTyped` at `flagIdx + 1` when
`controlIdx` and `flagIdx` are both out-of-band, with `controlIdx < flagIdx`. -/
theorem controlledModAddConstGate_wellTyped
    (bits N c controlIdx flagIdx : Nat) (hbits : 1 ≤ bits)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.WellTyped (flagIdx + 1) (controlledModAddConstGate bits N c controlIdx flagIdx) := by
  have hbits' : 2 ≤ bits + 1 := by omega
  have hcontrol_above : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  -- Each conditionalAddConstGate is WellTyped at `(its-flag) + 1`, then mono'd to `flagIdx + 1`.
  have h_cond_c_ctrl :
      Gate.WellTyped (flagIdx + 1) (conditionalAddConstGate (bits + 1) c controlIdx) :=
    Gate.WellTyped.mono
      (conditionalAddConstGate_wellTyped (bits+1) c controlIdx hbits' hcontrolIdx)
      (by omega)
  have h_cond_subN_ctrl :
      Gate.WellTyped (flagIdx + 1)
        (conditionalAddConstGate (bits + 1) (2^(bits+1) - N) controlIdx) :=
    Gate.WellTyped.mono
      (conditionalAddConstGate_wellTyped (bits+1) (2^(bits+1) - N) controlIdx hbits' hcontrolIdx)
      (by omega)
  have h_cond_N_flag :
      Gate.WellTyped (flagIdx + 1) (conditionalAddConstGate (bits + 1) N flagIdx) :=
    conditionalAddConstGate_wellTyped (bits+1) N flagIdx hbits' hcontrol_above
  have h_cond_subc_ctrl :
      Gate.WellTyped (flagIdx + 1)
        (conditionalAddConstGate (bits + 1) (2^(bits+1) - c) controlIdx) :=
    Gate.WellTyped.mono
      (conditionalAddConstGate_wellTyped (bits+1) (2^(bits+1) - c) controlIdx hbits' hcontrolIdx)
      (by omega)
  have h_ccx :
      Gate.WellTyped (flagIdx + 1) (Gate.CCX controlIdx (target_idx bits) flagIdx) := by
    unfold adder_n_qubits target_idx at *
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  have h_cx : Gate.WellTyped (flagIdx + 1) (Gate.CX controlIdx flagIdx) := by
    refine ⟨?_, ?_, ?_⟩
    · omega
    · omega
    · omega
  unfold controlledModAddConstGate
  exact ⟨h_cond_c_ctrl, h_cond_subN_ctrl, h_ccx, h_cond_N_flag, h_cond_subc_ctrl, h_ccx,
         h_cx, h_cond_c_ctrl⟩

/-! ### Tick 6b — `conditionalAddConstGate` full state-eq

The key reusable building block for `controlledModAddConstGate`
correctness: a STRONG (extensional) state-eq for `conditionalAddConstGate`
covering BOTH branches of the flag uniformly.  When `flag = false` the
gate is identity on the canonical input form; when `flag = true` it
adds `N` mod `2^bits`. -/

/-- **`conditionalAddConstGate` full state-eq.**  Applied to
`update (adder_input_F bits 0 x) flagIdx flag`, the gate produces
`update (adder_input_F bits 0 ((x + (if flag then N else 0)) % 2^bits))
flagIdx flag` — i.e. flag preserved, target = `(x + flag·N) mod 2^bits`,
read / carry restored. -/
theorem conditionalAddConstGate_state_eq
    (bits N flagIdx x : Nat) (flag : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx)
      (update (adder_input_F bits 0 x) flagIdx flag)
    = update (adder_input_F bits 0 ((x + (if flag then N else 0)) % 2^bits)) flagIdx flag := by
  have h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j := by
    intro j hj
    unfold adder_n_qubits read_idx at *; omega
  obtain ⟨_, _, h_read, h_carry, h_flag⟩ :=
    conditionalAddConstGate_clean bits N x flagIdx flag hbits hN hx hflagIdx
  have h_frame := conditionalAddConstGate_preserves_above_not_flag bits N flagIdx
  funext p
  by_cases h_p_flag : p = flagIdx
  · subst h_p_flag
    rw [h_flag, update_eq]
  · by_cases h_p_high : 3 * bits ≤ p
    · rw [h_frame _ p h_p_high]
      rw [update_neq _ _ _ _ h_p_flag, update_neq _ _ _ _ h_p_flag]
      unfold adder_input_F
      rcases h_mod : p % 3 with _ | _ | _
      · simp [show ¬(p/3 < bits) from by omega]
      · simp [show ¬(p/3 < bits) from by omega]
      · rfl
    · push_neg at h_p_high
      have h_p_div_lt : p / 3 < bits := by omega
      rcases h_mod : p % 3 with _ | _ | _
      · have h_p_eq : p = read_idx (p / 3) := by unfold read_idx; omega
        rw [h_p_eq, h_read (p/3) h_p_div_lt]
        rw [update_neq _ _ _ _ (by rw [← h_p_eq]; exact h_p_flag)]
        unfold adder_input_F
        rw [show (read_idx (p/3)) % 3 = 0 from by unfold read_idx; omega,
            show (read_idx (p/3)) / 3 = p/3 from by unfold read_idx; omega]
        simp [Nat.zero_testBit]
      · have h_p_eq : p = target_idx (p / 3) := by unfold target_idx; omega
        rw [h_p_eq]
        rw [conditionalAddConstGate_target_bit bits N flagIdx x (p/3) flag hbits hN hx hflagIdx
              h_p_div_lt]
        rw [update_neq _ _ _ _ (by rw [← h_p_eq]; exact h_p_flag)]
        unfold adder_input_F
        rw [show (target_idx (p/3)) % 3 = 1 from by unfold target_idx; omega,
            show (target_idx (p/3)) / 3 = p/3 from by unfold target_idx; omega]
        simp only [show decide (p/3 < bits) = true from decide_eq_true h_p_div_lt, Bool.true_and]
        rw [Nat.testBit_mod_two_pow]
        simp [h_p_div_lt]
      · have h_p_eq : p = carry_idx (p / 3) := by unfold carry_idx; omega
        rw [h_p_eq, h_carry (p/3) h_p_div_lt]
        rw [update_neq _ _ _ _ (by rw [← h_p_eq]; exact h_p_flag)]
        unfold adder_input_F
        rw [show (carry_idx (p/3)) % 3 = 2 from by unfold carry_idx; omega]

/-! ### Tick 6c — Commute lemmas for chaining `controlledModAddConstGate`

To prove `controlledModAddConstGate_correct` we need to chain step-eq's
across 8 sub-gates where each step's natural input is a *multi-update*
form (e.g., `update (update (adder_input_F …) flagIdx flag) controlIdx
controlBit`).  This requires showing each sub-gate commutes with the
"outer" update — i.e. doesn't read from or write to that position.

The first piece is a commute lemma for `prepareMaskedConstRead` past an
outer update at a position outside its read/write set. -/

/-- `prepareMaskedConstRead bits N flagIdx` commutes with `update _ p v`
when `p` is outside the gate's read/write set: `p ≠ flagIdx` (not read
as control) and `p ≠ read_idx k` for any `k < bits` (not written). -/
theorem prepareMaskedConstRead_commute_update_outer
    (bits N flagIdx p : Nat) (v : Bool)
    (h_p_ne_flag : p ≠ flagIdx)
    (h_p_ne_read : ∀ i, i < bits → p ≠ read_idx i) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (prepareMaskedConstRead bits N flagIdx) (update f p v)
      = update (Gate.applyNat (prepareMaskedConstRead bits N flagIdx) f) p v := by
  induction bits with
  | zero => intro f; rfl
  | succ k ih =>
      have h_p_ne_read_lt_k : ∀ i, i < k → p ≠ read_idx i :=
        fun i hi => h_p_ne_read i (by omega)
      have h_p_ne_read_k : p ≠ read_idx k := h_p_ne_read k (by omega)
      have ih' := ih h_p_ne_read_lt_k
      intro f
      show Gate.applyNat (Gate.seq (prepareMaskedConstRead k N flagIdx)
              (if N.testBit k then Gate.CX flagIdx (read_idx k) else Gate.I))
            (update f p v)
          = update (Gate.applyNat (Gate.seq (prepareMaskedConstRead k N flagIdx)
              (if N.testBit k then Gate.CX flagIdx (read_idx k) else Gate.I)) f) p v
      apply applyNat_seq_commute_update
      · intro f'; exact ih' f'
      · intro f'
        by_cases h_test : N.testBit k
        · simp [h_test]
          exact applyNat_CX_commute_update_disjoint flagIdx (read_idx k) f' p v
            h_p_ne_flag h_p_ne_read_k
        · simp [h_test]

/-- `conditionalAddConstGate bits N flagIdx` commutes with `update _ p v`
when `p` is outside the gate's actual support: `p ≥ adder_n_qubits bits`
and `p ≠ flagIdx`.  Composes prep + adder + prep commute lemmas. -/
theorem conditionalAddConstGate_commute_update_outer
    (bits N flagIdx p : Nat) (v : Bool)
    (hbits : 2 ≤ bits)
    (hp_dim : adder_n_qubits bits ≤ p)
    (h_p_ne_flag : p ≠ flagIdx) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (conditionalAddConstGate bits N flagIdx) (update f p v)
      = update (Gate.applyNat (conditionalAddConstGate bits N flagIdx) f) p v := by
  intro f
  unfold conditionalAddConstGate
  have h_p_ne_read : ∀ i, i < bits → p ≠ read_idx i := by
    intro i hi; unfold adder_n_qubits read_idx at *; omega
  have h_adder_wt : Gate.WellTyped (adder_n_qubits bits)
                      (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  apply applyNat_seq_commute_update
  · intro f'
    exact prepareMaskedConstRead_commute_update_outer bits N flagIdx p v
      h_p_ne_flag h_p_ne_read f'
  · intro f'
    apply applyNat_seq_commute_update
    · intro f''
      exact applyNat_commute_update_above_dim (adder_n_qubits bits)
        (gidney_adder_full_faithful_no_measurement_patched bits) h_adder_wt f'' p v hp_dim
    · intro f''
      exact prepareMaskedConstRead_commute_update_outer bits N flagIdx p v
        h_p_ne_flag h_p_ne_read f''

/-- State-eq for `conditionalAddConstGate` lifted past an outer update
at `outerIdx`.  This is the form that lets us chain through
`controlledModAddConstGate`'s 8 steps where each sub-state has both
`flagIdx` and `controlIdx` updates active simultaneously. -/
theorem conditionalAddConstGate_state_eq_with_outer
    (bits N flagIdx outerIdx x : Nat) (flag outerVal : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx)
    (hOuter : adder_n_qubits bits ≤ outerIdx) (hOuter_ne_flag : outerIdx ≠ flagIdx) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx)
      (update (update (adder_input_F bits 0 x) flagIdx flag) outerIdx outerVal)
    = update
        (update (adder_input_F bits 0 ((x + (if flag then N else 0)) % 2^bits))
          flagIdx flag) outerIdx outerVal := by
  rw [conditionalAddConstGate_commute_update_outer bits N flagIdx outerIdx outerVal
        hbits hOuter hOuter_ne_flag]
  rw [conditionalAddConstGate_state_eq bits N flagIdx x flag hbits hN hx hflagIdx]

/-- Helper: an `update` at a high `flagIdx` to `false` is idempotent
relative to `adder_input_F n 0 x` (since `adder_input_F` is already
`false` at any position `≥ 3 * n`).  Used in the `controlBit = false`
chain proof to insert/remove redundant flagIdx updates so state forms
match `conditionalAddConstGate_state_eq_with_outer`'s expected shape. -/
private theorem collapse_flag_false_update_at_high
    (n flagIdx outerIdx x : Nat) (outerVal : Bool)
    (hflag_high : 3 * n ≤ flagIdx) :
    update (update (adder_input_F n 0 x) flagIdx false) outerIdx outerVal
    = update (adder_input_F n 0 x) outerIdx outerVal := by
  have h_adder_input_at_flag : adder_input_F n 0 x flagIdx = false := by
    unfold adder_input_F
    rcases h_mod : flagIdx % 3 with _ | _ | _
    · have : flagIdx / 3 ≥ n := by omega
      simp [show ¬(flagIdx/3 < n) from by omega]
    · have : flagIdx / 3 ≥ n := by omega
      simp [show ¬(flagIdx/3 < n) from by omega]
    · rfl
  funext q
  by_cases h_q_outer : q = outerIdx
  · rw [h_q_outer, update_eq, update_eq]
  · rw [update_neq _ _ _ _ h_q_outer, update_neq _ _ _ _ h_q_outer]
    by_cases h_q_flag : q = flagIdx
    · rw [h_q_flag, update_eq, h_adder_input_at_flag]
    · rw [update_neq _ _ _ _ h_q_flag]

/-- Corollary of `conditionalAddConstGate_state_eq` for `flag = false`:
the gate is identity on the canonical input form. -/
theorem conditionalAddConstGate_identity_when_flag_false
    (bits N flagIdx x : Nat) (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx)
      (update (adder_input_F bits 0 x) flagIdx false)
    = update (adder_input_F bits 0 x) flagIdx false := by
  rw [conditionalAddConstGate_state_eq bits N flagIdx x false hbits hN hx hflagIdx]
  congr 2
  show (x + 0) % 2^bits = x
  rw [Nat.add_zero, Nat.mod_eq_of_lt hx]

/-- Corollary of `conditionalAddConstGate_state_eq_with_outer` for
`flag = false`: the gate is identity on the *double-update* form, useful
when chaining through `controlledModAddConstGate`'s steps. -/
theorem conditionalAddConstGate_identity_when_flag_false_with_outer
    (bits N flagIdx outerIdx x : Nat) (outerVal : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx)
    (hOuter : adder_n_qubits bits ≤ outerIdx) (hOuter_ne_flag : outerIdx ≠ flagIdx) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx)
      (update (update (adder_input_F bits 0 x) flagIdx false) outerIdx outerVal)
    = update (update (adder_input_F bits 0 x) flagIdx false) outerIdx outerVal := by
  rw [conditionalAddConstGate_state_eq_with_outer bits N flagIdx outerIdx x false outerVal
        hbits hN hx hflagIdx hOuter hOuter_ne_flag]
  congr 3
  show (x + 0) % 2^bits = x
  rw [Nat.add_zero, Nat.mod_eq_of_lt hx]

/-- **Tick 6g HEADLINE — `controlBit = false` branch of `controlledModAddConstGate_correct`**.
When the control bit is `false`, the entire 8-step controlled
modular-add pipeline is identity: target / read / carry / flag all
unchanged.  Proved by chaining 8 identity rewrites. -/
theorem controlledModAddConstGate_correct_false
    (bits N c x : Nat) (controlIdx flagIdx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx)
      (update (adder_input_F (bits + 1) 0 x) controlIdx false)
    = update (adder_input_F (bits + 1) 0 x) controlIdx false := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have hc_succ : c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hx_succ : x < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hN_succ : N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_pow_succ_pos : 0 < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hN_2sub : 2^(bits+1) - N < 2^(bits+1) := by omega
  have hc_2sub : 2^(bits+1) - c < 2^(bits+1) := by omega
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_3_succ_flag : 3 * (bits + 1) ≤ flagIdx := by
    unfold adder_n_qubits at h_flag_ge; omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := by omega
  have h_ctrl_ne_flag : controlIdx ≠ flagIdx := h_flag_ne_ctrl.symm
  have h_state_ctrl : (update (adder_input_F (bits + 1) 0 x) controlIdx false) controlIdx = false :=
    update_eq _ _ _
  have h_state_flag : (update (adder_input_F (bits + 1) 0 x) controlIdx false) flagIdx = false := by
    rw [update_neq _ _ _ _ h_flag_ne_ctrl]
    unfold adder_input_F
    rcases h_mod : flagIdx % 3 with _ | _ | _
    · have : flagIdx / 3 ≥ bits + 1 := by omega
      simp [show ¬(flagIdx/3 < bits + 1) from by omega]
    · have : flagIdx / 3 ≥ bits + 1 := by omega
      simp [show ¬(flagIdx/3 < bits + 1) from by omega]
    · rfl
  have h_update_self : update (update (adder_input_F (bits + 1) 0 x) controlIdx false) flagIdx false
                     = update (adder_input_F (bits + 1) 0 x) controlIdx false := by
    funext q
    by_cases h_q_flag : q = flagIdx
    · rw [h_q_flag, update_eq, update_neq _ _ _ _ h_flag_ne_ctrl]
      unfold adder_input_F
      rcases h_mod : flagIdx % 3 with _ | _ | _
      · have : flagIdx / 3 ≥ bits + 1 := by omega
        simp [show ¬(flagIdx/3 < bits + 1) from by omega]
      · have : flagIdx / 3 ≥ bits + 1 := by omega
        simp [show ¬(flagIdx/3 < bits + 1) from by omega]
      · rfl
    · rw [update_neq _ _ _ _ h_q_flag]
  unfold controlledModAddConstGate
  rw [Gate.applyNat_seq]
  rw [conditionalAddConstGate_identity_when_flag_false (bits+1) c controlIdx x
        hbits' hc_succ hx_succ hcontrolIdx]
  rw [Gate.applyNat_seq]
  rw [conditionalAddConstGate_identity_when_flag_false (bits+1) (2^(bits+1) - N) controlIdx x
        hbits' hN_2sub hx_succ hcontrolIdx]
  rw [Gate.applyNat_seq, Gate.applyNat_CCX]
  rw [h_state_ctrl, h_state_flag]
  simp only [Bool.false_and, Bool.false_xor]
  rw [h_update_self]
  rw [Gate.applyNat_seq]
  rw [(collapse_flag_false_update_at_high (bits+1) flagIdx controlIdx x false h_3_succ_flag).symm]
  rw [conditionalAddConstGate_identity_when_flag_false_with_outer (bits+1) N flagIdx controlIdx x
        false hbits' hN_succ hx_succ h_flag_ge hcontrolIdx h_ctrl_ne_flag]
  rw [collapse_flag_false_update_at_high (bits+1) flagIdx controlIdx x false h_3_succ_flag]
  rw [Gate.applyNat_seq]
  rw [conditionalAddConstGate_identity_when_flag_false (bits+1) (2^(bits+1) - c) controlIdx x
        hbits' hc_2sub hx_succ hcontrolIdx]
  rw [Gate.applyNat_seq, Gate.applyNat_CCX]
  rw [h_state_ctrl, h_state_flag]
  simp only [Bool.false_and, Bool.false_xor]
  rw [h_update_self]
  rw [Gate.applyNat_seq, Gate.applyNat_CX]
  rw [h_state_ctrl, h_state_flag]
  simp only [Bool.false_xor]
  rw [h_update_self]
  rw [conditionalAddConstGate_identity_when_flag_false (bits+1) c controlIdx x
        hbits' hc_succ hx_succ hcontrolIdx]

/-- Intermediate: applying step 1 of controlled pipeline (controlled
add c) with controlBit = true gives target = `x + c`. -/
private theorem controlled_step1_true
    (bits c x controlIdx : Nat) (hbits : 1 ≤ bits)
    (hc_succ : c < 2^(bits+1)) (hxc_lt : x + c < 2^(bits+1))
    (hx_succ : x < 2^(bits+1))
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx) :
    Gate.applyNat (conditionalAddConstGate (bits + 1) c controlIdx)
      (update (adder_input_F (bits + 1) 0 x) controlIdx true)
    = update (adder_input_F (bits + 1) 0 (x + c)) controlIdx true := by
  have hbits' : 2 ≤ bits + 1 := by omega
  rw [conditionalAddConstGate_state_eq (bits+1) c controlIdx x true hbits' hc_succ hx_succ hcontrolIdx]
  congr 2
  show (x + c) % 2^(bits+1) = x + c
  exact Nat.mod_eq_of_lt hxc_lt

/-- Intermediate: applying step 2 of controlled pipeline (controlled
sub N) with controlBit = true takes target from `x + c` to
`subConstPow2WideSpec bits N (x+c)`. -/
private theorem controlled_step2_true
    (bits N c x controlIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx) :
    Gate.applyNat (conditionalAddConstGate (bits + 1) (2^(bits+1) - N) controlIdx)
      (update (adder_input_F (bits + 1) 0 (x + c)) controlIdx true)
    = update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c))) controlIdx true := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have h_pow_succ_pos : 0 < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hN_2sub_lt : 2^(bits+1) - N < 2^(bits+1) := by omega
  have h_xc_lt_pow : x + c < 2^(bits+1) := by rw [h_pow_succ]; omega
  rw [conditionalAddConstGate_state_eq (bits+1) (2^(bits+1) - N) controlIdx (x+c) true
        hbits' hN_2sub_lt h_xc_lt_pow hcontrolIdx]
  rfl

/-- Intermediate: applying step 3 of controlled pipeline (CCX flag-copy)
with controlBit = true puts `decide ((x+c) < N)` into `flagIdx`. -/
private theorem controlled_step3_true
    (bits N c x controlIdx flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (Gate.CCX controlIdx (target_idx bits) flagIdx)
      (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c))) controlIdx true)
    = update (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)))
                controlIdx true) flagIdx (decide ((x + c) < N)) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_3_succ_flag : 3 * (bits + 1) ≤ flagIdx := by
    unfold adder_n_qubits at h_flag_ge; omega
  have h_target_bits_ne_ctrl : target_idx bits ≠ controlIdx := by
    unfold adder_n_qubits at hcontrolIdx; unfold target_idx; omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := by omega
  -- Compute state values at controlIdx, target_idx bits, flagIdx
  have h_state_ctrl : (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)))
                        controlIdx true) controlIdx = true := update_eq _ _ _
  have h_y_high : (subConstPow2WideSpec bits N (x + c)).testBit bits = decide ((x + c) < N) :=
    subConstPow2WideSpec_high_bit_bounded_sum bits N (x+c) hN_pos hN h_xc_lt_2N
  have h_state_tbits :
      (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c))) controlIdx true)
        (target_idx bits) = decide ((x + c) < N) := by
    rw [update_neq _ _ _ _ h_target_bits_ne_ctrl]
    unfold adder_input_F
    rw [show (target_idx bits) % 3 = 1 from by unfold target_idx; omega,
        show (target_idx bits) / 3 = bits from by unfold target_idx; omega]
    simp only [show decide (bits < bits + 1) = true from decide_eq_true (by omega), Bool.true_and]
    exact h_y_high
  have h_state_flag :
      (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c))) controlIdx true)
        flagIdx = false := by
    rw [update_neq _ _ _ _ h_flag_ne_ctrl]
    unfold adder_input_F
    rcases h_mod : flagIdx % 3 with _ | _ | _
    · have : flagIdx / 3 ≥ bits + 1 := by omega
      simp [show ¬(flagIdx/3 < bits + 1) from by omega]
    · have : flagIdx / 3 ≥ bits + 1 := by omega
      simp [show ¬(flagIdx/3 < bits + 1) from by omega]
    · rfl
  -- Apply CCX
  rw [Gate.applyNat_CCX]
  rw [h_state_ctrl, h_state_tbits, h_state_flag]
  simp only [Bool.true_and, Bool.false_xor]

/-- Intermediate: applying step 4 of controlled pipeline (flag-controlled
add-back of N) takes target from `subConstPow2WideSpec bits N (x+c)` to
`(x + c) % N` when flag holds `decide ((x+c) < N)`. -/
private theorem controlled_step4_true
    (bits N c x controlIdx flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (conditionalAddConstGate (bits + 1) N flagIdx)
      (update (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)))
                  controlIdx true) flagIdx (decide ((x + c) < N)))
    = update (update (adder_input_F (bits + 1) 0 ((x + c) % N))
                controlIdx true) flagIdx (decide ((x + c) < N)) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have hN_succ : N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_y_lt : subConstPow2WideSpec bits N (x + c) < 2^(bits+1) := by
    unfold subConstPow2WideSpec; exact Nat.mod_lt _ (by rw [h_pow_succ]; omega)
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_ctrl_ne_flag : controlIdx ≠ flagIdx := by omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := h_ctrl_ne_flag.symm
  -- Swap update order: flagIdx OUTER, controlIdx INNER → controlIdx OUTER, flagIdx INNER
  rw [update_update_comm _ controlIdx flagIdx true (decide ((x + c) < N)) h_ctrl_ne_flag]
  -- Now: update (update ad-inp-F flagIdx flag) controlIdx true. flagIdx INNER, controlIdx OUTER.
  rw [conditionalAddConstGate_state_eq_with_outer (bits + 1) N flagIdx controlIdx
        (subConstPow2WideSpec bits N (x + c)) (decide ((x + c) < N)) true
        hbits' hN_succ h_y_lt h_flag_ge hcontrolIdx h_ctrl_ne_flag]
  -- Bridge to modAddConstArithmeticSpec
  have h_bridge : (subConstPow2WideSpec bits N (x + c)
                  + (if decide ((x + c) < N) = true then N else 0)) % 2 ^ (bits + 1)
                  = (x + c) % N := by
    have h_arith_eq := modAddConstArithmeticSpec_eq_mod bits N c x hN_pos hN hx hc
    unfold modAddConstArithmeticSpec at h_arith_eq
    exact h_arith_eq
  rw [h_bridge]
  -- Swap back: controlIdx OUTER, flagIdx INNER → flagIdx OUTER, controlIdx INNER
  rw [update_update_comm _ flagIdx controlIdx (decide ((x + c) < N)) true h_flag_ne_ctrl]

/-- Intermediate: applying step 5 of controlled pipeline (controlled
sub c) with controlBit = true takes target from `(x+c) % N` to
`subConstPow2WideSpec bits c ((x+c) % N)`. -/
private theorem controlled_step5_true
    (bits N c x controlIdx flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (conditionalAddConstGate (bits + 1) (2^(bits+1) - c) controlIdx)
      (update (update (adder_input_F (bits + 1) 0 ((x + c) % N)) controlIdx true)
              flagIdx (decide ((x + c) < N)))
    = update (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits c ((x + c) % N)))
                controlIdx true) flagIdx (decide ((x + c) < N)) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have h_pow_succ_pos : 0 < 2^(bits + 1) := by rw [h_pow_succ]; omega
  have hc_2sub_lt : 2^(bits+1) - c < 2^(bits+1) := by omega
  have h_mod_lt_N : (x + c) % N < N := Nat.mod_lt _ hN_pos
  have h_mod_lt_pow : (x + c) % N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := by omega
  rw [conditionalAddConstGate_state_eq_with_outer (bits + 1) (2^(bits+1) - c) controlIdx flagIdx
        ((x + c) % N) true (decide ((x + c) < N))
        hbits' hc_2sub_lt h_mod_lt_pow hcontrolIdx h_flag_ge h_flag_ne_ctrl]
  rfl

/-- Intermediate: applying step 6 of controlled pipeline (second CCX
flag-copy) with controlBit = true sets flagIdx to `TRUE` (the XOR of
the comparison flag and its complement). -/
private theorem controlled_step6_true
    (bits N c x controlIdx flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (Gate.CCX controlIdx (target_idx bits) flagIdx)
      (update (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits c ((x + c) % N)))
                  controlIdx true) flagIdx (decide ((x + c) < N)))
    = update (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits c ((x + c) % N)))
                controlIdx true) flagIdx true := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_mod_lt_N : (x + c) % N < N := Nat.mod_lt _ hN_pos
  have h_mod_lt_2bits : (x + c) % N < 2^bits := by omega
  have h_c_lt_2bits : c < 2^bits := by omega
  have h_c_le_2bits : c ≤ 2^bits := by omega
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_ctrl_ne_flag : controlIdx ≠ flagIdx := by omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := h_ctrl_ne_flag.symm
  have h_target_bits_ne_ctrl : target_idx bits ≠ controlIdx := by
    unfold adder_n_qubits at hcontrolIdx; unfold target_idx; omega
  have h_target_bits_ne_flag : target_idx bits ≠ flagIdx := by
    unfold adder_n_qubits at h_flag_ge; unfold target_idx; omega
  -- Compute state values
  have h_state_ctrl : (update (update (adder_input_F (bits + 1) 0
                          (subConstPow2WideSpec bits c ((x + c) % N))) controlIdx true) flagIdx
                          (decide ((x + c) < N))) controlIdx = true := by
    rw [update_neq _ _ _ _ h_ctrl_ne_flag, update_eq]
  have h_target_bits_val : (subConstPow2WideSpec bits c ((x + c) % N)).testBit bits
                          = decide ((x + c) % N < c) :=
    subConstPow2WideSpec_high_bit bits c ((x + c) % N) h_c_le_2bits h_mod_lt_2bits
  have h_state_tbits : (update (update (adder_input_F (bits + 1) 0
                          (subConstPow2WideSpec bits c ((x + c) % N))) controlIdx true) flagIdx
                          (decide ((x + c) < N))) (target_idx bits) = decide ((x + c) % N < c) := by
    rw [update_neq _ _ _ _ h_target_bits_ne_flag, update_neq _ _ _ _ h_target_bits_ne_ctrl]
    unfold adder_input_F
    rw [show (target_idx bits) % 3 = 1 from by unfold target_idx; omega,
        show (target_idx bits) / 3 = bits from by unfold target_idx; omega]
    simp only [show decide (bits < bits + 1) = true from decide_eq_true (by omega), Bool.true_and]
    exact h_target_bits_val
  have h_state_flag : (update (update (adder_input_F (bits + 1) 0
                          (subConstPow2WideSpec bits c ((x + c) % N))) controlIdx true) flagIdx
                          (decide ((x + c) < N))) flagIdx = decide ((x + c) < N) := update_eq _ _ _
  -- Complementarity: decide ((x+c) < N) = !decide ((x+c)%N < c)
  have h_compl : decide ((x + c) < N) = !decide ((x + c) % N < c) := by
    by_cases h : x + c < N
    · rw [decide_eq_true h]
      have h_mod_eq : (x + c) % N = x + c := Nat.mod_eq_of_lt h
      rw [h_mod_eq, decide_eq_false (by omega : ¬ x + c < c)]
      rfl
    · rw [decide_eq_false h]
      have h_le : N ≤ x + c := by omega
      have h_lt : x + c < 2 * N := by omega
      have h_mod_eq : (x + c) % N = x + c - N := by
        have h_eq : x + c = (x + c - N) + N := by omega
        conv_lhs => rw [h_eq]
        rw [Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [h_mod_eq, decide_eq_true (by omega : x + c - N < c)]
      rfl
  -- Apply CCX
  rw [Gate.applyNat_CCX]
  rw [h_state_ctrl, h_state_tbits, h_state_flag]
  -- new flagIdx = decide((x+c)<N) XOR (true AND decide((x+c)%N<c)) = TRUE
  rw [h_compl]
  simp only [Bool.true_and]
  -- !b XOR b = true
  have h_xor : ∀ (b : Bool), ((!b) ^^ b) = true := fun b => by cases b <;> rfl
  rw [h_xor]
  -- Collapse double update at flagIdx (outer wins)
  have h_collapse : ∀ (f : Nat → Bool) (u v : Bool),
      update (update f flagIdx u) flagIdx v = update f flagIdx v := by
    intros f u v
    funext q
    by_cases hq : q = flagIdx
    · rw [hq, update_eq, update_eq]
    · rw [update_neq _ _ _ _ hq, update_neq _ _ _ _ hq, update_neq _ _ _ _ hq]
  rw [h_collapse]

/-- Intermediate: applying step 7 of controlled pipeline (controlled X
flipping flagIdx) takes flagIdx from `TRUE` to `FALSE`. -/
private theorem controlled_step7_true
    (bits c x controlIdx flagIdx : Nat) (y : Nat)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (Gate.CX controlIdx flagIdx)
      (update (update (adder_input_F (bits + 1) 0 y) controlIdx true) flagIdx true)
    = update (update (adder_input_F (bits + 1) 0 y) controlIdx true) flagIdx false := by
  have h_ctrl_ne_flag : controlIdx ≠ flagIdx := by omega
  -- Compute state values
  have h_state_ctrl : (update (update (adder_input_F (bits + 1) 0 y) controlIdx true) flagIdx true)
                        controlIdx = true := by
    rw [update_neq _ _ _ _ h_ctrl_ne_flag, update_eq]
  have h_state_flag : (update (update (adder_input_F (bits + 1) 0 y) controlIdx true) flagIdx true)
                        flagIdx = true := update_eq _ _ _
  -- Apply CX
  rw [Gate.applyNat_CX]
  rw [h_state_ctrl, h_state_flag]
  -- new flagIdx = true XOR true = false
  show update (update (update (adder_input_F (bits + 1) 0 y) controlIdx true) flagIdx true)
        flagIdx (true ^^ true)
      = update (update (adder_input_F (bits + 1) 0 y) controlIdx true) flagIdx false
  rw [show (true ^^ true : Bool) = false from rfl]
  -- Collapse double update at flagIdx
  funext q
  by_cases hq : q = flagIdx
  · rw [hq, update_eq, update_eq]
  · rw [update_neq _ _ _ _ hq, update_neq _ _ _ _ hq, update_neq _ _ _ _ hq]

/-- Intermediate: applying step 8 of controlled pipeline (final
controlled add c) takes target from `subConstPow2WideSpec bits c
((x + c) % N)` to `(x + c) % N` via algebraic cancellation. -/
private theorem controlled_step8_true
    (bits N c x controlIdx flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (conditionalAddConstGate (bits + 1) c controlIdx)
      (update (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits c ((x + c) % N)))
                  controlIdx true) flagIdx false)
    = update (update (adder_input_F (bits + 1) 0 ((x + c) % N)) controlIdx true) flagIdx false := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_pow_succ_pos : 0 < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hbits' : 2 ≤ bits + 1 := by omega
  have hc_succ : c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_mod_lt_N : (x + c) % N < N := Nat.mod_lt _ hN_pos
  have h_mod_lt_2bits : (x + c) % N < 2^bits := by omega
  have h_mod_lt_pow : (x + c) % N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_y_lt : subConstPow2WideSpec bits c ((x + c) % N) < 2^(bits+1) := by
    unfold subConstPow2WideSpec; exact Nat.mod_lt _ (by rw [h_pow_succ]; omega)
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := by omega
  -- Apply state_eq_with_outer
  rw [conditionalAddConstGate_state_eq_with_outer (bits + 1) c controlIdx flagIdx
        (subConstPow2WideSpec bits c ((x + c) % N)) true false
        hbits' hc_succ h_y_lt hcontrolIdx h_flag_ge h_flag_ne_ctrl]
  -- Now simplify: (subConstPow2WideSpec bits c ((x+c)%N) + c) % 2^(bits+1) = (x+c) % N
  congr 3
  show (subConstPow2WideSpec bits c ((x + c) % N) + c) % 2^(bits+1) = (x + c) % N
  unfold subConstPow2WideSpec
  rw [Nat.mod_add_mod]
  have h_eq : (x + c) % N + (2^(bits + 1) - c) + c = (x + c) % N + 2^(bits + 1) := by omega
  rw [h_eq, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt h_mod_lt_pow

/-- **Tick 6p HEADLINE — `controlBit = true` branch**.  When the
control bit is `true`, the full 8-step pipeline produces target =
`(x + c) % N` with all workspace restored. -/
theorem controlledModAddConstGate_correct_true
    (bits N c x : Nat) (controlIdx flagIdx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx)
      (update (adder_input_F (bits + 1) 0 x) controlIdx true)
    = update (adder_input_F (bits + 1) 0 ((x + c) % N)) controlIdx true := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have hc_succ : c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hx_succ : x < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_xc_lt_pow : x + c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_3_succ_flag : 3 * (bits + 1) ≤ flagIdx := by
    unfold adder_n_qubits at h_flag_ge; omega
  have h_ctrl_ne_flag : controlIdx ≠ flagIdx := by omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := h_ctrl_ne_flag.symm
  unfold controlledModAddConstGate
  rw [Gate.applyNat_seq]
  rw [controlled_step1_true bits c x controlIdx hbits hc_succ h_xc_lt_pow hx_succ hcontrolIdx]
  rw [Gate.applyNat_seq]
  rw [controlled_step2_true bits N c x controlIdx hbits hN_pos hN hx hc hcontrolIdx]
  rw [Gate.applyNat_seq]
  rw [controlled_step3_true bits N c x controlIdx flagIdx hbits hN_pos hN hx hc hcontrolIdx hflagIdx]
  rw [Gate.applyNat_seq]
  rw [controlled_step4_true bits N c x controlIdx flagIdx hbits hN_pos hN hx hc hcontrolIdx hflagIdx]
  rw [Gate.applyNat_seq]
  rw [controlled_step5_true bits N c x controlIdx flagIdx hbits hN_pos hN hx hc_pos hc
        hcontrolIdx hflagIdx]
  rw [Gate.applyNat_seq]
  rw [controlled_step6_true bits N c x controlIdx flagIdx hbits hN_pos hN hx hc_pos hc
        hcontrolIdx hflagIdx]
  rw [Gate.applyNat_seq]
  rw [controlled_step7_true bits c x controlIdx flagIdx
        (subConstPow2WideSpec bits c ((x + c) % N)) hcontrolIdx hflagIdx]
  rw [controlled_step8_true bits N c x controlIdx flagIdx hbits hN_pos hN hx hc_pos hc
        hcontrolIdx hflagIdx]
  -- Final state: update (update (ad-inp-F 0 ((x+c)%N)) controlIdx true) flagIdx false
  -- Need to simplify to: update (ad-inp-F 0 ((x+c)%N)) controlIdx true
  -- Swap order, then collapse the flagIdx-to-false update.
  rw [update_update_comm _ controlIdx flagIdx true false h_ctrl_ne_flag]
  rw [collapse_flag_false_update_at_high (bits + 1) flagIdx controlIdx ((x + c) % N) true
        h_3_succ_flag]

/-- **Tick 6 HEADLINE — full `controlledModAddConstGate_correct`**.
For any `controlBit`, the 8-step pipeline produces target =
`if controlBit then (x + c) % N else x` with all workspace restored. -/
theorem controlledModAddConstGate_correct
    (bits N c x : Nat) (controlBit : Bool) (controlIdx flagIdx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx)
      (update (adder_input_F (bits + 1) 0 x) controlIdx controlBit)
    = update (adder_input_F (bits + 1) 0 (if controlBit then (x + c) % N else x))
        controlIdx controlBit := by
  cases controlBit with
  | false =>
      show Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx)
            (update (adder_input_F (bits + 1) 0 x) controlIdx false)
          = update (adder_input_F (bits + 1) 0 x) controlIdx false
      exact controlledModAddConstGate_correct_false bits N c x controlIdx flagIdx
              hbits hN_pos hN hx hc_pos hc hcontrolIdx hflagIdx
  | true =>
      show Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx)
            (update (adder_input_F (bits + 1) 0 x) controlIdx true)
          = update (adder_input_F (bits + 1) 0 ((x + c) % N)) controlIdx true
      exact controlledModAddConstGate_correct_true bits N c x controlIdx flagIdx
              hbits hN_pos hN hx hc_pos hc hcontrolIdx hflagIdx

/-! ### Tick 7 — Modular multiplier by repeated controlled additions

The modular multiplier circuit applies, for each bit `i` of a
multiplier register `m`, a `controlledModAddConstGate` with constant
`(a * 2^i) % N` controlled by the `i`-th multiplier qubit.  The
cumulative effect is to send the adder's target register from `x` to
`(x + a * m) % N`, where `m = ∑_{i : bit_i = 1} 2^i`.

**Register layout**: positions `0 .. adder_n_qubits (bits+1) - 1` form
the adder block (read/target/carry).  Positions
`adder_n_qubits (bits+1) + 0 .. adder_n_qubits (bits+1) + multBits - 1`
are the multiplier qubits, and position
`adder_n_qubits (bits+1) + multBits` is the shared flag qubit (clean
before and after each iteration). -/

/-- Auxiliary recursive gate for the modular multiplier: applies
controlled modular-add of `(a * 2^i) % N` for bits `i = 0, 1, ..., k-1`.
The parameter `multBits` is the TOTAL multiplier width (used to
position the shared flag qubit); `k` is the recursion index running
from 0 up to `multBits`. -/
def modMultConstGateAux (bits N a multBits : Nat) : Nat → Gate
  | 0 => Gate.I
  | k+1 =>
    Gate.seq
      (modMultConstGateAux bits N a multBits k)
      (controlledModAddConstGate bits N ((a * 2^k) % N)
        (adder_n_qubits (bits + 1) + k)
        (adder_n_qubits (bits + 1) + multBits))

/-- Modular multiplier gate: applies `controlledModAddConstGate` for
each bit of the multiplier register, accumulating `(a * m) % N` into
the adder's target register, where `m` is the natural-number value of
the multiplier register. -/
def modMultConstGate (bits N a multBits : Nat) : Gate :=
  modMultConstGateAux bits N a multBits multBits

/-- `modMultConstGateAux ... 0 = Gate.I` by definition. -/
theorem modMultConstGateAux_zero (bits N a multBits : Nat) :
    modMultConstGateAux bits N a multBits 0 = Gate.I := rfl

/-- `modMultConstGate ... 0 = Gate.I` (zero-bit multiplier is the identity). -/
theorem modMultConstGate_zero (bits N a : Nat) :
    modMultConstGate bits N a 0 = Gate.I := rfl

/-- Recursive unfolding: `modMultConstGateAux ... (k+1)` is the seq of
the `k`-step and the controlled add at bit `k`. -/
theorem modMultConstGateAux_succ (bits N a multBits k : Nat) :
    modMultConstGateAux bits N a multBits (k + 1)
    = Gate.seq
        (modMultConstGateAux bits N a multBits k)
        (controlledModAddConstGate bits N ((a * 2^k) % N)
          (adder_n_qubits (bits + 1) + k)
          (adder_n_qubits (bits + 1) + multBits)) := rfl

/-- Well-typedness of the auxiliary gate at width
`adder_n_qubits (bits+1) + multBits + 1` for any `k ≤ multBits`. -/
theorem modMultConstGateAux_wellTyped
    (bits N a multBits k : Nat) (hbits : 1 ≤ bits) (hk : k ≤ multBits) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (modMultConstGateAux bits N a multBits k) := by
  induction k with
  | zero =>
      -- `modMultConstGateAux ... 0 = Gate.I`; WellTyped reduces to `0 < dim`.
      show Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1) Gate.I
      show 0 < adder_n_qubits (bits + 1) + multBits + 1
      omega
  | succ k ih =>
      have hk' : k ≤ multBits := by omega
      have ih' := ih hk'
      -- Step gate: controlledModAddConstGate at control = adder_n_qubits (bits+1) + k,
      -- flag = adder_n_qubits (bits+1) + multBits.
      have hctrl : adder_n_qubits (bits + 1) ≤ adder_n_qubits (bits + 1) + k := by omega
      have hflag : adder_n_qubits (bits + 1) + k < adder_n_qubits (bits + 1) + multBits := by
        have : k < multBits := by omega
        omega
      have h_step :
          Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
            (controlledModAddConstGate bits N ((a * 2^k) % N)
              (adder_n_qubits (bits + 1) + k)
              (adder_n_qubits (bits + 1) + multBits)) :=
        controlledModAddConstGate_wellTyped bits N ((a * 2^k) % N)
          (adder_n_qubits (bits + 1) + k)
          (adder_n_qubits (bits + 1) + multBits)
          hbits hctrl hflag
      show Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
        (Gate.seq (modMultConstGateAux bits N a multBits k) _)
      exact ⟨ih', h_step⟩

/-- **Well-typedness of `modMultConstGate`.** The full multiplier gate
is well-typed at width `adder_n_qubits (bits+1) + multBits + 1`
(adder block + `multBits` multiplier qubits + 1 flag qubit). -/
theorem modMultConstGate_wellTyped
    (bits N a multBits : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (modMultConstGate bits N a multBits) := by
  unfold modMultConstGate
  exact modMultConstGateAux_wellTyped bits N a multBits multBits hbits (le_refl _)

/-! #### Tick 7a — base cases and a commute lemma for the multiplier step. -/

/-- Base case: the zero-step multiplier auxiliary gate is identity. -/
theorem modMultConstGateAux_correct_zero
    (bits N a multBits : Nat) (f : Nat → Bool) :
    Gate.applyNat (modMultConstGateAux bits N a multBits 0) f = f := by
  show Gate.applyNat Gate.I f = f
  exact Gate.applyNat_I f

/-- Special case at `multBits = 0`: the full multiplier gate is identity
(no multiplier bits to control). -/
theorem modMultConstGate_correct_zero
    (bits N a : Nat) (f : Nat → Bool) :
    Gate.applyNat (modMultConstGate bits N a 0) f = f := by
  unfold modMultConstGate
  exact modMultConstGateAux_correct_zero bits N a 0 f

/-- State-level unfolding for the recursive step. -/
theorem modMultConstGateAux_apply_succ
    (bits N a multBits k : Nat) (f : Nat → Bool) :
    Gate.applyNat (modMultConstGateAux bits N a multBits (k + 1)) f
    = Gate.applyNat
        (controlledModAddConstGate bits N ((a * 2^k) % N)
          (adder_n_qubits (bits + 1) + k)
          (adder_n_qubits (bits + 1) + multBits))
        (Gate.applyNat (modMultConstGateAux bits N a multBits k) f) := by
  show Gate.applyNat (Gate.seq _ _) f = _
  exact Gate.applyNat_seq _ _ _

/-- **Commute lemma for `controlledModAddConstGate`.**  The gate commutes
with an `update _ p v` when `p` is outside the gate's read/write set:
`p ≥ adder_n_qubits (bits+1)` (above the adder block), `p ≠ controlIdx`,
and `p ≠ flagIdx`.  This is the key infrastructure for the inductive
multiplier correctness proof, where each iteration's gate must commute
past updates at OTHER multiplier-bit positions. -/
theorem controlledModAddConstGate_commute_update_outer
    (bits N c controlIdx flagIdx p : Nat) (v : Bool) (hbits : 1 ≤ bits)
    (hp_dim : adder_n_qubits (bits + 1) ≤ p)
    (h_p_ne_ctrl : p ≠ controlIdx) (h_p_ne_flag : p ≠ flagIdx) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx)
          (update f p v)
      = update (Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx) f)
          p v := by
  intro f
  have h2bits : 2 ≤ bits + 1 := by omega
  have h_p_ne_target : p ≠ target_idx bits := by
    unfold adder_n_qubits at hp_dim
    unfold target_idx
    omega
  -- Each sub-gate commutes with `update _ p v` because `p` is outside its support.
  have h_cond_ctrl : ∀ (cst : Nat) (f' : Nat → Bool),
      Gate.applyNat (conditionalAddConstGate (bits + 1) cst controlIdx) (update f' p v)
      = update (Gate.applyNat (conditionalAddConstGate (bits + 1) cst controlIdx) f') p v :=
    fun cst f' => conditionalAddConstGate_commute_update_outer (bits+1) cst controlIdx p v
      h2bits hp_dim h_p_ne_ctrl f'
  have h_cond_flag : ∀ (cst : Nat) (f' : Nat → Bool),
      Gate.applyNat (conditionalAddConstGate (bits + 1) cst flagIdx) (update f' p v)
      = update (Gate.applyNat (conditionalAddConstGate (bits + 1) cst flagIdx) f') p v :=
    fun cst f' => conditionalAddConstGate_commute_update_outer (bits+1) cst flagIdx p v
      h2bits hp_dim h_p_ne_flag f'
  have h_ccx : ∀ (f' : Nat → Bool),
      Gate.applyNat (Gate.CCX controlIdx (target_idx bits) flagIdx) (update f' p v)
      = update (Gate.applyNat (Gate.CCX controlIdx (target_idx bits) flagIdx) f') p v :=
    fun f' => applyNat_CCX_commute_update_disjoint controlIdx (target_idx bits) flagIdx f' p v
      h_p_ne_ctrl h_p_ne_target h_p_ne_flag
  have h_cx : ∀ (f' : Nat → Bool),
      Gate.applyNat (Gate.CX controlIdx flagIdx) (update f' p v)
      = update (Gate.applyNat (Gate.CX controlIdx flagIdx) f') p v :=
    fun f' => applyNat_CX_commute_update_disjoint controlIdx flagIdx f' p v
      h_p_ne_ctrl h_p_ne_flag
  show Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx) (update f p v)
      = update (Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx) f) p v
  -- Term-mode chain via applyNat_seq_commute_update across the 8-step composition.
  unfold controlledModAddConstGate
  exact applyNat_seq_commute_update _ _ _ _ _ (h_cond_ctrl c)
    (fun f1 => applyNat_seq_commute_update _ _ _ _ _ (h_cond_ctrl _)
      (fun f2 => applyNat_seq_commute_update _ _ _ _ _ h_ccx
        (fun f3 => applyNat_seq_commute_update _ _ _ _ _ (h_cond_flag N)
          (fun f4 => applyNat_seq_commute_update _ _ _ _ _ (h_cond_ctrl _)
            (fun f5 => applyNat_seq_commute_update _ _ _ _ _ h_ccx
              (fun f6 => applyNat_seq_commute_update _ _ _ _ _ h_cx
                (fun f7 => h_cond_ctrl c f7)))))))

/-! #### Tick 7b — multiplier-level commute lemma. -/

/-- **Commute lemma for `modMultConstGateAux`.**  At positions strictly
above the multiplier circuit's flag (i.e., `p > adder_n_qubits (bits+1)
+ multBits`), an `update _ p v` commutes through the full multiplier
auxiliary gate.  Proven directly via `applyNat_commute_update_above_dim`
applied to `modMultConstGateAux_wellTyped`. -/
theorem modMultConstGateAux_commute_update_outer
    (bits N a multBits k p : Nat) (v : Bool) (hbits : 1 ≤ bits)
    (hk : k ≤ multBits) (hp : adder_n_qubits (bits + 1) + multBits < p) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (modMultConstGateAux bits N a multBits k) (update f p v)
      = update (Gate.applyNat (modMultConstGateAux bits N a multBits k) f) p v := by
  intro f
  have h_wt := modMultConstGateAux_wellTyped bits N a multBits k hbits hk
  exact applyNat_commute_update_above_dim
    (adder_n_qubits (bits + 1) + multBits + 1)
    (modMultConstGateAux bits N a multBits k) h_wt f p v (by omega)

/-- **Commute lemma for `modMultConstGate`.**  Specialization of the
aux-level commute lemma at `k = multBits`. -/
theorem modMultConstGate_commute_update_outer
    (bits N a multBits p : Nat) (v : Bool) (hbits : 1 ≤ bits)
    (hp : adder_n_qubits (bits + 1) + multBits < p) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (modMultConstGate bits N a multBits) (update f p v)
      = update (Gate.applyNat (modMultConstGate bits N a multBits) f) p v := by
  intro f
  unfold modMultConstGate
  exact modMultConstGateAux_commute_update_outer bits N a multBits multBits p v
    hbits (le_refl _) hp f

/-- **`modMultConstGateAux` commute lemma at a multiplier-bit position.**
For positions in the multiplier-bit range
`p = adder_n_qubits (bits+1) + j` with `j < multBits` AND `j ≥ k`
(i.e., a multiplier bit that has NOT yet been touched by iterations
`0, 1, ..., k-1`), `update _ p v` commutes through
`modMultConstGateAux bits N a multBits k`.  Proven by induction on `k`,
using `controlledModAddConstGate_commute_update_outer` for the step. -/
theorem modMultConstGateAux_commute_update_mult_pos_above
    (bits N a multBits k j : Nat) (v : Bool) (hbits : 1 ≤ bits)
    (hk : k ≤ multBits) (hjk : k ≤ j) (hj : j < multBits) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (modMultConstGateAux bits N a multBits k)
          (update f (adder_n_qubits (bits + 1) + j) v)
      = update (Gate.applyNat (modMultConstGateAux bits N a multBits k) f)
          (adder_n_qubits (bits + 1) + j) v := by
  induction k with
  | zero =>
      intro f
      show Gate.applyNat Gate.I _ = update (Gate.applyNat Gate.I f) _ v
      rfl
  | succ k ih =>
      intro f
      have hk' : k ≤ multBits := by omega
      have hjk' : k ≤ j := by omega
      have h_step_ne_ctrl :
          adder_n_qubits (bits + 1) + j ≠ adder_n_qubits (bits + 1) + k := by omega
      have h_step_ne_flag :
          adder_n_qubits (bits + 1) + j ≠ adder_n_qubits (bits + 1) + multBits := by omega
      have h_p_dim :
          adder_n_qubits (bits + 1) ≤ adder_n_qubits (bits + 1) + j := by omega
      -- Unfold modMultConstGateAux at (k+1) on BOTH sides.
      simp only [modMultConstGateAux_apply_succ]
      -- Apply IH to the inner update on the LHS.
      rw [ih hk' hjk' f]
      -- Apply step commute to push update past the outer controlled-mod-add.
      exact controlledModAddConstGate_commute_update_outer bits N ((a * 2^k) % N)
              (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits)
              (adder_n_qubits (bits + 1) + j) v hbits h_p_dim h_step_ne_ctrl h_step_ne_flag
              (Gate.applyNat (modMultConstGateAux bits N a multBits k) f)

/-! #### Tick 7c — multiplier-encoded input. -/

/-- Auxiliary recursive helper for the multiplier-encoded input: starting
from `f`, applies an `update _ (adder_n_qubits (bits+1) + j) (Nat.testBit
m j)` for each `j = 0, 1, ..., i-1`, in order.  The last update written
is at `j = i - 1`. -/
def mult_input_F_aux (bits multBits m : Nat) : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, f => f
  | i+1, f =>
    update (mult_input_F_aux bits multBits m i f)
           (adder_n_qubits (bits + 1) + i) (Nat.testBit m i)

/-- **Multiplier-encoded input.**  Starts from `adder_input_F (bits+1) 0
x` (which puts value `x` in the adder's target register and 0 elsewhere
within the adder block; `false` outside), then fills the multiplier
qubits at positions `adder_n_qubits (bits+1) + j` (for `j = 0, ...,
multBits - 1`) with the bits of `m`. -/
def mult_input_F (bits multBits x m : Nat) : Nat → Bool :=
  mult_input_F_aux bits multBits m multBits (adder_input_F (bits + 1) 0 x)

/-- Recursion unfolding for the aux at `i+1`. -/
theorem mult_input_F_aux_succ (bits multBits m i : Nat) (f : Nat → Bool) :
    mult_input_F_aux bits multBits m (i + 1) f
    = update (mult_input_F_aux bits multBits m i f)
             (adder_n_qubits (bits + 1) + i) (Nat.testBit m i) := rfl

/-- Decoder at multiplier-bit positions: `mult_input_F_aux ... i f` at
position `adder_n_qubits (bits+1) + j` returns `Nat.testBit m j`, when
`j < i` (i.e., bit `j` has been written by some iteration ≤ i-1). -/
theorem mult_input_F_aux_at_mult_pos
    (bits multBits m i j : Nat) (hj : j < i) (f : Nat → Bool) :
    mult_input_F_aux bits multBits m i f (adder_n_qubits (bits + 1) + j)
    = Nat.testBit m j := by
  induction i with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ i ih =>
      rw [mult_input_F_aux_succ]
      by_cases h_j_eq_i : j = i
      · subst h_j_eq_i
        exact update_eq _ _ _
      · have h_j_lt_i : j < i := by omega
        have h_ne : adder_n_qubits (bits + 1) + j ≠ adder_n_qubits (bits + 1) + i := by
          omega
        rw [update_neq _ _ _ _ h_ne]
        exact ih h_j_lt_i

/-- Decoder at non-multiplier positions: `mult_input_F_aux ... i f` at
position `p` outside the multiplier-bit range
`[adder_n_qubits (bits+1), adder_n_qubits (bits+1) + i)` equals `f p`. -/
theorem mult_input_F_aux_at_non_mult_pos
    (bits multBits m i p : Nat)
    (h_outside : p < adder_n_qubits (bits + 1) ∨ adder_n_qubits (bits + 1) + i ≤ p)
    (f : Nat → Bool) :
    mult_input_F_aux bits multBits m i f p = f p := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [mult_input_F_aux_succ]
      have h_outside_i : p < adder_n_qubits (bits + 1) ∨ adder_n_qubits (bits + 1) + i ≤ p := by
        rcases h_outside with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      have h_p_ne : p ≠ adder_n_qubits (bits + 1) + i := by
        rcases h_outside with h | h
        · omega
        · omega
      rw [update_neq _ _ _ _ h_p_ne]
      exact ih h_outside_i

/-- Top-level decoder at multiplier-bit position. -/
theorem mult_input_F_at_mult_pos
    (bits multBits x m j : Nat) (hj : j < multBits) :
    mult_input_F bits multBits x m (adder_n_qubits (bits + 1) + j)
    = Nat.testBit m j := by
  unfold mult_input_F
  exact mult_input_F_aux_at_mult_pos bits multBits m multBits j hj _

/-- Top-level decoder at non-multiplier positions: equal to
`adder_input_F (bits+1) 0 x`. -/
theorem mult_input_F_at_non_mult_pos
    (bits multBits x m p : Nat)
    (h_outside : p < adder_n_qubits (bits + 1)
                 ∨ adder_n_qubits (bits + 1) + multBits ≤ p) :
    mult_input_F bits multBits x m p = adder_input_F (bits + 1) 0 x p := by
  unfold mult_input_F
  exact mult_input_F_aux_at_non_mult_pos bits multBits m multBits p h_outside _

/-! #### Tick 7d — `mult_input_F` reordering (pulling out the k-th
multiplier update). -/

/-- `mult_input_F_aux` commutes with an `update _ (adder_n_qubits (bits+1) + j) v`
when `j ≥ i` (i.e., the iteration hasn't touched position `pos j` yet). -/
theorem mult_input_F_aux_commute_update_above
    (bits multBits m i j : Nat) (hj : i ≤ j) (v : Bool) (f : Nat → Bool) :
    mult_input_F_aux bits multBits m i (update f (adder_n_qubits (bits + 1) + j) v)
    = update (mult_input_F_aux bits multBits m i f)
             (adder_n_qubits (bits + 1) + j) v := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hj_succ : i ≤ j := by omega
      have h_ne_succ : adder_n_qubits (bits + 1) + i ≠ adder_n_qubits (bits + 1) + j := by
        have : i < j := by omega
        omega
      have h_ne_succ' : adder_n_qubits (bits + 1) + j ≠ adder_n_qubits (bits + 1) + i :=
        Ne.symm h_ne_succ
      rw [mult_input_F_aux_succ, ih hj_succ]
      rw [update_update_comm _ _ _ _ _ h_ne_succ']
      rw [← mult_input_F_aux_succ]

/-- **`mult_input_F` isolation at position `k`.**  For `k < multBits`,
the full multiplier-encoded input is equal to `mult_input_F_aux` at
iteration `multBits` applied to a base that already carries the k-th
multiplier update on `adder_input_F`.  The k-th iteration of the aux
overwrites position `adder_n_qubits (bits+1) + k` to the same value
(`Nat.testBit m k`), so the additional update is absorbed; outside the
multiplier range the update at `pos k` is transparent. -/
theorem mult_input_F_isolate_k
    (bits multBits x m k : Nat) (hk : k < multBits) :
    mult_input_F bits multBits x m
    = mult_input_F_aux bits multBits m multBits
        (update (adder_input_F (bits + 1) 0 x)
                (adder_n_qubits (bits + 1) + k) (Nat.testBit m k)) := by
  funext q
  unfold mult_input_F
  by_cases h_q_in : adder_n_qubits (bits + 1) ≤ q
                    ∧ q < adder_n_qubits (bits + 1) + multBits
  · -- q in the multiplier range: q = pos j for some j < multBits.
    obtain ⟨h_q_lo, h_q_hi⟩ := h_q_in
    obtain ⟨j, hj_eq⟩ : ∃ j, q = adder_n_qubits (bits + 1) + j :=
      ⟨q - adder_n_qubits (bits + 1), by omega⟩
    have hj : j < multBits := by omega
    rw [hj_eq]
    rw [mult_input_F_aux_at_mult_pos bits multBits m multBits j hj
         (adder_input_F (bits + 1) 0 x)]
    rw [mult_input_F_aux_at_mult_pos bits multBits m multBits j hj
         (update (adder_input_F (bits + 1) 0 x)
                 (adder_n_qubits (bits + 1) + k) (Nat.testBit m k))]
  · -- q outside the multiplier range: both sides reduce to the base function at q.
    have h_outside : q < adder_n_qubits (bits + 1)
                   ∨ adder_n_qubits (bits + 1) + multBits ≤ q := by
      by_cases h_lo : q < adder_n_qubits (bits + 1)
      · exact Or.inl h_lo
      · push_neg at h_lo
        exact Or.inr (by
          rcases Nat.lt_or_ge q (adder_n_qubits (bits + 1) + multBits) with h | h
          · exact absurd ⟨h_lo, h⟩ h_q_in
          · exact h)
    rw [mult_input_F_aux_at_non_mult_pos bits multBits m multBits q h_outside
         (adder_input_F (bits + 1) 0 x)]
    rw [mult_input_F_aux_at_non_mult_pos bits multBits m multBits q h_outside
         (update (adder_input_F (bits + 1) 0 x)
                 (adder_n_qubits (bits + 1) + k) (Nat.testBit m k))]
    -- Goal: adder_input_F ... q = (update (adder_input_F) (pos k) (testBit m k)) q.
    have h_q_ne_k : q ≠ adder_n_qubits (bits + 1) + k := by
      rcases h_outside with h | h
      · omega
      · omega
    rw [update_neq _ _ _ _ h_q_ne_k]

/-! #### Tick 7e — full single-step correctness on `mult_input_F`. -/

/-- Absorption lemma: when an outer `update` at the k-th multiplier
position rewrites a value that the inner aux-at-iteration-k already
carries (because the inner has `update f (pos k) (testBit m k)` as base
and aux at k doesn't touch pos k), the outer update is a no-op. -/
private theorem mult_input_F_aux_absorb_at_k_position
    (bits multBits m k : Nat) (f : Nat → Bool) :
    mult_input_F_aux bits multBits m (k + 1)
        (update f (adder_n_qubits (bits + 1) + k) (Nat.testBit m k))
    = mult_input_F_aux bits multBits m k
        (update f (adder_n_qubits (bits + 1) + k) (Nat.testBit m k)) := by
  rw [mult_input_F_aux_succ]
  funext q
  by_cases hq : q = adder_n_qubits (bits + 1) + k
  · subst hq
    rw [update_eq]
    rw [mult_input_F_aux_at_non_mult_pos bits multBits m k
          (adder_n_qubits (bits + 1) + k) (Or.inr (le_refl _)) _]
    rw [update_eq]
  · rw [update_neq _ _ _ _ hq]

/-- Inductive helper for the single-step correctness on `mult_input_F`. -/
private theorem CMAcg_on_mult_input_F_aux_iso
    (bits N c x m multBits k : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N) (hk : k < multBits) :
    ∀ i, i ≤ multBits →
    Gate.applyNat
      (controlledModAddConstGate bits N c
        (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits))
      (mult_input_F_aux bits multBits m i
        (update (adder_input_F (bits + 1) 0 x)
                (adder_n_qubits (bits + 1) + k) (Nat.testBit m k)))
    = mult_input_F_aux bits multBits m i
        (update (adder_input_F (bits + 1) 0
                  (if Nat.testBit m k then (x + c) % N else x))
                (adder_n_qubits (bits + 1) + k) (Nat.testBit m k)) := by
  intro i hi
  induction i with
  | zero =>
      have h_ctrl_ge_adder :
          adder_n_qubits (bits + 1) ≤ adder_n_qubits (bits + 1) + k := by omega
      have h_flag_ge_ctrl :
          adder_n_qubits (bits + 1) + k + 1 ≤ adder_n_qubits (bits + 1) + multBits := by omega
      show Gate.applyNat _ (update _ _ _) = update _ _ _
      exact controlledModAddConstGate_correct bits N c x
              (Nat.testBit m k)
              (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits)
              hbits hN_pos hN hx hc_pos hc h_ctrl_ge_adder (by omega)
  | succ i ih =>
      have hi' : i ≤ multBits := by omega
      have ih' := ih hi'
      by_cases hi_eq_k : i = k
      · -- Outer update at pos i = pos k is absorbed via the absorption lemma.
        subst hi_eq_k
        rw [mult_input_F_aux_absorb_at_k_position bits multBits m i
              (adder_input_F (bits + 1) 0 x)]
        rw [mult_input_F_aux_absorb_at_k_position bits multBits m i
              (adder_input_F (bits + 1) 0 (if Nat.testBit m i then (x + c) % N else x))]
        exact ih'
      · -- Pos i ≠ controlIdx and ≠ flagIdx. Commute CMAcg past the outer update.
        rw [mult_input_F_aux_succ]
        rw [mult_input_F_aux_succ]
        have h_pos_i_above_adder :
            adder_n_qubits (bits + 1) ≤ adder_n_qubits (bits + 1) + i := by omega
        have h_pos_i_ne_ctrl :
            adder_n_qubits (bits + 1) + i ≠ adder_n_qubits (bits + 1) + k := by
          intro h_eq; apply hi_eq_k; omega
        have h_pos_i_ne_flag :
            adder_n_qubits (bits + 1) + i ≠ adder_n_qubits (bits + 1) + multBits := by
          have : i < multBits := by omega
          omega
        rw [controlledModAddConstGate_commute_update_outer bits N c
              (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits)
              (adder_n_qubits (bits + 1) + i) (Nat.testBit m i) hbits
              h_pos_i_above_adder h_pos_i_ne_ctrl h_pos_i_ne_flag _]
        rw [ih']

/-- **Single-step correctness for `controlledModAddConstGate` on
`mult_input_F`.**  Applied to the multiplier-encoded input
`mult_input_F bits multBits x m`, the controlled modular-add gate
(controlled by the `k`-th multiplier qubit, with shared flag at
position `adder_n_qubits (bits+1) + multBits`) advances the adder's
target register from `x` to `(x + c) % N` when bit `k` of `m` is set,
or leaves it unchanged otherwise. -/
theorem controlledModAddConstGate_on_mult_input_F
    (bits N c x m multBits k : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N) (hk : k < multBits) :
    Gate.applyNat
      (controlledModAddConstGate bits N c
        (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits))
      (mult_input_F bits multBits x m)
    = mult_input_F bits multBits
        (if Nat.testBit m k then (x + c) % N else x) m := by
  rw [mult_input_F_isolate_k bits multBits x m k hk]
  rw [mult_input_F_isolate_k bits multBits
        (if Nat.testBit m k then (x + c) % N else x) m k hk]
  exact CMAcg_on_mult_input_F_aux_iso bits N c x m multBits k
          hbits hN_pos hN hx hc_pos hc hk multBits (le_refl _)

/-! #### Tick 7f — full multiplier correctness. -/

/-- **Bit decomposition for the next power of two.**
`m mod 2^(k+1) = m mod 2^k + (testBit m k as Nat) * 2^k`. -/
private lemma m_mod_two_pow_succ_eq (m k : Nat) :
    m % 2^(k+1) = m % 2^k + (m / 2^k % 2) * 2^k := by
  have h_pow : 2^(k+1) = 2^k * 2 := by ring
  have h_pos : 0 < 2^k := Nat.two_pow_pos k
  have h_div_div : m / 2^(k+1) = m / 2^k / 2 := by
    rw [h_pow]; exact (Nat.div_div_eq_div_mul m (2^k) 2).symm
  have h1 : 2^k * (m / 2^k) + m % 2^k = m := Nat.div_add_mod m (2^k)
  have h2 : 2^(k+1) * (m / 2^(k+1)) + m % 2^(k+1) = m := Nat.div_add_mod m (2^(k+1))
  have h3 : 2 * (m / 2^k / 2) + m / 2^k % 2 = m / 2^k := Nat.div_add_mod (m / 2^k) 2
  have h2' : 2^k * 2 * (m / 2^k / 2) + m % 2^(k+1) = m := by
    rw [← h_pow, ← h_div_div]; exact h2
  nlinarith [h1, h2', h3, h_pos]

/-- **Inductive correctness for `modMultConstGateAux`.**  At iteration
`k ≤ multBits`, the aux gate has advanced the adder's target from `x`
to `(x + a * (m mod 2^k)) mod N`, given that each per-bit constant
`(a * 2^j) % N` is non-zero for `j < multBits`. -/
theorem modMultConstGateAux_correct
    (bits N a multBits x m : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N)
    (h_const_pos : ∀ j, j < multBits → 0 < (a * 2^j) % N) :
    ∀ k, k ≤ multBits →
    Gate.applyNat (modMultConstGateAux bits N a multBits k)
                  (mult_input_F bits multBits x m)
    = mult_input_F bits multBits ((x + a * (m % 2^k)) % N) m := by
  intro k hk
  induction k with
  | zero =>
      show Gate.applyNat Gate.I _ = _
      rw [Gate.applyNat_I]
      have h_mod : m % 2^0 = 0 := by rw [pow_zero]; exact Nat.mod_one m
      rw [h_mod, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hx]
  | succ k ih =>
      have hk' : k ≤ multBits := by omega
      have ih' := ih hk'
      rw [modMultConstGateAux_apply_succ, ih']
      have h_step_c_pos : 0 < (a * 2^k) % N := h_const_pos k (by omega)
      have h_step_c_lt : (a * 2^k) % N < N := Nat.mod_lt _ hN_pos
      have h_T_k_lt_N : (x + a * (m % 2^k)) % N < N := Nat.mod_lt _ hN_pos
      have hk_lt : k < multBits := by omega
      rw [controlledModAddConstGate_on_mult_input_F bits N ((a * 2^k) % N)
            ((x + a * (m % 2^k)) % N) m multBits k
            hbits hN_pos hN h_T_k_lt_N h_step_c_pos h_step_c_lt hk_lt]
      congr 1
      have h_decomp : m % 2^(k+1) = m % 2^k + (m / 2^k % 2) * 2^k :=
        m_mod_two_pow_succ_eq m k
      cases h_bit : Nat.testBit m k with
      | true =>
          have h_tb : (m / 2^k) % 2 = 1 := by
            rw [Nat.testBit_eq_decide_div_mod_eq] at h_bit
            exact of_decide_eq_true h_bit
          simp only [if_true]
          rw [h_decomp, h_tb, Nat.one_mul, Nat.mul_add]
          rw [show x + (a * (m % 2 ^ k) + a * 2 ^ k)
                = (x + a * (m % 2 ^ k)) + a * 2 ^ k from by ring]
          rw [← Nat.add_mod]
      | false =>
          have h_tb : (m / 2^k) % 2 = 0 := by
            rw [Nat.testBit_eq_decide_div_mod_eq] at h_bit
            have h := of_decide_eq_false h_bit
            omega
          rw [if_neg (by decide : ¬((false : Bool) = true))]
          rw [h_decomp, h_tb, Nat.zero_mul, Nat.add_zero]

/-- **Modular multiplier correctness.**  When `m < 2^multBits`, the
modular multiplier gate sends the adder's target from `x` to
`(x + a * m) mod N`, while preserving the multiplier register `m` and
the flag.  Equivalent form: each multiplier-bit `i` contributes
`(a * 2^i) mod N` to the target when set. -/
theorem modMultConstGate_correct
    (bits N a multBits x m : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N)
    (hm : m < 2^multBits)
    (h_const_pos : ∀ j, j < multBits → 0 < (a * 2^j) % N) :
    Gate.applyNat (modMultConstGate bits N a multBits)
                  (mult_input_F bits multBits x m)
    = mult_input_F bits multBits ((x + a * m) % N) m := by
  unfold modMultConstGate
  rw [modMultConstGateAux_correct bits N a multBits x m
        hbits hN_pos hN hx h_const_pos multBits (le_refl _)]
  rw [Nat.mod_eq_of_lt hm]

/-! ### Tick 8 — Initial-state form for Shor's modular multiplier.

The Shor oracle expects modular multiplication acting on an input state
where the multiplier register holds `x` and the adder register is
zeroed.  The gate then advances the adder's target from `0` to
`a * x mod N` (out-of-place form).

**Register-layout note.**  Our `mult_input_F bits multBits x m` places
the adder block at LOW positions (0 to `adder_n_qubits (bits+1) - 1`),
the multiplier register at positions `adder_n_qubits (bits+1) ..
adder_n_qubits (bits+1) + multBits - 1` (LITTLE-endian by
`Nat.testBit`), and the flag at the TOP.  The Shor encoding
`encodeDataZeroAnc n anc x` (in `MCPBridge.lean`) places data at LOW
positions 0..n-1 in BIG-endian order, and zero ancillas at n..n+anc-1.
These layouts are NOT identical — bridging fully to
`encodeDataZeroAnc` requires register permutation (swap-style)
and/or coordinate flipping, deferred to a future tick.

What we land here: the **initial-state correctness** theorem and the
WellTyped corollary at the Shor-compatible total dimension. -/

/-- Initial state for the multiplier: the multiplier register holds
`x`, the adder block and flag are zeroed. -/
def mult_state_init (bits multBits x : Nat) : Nat → Bool :=
  mult_input_F bits multBits 0 x

/-- Decoder at multiplier-bit positions. -/
theorem mult_state_init_at_mult_pos
    (bits multBits x j : Nat) (hj : j < multBits) :
    mult_state_init bits multBits x (adder_n_qubits (bits + 1) + j)
    = Nat.testBit x j := by
  unfold mult_state_init
  exact mult_input_F_at_mult_pos bits multBits 0 x j hj

/-- Decoder at non-multiplier positions: zero. -/
theorem mult_state_init_at_non_mult_pos
    (bits multBits x p : Nat)
    (h_outside : p < adder_n_qubits (bits + 1)
                 ∨ adder_n_qubits (bits + 1) + multBits ≤ p) :
    mult_state_init bits multBits x p = adder_input_F (bits + 1) 0 0 p := by
  unfold mult_state_init
  exact mult_input_F_at_non_mult_pos bits multBits 0 x p h_outside

/-- **Modular multiplier on the initial input state.**  When applied to
`mult_state_init bits multBits x` (multiplier register holds `x`,
adder zeroed), the gate produces a state whose adder-target register
encodes `(a * x) mod N` while the multiplier register `x` is
preserved.  Hypotheses ensure each per-bit constant `(a * 2^j) % N`
is positive (Shor's coprimality condition) and `x < 2^multBits`. -/
theorem modMultConstGate_on_init_correct
    (bits N a multBits x : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < 2^multBits)
    (h_const_pos : ∀ j, j < multBits → 0 < (a * 2^j) % N) :
    Gate.applyNat (modMultConstGate bits N a multBits)
                  (mult_state_init bits multBits x)
    = mult_input_F bits multBits ((a * x) % N) x := by
  unfold mult_state_init
  have h_0_lt_N : 0 < N := hN_pos
  rw [modMultConstGate_correct bits N a multBits 0 x
        hbits hN_pos hN (by omega) hx h_const_pos]
  congr 1
  rw [Nat.zero_add]

/-- **WellTyped corollary at the Shor-compatible dimension.**  Setting
`n := multBits` (the data register size) and `anc := adder_n_qubits
(bits+1) + 1` (the workspace including the flag), the modular
multiplier gate is well-typed at dimension `n + anc`, matching the
shape required by `encodeDataZeroAnc n anc` and
`MultiplyCircuitProperty a N n anc`. -/
theorem modMultConstGate_wellTyped_at_shor_dim
    (bits N a multBits : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
      (modMultConstGate bits N a multBits) := by
  have h := modMultConstGate_wellTyped bits N a multBits hbits
  -- adder_n_qubits (bits+1) + multBits + 1 = multBits + (adder_n_qubits (bits+1) + 1)
  have h_eq : adder_n_qubits (bits + 1) + multBits + 1
             = multBits + (adder_n_qubits (bits + 1) + 1) := by ring
  rw [← h_eq]
  exact h

/-! ### Tick 9 — Modular exponentiation step gate family.

The `i`-th step of QPE's controlled-multiplication cascade requires
multiplication by `a^(2^i) mod N`.  We define
`f_modmult_step_gate bits N a multBits i := modMultConstGate bits N
(a^(2^i) % N) multBits` and lift the multiplier's initial-state
correctness to the squared constant. -/

/-- The `i`-th step of the QPE multiplication cascade: multiplication
by the constant `a^(2^i) mod N` applied to the multiplier-encoded
state. -/
def f_modmult_step_gate (bits N a multBits i : Nat) : Gate :=
  modMultConstGate bits N (a^(2^i) % N) multBits

/-- **WellTyped** for the step gate at the Shor-compatible dimension. -/
theorem f_modmult_step_gate_wellTyped
    (bits N a multBits i : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
      (f_modmult_step_gate bits N a multBits i) := by
  unfold f_modmult_step_gate
  exact modMultConstGate_wellTyped_at_shor_dim bits N (a^(2^i) % N) multBits hbits

/-- **WellTyped** at the original aux dimension. -/
theorem f_modmult_step_gate_wellTyped_aux
    (bits N a multBits i : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (f_modmult_step_gate bits N a multBits i) := by
  unfold f_modmult_step_gate
  exact modMultConstGate_wellTyped bits N (a^(2^i) % N) multBits hbits

/-- **Step correctness on the initial state.**  Applied to
`mult_state_init bits multBits x`, the step gate at iterate `i`
produces a state whose adder-target register holds `(a^(2^i) * x) % N`
while the multiplier register `x` is preserved.  Hypotheses ensure
each per-bit constant `((a^(2^i)) * 2^j) % N` is positive (the
analogue of Shor's coprimality condition for the squared base). -/
theorem f_modmult_step_gate_on_init_correct
    (bits N a multBits i x : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < 2^multBits)
    (h_const_pos :
      ∀ j, j < multBits → 0 < ((a^(2^i) % N) * 2^j) % N) :
    Gate.applyNat (f_modmult_step_gate bits N a multBits i)
                  (mult_state_init bits multBits x)
    = mult_input_F bits multBits ((a^(2^i) * x) % N) x := by
  unfold f_modmult_step_gate
  rw [modMultConstGate_on_init_correct bits N (a^(2^i) % N) multBits x
        hbits hN_pos hN hx h_const_pos]
  -- Goal: mult_input_F bits multBits ((a^(2^i) % N) * x % N) x
  --     = mult_input_F bits multBits ((a^(2^i) * x) % N) x
  congr 1
  -- ((a^(2^i) % N) * x) % N = (a^(2^i) * x) % N
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-! ### Tick 10 — Out-of-place gate family + WellTyped over all iterates.

`f_modmult_gate_family bits N a multBits : Nat → Gate` provides the
full Shor-style multiplication cascade: at iterate `i`, multiplication
by `a^(2^i) mod N`.  WellTyped for all `i` follows by lifting the
single-step WellTyped theorem under the family. -/

/-- Modular multiplication gate family indexed by QPE iterate. -/
def f_modmult_gate_family (bits N a multBits : Nat) : Nat → Gate :=
  f_modmult_step_gate bits N a multBits

/-- **Family-level WellTyped.**  For every iterate `i`, the gate
`f_modmult_gate_family bits N a multBits i` is `Gate.WellTyped` at
the Shor-compatible dimension `n + anc = multBits +
(adder_n_qubits (bits+1) + 1)`. -/
theorem f_modmult_gate_family_wellTyped
    (bits N a multBits : Nat) (hbits : 1 ≤ bits) :
    ∀ i, Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
            (f_modmult_gate_family bits N a multBits i) := by
  intro i
  unfold f_modmult_gate_family
  exact f_modmult_step_gate_wellTyped bits N a multBits i hbits

/-- **Family-level out-of-place correctness on the initial state.**
For each iterate `i`, applied to `mult_state_init bits multBits x`,
the family member produces a state with adder-target register holding
`(a^(2^i) * x) mod N` and multiplier register `x` preserved. -/
theorem f_modmult_gate_family_on_init_correct
    (bits N a multBits : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (h_const_pos :
      ∀ i, ∀ j, j < multBits → 0 < ((a^(2^i) % N) * 2^j) % N) :
    ∀ i x, x < 2^multBits →
      Gate.applyNat (f_modmult_gate_family bits N a multBits i)
                    (mult_state_init bits multBits x)
      = mult_input_F bits multBits ((a^(2^i) * x) % N) x := by
  intro i x hx
  unfold f_modmult_gate_family
  exact f_modmult_step_gate_on_init_correct bits N a multBits i x
          hbits hN_pos hN hx (h_const_pos i)

/-! ### Tick 13 — Two-qubit SWAP primitive (path A foundation).

A SWAP between two qubits, expressed as the standard three-CNOT
decomposition `CX a b ; CX b a ; CX a b`.  This is the smallest
building block for the in-place modular multiplier wrapper
(`OOPmul(a) ; SWAP ; OOPmul^(-1)(a⁻¹)`) — see QUESTIONS.md
2026-05-28 03:24 path (A). -/

/-- Two-qubit SWAP: exchanges the values at qubits `a` and `b` via the
standard three-CNOT decomposition. -/
def qubit_swap (a b : Nat) : Gate :=
  Gate.seq (Gate.CX a b) (Gate.seq (Gate.CX b a) (Gate.CX a b))

/-- Well-typedness for `qubit_swap`. -/
theorem qubit_swap_wellTyped (dim a b : Nat)
    (ha : a < dim) (hb : b < dim) (hab : a ≠ b) :
    Gate.WellTyped dim (qubit_swap a b) := by
  refine ⟨⟨ha, hb, hab⟩, ⟨hb, ha, ?_⟩, ⟨ha, hb, hab⟩⟩
  exact fun h => hab h.symm

/-- **Boolean-state correctness for SWAP.**  Applied to `f`, the swap
gate produces a state with values at positions `a` and `b` exchanged. -/
theorem qubit_swap_correct (a b : Nat) (f : Nat → Bool) (hab : a ≠ b) :
    Gate.applyNat (qubit_swap a b) f
    = update (update f a (f b)) b (f a) := by
  unfold qubit_swap
  simp only [Gate.applyNat_seq, Gate.applyNat_CX]
  -- After unfolding, LHS is three nested updates with CX semantics:
  --   update (update (update f b (f b ⊕ f a)) a (...)) b (...)
  -- Evaluate the intermediate values that the inner CXs read.
  have hba : b ≠ a := Ne.symm hab
  -- After 1st CX(a,b): at position a still f a, at position b is f b ⊕ f a.
  have h_g1_a : update f b (xor (f b) (f a)) a = f a := update_neq _ _ _ _ hab
  have h_g1_b : update f b (xor (f b) (f a)) b = xor (f b) (f a) := update_eq _ _ _
  rw [h_g1_a, h_g1_b]
  -- After 2nd CX(b,a): writes (f a) ⊕ (f b ⊕ f a) = f b at position a.
  -- After 3rd CX(a,b): writes (intermediate at b) ⊕ (intermediate at a) at position b.
  have h_g2_a : update (update f b (xor (f b) (f a))) a (xor (f a) (xor (f b) (f a))) a
                = xor (f a) (xor (f b) (f a)) := update_eq _ _ _
  have h_g2_b : update (update f b (xor (f b) (f a))) a (xor (f a) (xor (f b) (f a))) b
                = xor (f b) (f a) := by
    rw [update_neq _ _ _ _ hba]; exact update_eq _ _ _
  rw [h_g2_b, h_g2_a]
  -- Now the LHS is fully expanded. Funext + case split on the queried position.
  funext q
  by_cases hqa : q = a
  · -- q = a: outer update at b (different), middle update at a (returns the xor expression).
    rw [hqa]
    rw [update_neq _ _ _ _ hab]
    rw [update_eq]
    -- RHS at a: update (update f a (f b)) b (f a) a = (update f a (f b)) a = f b.
    rw [update_neq _ _ _ _ hab]
    rw [update_eq]
    -- Goal: f a ⊕ (f b ⊕ f a) = f b. Boolean fact.
    cases h_fa : f a <;> cases h_fb : f b <;> rfl
  · by_cases hqb : q = b
    · -- q = b: outer update at b returns the xor expression.
      rw [hqb]
      rw [update_eq]
      -- RHS at b: f a.
      rw [update_eq]
      -- Goal: (f b ⊕ f a) ⊕ (f a ⊕ (f b ⊕ f a)) = f a. Boolean fact.
      cases h_fa : f a <;> cases h_fb : f b <;> rfl
    · -- q ≠ a, q ≠ b: all updates skip, both sides equal f q.
      rw [update_neq _ _ _ _ hqb]
      rw [update_neq _ _ _ _ hqa]
      rw [update_neq _ _ _ _ hqb]
      rw [update_neq _ _ _ _ hqb]
      rw [update_neq _ _ _ _ hqa]

/-! ### Tick 14 — Register SWAP primitive (multi-qubit SWAP). -/

/-- Auxiliary recursive register-swap helper.  At iteration count `n`,
applies pairwise `qubit_swap (offsetA + k) (offsetB + k)` for
`k = 0, 1, ..., n - 1`. -/
def register_swap_aux (offsetA offsetB : Nat) : Nat → Gate
  | 0 => Gate.I
  | k+1 => Gate.seq (register_swap_aux offsetA offsetB k)
                    (qubit_swap (offsetA + k) (offsetB + k))

/-- Register-level SWAP: exchanges two `multBits`-wide registers at
positions `[offsetA, offsetA + multBits)` and
`[offsetB, offsetB + multBits)`. -/
def register_swap (multBits offsetA offsetB : Nat) : Gate :=
  register_swap_aux offsetA offsetB multBits

/-- Recursion unfolding for `register_swap_aux`. -/
theorem register_swap_aux_succ
    (offsetA offsetB k : Nat) :
    register_swap_aux offsetA offsetB (k + 1)
    = Gate.seq (register_swap_aux offsetA offsetB k)
               (qubit_swap (offsetA + k) (offsetB + k)) := rfl

/-- **WellTyped for `register_swap_aux`.**  Requires non-empty
`dim`, both offset ranges fitting inside `dim`, and the two ranges
being disjoint. -/
theorem register_swap_aux_wellTyped
    (dim offsetA offsetB k : Nat) (hdim : 0 < dim)
    (hA : offsetA + k ≤ dim) (hB : offsetB + k ≤ dim)
    (h_disjoint : offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA) :
    Gate.WellTyped dim (register_swap_aux offsetA offsetB k) := by
  induction k with
  | zero =>
      show 0 < dim
      exact hdim
  | succ k ih =>
      have hA' : offsetA + k ≤ dim := by omega
      have hB' : offsetB + k ≤ dim := by omega
      have h_disjoint' :
          offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA := by
        rcases h_disjoint with h | h
        · left; omega
        · right; omega
      have h_ih := ih hA' hB' h_disjoint'
      have h_swap : Gate.WellTyped dim
          (qubit_swap (offsetA + k) (offsetB + k)) := by
        have hAk : offsetA + k < dim := by omega
        have hBk : offsetB + k < dim := by omega
        have hAk_ne_Bk : offsetA + k ≠ offsetB + k := by
          rcases h_disjoint with h | h
          · omega
          · omega
        exact qubit_swap_wellTyped dim (offsetA + k) (offsetB + k) hAk hBk hAk_ne_Bk
      show Gate.WellTyped dim
        (Gate.seq (register_swap_aux offsetA offsetB k) _)
      exact ⟨h_ih, h_swap⟩

/-- **WellTyped for `register_swap`.** -/
theorem register_swap_wellTyped
    (dim multBits offsetA offsetB : Nat) (hdim : 0 < dim)
    (hA : offsetA + multBits ≤ dim) (hB : offsetB + multBits ≤ dim)
    (h_disjoint : offsetA + multBits ≤ offsetB ∨ offsetB + multBits ≤ offsetA) :
    Gate.WellTyped dim (register_swap multBits offsetA offsetB) :=
  register_swap_aux_wellTyped dim offsetA offsetB multBits hdim hA hB h_disjoint

/-- **Correctness at "other" positions** of `register_swap_aux`.  At
any position outside both `[offsetA, offsetA + n)` and `[offsetB,
offsetB + n)`, the gate is identity. -/
theorem register_swap_aux_at_other
    (offsetA offsetB n : Nat) (f : Nat → Bool) (q : Nat)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA)
    (h_outside_A : q < offsetA ∨ offsetA + n ≤ q)
    (h_outside_B : q < offsetB ∨ offsetB + n ≤ q) :
    Gate.applyNat (register_swap_aux offsetA offsetB n) f q = f q := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have h_disjoint_k : offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA := by
        rcases h_disjoint with h | h
        · left; omega
        · right; omega
      have h_outside_A' : q < offsetA ∨ offsetA + k ≤ q := by
        rcases h_outside_A with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      have h_outside_B' : q < offsetB ∨ offsetB + k ≤ q := by
        rcases h_outside_B with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      have h_q_ne_Ak : q ≠ offsetA + k := by
        rcases h_outside_A with h | h
        · omega
        · omega
      have h_q_ne_Bk : q ≠ offsetB + k := by
        rcases h_outside_B with h | h
        · omega
        · omega
      have hAk_ne_Bk : offsetA + k ≠ offsetB + k := by
        rcases h_disjoint with h | h
        · omega
        · omega
      rw [register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      rw [update_neq _ _ _ _ h_q_ne_Bk]
      rw [update_neq _ _ _ _ h_q_ne_Ak]
      exact ih h_disjoint_k h_outside_A' h_outside_B'

/-- **Correctness at A positions**: at `offsetA + j` for `j < n`, the
gate returns `f (offsetB + j)`. -/
theorem register_swap_aux_at_A
    (offsetA offsetB n : Nat) (f : Nat → Bool) (j : Nat) (hj : j < n)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA) :
    Gate.applyNat (register_swap_aux offsetA offsetB n) f (offsetA + j)
    = f (offsetB + j) := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have h_disjoint_k : offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA := by
        rcases h_disjoint with h | h
        · left; omega
        · right; omega
      have hAk_ne_Bk : offsetA + k ≠ offsetB + k := by
        rcases h_disjoint with h | h
        · omega
        · omega
      rw [register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_neq _ _ _ _ (by omega : offsetA + k ≠ offsetB + k)]
        rw [update_eq]
        have h_outside_A_q : offsetB + k < offsetA ∨ offsetA + k ≤ offsetB + k := by
          rcases h_disjoint with h | h
          · right; omega
          · left; omega
        have h_outside_B_q : offsetB + k < offsetB ∨ offsetB + k ≤ offsetB + k := by
          right; omega
        exact register_swap_aux_at_other offsetA offsetB k f (offsetB + k)
                h_disjoint_k h_outside_A_q h_outside_B_q
      · have hj' : j < k := by omega
        have h_pos_A_ne_Bk : offsetA + j ≠ offsetB + k := by
          rcases h_disjoint with h | h
          · omega
          · omega
        have h_pos_A_ne_Ak : offsetA + j ≠ offsetA + k := by omega
        rw [update_neq _ _ _ _ h_pos_A_ne_Bk]
        rw [update_neq _ _ _ _ h_pos_A_ne_Ak]
        exact ih hj' h_disjoint_k

/-- **Correctness at B positions**: at `offsetB + j` for `j < n`, the
gate returns `f (offsetA + j)`. -/
theorem register_swap_aux_at_B
    (offsetA offsetB n : Nat) (f : Nat → Bool) (j : Nat) (hj : j < n)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA) :
    Gate.applyNat (register_swap_aux offsetA offsetB n) f (offsetB + j)
    = f (offsetA + j) := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have h_disjoint_k : offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA := by
        rcases h_disjoint with h | h
        · left; omega
        · right; omega
      have hAk_ne_Bk : offsetA + k ≠ offsetB + k := by
        rcases h_disjoint with h | h
        · omega
        · omega
      rw [register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_eq]
        have h_outside_A_q : offsetA + k < offsetA ∨ offsetA + k ≤ offsetA + k := by
          right; omega
        have h_outside_B_q : offsetA + k < offsetB ∨ offsetB + k ≤ offsetA + k := by
          rcases h_disjoint with h | h
          · left; omega
          · right; omega
        exact register_swap_aux_at_other offsetA offsetB k f (offsetA + k)
                h_disjoint_k h_outside_A_q h_outside_B_q
      · have hj' : j < k := by omega
        have h_pos_B_ne_Bk : offsetB + j ≠ offsetB + k := by omega
        have h_pos_B_ne_Ak : offsetB + j ≠ offsetA + k := by
          rcases h_disjoint with h | h
          · omega
          · omega
        rw [update_neq _ _ _ _ h_pos_B_ne_Bk]
        rw [update_neq _ _ _ _ h_pos_B_ne_Ak]
        exact ih hj' h_disjoint_k

/-! ### Tick 15 — Modular-inverse algebraic identities.

Two arithmetic facts about modular inverses that justify the third
stage of the in-place wrapper `OOPmul(a) ; SWAP ; OOPmul(N - a⁻¹)`:

(1) `ainv * (a*x mod N) mod N = x` — the modular inverse undoes the
    forward multiplication when `x < N` and `a * ainv ≡ 1 (mod N)`.

(2) `(x + (N - ainv) * (a*x mod N)) mod N = 0` — adding `(N - ainv) *
    (a*x mod N)` to `x` modular-cancels (where `N - ainv` plays the
    role of the additive inverse of `ainv` mod `N`).

Both are purely Nat arithmetic. -/

/-- **Modular-inverse "undo" identity.**  If `a * ainv ≡ 1 (mod N)`,
`x < N`, and `ainv < N`, then `ainv * (a*x mod N) mod N = x`. -/
theorem inv_mul_mod_eq_self (a ainv N x : Nat) (hN : 0 < N)
    (hx : x < N) (hainv : ainv < N) (h_inv : a * ainv % N = 1) :
    ainv * (a * x % N) % N = x := by
  -- Step 1: pull the inner `% N` out via Nat.mul_mod.
  have step : ainv * (a * x % N) % N = ainv * (a * x) % N := by
    conv_rhs => rw [Nat.mul_mod ainv (a * x) N]
    conv_lhs => rw [Nat.mul_mod ainv (a * x % N) N]
    rw [Nat.mod_mod]
  rw [step]
  -- Step 2: regroup and apply h_inv.
  rw [show ainv * (a * x) = (ainv * a) * x from by ring]
  rw [Nat.mul_mod (ainv * a) x N]
  rw [show ainv * a = a * ainv from Nat.mul_comm _ _]
  rw [h_inv, Nat.one_mul, Nat.mod_mod]
  exact Nat.mod_eq_of_lt hx

/-- **Modular cancellation by the additive-inverse-mod-N coefficient.**
If `a * ainv ≡ 1 (mod N)`, `x < N`, `ainv < N`, then
`(x + (N - ainv) * (a*x mod N)) mod N = 0`.  This is the algebraic
identity that justifies the third stage of the in-place modular
multiplier wrapper. -/
theorem mod_inv_cancel_identity (a ainv N x : Nat) (hN : 0 < N)
    (hx : x < N) (hainv : ainv < N) (h_inv : a * ainv % N = 1) :
    (x + (N - ainv) * (a * x % N)) % N = 0 := by
  have h1 := inv_mul_mod_eq_self a ainv N x hN hx hainv h_inv
  have hainv_le : ainv ≤ N := Nat.le_of_lt hainv
  set y := a * x % N with hy_def
  have h_sub : (N - ainv) * y = N * y - ainv * y := by rw [Nat.sub_mul]
  rw [h_sub]
  have h_le : ainv * y ≤ N * y := Nat.mul_le_mul_right _ hainv_le
  have h_add_sub : x + (N * y - ainv * y) = (x + N * y) - ainv * y := by omega
  rw [h_add_sub]
  -- ainv * y = N * (ainv * y / N) + (ainv * y % N) = N * (ainv * y / N) + x  (by h1)
  have h_ainv_y_decomp : ainv * y = N * (ainv * y / N) + x := by
    have := Nat.div_add_mod (ainv * y) N
    rw [h1] at this
    omega
  rw [h_ainv_y_decomp]
  have h_div_le : ainv * y / N ≤ y := by
    have h := Nat.div_le_div_right (c := N) h_le
    rw [Nat.mul_div_cancel_left _ hN] at h
    exact h
  have h_y_ge : N * (ainv * y / N) ≤ N * y := Nat.mul_le_mul_left N h_div_le
  -- (x + N*y - (N * (ainv*y / N) + x)) = N * y - N * (ainv*y / N) = N * (y - ainv*y/N).
  have h_collapse :
      (x + N * y - (N * (ainv * y / N) + x)) % N
      = (N * (y - ainv * y / N)) % N := by
    congr 1
    rw [Nat.mul_sub]
    omega
  rw [h_collapse]
  exact Nat.mul_mod_right _ _

/-! ### Tick 16 — In-place modular multiplier definition + WellTyped.

Compose the three stages of the Markov–Saeedi / Beauregard in-place
modular multiplier:

  modMultConstGate(a) ; mult_target_swap ; modMultConstGate(N - ainv)

The middle SWAP exchanges each multiplier-register qubit at position
`adder_n_qubits (bits+1) + k` with the corresponding adder-target
qubit at position `target_idx k = 3*k + 1`.  Because the target
register is interleaved with the adder's read/carry positions, this
SWAP is a sequence of `qubit_swap`s at NON-contiguous positions and
cannot be re-used from `register_swap`. -/

/-- Auxiliary recursive multiplier-target SWAP at iteration count `n`:
swaps `(adder_n_qubits (bits+1) + k, target_idx k)` for
`k = 0, ..., n - 1`. -/
def mult_target_swap_aux (bits : Nat) : Nat → Gate
  | 0 => Gate.I
  | k+1 => Gate.seq (mult_target_swap_aux bits k)
                    (qubit_swap (adder_n_qubits (bits + 1) + k) (target_idx k))

/-- Multiplier-target SWAP: pairwise exchanges multiplier-register
qubits at `adder_n_qubits (bits+1) + k` with adder-target qubits at
`target_idx k`, for `k = 0, ..., multBits - 1`. -/
def mult_target_swap (bits multBits : Nat) : Gate :=
  mult_target_swap_aux bits multBits

/-- Recursion unfolding for `mult_target_swap_aux`. -/
theorem mult_target_swap_aux_succ (bits k : Nat) :
    mult_target_swap_aux bits (k + 1)
    = Gate.seq (mult_target_swap_aux bits k)
               (qubit_swap (adder_n_qubits (bits + 1) + k) (target_idx k)) := rfl

/-- **WellTyped for `mult_target_swap_aux`.**  At dimension
`adder_n_qubits (bits + 1) + multBits + 1` (Shor-compatible), each
constituent `qubit_swap (adder_n_qubits + k) (target_idx k)` is
well-typed when `k ≤ multBits ≤ bits + 1`. -/
theorem mult_target_swap_aux_wellTyped
    (bits multBits k : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) (hk : k ≤ multBits) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (mult_target_swap_aux bits k) := by
  induction k with
  | zero =>
      show 0 < adder_n_qubits (bits + 1) + multBits + 1
      unfold adder_n_qubits
      omega
  | succ k ih =>
      have hk' : k ≤ multBits := by omega
      have h_ih := ih hk'
      have hk_lt_multBits : k < multBits := by omega
      have h_swap : Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
          (qubit_swap (adder_n_qubits (bits + 1) + k) (target_idx k)) := by
        apply qubit_swap_wellTyped
        · -- adder_n_qubits + k < dim = adder_n_qubits + multBits + 1
          omega
        · -- target_idx k = 3*k + 1 < dim.  k ≤ multBits ≤ bits + 1, so
          -- 3*k + 1 ≤ 3*(bits + 1) + 1 < 3*(bits + 1) + 2 = adder_n_qubits.
          unfold target_idx adder_n_qubits
          omega
        · -- adder_n_qubits + k ≠ target_idx k:  RHS ≤ 3*bits + 1 < adder_n_qubits + 0 ≤ LHS.
          unfold target_idx adder_n_qubits
          omega
      show Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
        (Gate.seq (mult_target_swap_aux bits k) _)
      exact ⟨h_ih, h_swap⟩

/-- **WellTyped for `mult_target_swap`.** -/
theorem mult_target_swap_wellTyped
    (bits multBits : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (mult_target_swap bits multBits) :=
  mult_target_swap_aux_wellTyped bits multBits multBits hbits h_multBits_le
    (le_refl _)

/-- **In-place modular multiplier gate.**  Three-stage composition:
1. `modMultConstGate bits N a multBits` — OOPmul(a): `|x⟩|0⟩ → |x⟩|a*x mod N⟩`.
2. `mult_target_swap bits multBits` — exchanges multiplier and target
   registers: `|x⟩|a*x mod N⟩ → |a*x mod N⟩|x⟩`.
3. `modMultConstGate bits N ((N - ainv) % N) multBits` — adds
   `(N - ainv) * (a*x mod N)` to the target, yielding 0 by
   `mod_inv_cancel_identity`.  Net effect: `|a*x mod N⟩|0⟩`.

The multiplier register holds the input `x` initially; after the
gate, it holds `(a * x) mod N`, with adder and flag clean.  This is
exactly the in-place semantics of `MultiplyCircuitProperty`. -/
def modMultInPlace (bits N a ainv multBits : Nat) : Gate :=
  Gate.seq (modMultConstGate bits N a multBits)
           (Gate.seq (mult_target_swap bits multBits)
                     (modMultConstGate bits N ((N - ainv) % N) multBits))

/-- **WellTyped for `modMultInPlace`.** -/
theorem modMultInPlace_wellTyped
    (bits N a ainv multBits : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (modMultInPlace bits N a ainv multBits) := by
  unfold modMultInPlace
  refine ⟨?_, ?_, ?_⟩
  · exact modMultConstGate_wellTyped bits N a multBits hbits
  · exact mult_target_swap_wellTyped bits multBits hbits h_multBits_le
  · exact modMultConstGate_wellTyped bits N ((N - ainv) % N) multBits hbits

/-- **In-place WellTyped at the Shor-compatible dimension.** -/
theorem modMultInPlace_wellTyped_at_shor_dim
    (bits N a ainv multBits : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) :
    Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
      (modMultInPlace bits N a ainv multBits) := by
  have h := modMultInPlace_wellTyped bits N a ainv multBits hbits h_multBits_le
  have h_eq : adder_n_qubits (bits + 1) + multBits + 1
             = multBits + (adder_n_qubits (bits + 1) + 1) := by ring
  rw [← h_eq]
  exact h

/-! ### Tick 17 — Position-level correctness for `mult_target_swap_aux`. -/

/-- **At-other for `mult_target_swap_aux`.**  If `q` is not equal to
any swap-paired position (multiplier-side or target-side) up to
iteration `n`, then the gate is identity at `q`.  Requires
`n ≤ bits + 1` to ensure each swap-pair has distinct positions. -/
theorem mult_target_swap_aux_at_other
    (bits n : Nat) (f : Nat → Bool) (q : Nat)
    (h_n_le : n ≤ bits + 1)
    (h_outside : ∀ k, k < n →
      q ≠ adder_n_qubits (bits + 1) + k ∧ q ≠ target_idx k) :
    Gate.applyNat (mult_target_swap_aux bits n) f q = f q := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have h_n_le' : k ≤ bits + 1 := by omega
      have h_outside_k : ∀ j, j < k →
          q ≠ adder_n_qubits (bits + 1) + j ∧ q ≠ target_idx j := by
        intro j hj; exact h_outside j (by omega)
      have h_q_ne_Ak : q ≠ adder_n_qubits (bits + 1) + k :=
        (h_outside k (by omega)).1
      have h_q_ne_Tk : q ≠ target_idx k :=
        (h_outside k (by omega)).2
      have hk_le_bits : k ≤ bits := by omega
      have h_Ak_ne_Tk : adder_n_qubits (bits + 1) + k ≠ target_idx k := by
        show 3 * (bits + 1) + 2 + k ≠ 3 * k + 1
        omega
      rw [mult_target_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ h_Ak_ne_Tk]
      rw [update_neq _ _ _ _ h_q_ne_Tk]
      rw [update_neq _ _ _ _ h_q_ne_Ak]
      exact ih h_n_le' h_outside_k

/-- **At multiplier-side position**: at `adder_n_qubits + j` for
`j < n`, the gate returns `f (target_idx j)`.  Requires
`n ≤ bits + 1`. -/
theorem mult_target_swap_aux_at_mult
    (bits n : Nat) (f : Nat → Bool) (j : Nat) (hj : j < n)
    (h_n_le : n ≤ bits + 1) :
    Gate.applyNat (mult_target_swap_aux bits n) f
      (adder_n_qubits (bits + 1) + j)
    = f (target_idx j) := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have h_n_le' : k ≤ bits + 1 := by omega
      have hk_le_bits : k ≤ bits := by omega
      have h_Ak_ne_Tk : adder_n_qubits (bits + 1) + k ≠ target_idx k := by
        show 3 * (bits + 1) + 2 + k ≠ 3 * k + 1
        omega
      rw [mult_target_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ h_Ak_ne_Tk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_neq _ _ _ _ h_Ak_ne_Tk]
        rw [update_eq]
        apply mult_target_swap_aux_at_other bits k f (target_idx k) h_n_le'
        intro k' hk'
        have hk'_le_bits : k' ≤ bits := by omega
        refine ⟨?_, ?_⟩
        · show target_idx k ≠ adder_n_qubits (bits + 1) + k'
          show 3 * k + 1 ≠ 3 * (bits + 1) + 2 + k'
          omega
        · show target_idx k ≠ target_idx k'
          show 3 * k + 1 ≠ 3 * k' + 1
          omega
      · have hj' : j < k := by omega
        have hj_le_bits : j ≤ bits := by omega
        have h_pos_Aj_ne_Tk : adder_n_qubits (bits + 1) + j ≠ target_idx k := by
          show 3 * (bits + 1) + 2 + j ≠ 3 * k + 1
          omega
        have h_pos_Aj_ne_Ak : adder_n_qubits (bits + 1) + j
                             ≠ adder_n_qubits (bits + 1) + k := by omega
        rw [update_neq _ _ _ _ h_pos_Aj_ne_Tk]
        rw [update_neq _ _ _ _ h_pos_Aj_ne_Ak]
        exact ih hj' h_n_le'

/-- **At target-side position**: at `target_idx j` for `j < n`, the
gate returns `f (adder_n_qubits + j)`.  Requires `n ≤ bits + 1`. -/
theorem mult_target_swap_aux_at_target
    (bits n : Nat) (f : Nat → Bool) (j : Nat) (hj : j < n)
    (h_n_le : n ≤ bits + 1) :
    Gate.applyNat (mult_target_swap_aux bits n) f (target_idx j)
    = f (adder_n_qubits (bits + 1) + j) := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have h_n_le' : k ≤ bits + 1 := by omega
      have hk_le_bits : k ≤ bits := by omega
      have h_Ak_ne_Tk : adder_n_qubits (bits + 1) + k ≠ target_idx k := by
        show 3 * (bits + 1) + 2 + k ≠ 3 * k + 1
        omega
      rw [mult_target_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ h_Ak_ne_Tk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_eq]
        apply mult_target_swap_aux_at_other bits k f
          (adder_n_qubits (bits + 1) + k) h_n_le'
        intro k' hk'
        have hk'_le_bits : k' ≤ bits := by omega
        refine ⟨?_, ?_⟩
        · show adder_n_qubits (bits + 1) + k ≠ adder_n_qubits (bits + 1) + k'
          omega
        · show adder_n_qubits (bits + 1) + k ≠ target_idx k'
          show 3 * (bits + 1) + 2 + k ≠ 3 * k' + 1
          omega
      · have hj' : j < k := by omega
        have hj_le_bits : j ≤ bits := by omega
        have h_pos_Tj_ne_Tk : target_idx j ≠ target_idx k := by
          show 3 * j + 1 ≠ 3 * k + 1
          omega
        have h_pos_Tj_ne_Ak : target_idx j ≠ adder_n_qubits (bits + 1) + k := by
          show 3 * j + 1 ≠ 3 * (bits + 1) + 2 + k
          omega
        rw [update_neq _ _ _ _ h_pos_Tj_ne_Tk]
        rw [update_neq _ _ _ _ h_pos_Tj_ne_Ak]
        exact ih hj' h_n_le'

/-! ### Tick 18 — SWAP semantics on `mult_input_F`. -/

/-- **HEADLINE: SWAP exchanges multiplier-register and target-register
values on `mult_input_F`.** Applied to `mult_input_F bits multBits x m`
(multiplier holds `m`, target holds `x`), the multiplier-target SWAP
produces `mult_input_F bits multBits m x` (multiplier holds `x`,
target holds `m`).  Requires `multBits ≤ bits + 1` (multiplier no
wider than adder) and `x, m < 2^multBits` (so they fit in the
multBits-wide register and have no high bits leaking into unswapped
positions). -/
theorem mult_target_swap_on_mult_input_F
    (bits multBits x m : Nat)
    (h_multBits_le : multBits ≤ bits + 1)
    (hx : x < 2^multBits) (hm : m < 2^multBits) :
    Gate.applyNat (mult_target_swap bits multBits)
                  (mult_input_F bits multBits x m)
    = mult_input_F bits multBits m x := by
  unfold mult_target_swap
  funext q
  -- Case 1: q = adder_n_qubits + j for some j < multBits (multiplier-side swap).
  by_cases h_mult : ∃ j, j < multBits ∧ q = adder_n_qubits (bits + 1) + j
  · obtain ⟨j, hj, hq_eq⟩ := h_mult
    rw [hq_eq]
    rw [mult_target_swap_aux_at_mult bits multBits _ j hj h_multBits_le]
    -- LHS: mult_input_F bits multBits x m (target_idx j) = adder_input_F (bits+1) 0 x (target_idx j)
    --      = x.testBit j (since (3j+1)%3 = 1, j < bits+1).
    -- RHS: mult_input_F bits multBits m x (adder_n_qubits + j) = Nat.testBit x j.
    have h_target_in_adder : target_idx j < adder_n_qubits (bits + 1) := by
      show 3 * j + 1 < 3 * (bits + 1) + 2
      omega
    have h_lhs_decode :
        mult_input_F bits multBits x m (target_idx j) = Nat.testBit x j := by
      rw [mult_input_F_at_non_mult_pos bits multBits x m (target_idx j)
            (Or.inl h_target_in_adder)]
      -- adder_input_F (bits+1) 0 x (target_idx j) = x.testBit j.
      unfold adder_input_F target_idx
      have h_mod : (3 * j + 1) % 3 = 1 := by omega
      have h_div : (3 * j + 1) / 3 = j := by omega
      rw [h_mod, h_div]
      have h_decide : decide (j < bits + 1) = true := by
        apply decide_eq_true; omega
      rw [h_decide]
      simp
    rw [h_lhs_decode]
    -- RHS via mult_input_F_at_mult_pos.
    rw [mult_input_F_at_mult_pos bits multBits m x j hj]
  -- Case 2: q = target_idx j for some j < multBits (target-side swap).
  · by_cases h_target : ∃ j, j < multBits ∧ q = target_idx j
    · obtain ⟨j, hj, hq_eq⟩ := h_target
      rw [hq_eq]
      rw [mult_target_swap_aux_at_target bits multBits _ j hj h_multBits_le]
      -- LHS: mult_input_F bits multBits x m (adder_n_qubits + j) = Nat.testBit m j.
      -- RHS: mult_input_F bits multBits m x (target_idx j) = m.testBit j.
      rw [mult_input_F_at_mult_pos bits multBits x m j hj]
      -- Now RHS.
      have h_target_in_adder : target_idx j < adder_n_qubits (bits + 1) := by
        show 3 * j + 1 < 3 * (bits + 1) + 2
        omega
      rw [mult_input_F_at_non_mult_pos bits multBits m x (target_idx j)
            (Or.inl h_target_in_adder)]
      unfold adder_input_F target_idx
      have h_mod : (3 * j + 1) % 3 = 1 := by omega
      have h_div : (3 * j + 1) / 3 = j := by omega
      rw [h_mod, h_div]
      have h_decide : decide (j < bits + 1) = true := by
        apply decide_eq_true; omega
      rw [h_decide]
      simp
    -- Case 3: identity case (q not a swap position).
    · push_neg at h_mult h_target
      -- Apply at_other: the gate is identity at q.
      have h_outside : ∀ k, k < multBits →
          q ≠ adder_n_qubits (bits + 1) + k ∧ q ≠ target_idx k := by
        intro k hk
        refine ⟨?_, ?_⟩
        · exact h_mult k hk
        · exact h_target k hk
      rw [mult_target_swap_aux_at_other bits multBits _ q h_multBits_le h_outside]
      -- Now need: mult_input_F bits multBits x m q = mult_input_F bits multBits m x q.
      -- Case-split on q's relation to the multiplier range and adder block.
      by_cases h_in_mult_range : adder_n_qubits (bits + 1) ≤ q
                                ∧ q < adder_n_qubits (bits + 1) + multBits
      · -- q in multiplier range: contradicts h_mult (q = adder_n_qubits + j for some j).
        obtain ⟨h_q_lo, h_q_hi⟩ := h_in_mult_range
        exfalso
        apply h_mult (q - adder_n_qubits (bits + 1)) (by omega)
        omega
      · -- q outside multiplier range.
        have h_outside_range : q < adder_n_qubits (bits + 1)
                               ∨ adder_n_qubits (bits + 1) + multBits ≤ q := by
          by_cases h_lo : q < adder_n_qubits (bits + 1)
          · exact Or.inl h_lo
          · push_neg at h_lo
            exact Or.inr (by
              rcases Nat.lt_or_ge q (adder_n_qubits (bits + 1) + multBits) with h | h
              · exact absurd ⟨h_lo, h⟩ h_in_mult_range
              · exact h)
        rw [mult_input_F_at_non_mult_pos bits multBits x m q h_outside_range]
        rw [mult_input_F_at_non_mult_pos bits multBits m x q h_outside_range]
        -- adder_input_F (bits+1) 0 x q = adder_input_F (bits+1) 0 m q.
        -- Case-split on q's adder-block role (read/target/carry/oob).
        unfold adder_input_F
        rcases Nat.lt_or_ge q (3 * (bits + 1)) with h_in_adder | h_above_adder
        · -- q in adder positions [0, 3*(bits+1)). Case-split on q % 3.
          have h_div_lt : q / 3 < bits + 1 := by omega
          rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 from by omega)
            with h_mod | h_mod | h_mod
          · -- read position: both sides return 0.testBit (q/3) = false.
            rw [h_mod]
          · -- target position: returns x.testBit (q/3) vs m.testBit (q/3).
            have h_q_eq_target : q = target_idx (q / 3) := by
              unfold target_idx
              have : q = 3 * (q / 3) + q % 3 := (Nat.div_add_mod q 3).symm
              omega
            have h_q_div_ge : q / 3 ≥ multBits := by
              by_contra h_lt
              push_neg at h_lt
              apply h_target (q / 3) h_lt
              exact h_q_eq_target
            have h_x_bit : x.testBit (q / 3) = false :=
              Nat.testBit_lt_two_pow (by
                calc x < 2^multBits := hx
                  _ ≤ 2^(q / 3) := Nat.pow_le_pow_right (by omega) h_q_div_ge)
            have h_m_bit : m.testBit (q / 3) = false :=
              Nat.testBit_lt_two_pow (by
                calc m < 2^multBits := hm
                  _ ≤ 2^(q / 3) := Nat.pow_le_pow_right (by omega) h_q_div_ge)
            rw [h_mod]
            simp [h_x_bit, h_m_bit]
          · -- carry position (q % 3 = 2): both sides return false.
            rw [h_mod]
        · -- q ≥ 3*(bits+1): adder_input_F returns false regardless.
          have h_div_ge : q / 3 ≥ bits + 1 := by omega
          have h_decide_false : decide (q / 3 < bits + 1) = false := by
            apply decide_eq_false; omega
          rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 from by omega)
            with h_mod | h_mod | h_mod
          · rw [h_mod, h_decide_false]
          · rw [h_mod, h_decide_false]; simp
          · rw [h_mod]

/-! ### Tick 19 — End-to-end in-place modular multiplier correctness. -/

/-- **HEADLINE: `modMultInPlace` is a correct in-place modular
multiplier.**  Applied to `mult_state_init bits multBits x` (multiplier
register holds `x`, adder zeroed), the gate produces `mult_input_F
bits multBits 0 ((a * x) % N)` — the multiplier register now holds the
result `a*x mod N` and the adder is zeroed.

Hypotheses:
- Structural: `1 ≤ bits`, `multBits ≤ bits + 1`, `N ≤ 2^multBits`.
- Modular: `0 < N`, `N ≤ 2^bits`, `0 < a < N`, `0 < ainv < N`,
  `a * ainv ≡ 1 (mod N)`.
- Input: `x < N`.
- Coprimality of each per-bit constant `(a * 2^j) % N` and
  `((N - ainv) % N * 2^j) % N` is non-zero, used by the
  `modMultConstGate_correct` invocations. -/
theorem modMultInPlace_correct
    (bits N a ainv multBits x : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (h_multBits_le : multBits ≤ bits + 1)
    (h_N_le_pow_multBits : N ≤ 2^multBits)
    (ha_pos : 0 < a) (ha_lt : a < N)
    (hainv_pos : 0 < ainv) (hainv_lt : ainv < N)
    (h_inv : a * ainv % N = 1)
    (hx_lt : x < N)
    (h_const_pos_a : ∀ j, j < multBits → 0 < (a * 2^j) % N)
    (h_const_pos_inv : ∀ j, j < multBits → 0 < ((N - ainv) % N * 2^j) % N) :
    Gate.applyNat (modMultInPlace bits N a ainv multBits)
                  (mult_state_init bits multBits x)
    = mult_input_F bits multBits 0 ((a * x) % N) := by
  -- Derive x < 2^multBits from x < N ≤ 2^multBits.
  have hx_lt_pow : x < 2^multBits :=
    lt_of_lt_of_le hx_lt h_N_le_pow_multBits
  -- Unfold and apply Step 1: modMultConstGate(a) on mult_state_init x.
  unfold modMultInPlace
  rw [Gate.applyNat_seq]
  rw [modMultConstGate_on_init_correct bits N a multBits x
        hbits hN_pos hN hx_lt_pow h_const_pos_a]
  -- State after Step 1: mult_input_F bits multBits (a*x mod N) x.
  rw [Gate.applyNat_seq]
  -- Step 2: SWAP exchanges target and multiplier.  Need both values
  -- < 2^multBits.
  have h_ax_mod_N_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have h_ax_mod_N_lt_pow : (a * x) % N < 2^multBits :=
    lt_of_lt_of_le h_ax_mod_N_lt_N h_N_le_pow_multBits
  rw [mult_target_swap_on_mult_input_F bits multBits ((a * x) % N) x
        h_multBits_le h_ax_mod_N_lt_pow hx_lt_pow]
  -- State after Step 2: mult_input_F bits multBits x (a*x mod N).
  -- Step 3: modMultConstGate((N - ainv) % N).
  rw [modMultConstGate_correct bits N ((N - ainv) % N) multBits x ((a * x) % N)
        hbits hN_pos hN hx_lt h_ax_mod_N_lt_pow h_const_pos_inv]
  -- Result: mult_input_F ((x + ((N - ainv) % N) * ((a*x) % N)) % N) ((a*x) % N).
  -- We need this to equal mult_input_F 0 ((a*x) % N).
  congr 1
  -- (N - ainv) % N = N - ainv (since 0 < N - ainv < N).
  rw [show (N - ainv) % N = N - ainv from Nat.mod_eq_of_lt (by omega)]
  -- Apply mod_inv_cancel_identity.
  exact mod_inv_cancel_identity a ainv N x hN_pos hx_lt hainv_lt h_inv

/-! ### Tick 20 — Reverse-pairing register SWAP (layout-conversion primitive).

The layout conversion from `encodeDataZeroAnc n anc x` (data at LOW
positions 0..n-1, BIG-endian) to `mult_state_init bits multBits x`
(data at HIGH positions adder_n_qubits..+multBits-1, LITTLE-endian)
is a REVERSED pairing: position `i ∈ [0, n)` swaps with position
`adder_n_qubits + (n - 1 - i) ∈ [adder_n_qubits, adder_n_qubits + n)`.

This tick defines `reverse_register_swap` and proves its position-level
correctness.  The next tick composes it with `modMultInPlace` to obtain
a layout-converting in-place modular multiplier acting on
`encodeDataZeroAnc`. -/

/-- Auxiliary recursive reverse-pairing register SWAP at iteration
count `k`: at step k, swaps `(offsetA + k, offsetB + (n - 1 - k))`. -/
def reverse_register_swap_aux (n offsetA offsetB : Nat) : Nat → Gate
  | 0 => Gate.I
  | k+1 => Gate.seq (reverse_register_swap_aux n offsetA offsetB k)
                    (qubit_swap (offsetA + k) (offsetB + (n - 1 - k)))

/-- Reverse-pairing register SWAP: exchanges positions
`[offsetA, offsetA + n)` and `[offsetB, offsetB + n)` with index
reversal (position `offsetA + i` swaps with `offsetB + (n - 1 - i)`). -/
def reverse_register_swap (n offsetA offsetB : Nat) : Gate :=
  reverse_register_swap_aux n offsetA offsetB n

/-- Recursion unfolding for `reverse_register_swap_aux`. -/
theorem reverse_register_swap_aux_succ
    (n offsetA offsetB k : Nat) :
    reverse_register_swap_aux n offsetA offsetB (k + 1)
    = Gate.seq (reverse_register_swap_aux n offsetA offsetB k)
               (qubit_swap (offsetA + k) (offsetB + (n - 1 - k))) := rfl

/-- **WellTyped for `reverse_register_swap_aux`.**  Disjoint ranges
suffice. -/
theorem reverse_register_swap_aux_wellTyped
    (dim n offsetA offsetB k : Nat) (hdim : 0 < dim)
    (hA : offsetA + n ≤ dim) (hB : offsetB + n ≤ dim)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA)
    (hk : k ≤ n) :
    Gate.WellTyped dim (reverse_register_swap_aux n offsetA offsetB k) := by
  induction k with
  | zero =>
      show 0 < dim
      exact hdim
  | succ k ih =>
      have hk' : k ≤ n := by omega
      have h_ih := ih hk'
      have h_swap : Gate.WellTyped dim
          (qubit_swap (offsetA + k) (offsetB + (n - 1 - k))) := by
        apply qubit_swap_wellTyped
        · -- offsetA + k < dim
          omega
        · -- offsetB + (n - 1 - k) < dim
          have : n - 1 - k < n := by omega
          omega
        · -- offsetA + k ≠ offsetB + (n - 1 - k)
          rcases h_disjoint with h | h
          · -- offsetA + n ≤ offsetB: offsetA + k < offsetB ≤ offsetB + (n-1-k).
            have : offsetA + k < offsetB := by omega
            omega
          · -- offsetB + n ≤ offsetA: offsetB + (n-1-k) < offsetA ≤ offsetA + k.
            have : offsetB + (n - 1 - k) < offsetA := by omega
            omega
      show Gate.WellTyped dim
        (Gate.seq (reverse_register_swap_aux n offsetA offsetB k) _)
      exact ⟨h_ih, h_swap⟩

/-- **WellTyped for `reverse_register_swap`.** -/
theorem reverse_register_swap_wellTyped
    (dim n offsetA offsetB : Nat) (hdim : 0 < dim)
    (hA : offsetA + n ≤ dim) (hB : offsetB + n ≤ dim)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA) :
    Gate.WellTyped dim (reverse_register_swap n offsetA offsetB) :=
  reverse_register_swap_aux_wellTyped dim n offsetA offsetB n hdim hA hB
    h_disjoint (le_refl _)

/-- **Correctness at "other" positions** of `reverse_register_swap_aux`.
At positions outside both `[offsetA, offsetA + k)` and `[offsetB +
n - k, offsetB + n)` (the touched range up to iteration `k`), the gate
is identity. -/
theorem reverse_register_swap_aux_at_other
    (n offsetA offsetB k : Nat) (f : Nat → Bool) (q : Nat)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA)
    (hk : k ≤ n)
    (h_outside : ∀ i, i < k →
      q ≠ offsetA + i ∧ q ≠ offsetB + (n - 1 - i)) :
    Gate.applyNat (reverse_register_swap_aux n offsetA offsetB k) f q = f q := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk' : k ≤ n := by omega
      have h_outside_k : ∀ i, i < k →
          q ≠ offsetA + i ∧ q ≠ offsetB + (n - 1 - i) := by
        intro i hi; exact h_outside i (by omega)
      have h_q_ne_Ak : q ≠ offsetA + k := (h_outside k (by omega)).1
      have h_q_ne_Bk : q ≠ offsetB + (n - 1 - k) := (h_outside k (by omega)).2
      have hAk_ne_Bk : offsetA + k ≠ offsetB + (n - 1 - k) := by
        rcases h_disjoint with h | h
        · -- offsetA + n ≤ offsetB
          have hk_lt : k < n := by omega
          omega
        · -- offsetB + n ≤ offsetA
          have hk_lt : k < n := by omega
          omega
      rw [reverse_register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      rw [update_neq _ _ _ _ h_q_ne_Bk]
      rw [update_neq _ _ _ _ h_q_ne_Ak]
      exact ih hk' h_outside_k

/-- **At A-side position**: at `offsetA + j` (j < k), the gate returns
`f (offsetB + (n - 1 - j))`.  The reversed-pairing semantics. -/
theorem reverse_register_swap_aux_at_A
    (n offsetA offsetB k : Nat) (f : Nat → Bool) (j : Nat) (hj : j < k)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA)
    (hk : k ≤ n) :
    Gate.applyNat (reverse_register_swap_aux n offsetA offsetB k) f
      (offsetA + j)
    = f (offsetB + (n - 1 - j)) := by
  induction k with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have hk_n : k ≤ n := by omega
      have hk_lt : k < n := by omega
      have hAk_ne_Bk : offsetA + k ≠ offsetB + (n - 1 - k) := by
        rcases h_disjoint with h | h
        · omega
        · omega
      rw [reverse_register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_neq _ _ _ _ hAk_ne_Bk]
        rw [update_eq]
        apply reverse_register_swap_aux_at_other n offsetA offsetB k f
                (offsetB + (n - 1 - k)) h_disjoint hk_n
        intro i hi
        have hi_lt_n : i < n := by omega
        refine ⟨?_, ?_⟩
        · rcases h_disjoint with h | h
          · omega
          · omega
        · -- offsetB + (n - 1 - k) ≠ offsetB + (n - 1 - i), since i < k.
          have h_ne_idx : n - 1 - k ≠ n - 1 - i := by omega
          omega
      · have hj' : j < k := by omega
        have h_pos_Aj_ne_Bk : offsetA + j ≠ offsetB + (n - 1 - k) := by
          rcases h_disjoint with h | h
          · omega
          · omega
        have h_pos_Aj_ne_Ak : offsetA + j ≠ offsetA + k := by omega
        rw [update_neq _ _ _ _ h_pos_Aj_ne_Bk]
        rw [update_neq _ _ _ _ h_pos_Aj_ne_Ak]
        exact ih hj' hk_n

/-- **At B-side position (reversed)**: at `offsetB + (n - 1 - j)`
(j < k), the gate returns `f (offsetA + j)`.  The dual of `_at_A`. -/
theorem reverse_register_swap_aux_at_B
    (n offsetA offsetB k : Nat) (f : Nat → Bool) (j : Nat) (hj : j < k)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA)
    (hk : k ≤ n) :
    Gate.applyNat (reverse_register_swap_aux n offsetA offsetB k) f
      (offsetB + (n - 1 - j))
    = f (offsetA + j) := by
  induction k with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have hk_n : k ≤ n := by omega
      have hk_lt : k < n := by omega
      have hAk_ne_Bk : offsetA + k ≠ offsetB + (n - 1 - k) := by
        rcases h_disjoint with h | h
        · omega
        · omega
      rw [reverse_register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_eq]
        apply reverse_register_swap_aux_at_other n offsetA offsetB k f
                (offsetA + k) h_disjoint hk_n
        intro i hi
        have hi_lt_n : i < n := by omega
        refine ⟨?_, ?_⟩
        · omega
        · rcases h_disjoint with h | h
          · omega
          · omega
      · have hj' : j < k := by omega
        have h_pos_B_ne_Bk : offsetB + (n - 1 - j)
                            ≠ offsetB + (n - 1 - k) := by
          have h_ne_idx : n - 1 - j ≠ n - 1 - k := by omega
          omega
        have h_pos_B_ne_Ak : offsetB + (n - 1 - j) ≠ offsetA + k := by
          rcases h_disjoint with h | h
          · omega
          · omega
        rw [update_neq _ _ _ _ h_pos_B_ne_Bk]
        rw [update_neq _ _ _ _ h_pos_B_ne_Ak]
        exact ih hj' hk_n

end FormalRV.BQAlgo
