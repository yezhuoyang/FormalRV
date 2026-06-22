/-
  FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderSpec
  ─────────────────────────────────────────────────────────
  The CLASSICAL specification of the Gidney adder — what "correct" means and how
  inputs/outputs are encoded. **Definitions only — no proofs, no circuits.**

    • `Adder.carry` / `Adder.sumfb` — the bit-level carry/sum recurrence
      (port of SQIR `ModMult.v`).
    • `adder_sum_bit_classical a b i = (a+b).testBit i` — the expected output bit.
    • `adder_input_F n a b` — the standard `|a⟩|b⟩|0⟩` input on the interleaved layout.
    • `gidney_read_val` / `gidney_target_val` / `gidney_carry_val` — LSB-first
      register decoders.

  The circuit itself is in `RippleCarryAdderDef.lean`; the correctness theorems
  that relate the two are in `RippleCarryAdderCorrectness.lean`.
-/
import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Framework.PaperClaims
import FormalRV.PPM.Magic.GidneyAND
import Mathlib.Tactic.IntervalCases
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderDef

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-! ## Bit-level carry / sum recurrence (SQIR `ModMult.v` port) -/

/-- **Classical carry function** (SQIR `ModMult.v` port). Given a carry-in
`b₀ : Bool` and two bit-streams `f g`, `Adder.carry b₀ n f g` is the carry-out
after processing bits `0..n-1` of `f + g`. -/
def Adder.carry (b₀ : Bool) : Nat → (Nat → Bool) → (Nat → Bool) → Bool
  | 0,     _, _ => b₀
  | n + 1, f, g =>
      let c := Adder.carry b₀ n f g
      let a := f n
      let b := g n
      xor (xor (a && b) (b && c)) (a && c)

/-- **Classical sum-bit function** (SQIR `ModMult.v` port).
`Adder.sumfb b₀ f g i = carry b₀ i f g ⊕ f i ⊕ g i` — bit `i` of `f + g` with
carry-in `b₀`. -/
def Adder.sumfb (b₀ : Bool) (f g : Nat → Bool) (i : Nat) : Bool :=
  xor (xor (Adder.carry b₀ i f g) (f i)) (g i)

/-- **Classical specification**: bit `i` of `(a + b) mod 2^n`, the value the
i-th target qubit should hold after the full adder. -/
def adder_sum_bit_classical (a b i : Nat) : Bool := (a + b).testBit i

/-! ## Standard input encoding -/

/-- **Generic input encoding** `|a⟩|b⟩|0⟩_carries` on the interleaved layout:
`read[i]` ↦ bit `i` of `a` (if `i < n`), `target[i]` ↦ bit `i` of `b`,
`carry[i]` ↦ `false`. -/
def adder_input_F (n a b : Nat) (k : Nat) : Bool :=
  match k % 3 with
  | 0 => decide (k / 3 < n) && a.testBit (k / 3)
  | 1 => decide (k / 3 < n) && b.testBit (k / 3)
  | _ => false

/-! ## Register decoders (LSB-first)

`read[i] = 3*i`, `target[i] = 3*i+1`, `carry[i] = 3*i+2` each contribute weight
`2^i`. NOTE: this is LSB-first, unlike the big-endian `Framework.funbool_to_nat`. -/

/-- Decoder: value of the `read` register at width `n`, LSB-first. -/
def gidney_read_val : Nat → (Nat → Bool) → Nat
  | 0,     _ => 0
  | n + 1, f =>
      gidney_read_val n f + (if f (read_idx n) then 2^n else 0)

/-- Decoder: value of the `target` register at width `n`, LSB-first. -/
def gidney_target_val : Nat → (Nat → Bool) → Nat
  | 0,     _ => 0
  | n + 1, f =>
      gidney_target_val n f + (if f (target_idx n) then 2^n else 0)

/-- Decoder: value of the `carry` register at width `n`, LSB-first. -/
def gidney_carry_val : Nat → (Nat → Bool) → Nat
  | 0,     _ => 0
  | n + 1, f =>
      gidney_carry_val n f + (if f (carry_idx n) then 2^n else 0)

/-! ## Concrete decide-test fixtures

Concrete classical inputs used by the small-`n` `decide` smoke checks in the
supporting proof files (`adder_input_F` specialized to fixed `(n, a, b)`). -/

/-- The all-zero input function. -/
abbrev zeroF : Nat → Bool := fun _ => false

/-- Input for `read = (1,0), target = (0,0)` (the `1 + 0` 2-bit case). -/
def inputF_1_plus_0 : Nat → Bool := fun i => i == 0

/-- Input for `(a=1, b=1)` 2-bit addition. -/
def inputF_1_plus_1 : Nat → Bool
  | 0 => true   -- read_0 = a_0 = 1
  | 1 => true   -- target_0 = b_0 = 1
  | _ => false

/-- Input for `(a=3, b=1)` 3-bit addition. -/
def inputF_3_plus_1 : Nat → Bool
  | 0 => true   -- read_0 = a_0 = 1
  | 1 => true   -- target_0 = b_0 = 1
  | 3 => true   -- read_1 = a_1 = 1
  | _ => false

/-- Input for `(a=7, b=1)` 4-bit addition. -/
def inputF_7_plus_1 : Nat → Bool
  | 0 => true   -- read_0 = a_0 = 1
  | 1 => true   -- target_0 = b_0 = 1
  | 3 => true   -- read_1 = a_1 = 1
  | 6 => true   -- read_2 = a_2 = 1
  | _ => false

/-- Concrete `1 + 1` input (LSB-first): `read = 1, target = 1` at width 2. -/
def inputF_1_plus_1_tickD : Nat → Bool
  | 0 => true   -- read[0] = 1 (LSB)
  | 1 => true   -- target[0] = 1 (LSB)
  | _ => false

end FormalRV.BQAlgo
