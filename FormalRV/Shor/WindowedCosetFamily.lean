/-
  FormalRV.Shor.WindowedCosetFamily — the CONCRETE, faithful coset oracle family
  for QPE, built on the VERIFIED in-place windowed multiplier.
  ════════════════════════════════════════════════════════════════════════════

  This is the real GE2021 coset multiplier as a concrete `Gate` family — NObody's
  free variable.  Per QPE iterate `i`, `cosetMulGate` multiplies the y-register
  IN PLACE by an ODD LIFT `c_i` of the residue `a^(2^i) mod N`:

    • ODD ⇒ `c_i` is invertible mod `2^bits` ⇒ `windowedMulInPlace` returns the
      accumulator/ancilla CLEAN (`windowedMulInPlace_correct`, already verified):
      the in-place uncompute `pass(c) ; swap ; pass(2^bits − c⁻¹)` clears exactly
      because `c·c⁻¹ ≡ 1 (mod 2^bits)`.
    • `c_i ≡ a^(2^i) (mod N)` ⇒ the y-register value `(c_i·v) mod 2^bits` is a
      COSET REPRESENTATIVE of `(a^(2^i)·v) mod N` whenever no wrap occurs
      (`c_i·v < 2^bits`) — the residue is read off mod `N`.

  Each iterate is a DIFFERENT gate (a different constant `c_i`), exactly the
  `ModMulImpl`-style "multiply by `a^(2^i)`" family QPE consumes; we do NOT need a
  power-of-one-unitary (a single U would have period `ord(c mod 2^bits)`, a power
  of 2 — useless for Shor; the residue structure lives in the eigenstates, built
  separately).

  WHAT THIS FILE PROVES (kernel-clean, on the real construction):
    • `oddLift` is odd (for odd `N`) and `≡` its argument mod `N`.
    • `cosetMulGate` is the literal `windowedMulInPlace` at the odd-lift constant.
    • `cosetMulGate_value`: the gate maps a `MulReady` state with y-value `v` to
      the `MulReady` state with y-value `(c_i·v) mod 2^bits` — accumulator and
      ancillas CLEAN (full in-place restoration).  Reuses the verified
      `windowedMulInPlace_correct`.
    • `cosetMulGate_residue`: off wrap (`c_i·v < 2^bits`) that value reduces mod
      `N` to `(a^(2^i)·v) mod N` — the coset-rep correctness on the real gate.

  The uniform-superposition coset eigenstate and the QPE/deviation discharge are
  built on top of this concrete family elsewhere.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Windowed.WindowedInPlace

namespace FormalRV.Shor.WindowedCosetFamily

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit

/-! ## §1. The odd lift of a residue (for odd modulus `N`). -/

/-- The ODD LIFT of `c` modulo `N`: `c` itself if odd, else `c + N`.  For ODD
    `N` this is always odd and congruent to `c` mod `N`, with value `< c + N`. -/
def oddLift (c N : Nat) : Nat := if c % 2 = 1 then c else c + N

/-- The odd lift is odd, provided `N` is odd. -/
theorem oddLift_odd (c N : Nat) (hN : N % 2 = 1) : oddLift c N % 2 = 1 := by
  unfold oddLift
  by_cases h : c % 2 = 1
  · rw [if_pos h]; exact h
  · rw [if_neg h]
    have hc0 : c % 2 = 0 := by omega
    omega

/-- The odd lift is congruent to `c` modulo `N`. -/
theorem oddLift_mod (c N : Nat) : oddLift c N % N = c % N := by
  unfold oddLift
  by_cases h : c % 2 = 1
  · rw [if_pos h]
  · rw [if_neg h, Nat.add_mod_right]

/-! ## §2. The concrete per-iterate coset multiplier gate. -/

/-- **The concrete coset multiplier gate** for QPE iterate `i`: the verified
    in-place windowed multiplier `windowedMulInPlace` at the ODD-LIFT constant
    `c_i = oddLift (a^(2^i) % N) N` (with inverse `cinv_i` mod `2^bits`).  This is
    the literal resource-saving coset gate — non-reducing windowed arithmetic. -/
def cosetMulGate (w bits N numWin a : Nat) (cinv : Nat) (i : Nat) : Gate :=
  windowedMulInPlace cuccaroAdder w bits
    (oddLift (a ^ (2 ^ i) % N) N) cinv numWin

/-! ## §3. Per-iterate value correctness — reuses `windowedMulInPlace_correct`. -/

/-- **`cosetMulGate_value` — full in-place restoration on the real gate.**  For
    `c_i = oddLift (a^(2^i) % N) N` invertible mod `2^bits` (inverse `cinv`), the
    concrete coset gate maps a `MulReady` state with y-value `v < 2^bits` to the
    `MulReady` state with y-value `(c_i·v) mod 2^bits` — accumulator, addend
    register and ancillas all CLEAN.  Directly the verified
    `windowedMulInPlace_correct`. -/
theorem cosetMulGate_value (w bits N numWin a cinv i v : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hv : v < 2 ^ bits)
    (hcinv : cinv < 2 ^ bits)
    (hinv : oddLift (a ^ (2 ^ i) % N) N * cinv % 2 ^ bits = 1)
    (f : Nat → Bool)
    (hf : MulReady cuccaroAdder w bits numWin v f) :
    MulReady cuccaroAdder w bits numWin
      (oddLift (a ^ (2 ^ i) % N) N * v % 2 ^ bits)
      (Gate.applyNat (cosetMulGate w bits N numWin a cinv i) f) := by
  unfold cosetMulGate
  exact windowedMulInPlace_correct cuccaroAdder w bits
    (oddLift (a ^ (2 ^ i) % N) N) cinv numWin v hw hbits hv hcinv hinv
    (fun i j hi hj h => cuccaroAdder_augendIdx_inj (1 + 2 * w) i j h) f hf

/-! ## §4. The residue read-off — off wrap, the value is `(a^(2^i)·v) mod N`. -/

/-- **`cosetMulGate_residue` — coset-rep correctness on the real gate.**  Off wrap
    (`c_i·v < 2^bits`), the y-register value `(c_i·v) mod 2^bits` reduces mod `N`
    to `(a^(2^i)·v) mod N`: the concrete coset gate computes the correct residue.
    Proof: no wrap makes `mod 2^bits` the identity, then `c_i ≡ a^(2^i) (mod N)`
    (`oddLift_mod`) propagates through the product. -/
theorem cosetMulGate_residue (bits N a i v : Nat)
    (hnowrap : oddLift (a ^ (2 ^ i) % N) N * v < 2 ^ bits) :
    (oddLift (a ^ (2 ^ i) % N) N * v % 2 ^ bits) % N
      = (a ^ (2 ^ i) * v) % N := by
  rw [Nat.mod_eq_of_lt hnowrap]
  calc (oddLift (a ^ (2 ^ i) % N) N * v) % N
      = ((oddLift (a ^ (2 ^ i) % N) N % N) * (v % N)) % N := by rw [Nat.mul_mod]
    _ = ((a ^ (2 ^ i) % N % N) * (v % N)) % N := by rw [oddLift_mod]
    _ = ((a ^ (2 ^ i) % N) * (v % N)) % N := by rw [Nat.mod_mod]
    _ = (a ^ (2 ^ i) * v) % N := by rw [← Nat.mul_mod]

end FormalRV.Shor.WindowedCosetFamily
