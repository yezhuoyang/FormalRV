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
import FormalRV.Shor.WindowedModNShor

namespace FormalRV.Shor.WindowedCosetFamily

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open FormalRV.BQAlgo.WindowedModNShor
  (wellTyped_foldl_seq_range lookupReadAt_wellTyped copyWindow_wellTyped
   accYSwap_cuccaro_wellTyped)

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

/-! ## §5. Well-typedness of the concrete coset gate (the QPE-oracle dimension).

The coset gate touches qubits in `[0, D)` with `D = cosetDim w bits = 2+2w+3·bits`
(ctrl `0`; lookup zone `1..2w`; Cuccaro block `1+2w .. 1+2w+2·bits`; y-register
`2+2w+2·bits .. 2+2w+3·bits−1`).  We compose the (now public) generic
well-typedness lemmas — `lookupReadAt_wellTyped`, `copyWindow_wellTyped`,
`cuccaro_n_bit_adder_full_wellTyped`, `accYSwap_cuccaro_wellTyped`,
`wellTyped_foldl_seq_range` — exactly mirroring the canonical
`windowedModNMulCircuit_wellTyped`, minus the mod-N reduce flag. -/

/-- The QPE-oracle dimension of the coset multiplier: `2 + 2w + 3·bits`. -/
def cosetDim (w bits : Nat) : Nat := 2 + 2 * w + 3 * bits

/-- One window step of the plain windowed multiplier is well-typed at `D`. -/
theorem windowStepOf_cuccaro_wellTyped (w bits a numWin j dim : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin)
    (hdim : 2 + 2 * w + 3 * bits ≤ dim) :
    Gate.WellTyped dim
      (windowStepOf cuccaroAdder w bits a bits (1 + 2 * w)
        (1 + 2 * w + cuccaroAdder.span bits) j) := by
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  have hjwi : ∀ i, i < w → j * w + i < bits := by
    intro i hi
    calc j * w + i < j * w + w := by omega
      _ = (j + 1) * w := by ring
      _ ≤ numWin * w := Nat.mul_le_mul_right w hj
      _ = bits := hbits
  have hcw : Gate.WellTyped dim
      (copyWindow w (1 + 2 * w + cuccaroAdder.span bits) j) := by
    rw [hspan]
    refine copyWindow_wellTyped w (1 + 2 * w + (2 * bits + 1)) j dim (by omega)
      (fun i hi => ?_) (fun i hi => by omega)
    have := hjwi i hi; omega
  have haddr_idx : ∀ k, cuccaroAdder.addendIdx (1 + 2 * w) k = 1 + 2 * w + 2 * k + 2 :=
    fun _ => rfl
  have hlook : Gate.WellTyped dim
      (lookupReadAt w (cuccaroAdder.addendIdx (1 + 2 * w)) bits
        (fun v => a * (2 ^ w) ^ j * v)) := by
    refine lookupReadAt_wellTyped w bits (cuccaroAdder.addendIdx (1 + 2 * w)) _ dim hw
      (by omega) (fun k hk => ?_)
    rw [haddr_idx k]
    exact ⟨by omega, by unfold ulookup_and_idx; omega⟩
  unfold windowStepOf lookupAddAtOf
  exact ⟨⟨hcw, ⟨⟨hlook,
    cuccaro_n_bit_adder_full_wellTyped bits (1 + 2 * w) dim (by omega)⟩, hlook⟩⟩, hcw⟩

/-- The plain windowed multiplier circuit is well-typed at `D`. -/
theorem windowedMulCircuitOf_cuccaro_wellTyped (w bits a numWin dim : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hdim : 2 + 2 * w + 3 * bits ≤ dim) :
    Gate.WellTyped dim (windowedMulCircuitOf cuccaroAdder w bits a numWin) := by
  unfold windowedMulCircuitOf windowedMulOf
  refine wellTyped_foldl_seq_range _ numWin dim (by omega) (fun j hj => ?_)
  exact windowStepOf_cuccaro_wellTyped w bits a numWin j dim hw hbits hj hdim

/-- The in-place windowed multiplier is well-typed at `D`. -/
theorem windowedMulInPlace_cuccaro_wellTyped (w bits a ainv numWin dim : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hdim : 2 + 2 * w + 3 * bits ≤ dim) :
    Gate.WellTyped dim (windowedMulInPlace cuccaroAdder w bits a ainv numWin) := by
  unfold windowedMulInPlace
  refine ⟨⟨windowedMulCircuitOf_cuccaro_wellTyped w bits a numWin dim hw hbits hdim, ?_⟩,
    windowedMulCircuitOf_cuccaro_wellTyped w bits (2 ^ bits - ainv) numWin dim hw hbits hdim⟩
  exact accYSwap_cuccaro_wellTyped w bits dim (by omega)

/-- **The concrete coset gate is well-typed** at `D = cosetDim w bits`. -/
theorem cosetMulGate_wellTyped (w bits N numWin a cinv i dim : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hdim : 2 + 2 * w + 3 * bits ≤ dim) :
    Gate.WellTyped dim (cosetMulGate w bits N numWin a cinv i) := by
  unfold cosetMulGate
  exact windowedMulInPlace_cuccaro_wellTyped w bits _ cinv numWin dim hw hbits hdim

/-! ## §6. The genuine `BaseUCom` QPE-oracle family. -/

/-- **The concrete coset oracle family** for QPE: each iterate compiled to a
    `BaseUCom (cosetDim w bits)` via `Gate.toUCom`.  `cinv i` is the `2^bits`-
    inverse of the iterate-`i` odd-lift constant. -/
noncomputable def cosetMulFamily (w bits N numWin a : Nat) (cinv : Nat → Nat) :
    Nat → BaseUCom (cosetDim w bits) :=
  fun i => Gate.toUCom (cosetDim w bits) (cosetMulGate w bits N numWin a (cinv i) i)

/-- **The coset oracle family is a genuine well-typed `BaseUCom` family** — every
    iterate is `uc_well_typed` (`= UCom.WellTyped (cosetDim w bits)`), the exact
    hypothesis QPE/`qpe_var_lsb_on_eigenfamily_initial` consume. -/
theorem cosetMulFamily_uc_well_typed (w bits N numWin a : Nat) (cinv : Nat → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) :
    ∀ i, FormalRV.SQIRPort.uc_well_typed (cosetMulFamily w bits N numWin a cinv i) := by
  intro i
  unfold cosetMulFamily
  exact uc_well_typed_toUCom_of_Gate_WellTyped (cosetDim w bits)
    (cosetMulGate w bits N numWin a (cinv i) i)
    (cosetMulGate_wellTyped w bits N numWin a (cinv i) i (cosetDim w bits) hw hbits
      (by unfold cosetDim; omega))

/-! ## §7. The matrix-level (`uc_eval`) action — the bridge into QPE.

`uc_eval_toUCom_acts_on_basis` lifts the gate's Boolean `applyNat` action to the
`uc_eval` matrix acting on basis vectors.  Combined with the verified value
(`windowedMulInPlace_value_cuccaro`) and residue (`cosetMulGate_residue`) facts,
this is precisely the per-iterate basis-permutation the uniform-superposition
coset eigenstate argument consumes: on the clean encoded input the QPE oracle
sends the y-register value `v` to `(c_i·v) mod 2^bits`, a coset rep of
`(a^(2^i)·v) mod N` off wrap. -/

/-- **Matrix action on the clean encoded input.**  The QPE oracle `uc_eval` acts
    on the encoded basis state exactly as the gate's `applyNat` (the Gate→matrix
    bridge `uc_eval_toUCom_acts_on_basis` at the verified well-typedness). -/
theorem cosetMulFamily_acts_on_mulInput (w bits N numWin a : Nat) (cinv : Nat → Nat)
    (i v : Nat) (hw : 0 < w) (hbits : numWin * w = bits) :
    uc_eval (cosetMulFamily w bits N numWin a cinv i)
        * f_to_vec (cosetDim w bits) (mulInputOf cuccaroAdder w bits numWin v)
      = f_to_vec (cosetDim w bits)
          (Gate.applyNat (cosetMulGate w bits N numWin a (cinv i) i)
            (mulInputOf cuccaroAdder w bits numWin v)) := by
  unfold cosetMulFamily
  exact uc_eval_toUCom_acts_on_basis (cosetDim w bits)
    (cosetMulGate w bits N numWin a (cinv i) i)
    (cosetMulGate_wellTyped w bits N numWin a (cinv i) i (cosetDim w bits) hw hbits
      (by unfold cosetDim; omega))
    (mulInputOf cuccaroAdder w bits numWin v)

/-- **The output y-register value** of the concrete coset gate on the clean
    encoded input is `(c_i·v) mod 2^bits` — the decode form of the verified
    in-place multiply (`windowedMulInPlace_value_cuccaro`). -/
theorem cosetMulGate_yvalue (w bits N numWin a cinv i v : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hv : v < 2 ^ bits)
    (hcinv : cinv < 2 ^ bits)
    (hinv : oddLift (a ^ (2 ^ i) % N) N * cinv % 2 ^ bits = 1) :
    decodeReg (fun k => 1 + 2 * w + cuccaroAdder.span bits + k) bits
        (Gate.applyNat (cosetMulGate w bits N numWin a cinv i)
          (mulInputOf cuccaroAdder w bits numWin v))
      = oddLift (a ^ (2 ^ i) % N) N * v % 2 ^ bits := by
  unfold cosetMulGate
  exact windowedMulInPlace_value_cuccaro w bits (oddLift (a ^ (2 ^ i) % N) N) cinv
    numWin v hw hbits hv hcinv hinv

/-- **The output y-register residue** — off wrap, the coset gate's output value
    reads off mod `N` as `(a^(2^i)·v) mod N` AT THE MATRIX LEVEL: the y-register
    of the post-`uc_eval` state decodes to a coset rep of the correct residue.
    Composes `cosetMulGate_yvalue` (the matrix-level value) with
    `cosetMulGate_residue` (the off-wrap residue). -/
theorem cosetMulGate_yvalue_residue (w bits N numWin a cinv i v : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hv : v < 2 ^ bits)
    (hcinv : cinv < 2 ^ bits)
    (hinv : oddLift (a ^ (2 ^ i) % N) N * cinv % 2 ^ bits = 1)
    (hnowrap : oddLift (a ^ (2 ^ i) % N) N * v < 2 ^ bits) :
    (decodeReg (fun k => 1 + 2 * w + cuccaroAdder.span bits + k) bits
        (Gate.applyNat (cosetMulGate w bits N numWin a cinv i)
          (mulInputOf cuccaroAdder w bits numWin v))) % N
      = (a ^ (2 ^ i) * v) % N := by
  rw [cosetMulGate_yvalue w bits N numWin a cinv i v hw hbits hv hcinv hinv]
  exact cosetMulGate_residue bits N a i v hnowrap

end FormalRV.Shor.WindowedCosetFamily
