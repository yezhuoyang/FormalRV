/-
  FormalRV.Shor.CosetEigenstate.CosetLayout — the explicit two-register layout for the
  out-of-place coset multiplier, with disjointness and frame lemmas in decoded values.
  ════════════════════════════════════════════════════════════════════════════

  The out-of-place coset multiplier reads an INPUT register (holding `x`) and writes a
  SCRATCH/target register (the coset accumulator), with an internal ancilla block.
  This file fixes the register split EXPLICITLY by index functions and proves the
  disjointness + frame facts, stated in terms of the decoded Nat values
  (`decodeReg`):

    * `inputIdx ibase i = ibase + i`     — input register `[ibase, ibase+bits)`,
    * `scratchIdx sbase i = sbase + i`    — scratch register `[sbase, sbase+sbits)`,
    * disjoint when `ibase + bits ≤ sbase`.

  `input_decode_frame` is the key fact: a multiplier circuit that only touches the
  scratch block (frame) leaves the INPUT register's decoded value unchanged — the
  precondition for the per-input-branch decomposition the deviation discharge uses.
  It reuses the existing register congruence `BQAlgo.decodeReg_ext`.

  These connect the Boolean (`applyNat`/`decodeReg`) layer to the deviation discharge
  `CosetTableSum.cosetOutOfPlace_hfwd`: a concrete coset `mulFwd` would establish its
  scratch-decodes-to-the-windowed-fold contract on THIS layout (input framed, ancilla
  restored), and the decoded input value drives the per-branch window constants.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Adder

namespace FormalRV.Shor.CosetEigenstate.CosetLayout

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-- The input register: bit `i` sits at qubit `ibase + i` (LSB-first). -/
def inputIdx (ibase : Nat) : Nat → Nat := fun i => ibase + i

/-- The scratch / target register: bit `i` sits at qubit `sbase + i` (LSB-first). -/
def scratchIdx (sbase : Nat) : Nat → Nat := fun i => sbase + i

/-- **Disjointness.**  When the input block ends at or before the scratch block
    starts (`ibase + bits ≤ sbase`), every input qubit lies strictly below the
    scratch block — so the two registers (and the ancilla above) never collide. -/
theorem inputIdx_lt_scratch (ibase bits sbase : Nat) (hdis : ibase + bits ≤ sbase)
    {i : Nat} (hi : i < bits) : inputIdx ibase i < sbase := by
  simp only [inputIdx]; omega

/-- **Frame (decoded form).**  A circuit `g` that fixes every qubit below the scratch
    block leaves the INPUT register's decoded value unchanged.  (`decodeReg_ext` on the
    input positions, which are all `< sbase` by disjointness.)  This is what lets the
    forward multiplier be analyzed per fixed input value — the input is a preserved
    classical control while the scratch runs the coset fold. -/
theorem input_decode_frame (g : Gate) (ibase bits sbase : Nat) (f : Nat → Bool)
    (hdis : ibase + bits ≤ sbase)
    (hframe : ∀ p, p < sbase → Gate.applyNat g f p = f p) :
    decodeReg (inputIdx ibase) bits (Gate.applyNat g f)
      = decodeReg (inputIdx ibase) bits f :=
  decodeReg_ext (inputIdx ibase) bits (Gate.applyNat g f) f
    (fun i hi => hframe (inputIdx ibase i) (inputIdx_lt_scratch ibase bits sbase hdis hi))

/-- **The decoded-value contract of an out-of-place coset multiplier** (the Boolean
    obligation a concrete `mulFwd` must meet on this layout).  On any basis function
    `f` with the ancilla clean, the circuit:
      (1) decodes the SCRATCH register to the windowed coset value `wval (input)`
          (the running coset accumulator after the windowed lookup-adds),
      (2) leaves the INPUT register's decoded value unchanged (frame, via
          `input_decode_frame`),
      (3) restores the ancilla block (so legs compose).
    `wval` is instantiated by the windowed fold whose value is `(a·x) mod N`
    (`CosetTableSum.idealAcc_cosetWindowConst`).  This structure is the explicit
    statement of the remaining concrete-circuit obligation; a NON-MODULAR (runway)
    coset multiplier discharges it (the existing modular `windowedMulCircuitOf` is the
    exact-value analogue). -/
structure CosetMulFwdContract (mulFwd : Gate) (ibase bits sbase sbits : Nat)
    (ancClean : (Nat → Bool) → Prop) (wval : Nat → Nat) : Prop where
  /-- The input and scratch registers are disjoint. -/
  disjoint : ibase + bits ≤ sbase
  /-- The circuit only touches qubits at or above the scratch base (frame). -/
  framed : ∀ f p, p < sbase → Gate.applyNat mulFwd f p = f p
  /-- The scratch register decodes to the windowed coset value of the input. -/
  scratchValue : ∀ f, ancClean f →
    decodeReg (scratchIdx sbase) sbits (Gate.applyNat mulFwd f)
      = wval (decodeReg (inputIdx ibase) bits f)
  /-- The ancilla block is returned clean. -/
  ancRestored : ∀ f, ancClean f → ancClean (Gate.applyNat mulFwd f)

/-- A circuit meeting the contract preserves the decoded input value. -/
theorem CosetMulFwdContract.input_preserved {mulFwd : Gate} {ibase bits sbase sbits : Nat}
    {ancClean : (Nat → Bool) → Prop} {wval : Nat → Nat}
    (C : CosetMulFwdContract mulFwd ibase bits sbase sbits ancClean wval) (f : Nat → Bool) :
    decodeReg (inputIdx ibase) bits (Gate.applyNat mulFwd f)
      = decodeReg (inputIdx ibase) bits f :=
  input_decode_frame mulFwd ibase bits sbase f C.disjoint (fun p => C.framed f p)

end FormalRV.Shor.CosetEigenstate.CosetLayout
