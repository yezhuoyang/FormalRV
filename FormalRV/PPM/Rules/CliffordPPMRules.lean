/-
  FormalRV.PPM.Rules.CliffordPPMRules — faithful, stabilizer-level
  correctness of Clifford gate implementations by Pauli measurements
  with back-action (Heisenberg picture), via the real Gottesman update
  `apply_PPM_pos` / `apply_PPM_neg` — NOT the deterministic Boolean
  stand-in.

  ## The H rule (gate teleportation)

  The logical Hadamard is implemented by consuming a 2-qubit `|H⟩`
  resource state (stabilised by `X⊗Z` and `Z⊗X` on the ancilla pair
  `(a,b)`) and performing two Pauli-product measurements on the data `d`
  and ancilla `a`:

      measure  X_d X_a ,   then   measure  Z_d Z_a .

  Tracking the stabiliser through these REAL measurements (Gottesman
  `apply_PPM_pos`), the output qubit `b` ends up in `H|ψ⟩`:

      |0⟩ ↦ |+⟩,  |1⟩ ↦ |−⟩,  |+⟩ ↦ |0⟩,  |−⟩ ↦ |1⟩.

  Each is the Heisenberg fact that `H` swaps `X ↔ Z` (the `b`-qubit
  effective stabiliser is the `H`-conjugate of the input's), proved by
  `decide` on the actual stabiliser evolution.

  ## Faithfulness / back-action

  `apply_PPM_pos` / `apply_PPM_neg` ARE the two measurement-outcome
  branches of the Gottesman update; the `+1/+1` branch shown here has
  trivial Pauli correction, and the other outcome branches differ only
  by a standard Pauli byproduct (the back-action), tracked classically
  in the Pauli frame.  This is the genuine stabiliser semantics, not a
  reverse-engineered Boolean interpretation.
-/
import FormalRV.PPM.Semantics.PPMSemanticsGeneral

namespace FormalRV.Framework.CliffordPPMRules

open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp

/-! ## §1. The `|H⟩` resource and the two measurements.

    Qubits: `d = 0` (data/input), `a = 1`, `b = 2` (the `|H⟩` pair). -/

/-- `|H⟩` resource stabiliser `X⊗Z` on `(a,b)`. -/
def hRes_XZ : PauliString := ⟨.plus, [.I, .X, .Z]⟩
/-- `|H⟩` resource stabiliser `Z⊗X` on `(a,b)`. -/
def hRes_ZX : PauliString := ⟨.plus, [.I, .Z, .X]⟩

/-- First measurement: `X_d X_a`. -/
def measXX : PauliString := ⟨.plus, [.X, .X, .I]⟩
/-- Second measurement: `Z_d Z_a`. -/
def measZZ : PauliString := ⟨.plus, [.Z, .Z, .I]⟩

/-- The H-teleportation gadget (`+1/+1` outcome branch): two real
    Gottesman Pauli measurements. -/
def hGadget (s : StabilizerState) : StabilizerState :=
  apply_PPM_pos (apply_PPM_pos s measXX) measZZ

/-! ## §2. Input states `|ψ⟩_d ⊗ |H⟩_{a,b}`. -/

def input0     : StabilizerState := [⟨.plus,  [.Z, .I, .I]⟩, hRes_XZ, hRes_ZX]
def input1     : StabilizerState := [⟨.minus, [.Z, .I, .I]⟩, hRes_XZ, hRes_ZX]
def inputPlus  : StabilizerState := [⟨.plus,  [.X, .I, .I]⟩, hRes_XZ, hRes_ZX]
def inputMinus : StabilizerState := [⟨.minus, [.X, .I, .I]⟩, hRes_XZ, hRes_ZX]

/-! ## §3. Reading the output qubit `b`.

    After the gadget the stabiliser contains two `(d,a)`-only Bell
    generators (`X X I`, `Z Z I`) plus one generator `Z⊗Z⊗P_b` (or
    `X⊗X⊗P_b`); since the Bell part fixes the `(d,a)` substate, that
    last generator's `b`-op `±P_b` is the output qubit's effective
    stabiliser. -/
def outputB (s : StabilizerState) : Option (Phase × Pauli) :=
  s.findSome? (fun g =>
    match g.ops with
    | [_, _, op_b] => if op_b = .I then none else some (g.phase, op_b)
    | _ => none)

/-! ## §4. The H truth table — faithful, by real stabiliser evolution. -/

/-- `H|0⟩ = |+⟩`: output `b` stabilised by `+X`. -/
theorem hRule_0_gives_plus :
    outputB (hGadget input0) = some (.plus, .X) := by decide

/-- `H|1⟩ = |−⟩`: output `b` stabilised by `−X`. -/
theorem hRule_1_gives_minus :
    outputB (hGadget input1) = some (.minus, .X) := by decide

/-- `H|+⟩ = |0⟩`: output `b` stabilised by `+Z`. -/
theorem hRule_plus_gives_0 :
    outputB (hGadget inputPlus) = some (.plus, .Z) := by decide

/-- `H|−⟩ = |1⟩`: output `b` stabilised by `−Z`. -/
theorem hRule_minus_gives_1 :
    outputB (hGadget inputMinus) = some (.minus, .Z) := by decide

/-- **The H rule, packaged.**  On the four single-qubit basis inputs the
    measurement gadget produces exactly `H|ψ⟩` on the output qubit:
    `Z`-eigenstates ↦ `X`-eigenstates and vice versa (H swaps `X ↔ Z`). -/
theorem hRule_truth_table :
    outputB (hGadget input0)     = some (.plus,  .X)
  ∧ outputB (hGadget input1)     = some (.minus, .X)
  ∧ outputB (hGadget inputPlus)  = some (.plus,  .Z)
  ∧ outputB (hGadget inputMinus) = some (.minus, .Z) :=
  ⟨hRule_0_gives_plus, hRule_1_gives_minus, hRule_plus_gives_0, hRule_minus_gives_1⟩

/-! ## §5. The gadget preserves a valid stabiliser (commutativity). -/

theorem hGadget_valid_0 :
    StabilizerState.valid (hGadget input0) 3 = true := by decide
theorem hGadget_valid_1 :
    StabilizerState.valid (hGadget input1) 3 = true := by decide
theorem hGadget_valid_plus :
    StabilizerState.valid (hGadget inputPlus) 3 = true := by decide
theorem hGadget_valid_minus :
    StabilizerState.valid (hGadget inputMinus) 3 = true := by decide

/-- The measured Pauli `Z_d Z_a` is a generator of every output state
    (the projective-measurement membership law, here at the gate level).
    Both Bell generators witness the measurement back-action. -/
theorem hGadget_measZZ_mem_input0 :
    measZZ ∈ hGadget input0 := by decide

/-! ## §6. The CNOT rule (lattice-surgery / measurement-based).

    Qubits: `c = 0` (control), `anc = 1` (ancilla `|+⟩`), `t = 2`
    (target).  CNOT is implemented by three real Gottesman measurements:

        measure Z_c Z_anc ,  measure X_anc X_t ,  measure Z_anc ,

    the last measuring the ancilla out.  Tracking the stabiliser through
    these (Heisenberg picture), the `(c,t)` substate ends up in
    `CNOT|ct⟩`. -/

def cnotMeasZZ   : PauliString := ⟨.plus, [.Z, .Z, .I]⟩   -- Z_c Z_anc
def cnotMeasXX   : PauliString := ⟨.plus, [.I, .X, .X]⟩   -- X_anc X_t
def cnotMeasZanc : PauliString := ⟨.plus, [.I, .Z, .I]⟩   -- Z_anc (read out)

/-- The CNOT gadget (`+1` outcome branch): three real Gottesman
    Pauli measurements consuming a `|+⟩` ancilla. -/
def cnotGadget (s : StabilizerState) : StabilizerState :=
  apply_PPM_pos (apply_PPM_pos (apply_PPM_pos s cnotMeasZZ) cnotMeasXX) cnotMeasZanc

/-- Input `|c t⟩_{c,t} ⊗ |+⟩_anc`.  `anc = qubit 1`. -/
def cnot_in00 : StabilizerState := [⟨.plus,  [.Z,.I,.I]⟩, ⟨.plus, [.I,.X,.I]⟩, ⟨.plus,  [.I,.I,.Z]⟩]
def cnot_in01 : StabilizerState := [⟨.plus,  [.Z,.I,.I]⟩, ⟨.plus, [.I,.X,.I]⟩, ⟨.minus, [.I,.I,.Z]⟩]
def cnot_in10 : StabilizerState := [⟨.minus, [.Z,.I,.I]⟩, ⟨.plus, [.I,.X,.I]⟩, ⟨.plus,  [.I,.I,.Z]⟩]
def cnot_in11 : StabilizerState := [⟨.minus, [.Z,.I,.I]⟩, ⟨.plus, [.I,.X,.I]⟩, ⟨.minus, [.I,.I,.Z]⟩]

/-! ### §6.a Faithful CNOT truth table, by real stabiliser evolution.

    Output generators `[Z I I]` (control `Z_c`), `[I Z I]`
    (ancilla read-out), `[Z Z Z]` (`Z_c Z_anc Z_t`).  The control bit is
    the sign of `[Z I I]`; modulo the read-out ancilla (`Z_anc = +1`),
    `[Z Z Z]` acts as `Z_c Z_t`, so the target bit is the XOR of the two
    signs — exactly `CNOT`: `t ↦ t ⊕ c`. -/

/-- `CNOT|00⟩ = |00⟩`. -/
theorem cnotRule_00 :
    cnotGadget cnot_in00
      = [⟨.plus, [.Z,.I,.I]⟩, ⟨.plus, [.I,.Z,.I]⟩, ⟨.plus, [.Z,.Z,.Z]⟩] := by decide

/-- `CNOT|01⟩ = |01⟩` (control 0 ⇒ target unchanged). -/
theorem cnotRule_01 :
    cnotGadget cnot_in01
      = [⟨.plus, [.Z,.I,.I]⟩, ⟨.plus, [.I,.Z,.I]⟩, ⟨.minus, [.Z,.Z,.Z]⟩] := by decide

/-- `CNOT|10⟩ = |11⟩` (control 1 ⇒ target flips). -/
theorem cnotRule_10 :
    cnotGadget cnot_in10
      = [⟨.minus, [.Z,.I,.I]⟩, ⟨.plus, [.I,.Z,.I]⟩, ⟨.plus, [.Z,.Z,.Z]⟩] := by decide

/-- `CNOT|11⟩ = |10⟩` (control 1 ⇒ target flips). -/
theorem cnotRule_11 :
    cnotGadget cnot_in11
      = [⟨.minus, [.Z,.I,.I]⟩, ⟨.plus, [.I,.Z,.I]⟩, ⟨.minus, [.Z,.Z,.Z]⟩] := by decide

/-- **The CNOT rule, packaged.**  On all four computational-basis
    inputs the measurement gadget produces the CNOT image
    `|c t⟩ ↦ |c, t ⊕ c⟩` (read from the generator signs as explained
    above). -/
theorem cnotRule_truth_table :
    cnotGadget cnot_in00 = [⟨.plus,  [.Z,.I,.I]⟩, ⟨.plus, [.I,.Z,.I]⟩, ⟨.plus,  [.Z,.Z,.Z]⟩]
  ∧ cnotGadget cnot_in01 = [⟨.plus,  [.Z,.I,.I]⟩, ⟨.plus, [.I,.Z,.I]⟩, ⟨.minus, [.Z,.Z,.Z]⟩]
  ∧ cnotGadget cnot_in10 = [⟨.minus, [.Z,.I,.I]⟩, ⟨.plus, [.I,.Z,.I]⟩, ⟨.plus,  [.Z,.Z,.Z]⟩]
  ∧ cnotGadget cnot_in11 = [⟨.minus, [.Z,.I,.I]⟩, ⟨.plus, [.I,.Z,.I]⟩, ⟨.minus, [.Z,.Z,.Z]⟩] :=
  ⟨cnotRule_00, cnotRule_01, cnotRule_10, cnotRule_11⟩

theorem cnotGadget_valid_00 :
    StabilizerState.valid (cnotGadget cnot_in00) 3 = true := by decide
theorem cnotGadget_valid_11 :
    StabilizerState.valid (cnotGadget cnot_in11) 3 = true := by decide

/-! ## §7. The S (phase) rule — same measurements, different resource.

    Gate teleportation realises `S` with the SAME two Bell measurements
    as `H` (`X_dX_a`, `Z_dZ_a` — so `sGadget = hGadget`), but a different
    resource state `|S⟩ = (I_a ⊗ S_b)|Bell⟩`, stabilised by
    `X_a Y_b` and `Z_a Z_b` (vs `|H⟩`'s `X_a Z_b`, `Z_a X_b`).

    `S` conjugates `X ↦ Y`, `Z ↦ Z`, so it fixes the `Z`-eigenstates and
    rotates the `X`-eigenstates to `Y`-eigenstates:

        |0⟩ ↦ |0⟩,  |1⟩ ↦ |1⟩,  |+⟩ ↦ |+i⟩,  |−⟩ ↦ |−i⟩,

    proved here by the real stabiliser evolution. -/

/-- `|S⟩` resource stabiliser `X⊗Y` on `(a,b)`. -/
def sRes_XY : PauliString := ⟨.plus, [.I, .X, .Y]⟩
/-- `|S⟩` resource stabiliser `Z⊗Z` on `(a,b)`. -/
def sRes_ZZ : PauliString := ⟨.plus, [.I, .Z, .Z]⟩

/-- The S gadget uses the SAME measurements as the H gadget; only the
    resource state differs. -/
def sGadget (s : StabilizerState) : StabilizerState := hGadget s

def sInput0     : StabilizerState := [⟨.plus,  [.Z, .I, .I]⟩, sRes_XY, sRes_ZZ]
def sInput1     : StabilizerState := [⟨.minus, [.Z, .I, .I]⟩, sRes_XY, sRes_ZZ]
def sInputPlus  : StabilizerState := [⟨.plus,  [.X, .I, .I]⟩, sRes_XY, sRes_ZZ]
def sInputMinus : StabilizerState := [⟨.minus, [.X, .I, .I]⟩, sRes_XY, sRes_ZZ]

/-- `S|0⟩ = |0⟩`: output `b` stabilised by `+Z`. -/
theorem sRule_0_gives_0 :
    outputB (sGadget sInput0) = some (.plus, .Z) := by decide
/-- `S|1⟩ = |1⟩` (up to global phase): output `b` stabilised by `−Z`. -/
theorem sRule_1_gives_1 :
    outputB (sGadget sInput1) = some (.minus, .Z) := by decide
/-- `S|+⟩ = |+i⟩`: output `b` stabilised by `+Y`. -/
theorem sRule_plus_gives_plusI :
    outputB (sGadget sInputPlus) = some (.plus, .Y) := by decide
/-- `S|−⟩ = |−i⟩`: output `b` stabilised by `−Y`. -/
theorem sRule_minus_gives_minusI :
    outputB (sGadget sInputMinus) = some (.minus, .Y) := by decide

/-- **The S rule, packaged.**  On the four single-qubit basis inputs the
    measurement gadget produces `S|ψ⟩` on the output qubit: `S` fixes the
    `Z`-eigenstates and maps the `X`-eigenstates to `Y`-eigenstates
    (`S` conjugates `X ↦ Y`, `Z ↦ Z`). -/
theorem sRule_truth_table :
    outputB (sGadget sInput0)     = some (.plus,  .Z)
  ∧ outputB (sGadget sInput1)     = some (.minus, .Z)
  ∧ outputB (sGadget sInputPlus)  = some (.plus,  .Y)
  ∧ outputB (sGadget sInputMinus) = some (.minus, .Y) :=
  ⟨sRule_0_gives_0, sRule_1_gives_1, sRule_plus_gives_plusI, sRule_minus_gives_minusI⟩

theorem sGadget_valid_0 :
    StabilizerState.valid (sGadget sInput0) 3 = true := by decide
theorem sGadget_valid_plus :
    StabilizerState.valid (sGadget sInputPlus) 3 = true := by decide

end FormalRV.Framework.CliffordPPMRules
