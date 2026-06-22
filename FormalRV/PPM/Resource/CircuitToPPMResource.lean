/-
  FormalRV.PPM.Resource.CircuitToPPMResource — GENERIC gate-by-gate PPM compilation and
  the proved WHOLE-CIRCUIT resource formula.

  Any higher-level circuit (any Shor implementation, expressed as a `List HLGate`)
  is compiled gate by gate to a concrete PPM program (`circuitToPPM`), and every
  resource count of the assembled program is proved EQUAL to the sum of per-gate
  costs (`*_circuitToPPM`).  So:

    * the framework works for ANY circuit / any Shor variant — it is parametric in
      the gate list `gs`;
    * the full Shor→Clifford+T→PPM program is assembled gate by gate on demand
      (`circuitToPPM na gs`);
    * a CONCRETE circuit yields a PROVED literal resource number (the sum, closed
      by `decide`/`native_decide`).

  Clifford gates compile to themselves (frame-tracked / "free"); T and CCZ consume a
  magic state via the teleportation gadgets of `PPMToQASM` (matching `GadgetChannel`).
  No `sorry`, no new `axiom`.
-/
import FormalRV.PPM.Resource.PPMResourceCount

namespace FormalRV.PPM.Resource.CircuitToPPMResource

open FormalRV.PPM.PPMToQASM
open FormalRV.PPM.Resource.PPMResourceCount

/-! ## §1. A higher-level gate set (any Clifford+T+CCZ circuit / Shor variant). -/

inductive HLGate where
  | H    (q : Nat)
  | S    (q : Nat)
  | T    (q : Nat)
  | X    (q : Nat)
  | Z    (q : Nat)
  | CNOT (c t : Nat)
  | CCZ  (a b c : Nat)
  deriving Repr, DecidableEq

/-! ## §2. Gate-by-gate PPM compilation.

    `na` = the ancilla base (data qubits `0..na-1`; each gadget's magic/syndrome
    ancillas live at `na..`).  Clifford gates apply directly; T and CCZ consume a
    magic state via teleportation (`PPMToQASM` gadget shapes). -/

def gateToPPM (na : Nat) : HLGate → List QasmOp
  | .H q       => [.opH q]
  | .S q       => [.opS q]
  | .X q       => [.opX q]
  | .Z q       => [.opZ q]
  | .CNOT c t  => [.opCX c t]
  | .T q       => [.opH na, .opT na, .opCX q na, .opMeas na 0, .opIf 0 (.opS q)]
  | .CCZ a b c =>
      [ .opH na, .opH (na+1), .opH (na+2), .opCCZ na (na+1) (na+2),
        .opCX a na, .opCX b (na+1), .opCX c (na+2),
        .opMeas na 0, .opMeas (na+1) 1, .opMeas (na+2) 2,
        .opIf 0 (.opCZ b c), .opIf 1 (.opCZ a c), .opIf 2 (.opCZ a b),
        .opIf2 0 1 (.opZ c), .opIf2 0 2 (.opZ b), .opIf2 1 2 (.opZ a) ]

/-- The whole compiled PPM program: each gate's gadget, concatenated. -/
def circuitToPPM (na : Nat) (gs : List HLGate) : List QasmOp :=
  gs.flatMap (gateToPPM na)

/-! ## §3. Per-gate costs (placement-independent). -/

def gateTMagic : HLGate → Nat | .T _ => 1 | _ => 0
def gateCCZMagic : HLGate → Nat | .CCZ _ _ _ => 1 | _ => 0
def gateMeas : HLGate → Nat | .T _ => 1 | .CCZ _ _ _ => 3 | _ => 0
def gateClifford : HLGate → Nat
  | .H _ => 1 | .S _ => 1 | .X _ => 1 | .Z _ => 1 | .CNOT _ _ => 1
  | .T _ => 2 | .CCZ _ _ _ => 6
def gateFeedforward : HLGate → Nat | .T _ => 1 | .CCZ _ _ _ => 6 | _ => 0

/-- Per-gate gadget counts agree with the per-gate cost functions (by cases). -/
theorem numTMagic_gateToPPM (na : Nat) (g : HLGate) :
    numTMagic (gateToPPM na g) = gateTMagic g := by cases g <;> rfl
theorem numCCZMagic_gateToPPM (na : Nat) (g : HLGate) :
    numCCZMagic (gateToPPM na g) = gateCCZMagic g := by cases g <;> rfl
theorem numMeas_gateToPPM (na : Nat) (g : HLGate) :
    numMeas (gateToPPM na g) = gateMeas g := by cases g <;> rfl
theorem numClifford_gateToPPM (na : Nat) (g : HLGate) :
    numClifford (gateToPPM na g) = gateClifford g := by cases g <;> rfl
theorem numFeedforward_gateToPPM (na : Nat) (g : HLGate) :
    numFeedforward (gateToPPM na g) = gateFeedforward g := by cases g <;> rfl

/-! ## §4. THE WHOLE-CIRCUIT RESOURCE FORMULA.

    Each resource count of the assembled PPM program equals the SUM of the per-gate
    costs — proved by induction over the gate list (concatenation additivity).  This
    is the parametric whole-circuit number, valid for ANY circuit `gs`. -/

theorem numTMagic_circuitToPPM (na : Nat) (gs : List HLGate) :
    numTMagic (circuitToPPM na gs) = (gs.map gateTMagic).sum := by
  unfold circuitToPPM
  induction gs with
  | nil => simp [numTMagic]
  | cons g gs ih =>
      rw [List.flatMap_cons, numTMagic_append, numTMagic_gateToPPM, ih,
          List.map_cons, List.sum_cons]

theorem numCCZMagic_circuitToPPM (na : Nat) (gs : List HLGate) :
    numCCZMagic (circuitToPPM na gs) = (gs.map gateCCZMagic).sum := by
  unfold circuitToPPM
  induction gs with
  | nil => simp [numCCZMagic]
  | cons g gs ih =>
      rw [List.flatMap_cons, numCCZMagic_append, numCCZMagic_gateToPPM, ih,
          List.map_cons, List.sum_cons]

theorem numMeas_circuitToPPM (na : Nat) (gs : List HLGate) :
    numMeas (circuitToPPM na gs) = (gs.map gateMeas).sum := by
  unfold circuitToPPM
  induction gs with
  | nil => simp [numMeas]
  | cons g gs ih =>
      rw [List.flatMap_cons, numMeas_append, numMeas_gateToPPM, ih,
          List.map_cons, List.sum_cons]

theorem numClifford_circuitToPPM (na : Nat) (gs : List HLGate) :
    numClifford (circuitToPPM na gs) = (gs.map gateClifford).sum := by
  unfold circuitToPPM
  induction gs with
  | nil => simp [numClifford]
  | cons g gs ih =>
      rw [List.flatMap_cons, numClifford_append, numClifford_gateToPPM, ih,
          List.map_cons, List.sum_cons]

theorem numFeedforward_circuitToPPM (na : Nat) (gs : List HLGate) :
    numFeedforward (circuitToPPM na gs) = (gs.map gateFeedforward).sum := by
  unfold circuitToPPM
  induction gs with
  | nil => simp [numFeedforward]
  | cons g gs ih =>
      rw [List.flatMap_cons, numFeedforward_append, numFeedforward_gateToPPM, ih,
          List.map_cons, List.sum_cons]

/-! ## §5. A concrete circuit ⇒ a PROVED literal whole-circuit number.

    A tiny demonstration circuit on 3 data qubits with a CCZ and two T gates —
    `[T 0, CNOT 0 1, T 1, CCZ 0 1 2, H 2]`.  The whole-program resource counts are
    LITERAL numbers, proved by reduction through the formula. -/

def demoCircuit : List HLGate :=
  [.T 0, .CNOT 0 1, .T 1, .CCZ 0 1 2, .H 2]

theorem demo_TMagic   : numTMagic   (circuitToPPM 3 demoCircuit) = 2 := by
  rw [numTMagic_circuitToPPM]; decide
theorem demo_CCZMagic : numCCZMagic (circuitToPPM 3 demoCircuit) = 1 := by
  rw [numCCZMagic_circuitToPPM]; decide
theorem demo_Meas     : numMeas     (circuitToPPM 3 demoCircuit) = 5 := by
  rw [numMeas_circuitToPPM]; decide
theorem demo_Clifford : numClifford (circuitToPPM 3 demoCircuit) = 12 := by
  rw [numClifford_circuitToPPM]; decide
theorem demo_Feedforward : numFeedforward (circuitToPPM 3 demoCircuit) = 8 := by
  rw [numFeedforward_circuitToPPM]; decide

-- Inspect the assembled program and its full resource vector:
#eval circuitToPPM 3 demoCircuit |>.length          -- total PPM op count
#eval (numTMagic (circuitToPPM 3 demoCircuit),
       numCCZMagic (circuitToPPM 3 demoCircuit),
       numMeas (circuitToPPM 3 demoCircuit),
       numClifford (circuitToPPM 3 demoCircuit),
       numFeedforward (circuitToPPM 3 demoCircuit),
       numQubits (circuitToPPM 3 demoCircuit))

/-! ## §6. A GENUINE Shor-15 instance ⇒ PROVED resource totals.

    The modular multiplier of the order-finding circuit that actually factors
    15 = 3·5 (a = 7, verified end-to-end in `PyCircuits/shor15_ppm_factoring.py`:
    the measured-phase order finding recovers the order r = 4 and hence the
    factors).  Transpiled to a Toffoli + Clifford basis that circuit's modmult is
    **27 Toffolis + 12 CNOTs**.  Each Toffoli is `H·CCZ·H`; the resource counts
    are index-independent (the cost functions ignore qubit indices), so we encode
    the multiplicities with representative indices and feed the gate list straight
    into `circuitToPPM`.  Every total below is PROVED through the whole-circuit
    formula of §4 — this is the literal instantiation the formula was built for.

    Caveat (honest): `numQubits` depends on the ancilla schedule.  `circuitToPPM`
    recycles the 3 syndrome ancillas across gadgets (the realistic sequential PPM
    picture, `na + 3` qubits), whereas the Qiskit check used fresh ancillas per
    gadget (89 qubits) so the gadgets simulate independently.  The magic-state,
    measurement, Clifford and feed-forward totals are schedule-independent. -/

/-- A Toffoli as `H·CCZ·H` in the high-level gate set. -/
def toffoli (a b c : Nat) : List HLGate := [.H c, .CCZ a b c, .H c]

/-- The Shor-15 (a = 7) modular multiplier: 27 Toffolis + 12 CNOTs. -/
def shor15Modmult : List HLGate :=
  ((List.range 27).flatMap fun _ => toffoli 0 1 2) ++ List.replicate 12 (.CNOT 0 1)

theorem shor15_TMagic      : numTMagic      (circuitToPPM 8 shor15Modmult) = 0 := by
  rw [numTMagic_circuitToPPM]; decide
theorem shor15_CCZMagic    : numCCZMagic    (circuitToPPM 8 shor15Modmult) = 27 := by
  rw [numCCZMagic_circuitToPPM]; decide
/-- 27 CCZ gadgets × 3 Z-basis syndrome measurements = 81 Pauli measurements,
    matching the Qiskit count exactly. -/
theorem shor15_Meas        : numMeas        (circuitToPPM 8 shor15Modmult) = 81 := by
  rw [numMeas_circuitToPPM]; decide
theorem shor15_Clifford    : numClifford    (circuitToPPM 8 shor15Modmult) = 228 := by
  rw [numClifford_circuitToPPM]; decide
theorem shor15_Feedforward : numFeedforward (circuitToPPM 8 shor15Modmult) = 162 := by
  rw [numFeedforward_circuitToPPM]; decide

#eval (numTMagic (circuitToPPM 8 shor15Modmult),
       numCCZMagic (circuitToPPM 8 shor15Modmult),
       numMeas (circuitToPPM 8 shor15Modmult),
       numClifford (circuitToPPM 8 shor15Modmult),
       numFeedforward (circuitToPPM 8 shor15Modmult))

/-! ## §7. PARAMETRIC over circuit size ⇒ scales to ANY Shor instance (incl. 2048-bit).

    A modular-multiplier block of `nToff` Toffolis + `nCnot` CNOTs.  The magic-state
    and Pauli-measurement totals are proved as CLOSED FORMS in `nToff` — so the
    framework returns proved totals for any Shor implementation just by supplying its
    Toffoli count: Shor-15 instantiates at `nToff = 27`, a 2048-bit run at its own
    (much larger) Toffoli count, with no new proof. -/

/-- Helper: sum of `f` over `n` concatenated copies of a block `L` is `n · (sum over L)`. -/
theorem sum_map_flatten_replicate (n : Nat) (L : List HLGate) (f : HLGate → Nat) :
    (((List.replicate n L).flatten).map f).sum = n * (L.map f).sum := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, List.map_append, List.sum_append, ih,
          Nat.succ_mul]
      exact Nat.add_comm _ _

/-- A generic modular-multiplier block: `nToff` Toffolis (each `H·CCZ·H`) + `nCnot` CNOTs. -/
def modmultBlock (nToff nCnot : Nat) : List HLGate :=
  (List.replicate nToff (toffoli 0 1 2)).flatten ++ List.replicate nCnot (.CNOT 0 1)

/-- Magic states scale exactly with the Toffoli count — for ANY size. -/
theorem modmult_CCZMagic (nToff nCnot : Nat) :
    numCCZMagic (circuitToPPM 8 (modmultBlock nToff nCnot)) = nToff := by
  rw [numCCZMagic_circuitToPPM, modmultBlock, List.map_append, List.sum_append,
      sum_map_flatten_replicate, List.map_replicate, List.sum_replicate_nat]
  have h1 : ((toffoli 0 1 2).map gateCCZMagic).sum = 1 := rfl
  have h2 : gateCCZMagic (HLGate.CNOT 0 1) = 0 := rfl
  rw [h1, h2]; omega

/-- Pauli measurements scale as `3·(Toffoli count)` — for ANY size. -/
theorem modmult_Meas (nToff nCnot : Nat) :
    numMeas (circuitToPPM 8 (modmultBlock nToff nCnot)) = 3 * nToff := by
  rw [numMeas_circuitToPPM, modmultBlock, List.map_append, List.sum_append,
      sum_map_flatten_replicate, List.map_replicate, List.sum_replicate_nat]
  have h1 : ((toffoli 0 1 2).map gateMeas).sum = 3 := rfl
  have h2 : gateMeas (HLGate.CNOT 0 1) = 0 := rfl
  rw [h1, h2]; omega

/-- Sanity: the parametric formula reproduces the proved Shor-15 totals at `nToff = 27`. -/
example : numCCZMagic (circuitToPPM 8 (modmultBlock 27 12)) = 27 := by
  rw [modmult_CCZMagic]
example : numMeas (circuitToPPM 8 (modmultBlock 27 12)) = 81 := by
  rw [modmult_Meas]

end FormalRV.PPM.Resource.CircuitToPPMResource
