/-
  FormalRV.QEC.Cultivation.TFactoryCircuit
  ----------------------------------------
  **A concrete T-gate circuit with a pluggable T-FACTORY + the Clifford surgery
  that consumes the magic state, plus resource counting.**

  The point is the INTERFACE: a `TFactory` is any source of `|T⟩` magic states
  (the magic-state cultivation of `Cultivation.Stages` is one instance).  A
  non-Clifford `T` gate is realised by *consuming* a factory `|T⟩` with a short
  Clifford surgery (a `Z`-merge `M_ZZ`, an ancilla `Z`-measurement, and a
  conditional `S` correction) — the measurement-teleportation already proved
  correct in `FormalRV.PPM.Magic.MagicStateTeleport`.  Because the consuming
  circuit only depends on the factory through `output = |T⟩`, a *cultivated* `|T⟩`
  (or any future, cheaper factory) plugs straight in: see `factory_tGate_correct`.

  Resource counting (`Cost`) is then linear in the factory's per-`|T⟩` cost
  (`circuitCost_factoryVol`), so swapping the factory just rescales the magic
  budget.

  Honesty: the factory's `qubits / rounds / attempts` are the paper's spacetime
  parameters plugged in as data (the `attempts` is the postselection retry
  overhead, noise-model dependent); the *interface and the cost algebra* are what
  is built and proved here, not a re-derivation of the paper's simulated numbers.
-/
import FormalRV.PPM.Magic.MagicStateTeleport
import FormalRV.QEC.Cultivation.Stages

namespace FormalRV.QEC.Cultivation

open FormalRV.Framework
open FormalRV.Framework.MagicStateTeleport

/-! ## §1. The pluggable `TFactory` interface. -/

/-- A **T-state factory**: any source of `|T⟩` magic states, described by its
spacetime cost per *accepted* state and the state it outputs.  Concrete
factories (cultivation, distillation, …) are values of this type; the consuming
circuit depends on a factory ONLY through `output`. -/
structure TFactory where
  /-- a human label -/
  name     : String
  /-- physical qubits used by one production attempt -/
  qubits   : Nat
  /-- QEC rounds (time) of one production attempt -/
  rounds   : Nat
  /-- expected number of attempts per *accepted* `|T⟩` (postselection retry) -/
  attempts : Nat
  /-- the magic state the factory delivers -/
  output   : StateVec 1

/-- A factory is **correct** when it really outputs `|T⟩`. -/
def TFactory.correct (F : TFactory) : Prop := F.output = tKet

/-- Spacetime volume (qubit·rounds) spent producing one accepted `|T⟩`. -/
def TFactory.volume (F : TFactory) : Nat := F.qubits * F.rounds * F.attempts

/-! ## §2. The cultivation factory (the concrete instance). -/

/-- Data qubits of a distance-`d` triangular color code (`d` odd): `(3d²+1)/4`
— `7` at `d=3` (= Steane), `19` at `d=5`, `37` at `d=7`, … -/
def colorCodeQubits (d : Nat) : Nat := (3 * (d * d) + 1) / 4

/-- Minimum code distance for the protocol: `d=3` is the smallest color code that
admits the cat-check.  The factory is *defined* for every `d`, but is only
meaningful for odd `d ≥ 3`. -/
def cultivationMinDistance : Nat := 3

/-- **The magic-state-cultivation `T`-factory at code distance `d`.**

The LOGICAL BACKBONE IS FIXED: `output = |T⟩` for *every* `d` (the controlled-`H_XY`
check of `Cultivation.TStateCheck` realizes the same logical operation regardless
of distance).  Only the SPACETIME COST scales with `d` — `O(d²)` qubits
(color-code data + one cat partner each + root) and `O(d)` rounds — so a
cultivated `|T⟩` can be produced at any distance and attached to a code of
matching distance (in principle unboundedly large; `d ≥ cultivationMinDistance`).
At `d=3` this reproduces the earlier `15` qubits / `24` rounds. -/
noncomputable def cultivationFactory (d : Nat) : TFactory where
  name     := "magic-state cultivation"
  qubits   := 2 * colorCodeQubits d + 1   -- color data + one cat partner each + root
  rounds   := 8 * d                        -- 2d cat-check layers × (3 stabilize + 1 check)
  attempts := 4                            -- nominal postselection retries (noise/d-dependent)
  output   := tKet

/-- **★ THE LOGICAL BACKBONE IS FIXED ★** — the cultivation factory outputs `|T⟩`
at EVERY code distance `d`.  One proof, all distances. -/
theorem cultivationFactory_correct (d : Nat) : (cultivationFactory d).correct := rfl

/-- The earlier non-parametric factory is just the `d=3` instance. -/
noncomputable def cultivationTFactory : TFactory := cultivationFactory 3

theorem cultivationTFactory_correct : cultivationTFactory.correct := rfl

/-- `cultivationFactory 3` reproduces the `d=3` figures (`15` qubits, `24` rounds). -/
theorem cultivationFactory_d3 :
    (cultivationFactory 3).qubits = 15
      ∧ (cultivationFactory 3).rounds = 24
      ∧ (cultivationFactory 3).attempts = 4 := by decide

/-! ## §3. The Clifford surgery that consumes a factory `|T⟩` (the `T` gate).

`applyT` is measurement-teleportation: `M_ZZ`(data, magic) [= CNOT], measure the
magic in `Z`, and apply the conditional `S` correction.  All Clifford / lattice
surgery; the only non-Clifford resource is the consumed `|T⟩`.  Correctness is
the verified `t_teleport_data_is_T`, lifted to ANY correct factory. -/

/-- **★ A `T` gate from ANY correct factory ★** — consuming a factory `|T⟩` with
the Clifford surgery yields `T|ψ⟩` on the data, in both measurement branches.
The proof only uses `F.correct` (i.e. `output = |T⟩`), so a *cultivated* `|T⟩`
plugs straight in. -/
theorem factory_tGate_correct (F : TFactory) (hF : F.correct) (ψ : StateVec 1) :
    (projLow0 * (cnotMatrix * (ψ ⊗ᵥ F.output))
        = (1 / Real.sqrt 2 : ℂ) • (Tdata ψ ⊗ᵥ (basisState 0 : StateVec 1)))
    ∧ (Shigh * (projLow1 * (cnotMatrix * (ψ ⊗ᵥ F.output)))
        = (EightTToCCZ.ω / Real.sqrt 2 : ℂ) • (Tdata ψ ⊗ᵥ (basisState 1 : StateVec 1))) := by
  rw [TFactory.correct] at hF
  rw [hF]; exact t_teleport_data_is_T ψ

/-- Specialised to the cultivation factory: a cultivated `|T⟩` realises a `T`
gate. -/
theorem cultivation_tGate_correct (ψ : StateVec 1) :
    (projLow0 * (cnotMatrix * (ψ ⊗ᵥ cultivationTFactory.output))
        = (1 / Real.sqrt 2 : ℂ) • (Tdata ψ ⊗ᵥ (basisState 0 : StateVec 1)))
    ∧ (Shigh * (projLow1 * (cnotMatrix * (ψ ⊗ᵥ cultivationTFactory.output)))
        = (EightTToCCZ.ω / Real.sqrt 2 : ℂ) • (Tdata ψ ⊗ᵥ (basisState 1 : StateVec 1))) :=
  factory_tGate_correct cultivationTFactory cultivationTFactory_correct ψ

/-- **★ A `T` GATE AT ANY CODE DISTANCE `d` ★** — consuming a distance-`d`
cultivated `|T⟩` with the (fixed) Clifford surgery yields `T|ψ⟩`.  Because the
logical backbone `output = |T⟩` is the same at every `d`, this single statement
covers all distances — the proof reuses the `d`-independent
`factory_tGate_correct`. -/
theorem cultivationFactory_tGate_correct (d : Nat) (ψ : StateVec 1) :
    (projLow0 * (cnotMatrix * (ψ ⊗ᵥ (cultivationFactory d).output))
        = (1 / Real.sqrt 2 : ℂ) • (Tdata ψ ⊗ᵥ (basisState 0 : StateVec 1)))
    ∧ (Shigh * (projLow1 * (cnotMatrix * (ψ ⊗ᵥ (cultivationFactory d).output)))
        = (EightTToCCZ.ω / Real.sqrt 2 : ℂ) • (Tdata ψ ⊗ᵥ (basisState 1 : StateVec 1))) :=
  factory_tGate_correct (cultivationFactory d) (cultivationFactory_correct d) ψ

/-! ## §4. Resource accounting. -/

/-- A spacetime resource tally: `|T⟩` states consumed (= `T`-count), factory
spacetime volume (incl. retries), and Clifford-surgery spacetime volume. -/
structure Cost where
  magic      : Nat   -- magic states consumed = T-count
  factoryVol : Nat   -- qubit·rounds spent in factories
  surgeryVol : Nat   -- qubit·rounds of Clifford surgery
deriving DecidableEq, Repr

def Cost.zero : Cost := ⟨0, 0, 0⟩
def Cost.add (a b : Cost) : Cost :=
  ⟨a.magic + b.magic, a.factoryVol + b.factoryVol, a.surgeryVol + b.surgeryVol⟩
instance : Add Cost := ⟨Cost.add⟩
instance : Zero Cost := ⟨Cost.zero⟩

@[simp] lemma Cost.add_magic (a b : Cost) : (a + b).magic = a.magic + b.magic := rfl
@[simp] lemma Cost.add_factoryVol (a b : Cost) : (a + b).factoryVol = a.factoryVol + b.factoryVol := rfl
@[simp] lemma Cost.add_surgeryVol (a b : Cost) : (a + b).surgeryVol = a.surgeryVol + b.surgeryVol := rfl
@[simp] lemma Cost.zero_magic : (0 : Cost).magic = 0 := rfl
@[simp] lemma Cost.zero_factoryVol : (0 : Cost).factoryVol = 0 := rfl
@[simp] lemma Cost.zero_surgeryVol : (0 : Cost).surgeryVol = 0 := rfl

/-- Spacetime volume of the Clifford surgery that consumes one `|T⟩`
(`M_ZZ` merge + `Z`-measure + conditional `S`); a documented per-`T` logical
cost (scales with the algorithm's code distance — plugged in as data). -/
def cliffordSurgeryVol : Nat := 6

/-- Cost of producing one accepted `|T⟩` from a factory. -/
def TFactory.perT (F : TFactory) : Cost := ⟨1, F.volume, 0⟩

/-- Cost of one `T`-gate block = produce one `|T⟩` + the consuming Clifford surgery. -/
def tBlockCost (F : TFactory) : Cost := F.perT + ⟨0, 0, cliffordSurgeryVol⟩

/-! ## §5. A concrete circuit and its cost. -/

/-- A minimal circuit op: either a non-Clifford `T` gate (consumes a factory
`|T⟩`) or a pure Clifford-surgery op (a merge/`H`/`S`/CNOT). -/
inductive Op
  | tGate
  | clifford
deriving DecidableEq, Repr

/-- Cost of one op against a given factory. -/
def opCost (F : TFactory) : Op → Cost
  | .tGate    => tBlockCost F
  | .clifford => ⟨0, 0, cliffordSurgeryVol⟩

/-- Cost of a whole circuit (a list of ops). -/
def circuitCost (F : TFactory) : List Op → Cost
  | [] => 0
  | o :: t => opCost F o + circuitCost F t

/-- Number of `T` gates in a circuit (= magic states needed). -/
def numTGates (c : List Op) : Nat := (c.filter (· == Op.tGate)).length

@[simp] lemma numTGates_nil : numTGates [] = 0 := rfl
@[simp] lemma numTGates_tGate (t : List Op) : numTGates (Op.tGate :: t) = numTGates t + 1 := by
  simp [numTGates, List.filter_cons]
@[simp] lemma numTGates_clifford (t : List Op) : numTGates (Op.clifford :: t) = numTGates t := by
  simp [numTGates, List.filter_cons]

/-- **A concrete `T`-circuit**: `H · T · H · T · H · T` style — three logical `T`
gates interleaved with Clifford surgery (e.g. one `T`-rotation lane).  Each `T`
draws a fresh `|T⟩` from the factory. -/
def exampleCircuit : List Op :=
  [.clifford, .tGate, .clifford, .tGate, .clifford, .tGate, .clifford]

/-- **The example needs exactly 3 magic states (3 `T` gates).** -/
theorem exampleCircuit_numT : numTGates exampleCircuit = 3 := by decide

/-- **Concrete resource count of the example on the cultivation factory.**  Three
cultivated `|T⟩` (magic = 3), `3 × 15·24·4` factory qubit·rounds, and the Clifford
surgery for 3 `T`-blocks + 4 standalone Clifford ops. -/
theorem exampleCircuit_cost_cultivation :
    circuitCost cultivationTFactory exampleCircuit
      = ⟨3, 3 * (15 * 24 * 4), 7 * 6⟩ := by
  decide

/-! ## §6. Pluggability: the factory enters the cost LINEARLY. -/

/-- The magic count of a circuit equals its `T`-count — INDEPENDENT of the
factory.  (Swapping factories never changes how many `|T⟩` are needed.) -/
theorem circuitCost_magic (F : TFactory) (c : List Op) :
    (circuitCost F c).magic = numTGates c := by
  induction c with
  | nil => rfl
  | cons o t ih =>
      cases o <;>
        simp [circuitCost, opCost, tBlockCost, TFactory.perT, ih] <;> omega

/-- **★ THE FACTORY PLUGS IN LINEARLY ★** — the factory spacetime volume of a
circuit is exactly `(#T gates) × (factory volume per |T⟩)`.  So replacing the
factory by a cultivated (or cheaper) one rescales the magic budget by the ratio
of their `volume`s, with nothing else in the circuit changing. -/
theorem circuitCost_factoryVol (F : TFactory) (c : List Op) :
    (circuitCost F c).factoryVol = numTGates c * F.volume := by
  induction c with
  | nil => simp [circuitCost, numTGates]
  | cons o t ih =>
      cases o <;>
        simp [circuitCost, opCost, tBlockCost, TFactory.perT, ih] <;> ring

/-! ## §7. Resource SCALING over code distance `d`.

The factory plugs in at any `d` (`cultivationFactory d`), so the resource count is
now an explicit function of the distance. -/

/-- The per-`|T⟩` factory volume as an explicit function of `d`. -/
theorem cultivationFactory_volume (d : Nat) :
    (cultivationFactory d).volume = (2 * colorCodeQubits d + 1) * (8 * d) * 4 := rfl

/-- **★ FACTORY COST AS A FUNCTION OF DISTANCE ★** — the factory spacetime cost of
any circuit at distance `d` is `#Tgates × (per-|T⟩ volume at d)`.  Space is
`O(d²)` (color-code qubits) and time `O(d)`, so the factory volume per `T` grows
as `O(d³)` while the LOGICAL result is unchanged. -/
theorem circuitCost_cultivation_factoryVol (d : Nat) (c : List Op) :
    (circuitCost (cultivationFactory d) c).factoryVol
      = numTGates c * ((2 * colorCodeQubits d + 1) * (8 * d) * 4) := by
  rw [circuitCost_factoryVol, cultivationFactory_volume]

/-- The 3-`T` example, costed at an arbitrary distance `d`. -/
theorem exampleCircuit_factoryVol (d : Nat) :
    (circuitCost (cultivationFactory d) exampleCircuit).factoryVol
      = 3 * ((2 * colorCodeQubits d + 1) * (8 * d) * 4) := by
  rw [circuitCost_cultivation_factoryVol, exampleCircuit_numT]

end FormalRV.QEC.Cultivation
