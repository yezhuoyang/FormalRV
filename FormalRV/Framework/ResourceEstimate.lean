/-
  FormalRV.Framework.ResourceEstimate — the GENERAL parametric resource model.

  The Xiaodi reframe (`memory/feedback_framework_not_gotcha.md`): we do NOT
  re-derive any single paper's headline number from first principles, and we do
  NOT try to prove a paper's estimate is optimal.  Instead we build ONE
  GENERAL, parametric resource-estimate FUNCTION — the same for every corpus
  paper — and let the reviewer plug in their own inputs.  The inputs split into
  three classes:

    • HARDWARE      — measured device parameters (the QEC code-cycle time).
                      USER-SET.  Different per platform (superconducting,
                      neutral atom), never derived by us.
    • WORKLOAD      — the algorithm's demand: #Toffoli of the logical
                      Clifford+Toffoli circuit and its #logical qubits.
                      A function of the problem (RSA-2048, ECC-256); supplied
                      per instance from the L1/L2 layers.
    • ARCHITECTURE  — the compilation method's per-operation cost + footprint:
      + ASSUMPTIONS   code-cycles per logical Toffoli, physical qubits per
                      logical, routing/ancilla footprint, magic-factory
                      footprint.  These are the mathematically-UNVERIFIABLE
                      inputs (Type A hardware + Type B method assumptions, see
                      `memory/feedback_type_AB_assumptions.md`): the framework
                      does NOT derive them — the paper/user supplies and
                      justifies them by their own analysis.

  The framework's job is the *verified derivation* (the composition):

      time   = n_toff · tau_toff · t_cycle              (critical path)
      qubits = n_logical · phys_per_logical + ancilla + factory

  i.e. "we verify that Shor takes time T with Q qubits ON THEIR hardware and
  architecture, mathematically."  The composition is the theorem; the inputs
  are the reviewer's to plug in.  Monotonicity lemmas (§3) make the sensitivity
  analysis mechanical: varying an input moves the output in the proven
  direction.  General across all seven corpus papers — see the corpus
  instantiations under `Corpus/` and the verified upper-bound + gap analysis in
  `System/NaiveUpperBound.lean`.

  No Mathlib.  Pure Nat / Bool.  No `sorry`, no `axiom`.
-/
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Framework.Resource

open FormalRV.Framework FormalRV.Qualtran

/-! ## (1) The three input classes -/

/-- HARDWARE (user-set, measured): the QEC code-cycle time, in 1/10 μs units
    (matching `QualtranPhysicalParameters.cycle_time_us_tenths`; 10 ↔ 1 μs). -/
structure Hardware where
  cycle_time_us_tenths : Nat
  deriving Repr, DecidableEq, Inhabited

/-- WORKLOAD (the algorithm's demand): the Toffoli count and logical-qubit
    footprint of the logical Clifford+Toffoli circuit.  A function of the
    problem size, supplied from the L1 (algorithm) / L2 (gadget) layers. -/
structure Workload where
  /-- Number of logical Toffoli gates on the critical path. -/
  n_toff    : Nat
  /-- Number of logical (data) qubits the circuit operates on. -/
  n_logical : Nat
  deriving Repr, DecidableEq, Inhabited

/-- ARCHITECTURE + ASSUMPTIONS (method + hardware-derived; NOT verified by the
    framework — the user/paper supplies and justifies these):
      • `tau_toff_cycles`  : code-cycles to execute one logical Toffoli
                             (lattice-surgery / magic-factory method-dependent).
      • `phys_per_logical` : physical qubits per logical qubit
                             (code-dependent: 2(d+1)² for a surface patch,
                             ⌈n/k⌉ for a qLDPC block).
      • `ancilla_qubits`   : routing / operation-zone ancilla footprint.
      • `factory_qubits`   : magic-state factory footprint. -/
structure Architecture where
  tau_toff_cycles  : Nat
  phys_per_logical : Nat
  ancilla_qubits   : Nat
  factory_qubits   : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The DERIVED estimate: wallclock (1/10 μs units) + total physical qubits. -/
structure ResourceEstimate where
  time_us_tenths : Nat
  qubits         : Nat
  deriving Repr, DecidableEq, Inhabited

/-! ## (2) The verified derivation (the composition) -/

/-- Total code-cycles on the sequential critical path: one Toffoli at a time. -/
def totalCycles (w : Workload) (a : Architecture) : Nat :=
  w.n_toff * a.tau_toff_cycles

/-- Total wallclock (1/10 μs units) = cycles × cycle-time. -/
def totalTime (hw : Hardware) (w : Workload) (a : Architecture) : Nat :=
  totalCycles w a * hw.cycle_time_us_tenths

/-- Total physical qubits = data + routing/ancilla + factory. -/
def totalQubits (w : Workload) (a : Architecture) : Nat :=
  w.n_logical * a.phys_per_logical + a.ancilla_qubits + a.factory_qubits

/-- THE GENERAL RESOURCE ESTIMATE: the same function for every corpus paper. -/
def estimate (hw : Hardware) (w : Workload) (a : Architecture) : ResourceEstimate :=
  { time_us_tenths := totalTime hw w a, qubits := totalQubits w a }

/-- "Resource count follows": the wallclock is exactly the composition. -/
theorem estimate_time (hw : Hardware) (w : Workload) (a : Architecture) :
    (estimate hw w a).time_us_tenths
      = w.n_toff * a.tau_toff_cycles * hw.cycle_time_us_tenths := rfl

/-- "Resource count follows": the qubit count is exactly the composition. -/
theorem estimate_qubits (hw : Hardware) (w : Workload) (a : Architecture) :
    (estimate hw w a).qubits
      = w.n_logical * a.phys_per_logical + a.ancilla_qubits + a.factory_qubits := rfl

/-! ## (3) Sensitivity / monotonicity — varying an input moves the output in
    the proven direction.  This is the formal backing for "plug in your own
    hardware / assumptions and read off how the estimate responds". -/

/-- Slower cycle time ⇒ at least as much wallclock (all else equal). -/
theorem time_mono_cycle (w : Workload) (a : Architecture) {hw hw' : Hardware}
    (h : hw.cycle_time_us_tenths ≤ hw'.cycle_time_us_tenths) :
    (estimate hw w a).time_us_tenths ≤ (estimate hw' w a).time_us_tenths := by
  simp only [estimate_time]
  exact Nat.mul_le_mul (Nat.le_refl _) h

/-- More Toffolis ⇒ at least as much wallclock (all else equal). -/
theorem time_mono_toff (hw : Hardware) (a : Architecture) {w w' : Workload}
    (h : w.n_toff ≤ w'.n_toff) :
    (estimate hw w a).time_us_tenths ≤ (estimate hw w' a).time_us_tenths := by
  simp only [estimate_time]
  exact Nat.mul_le_mul (Nat.mul_le_mul h (Nat.le_refl _)) (Nat.le_refl _)

/-- More expensive Toffolis (more cycles each) ⇒ at least as much wallclock. -/
theorem time_mono_tau (hw : Hardware) (w : Workload) {a a' : Architecture}
    (h : a.tau_toff_cycles ≤ a'.tau_toff_cycles) :
    (estimate hw w a).time_us_tenths ≤ (estimate hw w a').time_us_tenths := by
  simp only [estimate_time]
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) h) (Nat.le_refl _)

/-- More logical qubits ⇒ at least as many physical qubits (all else equal). -/
theorem qubits_mono_logical (hw : Hardware) (a : Architecture) {w w' : Workload}
    (h : w.n_logical ≤ w'.n_logical) :
    (estimate hw w a).qubits ≤ (estimate hw w' a).qubits := by
  simp only [estimate_qubits]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul h (Nat.le_refl _)) _) _

/-- A larger per-logical physical footprint ⇒ at least as many physical qubits. -/
theorem qubits_mono_phys (hw : Hardware) (w : Workload) {a a' : Architecture}
    (hp : a.phys_per_logical ≤ a'.phys_per_logical)
    (ha : a.ancilla_qubits = a'.ancilla_qubits)
    (hf : a.factory_qubits = a'.factory_qubits) :
    (estimate hw w a).qubits ≤ (estimate hw w a').qubits := by
  simp only [estimate_qubits, ha, hf]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul (Nat.le_refl _) hp) _) _

/-! ## (4) Adapters to the existing framework types -/

/-- Read the hardware cycle time straight from a Qualtran physical-parameter
    record (so a corpus instance's `QualtranPhysicalParameters` drives the
    estimate directly). -/
def Hardware.ofQualtran (q : QualtranPhysicalParameters) : Hardware :=
  { cycle_time_us_tenths := q.cycle_time_us_tenths }

/-- Standard physical-qubits-per-logical read off a code: `⌈n/k⌉` for a qLDPC
    block packing `k` logicals into `n` physical qubits; `n` itself when
    `k = 0` (degenerate) or `k = 1` (a single-logical surface patch, where
    `n = 2(d+1)²`). -/
def physPerLogical (c : QECCode) : Nat :=
  if c.k = 0 then c.n else (c.n + c.k - 1) / c.k

/-- Smoke: surface patch (k = 1) gives the whole patch per logical. -/
example : physPerLogical { n := 1568, k := 1, d := 27, hx := [], hz := [] } = 1568 := by
  decide

/-- Smoke: a qLDPC block [[5278, 1480, 24]] (qianxu lp_24) packs ≈ ⌈5278/1480⌉ = 4
    physical per logical. -/
example : physPerLogical { n := 5278, k := 1480, d := 24, hx := [], hz := [] } = 4 := by
  decide

/-! ## (5) A toy end-to-end instance (decide-checkable smoke test of §2). -/

/-- Toy hardware: 1 μs cycle. -/
def toyHW : Hardware := { cycle_time_us_tenths := 10 }

/-- Toy workload: 100 Toffolis over 4 logical qubits. -/
def toyWork : Workload := { n_toff := 100, n_logical := 4 }

/-- Toy architecture: 13 cycles/Toffoli, 1568 physical/logical, 900 ancilla,
    2565 factory (qianxu-ish numbers, but at a toy 100-Toffoli scale). -/
def toyArch : Architecture :=
  { tau_toff_cycles := 13, phys_per_logical := 1568,
    ancilla_qubits := 900, factory_qubits := 2565 }

/-- The composition fires: 4·1568 + 900 + 2565 = 9737 qubits. -/
example : (estimate toyHW toyWork toyArch).qubits = 9737 := by decide

/-- The composition fires: 100·13·10 = 13000 tenths-μs = 1300 μs. -/
example : (estimate toyHW toyWork toyArch).time_us_tenths = 13000 := by decide

end FormalRV.Framework.Resource
