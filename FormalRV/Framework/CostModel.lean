/-
  FormalRV.Framework.CostModel — the resource COST RULE as a first-class,
  PLUGGABLE component INSIDE the framework, with PURPOSE-TAGGED ancilla.

  Why this file exists (John, 2026-06-02).  An earlier version hardcoded the
  surface-code routing-ancilla rule directly inside the naive schedule and waved
  at qLDPC "as future work outside the framework".  That is wrong on principle:
  verification should live at the GENERAL level, and any code/hardware-specific
  rule must be modelled AS A FRAMEWORK INSTANCE — never special-cased outside.
  Same extensibility discipline as `System/InvariantFramework.lean` (a general
  `SpaceTimeInvariant` type + instances, the theorem proven once `∀`).

  The *general* `estimate` (`ResourceEstimate.lean`) already takes the
  architecture numbers as free inputs.  Here we add the abstraction that
  PRODUCES those numbers from a code: a `CostModel` (a named bundle of pluggable
  rules), with `surfaceModel` and `qldpcModel` as two INSTANCES.  The composition
  theorem `estimateWith_{time,qubits}` is proven ONCE over `∀ m : CostModel`
  (by `rfl`); swapping surface ↔ qLDPC is a parameter change, not a code change.

  PURPOSE-TAGGED ANCILLA (John, 2026-06-02).  At the SYSTEM level every ancilla
  qubit is the SAME thing — a qubit handed out by the `RequestFreshAncilla`
  syscall, which is purpose-agnostic and provisions the untagged `.total`.  The
  purpose tags are NOT a system-level distinction; they exist for VERIFICATION:
    (1) to check the compiler allocated the right count for each purpose, and
    (2) to FORCE us to remember to add ancilla qubits at the physical level
        during QEC (syndrome extraction) and lattice-surgery compilation — a
        purpose left untagged is a purpose easy to forget to allocate.
  After deciding the taxonomy from qianxu's qubit budget (App. E / Extended Data
  Tables) we keep exactly TWO purposes:
    • SYNDROME — syndrome-extraction (check) ancilla; the always-on QEC cost
      (≈ one per parity check; qLDPC counts these separately from data qubits).
    • SURGERY  — lattice-surgery ancilla = the operation-zone N_A.  NOTE
      "measuring a logical Pauli operator" IS lattice surgery (a logical
      Pauli-PRODUCT measurement), so it shares this ancilla — it is NOT a
      separate purpose.
  ROUTING is deliberately NOT a tag: on qianxu's reconfigurable neutral-atom
  array, qubit "routing" is ATOM TRANSPORT — a TIME cost in the schedule (the
  `AtomMove` / latency-invariant layer), not dedicated ancilla qubits.  Surface
  code's standing routing area IS a real cost, but it is a PER-LOGICAL LAYOUT
  cost and lives in `physPer` (the ~2× patch), not in the operation-ancilla
  budget.

  WHERE THE SURFACE ↔ qLDPC DIFFERENCE LIVES (now inspectable):
    • surface — SURGERY/SYNDROME are bundled into the standing ~2× patch
      (`physPer`); the operation-ancilla tags are 0.  Footprint scales with
      DATA AREA, INDEPENDENT of the measured operator (gidney-ekera-2021 §2.14:
      2(d+1)² per logical).
    • qLDPC  — SURGERY scales with the measured operator's PHYSICAL WEIGHT
      (Θ(w)·parallel; qianxu p.5 verbatim: "the ancilla qubit count scales with
      the maximum physical weight of the target logical operators"; Cross et al.
      2024, arXiv:2407.18393), INDEPENDENT of block area; SYNDROME = the explicit
      parity-check count `|hx| + |hz|`.

  No Mathlib.  Pure Nat / String / List.length.  No `sorry`, no `axiom`.
-/
import FormalRV.Framework.ResourceEstimate

namespace FormalRV.Framework.Resource

open FormalRV.Framework

/-! ## (1) Purpose-tagged ancilla budget

    At the SYSTEM level these are all just ancilla qubits from the one
    `RequestFreshAncilla` syscall (it provisions `.total`).  The tags are a
    VERIFICATION aid: they let an audit check each purpose's rule independently,
    and they force the physical QEC / surgery compilation to remember to allocate
    ancilla for each purpose. -/

/-- Ancilla qubits broken down by PURPOSE, for verification.  `total` is the flat
    count the system actually requests (purpose-agnostic); the two tags attribute
    it so the compiler's allocation can be checked per purpose and no purpose is
    forgotten. -/
structure AncillaBudget where
  /-- syndrome-extraction (check) ancilla — the always-on QEC cost
      (≈ one per stabilizer parity check). -/
  syndrome : Nat
  /-- lattice-surgery ancilla (the operation-zone N_A).  "Measuring a logical
      Pauli" is lattice surgery, so it shares this — not a separate purpose. -/
  surgery  : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The total ancilla the system requests = sum over purposes.  This is what the
    purpose-agnostic `RequestFreshAncilla` syscall provisions. -/
def AncillaBudget.total (a : AncillaBudget) : Nat :=
  a.syndrome + a.surgery

/-! ## (2) The pluggable cost model

    Mirrors `SpaceTimeInvariant`: a named bundle of computable rules.  Instances
    are *values*; the composition theorem is proven once over `∀ m`.  No
    `deriving` (the fields are functions — no `DecidableEq`/`Repr`); we never
    compare models, we quantify over them. -/

/-- A resource cost model: the pluggable rules that turn a code (+ workload +
    measured-operator weight + parallel-PPM count) into the architecture numbers
    the general `estimate` consumes.

    `ancilla c w op_weight parallel : AncillaBudget` is the purpose-tagged rule
    that differs between code families.  `op_weight` is the measured logical
    operator's PHYSICAL Hamming weight `w` (in the repo, `rowWeight (L.selectZ S)`);
    `parallel` is the number of PPMs run simultaneously; `w : Workload` supplies
    `n_logical` where a rule needs it.  (Surface's per-logical routing area lives
    in `physPer`, NOT here — see the module header.) -/
structure CostModel where
  /-- Human-readable tag (mirrors `SpaceTimeInvariant.name`). -/
  name    : String
  /-- code-cycles to execute one logical Toffoli, from the code. -/
  tauToff : QECCode → Nat
  /-- physical qubits per logical qubit, from the code (for surface this INCLUDES
      the standing routing area — a per-logical layout cost). -/
  physPer : QECCode → Nat
  /-- purpose-tagged operation-ancilla footprint:
      `code → workload → op_weight → parallel → AncillaBudget`. -/
  ancilla : QECCode → Workload → Nat → Nat → AncillaBudget
  /-- magic-state factory footprint, from the code. -/
  factory : QECCode → Nat

/-- Build the existing `Architecture` record from a model + workload + code + the
    measured operator's weight + the parallel-PPM count.  The flat
    `ancilla_qubits` field — what the purpose-agnostic syscall sees — receives the
    budget's `total`; everything downstream is reused unchanged. -/
def CostModel.toArch (m : CostModel) (w : Workload) (c : QECCode)
    (op_weight parallel : Nat) : Architecture :=
  { tau_toff_cycles  := m.tauToff c
    phys_per_logical := m.physPer c
    ancilla_qubits   := (m.ancilla c w op_weight parallel).total
    factory_qubits   := m.factory c }

/-- SYSTEM-LEVEL view: the architecture's flat `ancilla_qubits` (what
    `RequestFreshAncilla` provisions) is exactly the budget `total` — the
    purpose tags do not change the system interface; they are a verification aid. -/
theorem toArch_ancilla_total (m : CostModel) (w : Workload) (c : QECCode)
    (op_weight parallel : Nat) :
    (m.toArch w c op_weight parallel).ancilla_qubits
      = (m.ancilla c w op_weight parallel).total := rfl

/-- THE ENTRY POINT: estimate resources under a plugged-in cost model. -/
def estimateWith (m : CostModel) (hw : Hardware) (w : Workload) (c : QECCode)
    (op_weight parallel : Nat) : ResourceEstimate :=
  estimate hw w (m.toArch w c op_weight parallel)

/-! ## (3) The general composition theorem — proven ONCE, `∀ model`, by `rfl`. -/

/-- For EVERY cost model, the wallclock is the explicit composition of the
    model's own `tauToff` rule with the workload and hardware. -/
theorem estimateWith_time (m : CostModel) (hw : Hardware) (w : Workload)
    (c : QECCode) (op_weight parallel : Nat) :
    (estimateWith m hw w c op_weight parallel).time_us_tenths
      = w.n_toff * m.tauToff c * hw.cycle_time_us_tenths := rfl

/-- For EVERY cost model, the physical-qubit count is the explicit composition
    of `physPer` / the ancilla budget `total` / `factory`. -/
theorem estimateWith_qubits (m : CostModel) (hw : Hardware) (w : Workload)
    (c : QECCode) (op_weight parallel : Nat) :
    (estimateWith m hw w c op_weight parallel).qubits
      = w.n_logical * m.physPer c
        + (m.ancilla c w op_weight parallel).total
        + m.factory c := rfl

/-- The SAME count, with the ancilla expanded BY PURPOSE — the audit view:
    data + syndrome + surgery + factory. -/
theorem estimateWith_qubits_tagged (m : CostModel) (hw : Hardware) (w : Workload)
    (c : QECCode) (op_weight parallel : Nat) :
    (estimateWith m hw w c op_weight parallel).qubits
      = w.n_logical * m.physPer c
        + (m.ancilla c w op_weight parallel).syndrome
        + (m.ancilla c w op_weight parallel).surgery
        + m.factory c := by
  rw [estimateWith_qubits]; simp only [AncillaBudget.total]; omega

/-- Monotonicity carries over for free: `estimateWith m …` is *definitionally* an
    `estimate` call, so the sensitivity lemmas (`time_mono_*`, `qubits_mono_*`)
    apply to every plugged-in model without re-proof. -/
theorem estimateWith_eq_estimate (m : CostModel) (hw : Hardware) (w : Workload)
    (c : QECCode) (op_weight parallel : Nat) :
    estimateWith m hw w c op_weight parallel
      = estimate hw w (m.toArch w c op_weight parallel) := rfl

/-! ## (4) Instance: SURFACE CODE — operation-ancilla bundled into a standing
    ~2× patch (area-scaling, weight-INDEPENDENT).

    `physPer = 2 · physPerLogical`: the per-logical patch (which already bundles
    the in-patch syndrome-measure qubits) PLUS an equal-area standing ROUTING
    region — a per-logical LAYOUT cost (gidney-ekera-2021 §2.14 + Fig. 8: 2(d+1)²
    per logical; Litinski 2019: ~1.5–2×).  The operation-ancilla tags are both 0:
    surface syndrome is in-patch, and surgery merges happen in the already-
    allocated routing area.  So the audit-relevant ancilla is the standing
    footprint, not a transient per-operation cost. -/
def surfaceModel (factory : Nat) : CostModel :=
  { name    := "surface-code lattice surgery (standing ~2x patch, area-scaling)"
    tauToff := fun c => c.d
    physPer := fun c => 2 * physPerLogical c
    ancilla := fun _ _ _ _ =>
      { syndrome := 0     -- bundled in the patch (physPer)
        surgery  := 0 }   -- merges happen in the already-allocated routing area
    factory := fun _ => factory }

/-! ## (5) Instance: qLDPC CODE — SURGERY scales with operator WEIGHT,
    area-INDEPENDENT; SYNDROME = explicit parity-check count.

    The data block packs `k` logicals into `n` DATA qubits, so
    `physPer = ⌈n/k⌉`.  SYNDROME ancilla = `|hx| + |hz|` (one per parity check —
    read straight from the code's check matrices).  SURGERY ancilla =
    `parallel · op_weight` (Θ(w) per measured operator, coefficient 1 matching
    `cross_2025_ancilla_per_weight`, summed over parallel PPMs), and it does NOT
    see the code's area `n`.  Qubit ROUTING is atom transport — a TIME cost in
    the schedule layer, NOT an ancilla-qubit tag here.

    HONEST RESIDUES (documented, not hidden): the Θ(w) coefficient assumes good
    Tanner-graph boundary expansion (β = Θ(1); otherwise O(w·log³w), qianxu
    App. B / Cross §); a cross-block bridge adds a subleading `d` qubits. -/
def qldpcModel (factory : Nat) : CostModel :=
  { name    := "qLDPC code surgery (surgery weight-scaling, area-independent)"
    tauToff := fun c => c.d
    physPer := fun c => physPerLogical c
    ancilla := fun c _w op_weight parallel =>
      { syndrome := c.hx.length + c.hz.length     -- one ancilla per parity check
        surgery  := parallel * op_weight }        -- Θ(w)·parallel  (coeff 1 = cross_2025)
    factory := fun _ => factory }

/-! ## (6) The headline contrast, machine-checked — by purpose. -/

/-- qLDPC SURGERY ancilla is INDEPENDENT of the code (its data-block size `n`):
    it depends only on the measured operator's weight and the parallel count. -/
theorem qldpc_surgery_area_independent (factory : Nat) (c c' : QECCode)
    (w : Workload) (op_weight parallel : Nat) :
    ((qldpcModel factory).ancilla c w op_weight parallel).surgery
      = ((qldpcModel factory).ancilla c' w op_weight parallel).surgery := rfl

/-- qLDPC SURGERY ancilla in closed form: `parallel · op_weight`. -/
theorem qldpc_surgery_eq (factory : Nat) (c : QECCode) (w : Workload)
    (op_weight parallel : Nat) :
    ((qldpcModel factory).ancilla c w op_weight parallel).surgery = parallel * op_weight := rfl

/-- qLDPC SYNDROME ancilla = the explicit parity-check count of the code. -/
theorem qldpc_syndrome_eq_checks (factory : Nat) (c : QECCode) (w : Workload)
    (op_weight parallel : Nat) :
    ((qldpcModel factory).ancilla c w op_weight parallel).syndrome
      = c.hx.length + c.hz.length := rfl

/-- Surface footprint scales with DATA AREA: per-logical cost is
    `2 · physPerLogical c`, proportional to the patch size — and INDEPENDENT of
    the measured operator's weight (this is where surface routing-area lives). -/
theorem surface_phys_area_scaling (factory : Nat) (c : QECCode) :
    (surfaceModel factory).physPer c = 2 * physPerLogical c := rfl

/-- Surface has NO per-operation surgery ancilla (it is 0 — bundled in physPer). -/
theorem surface_surgery_zero (factory : Nat) (c : QECCode) (w : Workload)
    (op_weight parallel : Nat) :
    ((surfaceModel factory).ancilla c w op_weight parallel).surgery = 0 := rfl

/-- Surface has NO separate syndrome ancilla tag (it is 0 — bundled in physPer). -/
theorem surface_syndrome_zero (factory : Nat) (c : QECCode) (w : Workload)
    (op_weight parallel : Nat) :
    ((surfaceModel factory).ancilla c w op_weight parallel).syndrome = 0 := rfl

/-! ### Concrete qLDPC SURGERY ancilla vs qianxu Extended Data Table III (p.18),
    low-rate surgery (`parallel = 1`).  The rule reproduces the Θ(w) surgery
    qubit term (syndrome checks tracked separately in `.syndrome`). -/

/-- Dummy workload (the surgery term ignores it). -/
private def w0 : Workload := { n_toff := 0, n_logical := 0 }

/-- Processor bb18, physical weight 104 ⇒ 104 surgery ancilla qubits
    (Table 189 total = 104 surgery + 85 checks). -/
example : ((qldpcModel 0).ancilla { n := 248, k := 10, d := 18, hx := [], hz := [] } w0 104 1).surgery
    = 104 := by decide

/-- Processor lp_20^{3,5}, physical weight 460 ⇒ 460 surgery ancilla (Table 813 = 460+353). -/
example : ((qldpcModel 0).ancilla { n := 1122, k := 148, d := 20, hx := [], hz := [] } w0 460 1).surgery
    = 460 := by decide

/-- High-rate / parallel: 8 simultaneous weight-104 PPMs ⇒ 8·104 = 832 surgery
    ancilla (the Õ(k·ω) parallel family). -/
example : ((qldpcModel 0).ancilla { n := 248, k := 10, d := 18, hx := [], hz := [] } w0 104 8).surgery
    = 832 := by decide

/-! ### End-to-end smokes: the instances are corollaries of the general theorem. -/

/-- qLDPC end-to-end qubit composition, tagged by purpose (instance of
    `estimateWith_qubits_tagged`): data + syndrome(=|hx|+|hz|) + Θ(w)·p + factory. -/
example (hw : Hardware) (w : Workload) (c : QECCode) (ow p : Nat) :
    (estimateWith (qldpcModel 2565) hw w c ow p).qubits
      = w.n_logical * physPerLogical c + (c.hx.length + c.hz.length) + p * ow + 2565 := by
  simp only [estimateWith_qubits_tagged, qldpcModel]

/-- Surface end-to-end qubit composition: data area `2 · physPerLogical c` per
    logical, with BOTH operation-ancilla tags 0 (bundled in the standing patch). -/
example (hw : Hardware) (w : Workload) (c : QECCode) (ow p : Nat) :
    (estimateWith (surfaceModel 2565) hw w c ow p).qubits
      = w.n_logical * (2 * physPerLogical c) + 2565 := by
  simp only [estimateWith_qubits_tagged, surfaceModel, Nat.add_zero]

end FormalRV.Framework.Resource
