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

  So: the *general* `estimate` (`ResourceEstimate.lean`) already takes the
  architecture numbers as free inputs.  Here we add the abstraction that
  PRODUCES those numbers from a code: a `CostModel` (a named bundle of pluggable
  rules), with `surfaceModel` and `qldpcModel` as two INSTANCES.  The composition
  theorem `estimateWith_{time,qubits}` is proven ONCE over `∀ m : CostModel`
  (by `rfl`); each code family is a plug-in; swapping surface ↔ qLDPC is a
  parameter change, not a code change.

  PURPOSE-TAGGED ANCILLA (John, 2026-06-02).  Ancilla qubits serve different
  PURPOSES, all provided by the `RequestFreshAncilla` syscall but distinct for
  auditing:
    • SYNDROME ancilla — extract stabilizer syndromes (≈ one per parity check).
    • ROUTING  ancilla — transport / route logical qubits between operations.
    • SURGERY  ancilla — the lattice-surgery gadget systems (merge regions).
  `CostModel.ancilla` returns an `AncillaBudget` tagging the three, so a verifier
  can check each purpose's rule separately.  This is exactly where the surface ↔
  qLDPC difference lives and becomes inspectable:
    • surface — ROUTING dominates and scales with DATA AREA (≈ a full extra patch
      per logical; gidney-ekera-2021 §2.14: 2(d+1)² per logical ⇒ ~2× footprint),
      INDEPENDENT of which operator is measured.
    • qLDPC  — SURGERY scales with the measured operator's PHYSICAL WEIGHT
      (Θ(w)·parallel; qianxu p.5 verbatim: "the ancilla qubit count scales with
      the maximum physical weight of the target logical operators"; Cross et al.
      2024, arXiv:2407.18393), INDEPENDENT of the block area; SYNDROME ancilla is
      the explicit parity-check count from the code's H matrices.

  No Mathlib.  Pure Nat / String / List.length.  No `sorry`, no `axiom`.
-/
import FormalRV.Framework.ResourceEstimate

namespace FormalRV.Framework.Resource

open FormalRV.Framework

/-! ## (1) Purpose-tagged ancilla budget

    All ancilla qubits come from the `RequestFreshAncilla` syscall, but they
    serve distinct purposes.  Tagging them makes the accounting auditable: a
    verifier checks each purpose's rule independently. -/

/-- Ancilla qubits broken down by PURPOSE.  `total` is what the architecture
    actually requests; the tags let an audit attribute each qubit. -/
structure AncillaBudget where
  /-- syndrome-extraction ancilla (≈ one per stabilizer parity check). -/
  syndrome : Nat
  /-- qubit-routing / transport ancilla. -/
  routing  : Nat
  /-- lattice-surgery gadget ancilla (merge regions / Θ(w) systems). -/
  surgery  : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The total ancilla requested = sum over purposes. -/
def AncillaBudget.total (a : AncillaBudget) : Nat :=
  a.syndrome + a.routing + a.surgery

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
    `n_logical` for the per-logical routing term. -/
structure CostModel where
  /-- Human-readable tag (mirrors `SpaceTimeInvariant.name`). -/
  name    : String
  /-- code-cycles to execute one logical Toffoli, from the code. -/
  tauToff : QECCode → Nat
  /-- DATA physical qubits per logical qubit, from the code. -/
  physPer : QECCode → Nat
  /-- purpose-tagged routing/ancilla footprint:
      `code → workload → op_weight → parallel → AncillaBudget`. -/
  ancilla : QECCode → Workload → Nat → Nat → AncillaBudget
  /-- magic-state factory footprint, from the code. -/
  factory : QECCode → Nat

/-- Build the existing `Architecture` record from a model + workload + code + the
    measured operator's weight + the parallel-PPM count.  The flat
    `ancilla_qubits` field receives the budget's `total`; everything downstream
    (`estimate`, `totalTime`, `totalQubits`, monotonicity) is reused unchanged. -/
def CostModel.toArch (m : CostModel) (w : Workload) (c : QECCode)
    (op_weight parallel : Nat) : Architecture :=
  { tau_toff_cycles  := m.tauToff c
    phys_per_logical := m.physPer c
    ancilla_qubits   := (m.ancilla c w op_weight parallel).total
    factory_qubits   := m.factory c }

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
    data + syndrome + routing + surgery + factory. -/
theorem estimateWith_qubits_tagged (m : CostModel) (hw : Hardware) (w : Workload)
    (c : QECCode) (op_weight parallel : Nat) :
    (estimateWith m hw w c op_weight parallel).qubits
      = w.n_logical * m.physPer c
        + (m.ancilla c w op_weight parallel).syndrome
        + (m.ancilla c w op_weight parallel).routing
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

/-! ## (4) Instance: SURFACE CODE — ROUTING dominates, area-scaling,
    weight-INDEPENDENT.

    Per-logical patch (`physPer = physPerLogical`, which already bundles the
    in-patch syndrome-measure qubits).  The extra footprint is a ROUTING region
    of ≈ one more patch per logical (the surface "~2×"); syndrome is bundled in
    the patch (tagged 0 here) and there is no separate surgery system.
    (gidney-ekera-2021 §2.14 + Fig. 8: 2(d+1)² per logical; Litinski 2019: ~1.5–2×.) -/
def surfaceModel (factory : Nat) : CostModel :=
  { name    := "surface-code lattice surgery (routing area-scaling, ~2x)"
    tauToff := fun c => c.d
    physPer := fun c => physPerLogical c
    ancilla := fun c w _ _ =>
      { syndrome := 0                               -- bundled in the patch (physPer)
        routing  := w.n_logical * physPerLogical c  -- ~1 extra patch-area per logical
        surgery  := 0 }                             -- merge region lives in the routing area
    factory := fun _ => factory }

/-! ## (5) Instance: qLDPC CODE — SURGERY scales with operator WEIGHT,
    area-INDEPENDENT; SYNDROME = explicit parity-check count.

    The data block packs `k` logicals into `n` DATA qubits, so
    `physPer = ⌈n/k⌉`.  SYNDROME ancilla = `|hx| + |hz|` (one per parity check —
    read straight from the code's check matrices).  SURGERY ancilla =
    `parallel · op_weight` (Θ(w) per measured operator, coefficient 1 matching
    `cross_2025_ancilla_per_weight`, summed over parallel PPMs), and it does NOT
    see the code's area `n`.  ROUTING is minimal (qLDPC needs little transport;
    tagged 0 — an honest simplification).

    HONEST RESIDUES (documented, not hidden): the Θ(w) coefficient assumes good
    Tanner-graph boundary expansion (β = Θ(1); otherwise O(w·log³w), qianxu
    App. B / Cross §); a cross-block bridge adds a subleading `d` qubits. -/
def qldpcModel (factory : Nat) : CostModel :=
  { name    := "qLDPC code surgery (surgery weight-scaling, area-independent)"
    tauToff := fun c => c.d
    physPer := fun c => physPerLogical c
    ancilla := fun c _w op_weight parallel =>
      { syndrome := c.hx.length + c.hz.length       -- one ancilla per parity check
        routing  := 0                               -- minimal transport (honest residue)
        surgery  := parallel * op_weight }          -- Θ(w)·parallel  (coeff 1 = cross_2025)
    factory := fun _ => factory }

/-! ## (6) The headline contrast, machine-checked — now PER PURPOSE. -/

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

/-- Surface ROUTING ancilla scales with DATA AREA: `n_logical · physPerLogical c`,
    proportional to the patch size and the logical count — and INDEPENDENT of the
    measured operator's weight (contrast `qldpc_surgery_eq`). -/
theorem surface_routing_area_scaling (factory : Nat) (c : QECCode) (w : Workload)
    (op_weight parallel : Nat) :
    ((surfaceModel factory).ancilla c w op_weight parallel).routing
      = w.n_logical * physPerLogical c := rfl

/-- Surface has NO weight-scaling surgery ancilla (it is 0). -/
theorem surface_surgery_zero (factory : Nat) (c : QECCode) (w : Workload)
    (op_weight parallel : Nat) :
    ((surfaceModel factory).ancilla c w op_weight parallel).surgery = 0 := rfl

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

/-! ### End-to-end smokes: the instances are corollaries of the general theorem
    by `rfl` (no new proof effort). -/

/-- qLDPC end-to-end qubit composition, tagged by purpose (instance of
    `estimateWith_qubits_tagged`): data + syndrome(=|hx|+|hz|) + 0 + Θ(w)·p + factory. -/
example (hw : Hardware) (w : Workload) (c : QECCode) (ow p : Nat) :
    (estimateWith (qldpcModel 2565) hw w c ow p).qubits
      = w.n_logical * physPerLogical c + (c.hx.length + c.hz.length) + 0 + p * ow + 2565 := by
  simp only [estimateWith_qubits_tagged, qldpcModel]

/-- Surface end-to-end qubit composition: data + 0 + (n_logical·phys routing) + 0
    + factory = the area-scaling ~2× footprint, with NO weight term. -/
example (hw : Hardware) (w : Workload) (c : QECCode) (ow p : Nat) :
    (estimateWith (surfaceModel 2565) hw w c ow p).qubits
      = w.n_logical * physPerLogical c + 0 + w.n_logical * physPerLogical c + 0 + 2565 := by
  simp only [estimateWith_qubits_tagged, surfaceModel]

end FormalRV.Framework.Resource
