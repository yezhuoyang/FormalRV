# PPM — the Pauli-Product-Measurement layer

Logical computation expressed as sequences of **Pauli-product measurements**
(Litinski-style). It builds the Pauli algebra from first principles, the
Gottesman stabilizer-update semantics of a single PPM, a compiler lowering the
arithmetic `Gate` IR into PPM programs, an honest magic-state-factory / Gidney
measurement-AND model, and a matrix-level stabilizer-PVM / logical-state model.
The layer sits *above* the QEC/backend SysCall layer and *below* the
logical-circuit arithmetic layer; it deliberately does not model decoders, code
distance, or fault tolerance.

The canonical front-end is **the PPM program syntax** (below): outcome-binding
measurements `c2 = Measure X[0]Z[1]X[3]` plus explicit `if c2 == 1 then …`
Pauli-frame corrections. Every higher-level logical program is to be compiled
to this syntax with a correctness proof (the `Gate → PPMProg` compiler is the
in-flight Phase D; see *Status* below).

## The PPM program syntax

### Surface grammar

A program is declared once as PPM (`ppm_program name { … }`); the instructions
inside are bare. Grammar (`Syntax/Notation.lean`):

```
factor   ::=  X[n] | Y[n] | Z[n]                      -- Pauli on qubit n
product  ::=  factor+                                 -- e.g. X[0]Z[1]X[3]
stmt     ::=  cᵢ = Measure product                    -- outcome-binding PPM
           |  frame product                           -- unconditional frame update
           |  if cᵢ (^^ cⱼ)* == 1 then product else skip
           |  if cᵢ (^^ cⱼ)* == 1 then product else product
           |  useT[q]                                 -- consume one T state on qubit q
           |  useCCZ[a,b,c]                           -- consume one CCZ state on a,b,c
program  ::=  ppm_program name { stmt (; stmt)* }     -- command: def name : PPMProg := …
           |  ppm! { stmt (; stmt)* }                 -- term form, for inline use
```

Conditions are the **XOR-parity of bound outcome slots** — `if c0 ^^ c2 == 1`
covers both single-outcome corrections and the multi-outcome parity
corrections lattice surgery needs. The notation is a paper-thin macro: it
elaborates to a plain syntax tree and is never load-bearing (round-trip `rfl`
smokes in `Syntax/Notation.lean` §4).

### The IR (`Syntax/Program.lean` — the leaf, **zero imports**)

A sparse Pauli product lists its non-identity factors in strictly increasing
qubit order (identity factors are unrepresentable by construction):

```lean
/-- A non-identity single-qubit Pauli kind (sparse products never mention `I`). -/
inductive PKind where
  | x | y | z

/-- One factor of a sparse Pauli product: `X[3]` = `⟨3, .x⟩`. -/
structure PFactor where
  qubit : Nat
  kind  : PKind

/-- A sparse logical Pauli product, e.g. `X[0]Z[1]X[3]`. -/
abbrev PauliProduct := List PFactor

/-- Strictly-increasing qubit indices (canonical sparse representation). -/
def sortedStrict : PauliProduct → Bool
  | []           => true
  | [_]          => true
  | a :: b :: t  => decide (a.qubit < b.qubit) && sortedStrict (b :: t)

/-- SPACE of a product: the largest qubit index it touches, plus one. -/
def PauliProduct.width : PauliProduct → Nat
  | []      => 0
  | f :: t  => max (f.qubit + 1) (PauliProduct.width t)
```

Statements and programs (`CVar := Nat` is a classical outcome slot,
pretty-printed `c0, c1, …`):

```lean
inductive PPMStmt where
  /-- `c<dst> = Measure P` — measure the Pauli product `P`, binding the ±1
  outcome to classical slot `dst`. -/
  | measure (dst : CVar) (P : PauliProduct)
  /-- `frame P` — unconditional Pauli-frame update by `P`. -/
  | frame (P : PauliProduct)
  /-- `if c_{i₁} ^^ … ^^ c_{iₖ} == 1 then thn else els` — conditional
  Pauli-frame correction on the XOR-parity of the listed outcomes
  (`els = []` renders as `skip`). -/
  | correct (parity : List CVar) (thn els : PauliProduct)
  /-- `useT[q]` — inject (consume) one T magic state on logical qubit `q`. -/
  | useT (q : Nat)
  /-- `useCCZ[a,b,c]` — inject one CCZ magic state on logical qubits `a,b,c`. -/
  | useCCZ (a b c : Nat)

/-- A PPM program: a list of statements, executed in order. -/
abbrev PPMProg := List PPMStmt
```

Well-formedness is decidable: slots bind **sequentially** from `c0`, every
correction references only already-bound outcomes, every product is canonical
and nonempty, CCZ targets are distinct:

```lean
def PPMStmt.binds : PPMStmt → Nat
  | .measure .. => 1
  | _           => 0

def PPMStmt.wfAt (bound : Nat) : PPMStmt → Bool
  | .measure dst P       => decide (dst = bound) && sortedStrict P && !P.isEmpty
  | .frame P             => sortedStrict P && !P.isEmpty
  | .correct par thn els =>
      !par.isEmpty && par.all (fun c => decide (c < bound))
        && sortedStrict thn && !thn.isEmpty && sortedStrict els
  | .useT _              => true
  | .useCCZ a b c        => decide (a ≠ b) && decide (a ≠ c) && decide (b ≠ c)

def PPMProg.wfFrom : Nat → PPMProg → Bool
  | _,     []     => true
  | bound, s :: p => s.wfAt bound && PPMProg.wfFrom (bound + s.binds) p

def PPMProg.wf (p : PPMProg) : Bool := PPMProg.wfFrom 0 p
```

The honest SPACE readouts are structural walks over the same tree:
`PPMProg.width` (qubits touched — magic injections count) and
`PPMProg.cwidth` (classical outcome slots bound). Append laws
(`wfFrom_append`, `width_append`, `cwidth_append`) make programs composable.

## The semantics

### Frame algebra (`Syntax/PauliAlgebra.lean`)

A Pauli frame is a Pauli operator *up to global phase*, so the product of two
sparse products is a **sorted merge** — factors on distinct qubits interleave,
factors on the same qubit combine, equal kinds cancel (sparse products never
mention identity):

```lean
/-- Phase-free product of two non-identity Pauli kinds: equal kinds cancel to
identity (`none`); distinct kinds give the third (`X·Y ~ Z` up to phase). -/
def PKind.mulK : PKind → PKind → Option PKind
  | .x, .x => none | .y, .y => none | .z, .z => none
  | .x, .y => some .z | .y, .x => some .z
  | .x, .z => some .y | .z, .x => some .y
  | .y, .z => some .x | .z, .y => some .x

def mulF : PauliProduct → PauliProduct → PauliProduct
  | [], Q => Q
  | P, [] => P
  | a :: P, b :: Q =>
      if a.qubit < b.qubit then a :: mulF P (b :: Q)
      else if b.qubit < a.qubit then b :: mulF (a :: P) Q
      else
        match PKind.mulK a.kind b.kind with
        | none   => mulF P Q
        | some k => ⟨a.qubit, k⟩ :: mulF P Q
```

Proven (axiom-clean, `[propext, Quot.sound]`):

```lean
theorem mulF_self   (P : PauliProduct) : mulF P P = []          -- involution: P is its own inverse
theorem mulF_sorted (P Q) : sortedStrict P → sortedStrict Q → sortedStrict (mulF P Q)
theorem mulF_width  (P Q) : (mulF P Q).width ≤ max P.width Q.width
```

so the frame the executor accumulates is always a canonical sparse product on
the program's own qubits.

### Operational semantics (`Semantics/ProgramSemantics.lean`)

Defined **by reuse** of the already-proven machinery: a sparse product is sent
through the dense bridge into the existing Gottesman stabilizer update
(`apply_PPM_pos/neg`, `Semantics/PPMOperational.lean`); corrections fold into
the frame via `mulF`. Measurement outcomes are nondeterministic, so a run is
parametrized by an outcome stream `ω : Nat → Bool` (slot index ↦ outcome) —
the standard branch-explicit treatment.

```lean
/-- Sparse → dense: `X[0]Z[1]X[3]` at width `n` becomes the positive-phase
dense string `X Z I X I …` the proven Gottesman update consumes. -/
def PauliProduct.toDense (n : Nat) (P : PauliProduct) : PauliString :=
  ⟨Phase.plus, (List.range n).map (fun i =>
      match P.lookupK i with
      | some k => k.toPauli
      | none   => Pauli.I)⟩

/-- The operational state of a PPM-program run. -/
structure ExecState where
  stab     : StabilizerState   -- the (reused) Gottesman stabilizer
  outs     : List Bool         -- outcome trace: outs[i] = outcome of slot cᵢ
  frame    : PauliProduct      -- the accumulated Pauli frame
  magicT   : Nat               -- magic audit
  magicCCZ : Nat

/-- XOR-parity of the listed outcome slots. -/
def xorParity (outs : List Bool) (par : List CVar) : Bool :=
  par.foldl (fun acc c => acc ^^ outs.getD c false) false

def stepStmt (n : Nat) (outcome : Bool) (st : ExecState) : PPMStmt → ExecState
  | .measure _ P =>
      let dense := P.toDense n
      { st with
          stab := if outcome then apply_PPM_neg st.stab dense
                  else apply_PPM_pos st.stab dense
          outs := st.outs ++ [outcome] }
  | .frame P => { st with frame := mulF st.frame P }
  | .correct par thn els =>
      if xorParity st.outs par then { st with frame := mulF st.frame thn }
      else { st with frame := mulF st.frame els }
  | .useT _ => { st with magicT := st.magicT + 1 }
  | .useCCZ _ _ _ => { st with magicCCZ := st.magicCCZ + 1 }

/-- Run a program at width `n` under outcome stream `ω`. -/
def run (n : Nat) (ω : Nat → Bool) : ExecState → PPMProg → ExecState
  | st, []     => st
  | st, s :: p => run n ω (stepStmt n (ω st.outs.length) st s) p
```

**Semantics ↔ resource reconciliation** (proven for *every* outcome stream and
start state) — the independent `Resource/` counters provably predict what an
execution does:

```lean
theorem run_append      : run n ω st (p ++ q) = run n ω (run n ω st p) q
theorem run_outs_length : (run n ω st p).outs.length = st.outs.length + countMeas p
theorem run_magicT      : (run n ω st p).magicT   = st.magicT   + countMagicT p
theorem run_magicCCZ    : (run n ω st p).magicCCZ = st.magicCCZ + countMagicCCZ p
```

### Resource counters (`FormalRV/Resource/PPMCount.lean` — top-level `Resource/`, *outside* this folder by the layering rule)

The counters import **only** the leaf IR — never a semantics, compiler, or
gadget builder — so no proof can fudge a count; a skeptic can `#eval` them on
any constructed program without reading a proof:

```lean
def countMeas     : PPMProg → Nat   -- Pauli-product measurements (dominant cost unit)
def countCorrect  : PPMProg → Nat   -- conditional-correction statements
def countMagicT   : PPMProg → Nat   -- T states consumed
def countMagicCCZ : PPMProg → Nat   -- CCZ states consumed
def countMagic    (p : PPMProg) : Nat := countMagicT p + countMagicCCZ p
```

with append laws for all of them and `cwidth_eq_countMeas` (the IR's classical
width and the counter are two independent walks, reconciled by proof).

## Example programs (with PPM diagrams)

Diagram conventions: time flows left to right; a vertical box is **one joint
Pauli-product measurement** with its tensor factor written on each wire it
touches; `─▶ cᵢ` binds the outcome; `[P if …]` is a conditional Pauli-frame
correction; `◆|T⟩` marks magic-state injection (`useT`).

### 1. T gate by magic-state teleportation (`tTeleportSkeleton`, `Syntax/Notation.lean`)

```lean
ppm_program tTeleportSkeleton {
  useT[1];
  c0 = Measure Z[0]Z[1];
  if c0 == 1 then X[1] else skip
}
```

```
                     ╔═══╗
q0 (data) ───────────╢ Z ╟───────────────────────
                     ║   ║──▶ c0
q1 ───◆|T⟩───────────╢ Z ╟───────[X if c0 = 1]───
                     ╚═══╝
      useT[1]    c0 = Measure Z[0]Z[1]
```

Machine-checked facts, all `decide`/`rfl` (`Syntax/Notation.lean` §4; the
executor facts are the `Semantics/ProgramSemantics.lean` §5 smokes, which state
the same program as its raw statement list):

```lean
example : tTeleportSkeleton.wf     = true := by decide
example : tTeleportSkeleton.width  = 2    := by decide   -- qubits
example : tTeleportSkeleton.cwidth = 1    := by decide   -- outcome slots

-- the executor consumes exactly one T state, records exactly one outcome:
example : (run 2 (fun _ => false) (ExecState.init []) tTeleportSkeleton).magicT = 1
example : (run 2 (fun _ => true)  (ExecState.init []) tTeleportSkeleton).outs = [true]
```

### 2. Parity-conditioned correction across two measurements

The multi-outcome form lattice surgery needs — the correction fires on
`c0 ^^ c1`, with both branches explicit:

```lean
ppm! { c0 = Measure X[0]X[1];
       c1 = Measure Z[1]Z[2];
       if c0 ^^ c1 == 1 then Z[0] else X[2];
       useT[2] }
```

```
        ╔═══╗
q0 ─────╢ X ╟──────────────────[Z if p = 1]──────────
        ║   ║──▶ c0   ╔═══╗
q1 ─────╢ X ╟─────────╢ Z ╟──────────────────────────
        ╚═══╝         ║   ║──▶ c1
q2 ───────────────────╢ Z ╟────[X if p = 0]───◆|T⟩───
                      ╚═══╝
                                      p := c0 ^^ c1
```

The notation is nothing but the data tree (a `rfl` smoke in
`Syntax/Notation.lean`):

```lean
example :
    (ppm! { c0 = Measure X[0]X[1];
            c1 = Measure Z[1]Z[2];
            if c0 ^^ c1 == 1 then Z[0] else X[2];
            useT[2] })
      = [PPMStmt.measure 0 [⟨0, .x⟩, ⟨1, .x⟩],
         PPMStmt.measure 1 [⟨1, .z⟩, ⟨2, .z⟩],
         PPMStmt.correct [0, 1] [⟨0, .z⟩] [⟨2, .x⟩],
         PPMStmt.useT 2] := rfl
```

so a skeptic can `#eval countMeas`, `#eval PPMProg.width`, `#eval PPMProg.wf`,
or `#eval (run …)` on it directly — no proofs required to audit the numbers.

### Status of the program layer (2026-06-10)

Done and green: the IR + notation + decidable well-formedness; the frame
algebra with canonicality (`mulF_self/sorted/width`); the stabilizer-level
executor by reuse of the proven Gottesman update; the independent counters
with the semantics↔resource reconciliation theorems. In flight (Phase C/D):
the frame-soundness theorem (deferred ≡ applied corrections), the semantic
retrofit of the teleport gadgets onto `tTeleportSkeleton`-style programs (the
*Skeleton* suffix is honest — the state-vector proof currently lives in
`Magic/MagicStateTeleport.lean` against the old formulation), the [[4,2,2]]
schedule **with** corrections, and the `Gate → PPMProg` compiler with
`compilePPM_correct` (the keystone: every higher-level logical program lands
in this syntax with a correctness proof).

## The hierarchy (restructured 2026-06-10; was 48 flat files)

| Folder | Concern | Key contents |
|---|---|---|
| `Syntax/` | **The PPM IR** — data only | `Program.lean` (**the PPM program IR**, zero imports), `Notation.lean` (`ppm_program` command + pretty-printer), `PauliAlgebra.lean` (frame algebra `mulF` + canonicality), `Core.lean` (Pauli, PauliString, PPM, the [[4,2,2]] schedule objects), `PauliSemantics.lean` (decidable Pauli algebra), `PauliOps.lean` (logical-operator claims + syntactic verifier) |
| `Semantics/` | What programs *mean* | `ProgramSemantics.lean` (**the program executor**, by reuse), `PPMDenote.lean` (state-vector denotation + PVM laws), `PPMOperational.lean` (Gottesman update), `LogicalState.lean` (matrix model), `PPMSemanticsGeneral.lean`, `StabilizerBasisBridge.lean`, `GadgetChannel.lean`, and the observation/semantic bridges to `Gate.applyNat` |
| `Rules/` | Rewrite laws | `CliffordConj.lean` / `CliffordPPMRules.lean` (Clifford conjugation of PPMs), `PPMUpdateInvariants.lean`, `EightTToCCZScheme.lean`, `ToffoliFromCCZ.lean`, `ZXSpiderFusion.lean`, `ZXStabilizer.lean` |
| `Compiler/` | Circuit → PPM lowering | `CircuitFragmentClassifierAndCompiler.lean` (`compileArithmeticGateToPPM`), `PPMCompilerCorrectness.lean`, `StabProgram.lean`, `ToffoliScheme(+Discharge).lean`, surgery-gadget / backend trace lowering |
| `Magic/` | Magic states | T/CCZ teleportation gadgets (proven at state-vector level), `GidneyAND.lean`, `CircuitToPPMMagicFactory.lean`, `CircuitToPPMToffoliMagic.lean` |
| `Resource/` | **Counters + anchored counts** | `PPMResourceCount.lean`, `CircuitToPPMResource.lean` (`numMeas`/`numTMagic`/`numCCZMagic` over compiled programs), `GateToPPMResource.lean`, `ModMultPPMResource.lean` — the program-IR counters (`countMeas` …) live at top-level `FormalRV/Resource/PPMCount.lean` by the layering rule |
| `QECBridge/` | PPM ↔ QEC interfaces | `LayeredPPMQECInterface.lean`, `FactoryHierarchy.lean`, `CircuitToPPMFactoryProvision.lean` |
| `Pipeline/` | End-to-end assemblies | `PPMShorPipeline.lean` (success-probability transfer), `GE2021PPMSysInv.lean` (paper instantiation, derived numbers) |
| `Codegen/` | Text emission | `PPMToQASM.lean` |

Layering: `Syntax < Semantics < Rules < Compiler < Magic < Resource < QECBridge < Pipeline`.
Two back-compat stubs (`PPM/GE2021PPMSysInv.lean`, `PPM/PPMToQASM.lean`)
re-export moved modules for in-flight importers; remove after migration.

## Key definitions

- `PPMStmt` / `PPMProg` + `PPMProg.wf` (`Syntax/Program.lean`) — **the PPM program IR** (above).
- `mulF` + `mulF_self/sorted/width` (`Syntax/PauliAlgebra.lean`) — the Pauli-frame algebra.
- `run` / `stepStmt` / `ExecState` (`Semantics/ProgramSemantics.lean`) — the program executor.
- `Pauli`, `Phase`, `Pauli.mul` (`Syntax/`) — single-qubit Pauli group with `{±1,±i}` phase tracking.
- `PauliString` + `commutes` (`Syntax/Core.lean`) — n-qubit Paulis; commute iff anticommuting positions are even.
- `StabilizerState`, `apply_PPM_pos/neg` (`Semantics/PPMOperational.lean`) — the Gottesman measurement update.
- `Pauli.toMatrix` / `PauliString.toMatrix` (`Semantics/LogicalState.lean`) — complex-matrix interpretation.
- `PPMCommand`/`PPMProgram` and the `Gate → PPMProgram` compiler (`Compiler/`) — the (old-IR) lowering target.
- `TFactoryContract`, `MagicToken`, `teleportCCX` (`Magic/`) — factory + Toffoli-teleportation interfaces.
- `GidneyAND_forward/reverse` (`Magic/GidneyAND.lean`) — the measurement-AND construction.

## Resource honesty (audited 2026-06-10, all 48 files)

PPM resource counting follows the project triple — concrete syntactic object +
semantic proof + an independent counter walking **that same object**:

- The program-IR counters (`countMeas`, `countCorrect`, `countMagicT/CCZ`,
  `FormalRV/Resource/PPMCount.lean`) import ONLY the leaf IR, and the
  reconciliation theorems (`run_outs_length`, `run_magicT`, `run_magicCCZ`)
  prove they predict every execution trace.
- The old-IR counters (`numMeas`, `numTMagic`, `numCCZMagic`,
  `ppmProgramResourceSummary`, `magicRequestCount`, `count_measure`) are
  **structural walks** over the PPM IR / compiled program lists — no asserted
  constants anywhere in the layer.
- Anchored instances close by `decide` on **compiled** programs:
  `numCCZMagic (circuitToPPM 8 shor15Modmult) = 27`, `numMeas … = 81 (= 27 × 3)`,
  and the Gidney adder's `verified_adder_end_to_end` (semantic correctness **and**
  `numCCZMagic = 2(n+2)` about one Gate term — the full triple).
- `shorMagicDemand_eq_ccxCount` proves demand = the gate's CCX count by induction.
- `Pipeline/GE2021PPMSysInv` is **anti-spreadsheet**: wallclock / peak-qubits /
  distinct-qubits are `foldl`-derived from the actual SysCall schedule and
  `decide`-checked — never typed-in numbers.

## Honesty boundaries (open, explicitly fenced — do NOT cite as verified)

1. **The [[4,2,2]] surgery schedule is a syntactic placeholder, not a logical
   CNOT.** `Syntax/Core.lean` documents (with out-of-band Qiskit evidence) that
   all 5 PPMs commute with all 8 logicals, so the schedule's logical action is
   identity-like; the *emergent-CNOT* semantics is an open obligation.
   `Semantics/LogicalState.lean`'s `Code4Code4_surgery_implements_logical_CNOT`
   currently holds by `rfl` over placeholder (identity) semantics — structurally
   committed, operationally empty. (The program-syntax retrofit WITH
   corrections — Phase C — is the designated fix.)
2. **CCX/Toffoli magic injection** is an interface obligation (`teleportCCXRel`,
   `MagicInjectionObligations.CCX_ok`) — discharged structurally, not derived
   from Clifford+T teleportation; the CCZ teleport gadget is proven only on the
   `000` outcome branch.
3. **Backend alignment parameters** (`backendSummary`, `qecSpecsLowerToSchedule`,
   `specMatch`, `qecRel`) are caller-supplied: the trace lowering is
   observational (right syscalls at right qubits), not QEC-semantic.
4. `Resource/ModMultPPMResource` exposes **bounds (≤)**, not equalities, where
   the source T-count is a sizing bound; flagged in-file.
5. `Magic/GidneyAND`: the `reverse_tcount = 0` is arithmetic-only (no
   measurement-semantics equivalence proof yet).
