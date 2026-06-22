/-
  FormalRV.PPM.Semantics.ProgramSemantics
  ────────────────────────────────────────
  Operational (stabilizer-level) semantics for the new PPM program syntax
  (`Syntax/Program.lean`) — defined BY REUSE of the existing, already-proven
  machinery (John's directive: "I'm just changing the syntax"):

    • `c = Measure P`  steps the stabilizer by the EXISTING Gottesman update
      `apply_PPM_pos/neg` (`Semantics/PPMOperational.lean`), via the sparse →
      dense bridge `PauliProduct.toDense`, and records the outcome in slot `c`.
    • `frame P` / fired `if … == 1 then …` corrections fold into the Pauli
      frame via the frame algebra `mulF` (`Syntax/PauliAlgebra.lean`).
    • `useT[q]` / `useCCZ[a,b,c]` tick the magic audit counters.

  Measurement outcomes are nondeterministic: a run is parametrized by an
  outcome stream `ω : Nat → Bool` (slot index ↦ outcome), the standard
  branch-explicit treatment.

  §4 proves the SEMANTICS ↔ RESOURCE reconciliation: the trace lengths of an
  actual run are EXACTLY the `Resource/PPMCount.lean` counters — the counters
  honestly predict what an execution does.
-/
import FormalRV.PPM.Syntax.PauliAlgebra
import FormalRV.PPM.Semantics.PPMOperational
import FormalRV.Resource.PPMCount

namespace FormalRV.PPM.Prog

open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp
open FormalRV.Resource

/-! ## §1. Sparse → dense bridge (into the proven Gottesman machinery). -/

/-- A sparse kind as a dense single-qubit Pauli. -/
def PKind.toPauli : PKind → Pauli
  | .x => .X
  | .y => .Y
  | .z => .Z

/-- The kind a sparse product applies at qubit `i` (if any). -/
def PauliProduct.lookupK (P : PauliProduct) (i : Nat) : Option PKind :=
  (P.find? (fun f => f.qubit == i)).map (fun f => f.kind)

/-- **The sparse → dense bridge**: `X[0]Z[1]X[3]` at width `n` becomes the
positive-phase dense string `X Z I X I …` of length `n` — the representation
the proven Gottesman update consumes. -/
def PauliProduct.toDense (n : Nat) (P : PauliProduct) : PauliString :=
  ⟨Phase.plus, (List.range n).map (fun i =>
      match P.lookupK i with
      | some k => k.toPauli
      | none   => Pauli.I)⟩

@[simp] theorem PauliProduct.toDense_length (n : Nat) (P : PauliProduct) :
    (P.toDense n).ops.length = n := by
  simp [PauliProduct.toDense]

/-! ## §2. Execution state and the step function. -/

/-- The operational state of a PPM-program run: the stabilizer (reusing the
proven `PPMOp.StabilizerState`), the classical outcome trace (`outs[i]` =
outcome of slot `cᵢ`), the accumulated Pauli frame, and the magic audit. -/
structure ExecState where
  stab     : StabilizerState
  outs     : List Bool
  frame    : PauliProduct
  magicT   : Nat
  magicCCZ : Nat
  deriving Repr

/-- The initial state over a given stabilizer. -/
def ExecState.init (s : StabilizerState) : ExecState :=
  { stab := s, outs := [], frame := [], magicT := 0, magicCCZ := 0 }

/-- XOR-parity of the listed outcome slots (out-of-range reads `false`;
well-formed programs never produce them). -/
def xorParity (outs : List Bool) (par : List CVar) : Bool :=
  par.foldl (fun acc c => acc ^^ outs.getD c false) false

/-- AND of the listed outcome slots (a monomial). -/
def andParity (outs : List Bool) (mon : List CVar) : Bool :=
  mon.all (fun c => outs.getD c false)

/-- XOR of AND-monomials — the quadratic parity language `correctQ` fires
on (degree-2 monomials are intrinsic to CCZ-state injection). -/
def qParity (outs : List Bool) (mons : List (List CVar)) : Bool :=
  mons.foldl (fun acc mon => acc ^^ andParity outs mon) false

/-- One statement step at width `n`, with `outcome` the (externally chosen)
result if the statement is a measurement.  Measurement REUSES the proven
Gottesman update; corrections fold into the frame via `mulF`. -/
def stepStmt (n : Nat) (outcome : Bool) (st : ExecState) : PPMStmt → ExecState
  | .measure _ P =>
      let dense := P.toDense n
      { st with
          stab := if outcome then apply_PPM_neg st.stab dense
                  else apply_PPM_pos st.stab dense
          outs := st.outs ++ [outcome] }
  | .measureSel sel _ Pthen Pels =>
      let dense := (if xorParity st.outs sel then Pthen else Pels).toDense n
      { st with
          stab := if outcome then apply_PPM_neg st.stab dense
                  else apply_PPM_pos st.stab dense
          outs := st.outs ++ [outcome] }
  | .measureSel2 sel1 sel2 _ P00 P01 P10 P11 =>
      let chosen :=
        if xorParity st.outs sel1 then
          (if xorParity st.outs sel2 then P11 else P10)
        else (if xorParity st.outs sel2 then P01 else P00)
      { st with
          stab := if outcome then apply_PPM_neg st.stab (chosen.toDense n)
                  else apply_PPM_pos st.stab (chosen.toDense n)
          outs := st.outs ++ [outcome] }
  | .frame P => { st with frame := mulF st.frame P }
  | .correct par thn els =>
      if xorParity st.outs par then { st with frame := mulF st.frame thn }
      else { st with frame := mulF st.frame els }
  | .correctQ mons thn els =>
      if qParity st.outs mons then { st with frame := mulF st.frame thn }
      else { st with frame := mulF st.frame els }
  | .useT _ => { st with magicT := st.magicT + 1 }
  | .useCCZ _ _ _ => { st with magicCCZ := st.magicCCZ + 1 }

/-- Run a program at width `n` under outcome stream `ω` (slot ↦ outcome). -/
def run (n : Nat) (ω : Nat → Bool) : ExecState → PPMProg → ExecState
  | st, []     => st
  | st, s :: p => run n ω (stepStmt n (ω st.outs.length) st s) p

/-! ## §3. Structural run laws. -/

theorem run_append (n : Nat) (ω : Nat → Bool) (st : ExecState) (p q : PPMProg) :
    run n ω st (p ++ q) = run n ω (run n ω st p) q := by
  induction p generalizing st with
  | nil => rfl
  | cons s t ih =>
      show run n ω (stepStmt n (ω st.outs.length) st s) (t ++ q) = _
      exact ih _

/-! ## §4. Semantics ↔ Resource reconciliation: the counters predict the run.

These tie the INDEPENDENT `Resource/PPMCount.lean` walkers to what an actual
execution does — the trace lengths of a run are exactly the counted numbers,
for EVERY outcome stream. -/

private theorem stepStmt_outs_length (n : Nat) (b : Bool) (st : ExecState)
    (s : PPMStmt) :
    (stepStmt n b st s).outs.length = st.outs.length + countMeasS s := by
  cases s with
  | measure dst P => simp [stepStmt, countMeasS]
  | measureSel sel dst Pt Pe =>
      by_cases h : xorParity st.outs sel = true <;> simp [stepStmt, countMeasS, h]
  | measureSel2 sel1 sel2 dst P00 P01 P10 P11 =>
      by_cases h1 : xorParity st.outs sel1 = true <;>
        by_cases h2 : xorParity st.outs sel2 = true <;>
        simp [stepStmt, countMeasS, h1, h2]
  | correctQ mons thn els =>
      by_cases h : qParity st.outs mons = true <;> simp [stepStmt, countMeasS, h]
  | frame P => simp [stepStmt, countMeasS]
  | correct par thn els =>
      by_cases h : xorParity st.outs par = true <;> simp [stepStmt, countMeasS, h]
  | useT q => simp [stepStmt, countMeasS]
  | useCCZ a b c => simp [stepStmt, countMeasS]

/-- **A run records exactly `countMeas p` outcomes** (for every outcome stream
and start state) — the measurement counter is the run's trace length. -/
theorem run_outs_length (n : Nat) (ω : Nat → Bool) (st : ExecState) (p : PPMProg) :
    (run n ω st p).outs.length = st.outs.length + countMeas p := by
  induction p generalizing st with
  | nil => simp [run, countMeas]
  | cons s t ih =>
      show (run n ω (stepStmt n (ω st.outs.length) st s) t).outs.length = _
      rw [ih, stepStmt_outs_length]
      show st.outs.length + countMeasS s + countMeas t
          = st.outs.length + (countMeasS s + countMeas t)
      omega

private theorem stepStmt_magicT (n : Nat) (b : Bool) (st : ExecState) (s : PPMStmt) :
    (stepStmt n b st s).magicT = st.magicT + countMagicTS s := by
  cases s with
  | measure dst P => simp [stepStmt, countMagicTS]
  | measureSel sel dst Pt Pe =>
      by_cases h : xorParity st.outs sel = true <;> simp [stepStmt, countMagicTS, h]
  | measureSel2 sel1 sel2 dst P00 P01 P10 P11 =>
      by_cases h1 : xorParity st.outs sel1 = true <;>
        by_cases h2 : xorParity st.outs sel2 = true <;>
        simp [stepStmt, countMagicTS, h1, h2]
  | correctQ mons thn els =>
      by_cases h : qParity st.outs mons = true <;> simp [stepStmt, countMagicTS, h]
  | frame P => simp [stepStmt, countMagicTS]
  | correct par thn els =>
      by_cases h : xorParity st.outs par = true <;> simp [stepStmt, countMagicTS, h]
  | useT q => simp [stepStmt, countMagicTS]
  | useCCZ a b c => simp [stepStmt, countMagicTS]

/-- **A run consumes exactly `countMagicT p` T states.** -/
theorem run_magicT (n : Nat) (ω : Nat → Bool) (st : ExecState) (p : PPMProg) :
    (run n ω st p).magicT = st.magicT + countMagicT p := by
  induction p generalizing st with
  | nil => simp [run, countMagicT]
  | cons s t ih =>
      show (run n ω (stepStmt n (ω st.outs.length) st s) t).magicT = _
      rw [ih, stepStmt_magicT]
      show st.magicT + countMagicTS s + countMagicT t
          = st.magicT + (countMagicTS s + countMagicT t)
      omega

private theorem stepStmt_magicCCZ (n : Nat) (b : Bool) (st : ExecState) (s : PPMStmt) :
    (stepStmt n b st s).magicCCZ = st.magicCCZ + countMagicCCZS s := by
  cases s with
  | measure dst P => simp [stepStmt, countMagicCCZS]
  | measureSel sel dst Pt Pe =>
      by_cases h : xorParity st.outs sel = true <;> simp [stepStmt, countMagicCCZS, h]
  | measureSel2 sel1 sel2 dst P00 P01 P10 P11 =>
      by_cases h1 : xorParity st.outs sel1 = true <;>
        by_cases h2 : xorParity st.outs sel2 = true <;>
        simp [stepStmt, countMagicCCZS, h1, h2]
  | correctQ mons thn els =>
      by_cases h : qParity st.outs mons = true <;> simp [stepStmt, countMagicCCZS, h]
  | frame P => simp [stepStmt, countMagicCCZS]
  | correct par thn els =>
      by_cases h : xorParity st.outs par = true <;> simp [stepStmt, countMagicCCZS, h]
  | useT q => simp [stepStmt, countMagicCCZS]
  | useCCZ a b c => simp [stepStmt, countMagicCCZS]

/-- **A run consumes exactly `countMagicCCZ p` CCZ states.** -/
theorem run_magicCCZ (n : Nat) (ω : Nat → Bool) (st : ExecState) (p : PPMProg) :
    (run n ω st p).magicCCZ = st.magicCCZ + countMagicCCZ p := by
  induction p generalizing st with
  | nil => simp [run, countMagicCCZ]
  | cons s t ih =>
      show (run n ω (stepStmt n (ω st.outs.length) st s) t).magicCCZ = _
      rw [ih, stepStmt_magicCCZ]
      show st.magicCCZ + countMagicCCZS s + countMagicCCZ t
          = st.magicCCZ + (countMagicCCZS s + countMagicCCZ t)
      omega

/-! ## §5. Smoke: running the T-teleport skeleton shape. -/

example :
    (run 2 (fun _ => false) (ExecState.init [])
       [.useT 1, .measure 0 [⟨0, .z⟩, ⟨1, .z⟩], .correct [0] [⟨1, .x⟩] []]).magicT
      = 1 := by
  rw [run_magicT]
  rfl

example :
    (run 2 (fun _ => true) (ExecState.init [])
       [.useT 1, .measure 0 [⟨0, .z⟩, ⟨1, .z⟩], .correct [0] [⟨1, .x⟩] []]).outs
      = [true] := rfl

end FormalRV.PPM.Prog
