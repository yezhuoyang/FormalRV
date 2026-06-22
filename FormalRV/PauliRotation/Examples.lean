/-
  FormalRV.PauliRotation.Examples
  ───────────────────────────────
  Worked examples of PARALLEL Pauli rotations expressed SYNTACTICALLY:
  a `RotLayer` is a list of rotations whose axes pairwise commute
  (`RotLayer.wf` checks this by the structural test `commF`), and a
  well-formed layer is ONE unit of parallel logical depth.

  Every claim below closes by `decide` on the concrete syntax tree — a
  skeptic can `#eval` `RotLayer.wf` / `depth` / `countPi8` on any of these
  programs without reading a proof.

  HONESTY: these anchors witness SYNTACTIC parallelism (pairwise
  commutation) plus the counters.  The `commF` ⇒ matrix-commutation bridge
  they once waited on is PROVEN (CommBridge.lean `axisMat_comm_of_commF`,
  `Rot.denote_swap`); Scheduler.lean carries it to the verified ASAP
  parallelizer (`scheduleList_denote`), and PushRules.lean to the Litinski
  anticommuting push.
-/
import FormalRV.PauliRotation.Compiler.GateDictionary

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource

/-! ## Example 1 — transversal T: four π/8 rotations in ONE layer.

Disjoint supports always commute, so a "T on every qubit" round is depth 1:

      q0 ──[ Z_{π/8} ]──
      q1 ──[ Z_{π/8} ]──     one layer,
      q2 ──[ Z_{π/8} ]──     depth 1, T-count 4
      q3 ──[ Z_{π/8} ]──
-/

def transversalT4 : RotProg :=
  [[⟨false, .piEighth, [⟨0, .z⟩]⟩,
    ⟨false, .piEighth, [⟨1, .z⟩]⟩,
    ⟨false, .piEighth, [⟨2, .z⟩]⟩,
    ⟨false, .piEighth, [⟨3, .z⟩]⟩]]

example : RotProg.wf transversalT4 = true := by decide
example : rotDepth transversalT4 = 1 := by decide
example : countPi8 transversalT4 = 4 := by decide
example : RotProg.width transversalT4 = 4 := by decide

/-! ## Example 2 — overlapping but commuting: XX ∥ ZZ on the SAME qubits.

Parallelism is NOT just disjointness: `X[0]X[1]` and `Z[0]Z[1]` anticommute
at BOTH positions, so they commute overall (even overlap count) — the
[[4,2,2]]-style stabilizer pair as one parallel Clifford layer:

      q0 ──┤ X_{π/4} ├──┤ Z_{−π/4} ├──      both boxes in the SAME
      q1 ──┤ X_{π/4} ├──┤ Z_{−π/4} ├──      time step: depth 1
-/

def xxzzLayer : RotProg :=
  [[⟨false, .piQuarter, [⟨0, .x⟩, ⟨1, .x⟩]⟩,
    ⟨true,  .piQuarter, [⟨0, .z⟩, ⟨1, .z⟩]⟩]]

example : RotProg.wf xxzzLayer = true := by decide
example : rotDepth xxzzLayer = 1 := by decide

/-! ## Example 3 — a whole CNOT is ONE layer.

The three rotations of `CNOT(c,t) = (Z_c X_t)_{π/4} (Z_c)_{−π/4} (X_t)_{−π/4}`
MUTUALLY COMMUTE (`Z_cX_t` meets `Z_c` on qubit `c` with EQUAL kinds, and
`X_t` on qubit `t` with equal kinds), so the sequential `cnotGate` (depth 3)
regroups into a single parallel layer (depth 1):

      q0 ──┤ Z      ├──┤ Z_{−π/4} ├──────────────        ⎫ all three in
      q1 ──┤ X_{π/4}├──────────────┤ X_{−π/4} ├──        ⎭ one time step
-/

def cnotLayer (c t : Nat) : RotProg :=
  [[⟨false, .piQuarter, mk2 c .z t .x⟩,
    ⟨true,  .piQuarter, [⟨c, .z⟩]⟩,
    ⟨true,  .piQuarter, [⟨t, .x⟩]⟩]]

example : RotProg.wf (cnotLayer 0 1) = true := by decide
example : rotDepth (cnotLayer 0 1) = 1 := by decide   -- vs. rotDepth (cnotGate 0 1) = 3
example : rotDepth (cnotGate 0 1) = 3 := by decide

/-! ## Example 4 — two CNOTs side by side: SIX rotations, ONE layer.

`CNOT(0,1) ∥ CNOT(2,3)`: the two triples act on disjoint pairs, and within
each triple the rotations commute (Example 3) — so all six rotations form a
single well-formed parallel layer. -/

def twoCnotLayer : RotProg :=
  [[⟨false, .piQuarter, mk2 0 .z 1 .x⟩,
    ⟨true,  .piQuarter, [⟨0, .z⟩]⟩,
    ⟨true,  .piQuarter, [⟨1, .x⟩]⟩,
    ⟨false, .piQuarter, mk2 2 .z 3 .x⟩,
    ⟨true,  .piQuarter, [⟨2, .z⟩]⟩,
    ⟨true,  .piQuarter, [⟨3, .x⟩]⟩]]

example : RotProg.wf twoCnotLayer = true := by decide
example : rotDepth twoCnotLayer = 1 := by decide

/-! ## Example 5 — the CCZ phase polynomial: seven π/8 rotations, ONE layer.

All seven axes are Z-type (Z-type products always pairwise commute), so the
entire non-Clifford content of a Toffoli is a single parallel layer —
`cczLayer` from `Compile.lean`:

      q0 ──[Z]────[Z·Z]──[Z·Z]────────[Z·Z·Z]──
      q1 ──[Z]────[Z·Z]──────────[Z·Z]─[Z·Z·Z]──   depth 1, T-count 7
      q2 ──[Z]───────────[Z·Z]───[Z·Z]─[Z·Z·Z]──   (gate-by-gate: depth 7)
            π/8    −π/8   −π/8    −π/8    π/8
-/

example : RotProg.wf (cczLayer 0 1 2) = true := by decide
example : rotDepth (cczLayer 0 1 2) = 1 := by decide
example : countPi8 (cczLayer 0 1 2) = 7 := by decide

/-! ## Example 6 — what parallelism REJECTS: anticommuting rotations.

`X[0]` and `Z[0]` overlap at one qubit with different kinds (odd count), so
they anticommute — NOT simultaneously executable, and the wf-checker says so: -/

example : RotLayer.wf
    [⟨false, .piEighth, [⟨0, .x⟩]⟩, ⟨false, .piEighth, [⟨0, .z⟩]⟩] = false := by
  decide

/-- The same two rotations ARE expressible sequentially (two layers). -/
example : RotProg.wf
    [[⟨false, .piEighth, [⟨0, .x⟩]⟩], [⟨false, .piEighth, [⟨0, .z⟩]⟩]] = true := by
  decide

/-! ## Example 7 — a small program mixing parallel layers.

Round 1: transversal T on qubits 0,1; Round 2: the XX∥ZZ Clifford pair;
Round 3: a single S†.  Three layers — depth 3, T-count 2: -/

def mixedProg : RotProg :=
  [[⟨false, .piEighth, [⟨0, .z⟩]⟩, ⟨false, .piEighth, [⟨1, .z⟩]⟩],
   [⟨false, .piQuarter, [⟨0, .x⟩, ⟨1, .x⟩]⟩,
    ⟨true,  .piQuarter, [⟨0, .z⟩, ⟨1, .z⟩]⟩],
   [⟨true,  .piQuarter, [⟨1, .z⟩]⟩]]

example : RotProg.wf mixedProg = true := by decide
example : rotDepth mixedProg = 3 := by decide
example : countPi8 mixedProg = 2 := by decide
example : countRot mixedProg = 5 := by decide

end FormalRV.PauliRotation
