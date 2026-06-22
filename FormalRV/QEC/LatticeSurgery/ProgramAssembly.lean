/-
  FormalRV.QEC.LatticeSurgery.ProgramAssembly
  -------------------------------------------
  **PROGRAM-LEVEL ASSEMBLY — welding a whole gadget SEQUENCE into one spacetime
  diagram, verified by `LaSCorrectFull`.**

  The conjugation welds (`ConjugationWeld`) showed `weld3`/`weld2` assemble a
  three- or two-gadget sequence.  But those combinators are NOT conjugation-specific —
  they weld ANY gadget sequence on a shared qubit board.  This file:

    1. assembles a genuine 2-qubit MEASUREMENT PROGRAM
       (`measure Z̄₁Z̄₂ ; idle ; measure Z̄₁Z̄₂`) from the SAME `weld3`, verified
       end to end (`measProgram_correct`) — a real PPM program, one diagram;
    2. gives the GENERAL N-gadget chain `weldChain`/`weldChainSurf` (fold `weldK`
       over a list) so an arbitrary-length program is expressible;
    3. CONFRONTS the scaling wall honestly (§4): `native_decide` on the welded
       diagram is the per-instance certificate, and it does NOT scale to the
       780-gadget modexp — the missing piece is a GENERAL `weldK`-preserves-
       `LaSCorrectFull` theorem (so a long chain is certified gadget-by-gadget,
       not by one giant decision).  See the gap report at the file end.
-/
import FormalRV.QEC.LatticeSurgery.ConjugationWeld

namespace FormalRV.QEC.LaSre

open FormalRV.QEC.Gidney21 (mergeZLaS mergeZSurf)

/-! ## §1. A 2-qubit MEASUREMENT PROGRAM via `weld3` — `M_{Z₁Z₂} ; idle ; M_{Z₁Z₂}`.

  Three gadgets on `q₁=(0,0)`, `q₂=(1,0)`: a Z-merge, a 2-patch idle, a Z-merge.
  The SAME `weld3`/`weld3Surf` as the mixed merge — here with DIRECT (identity)
  flow maps on the merges and the product map `Z̄₁Z̄₂ = Z̄₁⊕Z̄₂` through the idle. -/

/-- Both worldlines welded across each interface. -/
def measConn : List (Nat × Nat) := [(0, 0), (1, 0)]

/-- Merge flow map: identity (`Z̄₁Z̄₂`, `X̄₁`, `X̄₂` pass straight). -/
def fmMergeId : Nat → List Nat := fun s => [s]

/-- Idle flow map: composite `Z̄₁Z̄₂` = idle `Z̄₁⊕Z̄₂` (gens 0,2); `X̄₁`=gen 1;
`X̄₂`=gen 3. -/
def fmIdleZZ : Nat → List Nat := fun s => if s == 0 then [0, 2] else if s == 1 then [1] else [3]

/-- The assembled program diagram: `Z-merge ; idle ; Z-merge`. -/
def measProgramLaS : LaSre := weld3 3 6 mergeZLaS parIdle mergeZLaS measConn

/-- The assembled surface (the SAME `weld3Surf`). -/
def measProgramSurf : Surf :=
  weld3Surf 3 6 mergeZSurf parIdleSurf mergeZSurf fmMergeId fmIdleZZ fmMergeId

/-- Ports: `q₁` in/out at `(0,0)`, `q₂` in/out at `(1,0)`, all blue=`KI`. -/
def measProgramPorts : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨0, 0, 8, 4, 5⟩, ⟨1, 0, 0, 4, 5⟩, ⟨1, 0, 8, 4, 5⟩]

/-- Spec: flow 0 `Z̄₁Z̄₂` (the measured joint, twice); flow 1 `X̄₁`; flow 2 `X̄₂`. -/
def measProgramPaulis : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, _ => Pauli.Z
  | 1, 0 => Pauli.X | 1, 1 => Pauli.X
  | 2, 2 => Pauli.X | 2, 3 => Pauli.X
  | _, _ => Pauli.I

theorem measProgram_report :
    LaSReport measProgramLaS measProgramSurf measProgramPorts measProgramPaulis 3 = [] := by
  native_decide

/-- **★ A 2-QUBIT MEASUREMENT PROGRAM, ASSEMBLED AND VERIFIED ★** — three real
gadgets (`Z-merge ; idle ; Z-merge`) welded by the GENERAL `weld3` into one
spacetime diagram passing the complete `LaSCorrectFull`.  So `weld3` is not
conjugation-specific: it assembles arbitrary gadget SEQUENCES on a shared qubit
board — the program-assembly primitive. -/
theorem measProgram_correct :
    LaSCorrectFull measProgramLaS measProgramSurf measProgramPorts measProgramPaulis 3 = true := by
  native_decide

/-- The assembled program is 9 steps tall (three 3-step gadgets). -/
theorem measProgram_maxK : measProgramLaS.maxK = 9 := by native_decide

/-! ## §2. THE GENERAL N-GADGET CHAIN (arbitrary-length program). -/

/-- **`weldChain`** — weld a list of uniform-height-`h` gadgets sequentially in
time: `[g₀, g₁, …]` ↦ `g₀` (bottom) welded to the chain of the rest, each across
`conn`.  An arbitrary-length program is `weldChain h conn gadgets`. -/
def weldChain (h : Nat) (conn : List (Nat × Nat)) : List LaSre → LaSre
  | []        => memoryLaS
  | [g]       => g
  | g :: rest => weldK h g (weldChain h conn rest) conn

/-- The matching surface chain: thread each gadget's flows up (DIRECT maps here;
product maps are supplied per-gadget for non-idle threading, as in §1). -/
def weldChainSurf (h : Nat) : List Surf → Surf
  | []        => idSurf
  | [s]       => s
  | s :: rest => weldSurf h s (weldChainSurf h rest) (fun x => (x, x))

/-- A 4-gadget chain is `4·h` tall — the machinery scales to any length. -/
theorem weldChain_len4_maxK (h : Nat) (g : LaSre) (conn : List (Nat × Nat))
    (hg : g.maxK = h) :
    (weldChain h conn [g, g, g, g]).maxK = 4 * h := by
  simp [weldChain, weldK, hg]; ring

/-! ## §3. A 6-step single-qubit idle chain — `weldChain` certified. -/

def idleChain : LaSre := weldChain 3 [(0, 0)] [memoryLaS, memoryLaS]
def idleChainSurf : Surf := weldChainSurf 3 [idSurf, idSurf]
def idleChainPorts : List Port := [⟨0, 0, 0, 4, 5⟩, ⟨0, 0, 5, 4, 5⟩]
def idleChainPaulis : Nat → Nat → Pauli := fun s _ => if s == 0 then Pauli.Z else Pauli.X

/-- **★ `weldChain` ASSEMBLES A MULTI-GADGET IDLE WORLDLINE, VERIFIED ★** — the
folded `weldK` chain passes the complete `LaSCorrectFull` for both flows. -/
theorem idleChain_correct :
    LaSCorrectFull idleChain idleChainSurf idleChainPorts idleChainPaulis 2 = true := by
  native_decide

/-! ## §4. THE SCALING WALL — what program assembly still needs.

  WHAT WORKS (verified, this file + `ConjugationWeld` + `Weld`):
    * `weld2`/`weld3`/`weldChain` assemble 2-, 3-, and N-gadget sequences into ONE
      diagram, re-verified by `LaSCorrectFull`;
    * a real 2-qubit measurement PROGRAM (`measProgram_correct`) and the
      conjugation gadgets (mixed merge, Y-readout) are all instances.

  THE WALL.  Each assembly is certified by `native_decide` on the WHOLE welded
  diagram.  That cost grows with the diagram (cubes × flows), so it does NOT
  reach the 780-gadget modexp: the grid is enormous and the decision explodes.

  THE MISSING THEOREM (the critical next piece).  A GENERAL
      `weldK_preserves_correct`:
        `LaSCorrectFull A SA ..` ∧ `LaSCorrectFull B SB ..` ∧ `interfaceOK A B ..`
          → `LaSCorrectFull (weldK kA A B conn) (weldSurf ..) ..`
  where `interfaceOK` is a SMALL decidable check on the two interface layers
  only.  With it, a length-`n` program is certified by `n` small per-gadget
  decisions + `n` small interface checks — LINEAR, not one exponential blob —
  by induction on `weldChain`.  This is THE unlock for full-modexp assembly.
  It is non-trivial (the interface cubes, which were degree-1 PORTS in `A`/`B`
  and are skipped by their `funcOK`, become interior on welding, so their parity
  is a genuinely new obligation — exactly what `interfaceOK` must capture, and
  what `memWeld_badInterface_rejected` shows is real).

  ALSO MISSING for true end-to-end (tracked elsewhere):
    * AUTOMATED placement+threading: build `weldChainSurf` flow maps and ports
      from a routed program automatically (now hand-written per assembly);
    * multi-qubit worldline routing across non-adjacent gadgets (the
      `PlacedGadgetRouting` board + channels, not yet fused with the weld);
    * the weight-3 mixed merge (`weld3 layerA mergeZ3 layerA`) and adaptive
      branch (`if c==1`) wiring;
    * the per-gadget QUANTUM-projection link (stabilizer ⇒ state evolution).
-/

end FormalRV.QEC.LaSre
