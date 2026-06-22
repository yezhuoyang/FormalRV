/-
  FormalRV.QEC.LatticeSurgery.ConjugationWeld
  -------------------------------------------
  **★ A GENERAL, REUSABLE CONJUGATION-WELD RULE — `V ; M ; V†` faithfully
  realizes `M_{V P V†}` for ANY verified Clifford `V` and native measurement
  `M`. ★**

  `FaithfulMixedMerge` proved ONE gadget (the `H`-conjugated Z-merge).  But the
  pattern is general: a non-native measurement `M_P` is realized faithfully by
  conjugating a NATIVE measurement with a verified Clifford that rotates the
  basis.  This file extracts the REUSABLE machinery so every such gadget is a
  uniform INSTANCE, not a bespoke construction:

    * `weld2`/`weld2Surf` — weld `gate ; core` (for a conjugated READOUT);
    * `weld3`/`weld3Surf` — weld `gate ; core ; gate` (for a conjugated MERGE);
  both package `weldK` + `weldSurfP` (sequential weld + flow-product threading).

  THE RULE (one decidable certificate per instance, ONE construction for all):
  build the conjugation with `weld2`/`weld3` from VERIFIED pieces, thread the
  composite stabilizer flows as PRODUCTS of generator flows (`fm` maps), and
  `LaSCorrectFull` certifies the result.  Instantiated here on TWO gadgets from
  the SAME combinators:
    * the `H`-conjugated Z-merge `M_{X₁Z₂}` (= the `FaithfulMixedMerge` diagram,
      now shown to BE `weld3` of its pieces, `mixLaS_is_weld3` by `rfl`);
    * the `S`-conjugated readout `M_Y = S ; M_X` (`yReadWeld_correct`, NEW).
  Adding the weight-3 mixed merge, `M_{Y₁Z₂}`, etc. is the same two lines.
-/
import FormalRV.QEC.LatticeSurgery.FaithfulMixedMerge

namespace FormalRV.QEC.LaSre

/-! ## §1. THE GENERAL COMBINATORS (reusable for any conjugation weld). -/

/-- **`weld2`** — sequential weld `gate G ; core M` (G on `k<kG`, M above),
welding the worldlines in `conn`.  The conjugated-READOUT builder. -/
def weld2 (kG : Nat) (G M : LaSre) (conn : List (Nat × Nat)) : LaSre :=
  weldK kG G M conn

/-- The welded surface for `weld2`, threading each composite flow as a PRODUCT of
generator flows on each half (`fmG` for the gate, `fmM` for the core). -/
def weld2Surf (kG : Nat) (SG SM : Surf) (fmG fmM : Nat → List Nat) : Surf :=
  weldSurfP kG SG SM fmG fmM

/-- **`weld3`** — sequential weld `gate A ; core M ; gate C` (the conjugated-MERGE
builder): `A` on `k<kA`, `M` on `[kA,kB)`, `C` above `kB`. -/
def weld3 (kA kB : Nat) (A M C : LaSre) (conn : List (Nat × Nat)) : LaSre :=
  weldK kB (weldK kA A M conn) C conn

/-- The welded surface for `weld3`: thread `A`'s flows up through `M`
(`fmA`,`fmM`), then copy that composite and thread up through `C` (`fmC`). -/
def weld3Surf (kA kB : Nat) (SA SM SC : Surf) (fmA fmM fmC : Nat → List Nat) : Surf :=
  weldSurfP kB (weldSurfP kA SA SM fmA fmM) SC (fun s => [s]) fmC

/-! ## §2. INSTANCE 1 — the `H`-conjugated Z-merge IS `weld3` of its pieces.

  The `FaithfulMixedMerge` diagram, built ad hoc, is DEFINITIONALLY the general
  `weld3`/`weld3Surf` applied to `[layerA, Z-merge, layerA]` — so its proven
  correctness is the general rule at work, not a special case. -/

theorem mixLaS_is_weld3 :
    mixLaS = weld3 3 6 layerA FormalRV.QEC.Gidney21.mergeZLaS layerA mixConn := rfl

theorem mixSurf_is_weld3Surf :
    mixSurf = weld3Surf 3 6 layerASurf FormalRV.QEC.Gidney21.mergeZSurf layerASurf
                fmLayer fmMerge fmLayer := rfl

/-- **★ THE GENERAL `weld3` RULE, CERTIFIED ON THE MIXED MERGE ★** — `weld3` of
the verified `[H∥idle, Z-merge, H∥idle]`, surface threaded by `weld3Surf`,
passes the complete `LaSCorrectFull` against `X̄₁Z̄₂`.  (Same theorem as
`faithfulMixedMerge_fully_correct`, now read through the general combinator.) -/
theorem weld3_mixedMerge_correct :
    LaSCorrectFull
      (weld3 3 6 layerA FormalRV.QEC.Gidney21.mergeZLaS layerA mixConn)
      (weld3Surf 3 6 layerASurf FormalRV.QEC.Gidney21.mergeZSurf layerASurf
        fmLayer fmMerge fmLayer)
      mixPorts mixPaulis 3 = true :=
  faithfulMixedMerge_fully_correct

/-! ## §3. INSTANCE 2 — the `S`-conjugated readout `M_Y = S ; M_X` (NEW).

  `sLaS` realizes `X̄→Ȳ`, `Z̄→Z̄`; so its product flow `[0,1]` realizes `Ȳ→X̄`
  (`Y = XZ` up to phase).  Welding `S` to an idle readout worldline (the native
  `X`-measurement boundary) gives a gadget whose INPUT is `Ȳ` and whose readout
  is `X` — i.e. `M_Y` done by `S` then a native `M_X`.  Built with `weld2`. -/

/-- The readout idle in the S-OUTPUT convention (z_basis J: blue=`KJ`=`Z`,
red=`KI`=`X`) — generator 1 is the `X̄` the product flow rides up to the port. -/
def memJSurf : Surf :=
  { IJ := fun _ _ _ _ => false, IK := fun _ _ _ _ => false
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KJ := fun s i j _ => s == 0 && i == 0 && j == 0   -- Z̄ (blue, z_basis J)
    KI := fun s i j _ => s == 1 && i == 0 && j == 0 } -- X̄ (red)

/-- The `M_Y` diagram: `weld2 3 (S) (idle-readout)`. -/
def yReadLaS : LaSre := weld2 3 sLaS memoryLaS [(0, 0)]

/-- The composite flow 0 (`Ȳ`): the S product flow `[0,1]` (`Ȳ→X̄`) up through the
readout's `X̄` generator `[1]`. -/
def yReadSurf : Surf := weld2Surf 3 sSurf memJSurf (fun _ => [0, 1]) (fun _ => [1])

/-- Ports: `S` input at `(0,0,0)` z_basis J (the MEASURED `Ȳ`); readout output at
`(0,0,5)` z_basis J (the native `X̄` read). -/
def yReadPorts : List Port := [⟨0, 0, 0, 5, 4⟩, ⟨0, 0, 5, 5, 4⟩]

/-- Spec: flow 0 `Ȳ` at the input, `X̄` at the readout. -/
def yReadPaulis : Nat → Nat → Pauli := fun s p =>
  if s == 0 then (if p == 0 then Pauli.Y else Pauli.X) else Pauli.I

theorem yRead_report : LaSReport yReadLaS yReadSurf yReadPorts yReadPaulis 1 = [] := by
  native_decide

/-- **★ THE `S`-CONJUGATED `M_Y` READOUT IS VERIFIED LATTICE SURGERY ★** — the
welded `S ; idle-readout` diagram passes the complete `LaSCorrectFull`: its input
port carries `Ȳ` (both blue+red present), the `S` rotates it to `X̄`, read by the
native `X`-measurement boundary.  So `M_Y` is faithfully realized by `S` + a
native `M_X` — the SAME `weld2`/`weld2Surf` machinery as the mixed merge.  The
flow-level `mY1` is promoted to a verified, color-consistent readout. -/
theorem yReadWeld_correct :
    LaSCorrectFull yReadLaS yReadSurf yReadPorts yReadPaulis 1 = true := by native_decide

/-- TEETH: the same diagram does NOT realize `X̄` at the input — claiming the
measured observable is `X` (not `Y`) fails `portsOK`, because the input port's
blue piece IS present (the product flow's `Z̄` part).  So it genuinely measures
`Y`, not `X`. -/
def yReadPaulis_wrongX : Nat → Nat → Pauli := fun s _ =>
  if s == 0 then Pauli.X else Pauli.I

theorem yReadWeld_not_X :
    LaSCorrectFull yReadLaS yReadSurf yReadPorts yReadPaulis_wrongX 1 = false := by native_decide

/-! ## §4. THE GENERAL RULE — both gadgets, one construction.

  `M_{X₁Z₂}` (`weld3`, `H`-conjugated merge) and `M_Y` (`weld2`, `S`-conjugated
  readout) are built and verified by the SAME combinators (`weld2`/`weld3` =
  `weldK`+`weldSurfP`) with the SAME workflow: weld verified pieces, thread
  composite flows as products, certify with `LaSCorrectFull`.  No gadget-specific
  primitive.  Extending to the weight-3 mixed merge (`weld3 layerA mergeZ3 layerA`)
  or any `M_{V P V†}` is the same two lines + its flow maps. -/

end FormalRV.QEC.LaSre
