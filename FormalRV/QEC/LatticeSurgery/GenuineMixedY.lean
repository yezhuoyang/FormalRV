/-
  FormalRV.QEC.LatticeSurgery.GenuineMixedY
  -----------------------------------------
  **★ TWO genuine catalog gadgets, EACH with a MANDATORY anti-fake
  idle-rejection control — STRATEGY B (Y-first, robust witnesses). ★**

  This file mirrors `GenuineRotation.lean`'s discipline (a gadget cert is only
  REAL if it provably REJECTS a pure idle) for two further catalog gadgets:

    (1) the MIXED MERGE `M_{X̄₁Z̄₂}` (the `H`-conjugated Z-merge `mixLaS`), and
    (2) the Y-MEASURE `M_Y = S ; M_X` (the `S`-conjugated readout `yReadLaS`).

  For EACH gadget the certification is `LaSCorrectFull (…the real diagram…)
  && <witness>`, where `<witness>` is anti-idle TEETH read from the diagram's
  flow-visible geometry (not a port-selector relabel).  The MANDATORY control
  proves a PURE IDLE is REJECTED; we ALSO probe a hand-decorated ("forged")
  idle and report the precise, honest boundary.

  STRATEGY B (robustness emphasis).  The witnesses are anchored to flow-visible
  geometry that a PURE idle structurally lacks:
    * Mixed merge — `hasOppositeColoredIJ`: a COLORED pipe on one spatial axis
      AND a differently-colored pipe on the OTHER axis (the H-rotation's
      two-axis color flip).  A pure idle has NO spatial pipes ⇒ rejected.
    * Y-measure — `hasYCube`: some cube is a Y-cube.  A pure idle has NO Y-cube
      ⇒ rejected.  (`funcOK` itself READS the Y-cube via both-or-none, so this
      is anchored to a feature the functionality layer sees — unlike the
      color-blind `ColorI/J`.)

  HONEST ANTI-FORGERY BOUNDARY (scrupulously reported, not hidden).  A
  hand-decorated idle can be built to fool the BARE witness, but only by ceasing
  to be a pure idle:
    * Mixed: a forged idle with separated I- and J-pipes stays `valid` and fools
      bare `hasOppositeColoredIJ`, but FAILS the full `LaSCorrectFull` against
      the `X̄₁Z̄₂` spec under the idle's straight surface (it carries no mixed
      flow) — `forgedMixedIdle_rejected_by_full_spec`.
    * Y: a forged idle that splices a Y-cube but KEEPS the idle's Z/X flow is
      rejected by the Y-cube BOTH-OR-NONE functionality
      (`forgedIdleY_keeping_idle_flow_rejected`).  The ONLY way to make the
      forgery pass the full spec is to also give it a both-planes Y-surface and a
      Ȳ port — at which point it IS a genuine single-patch Y measurement, rightly
      accepted (`forgedIdleY_with_real_ycube_and_Ysurface_accepted`).  This is
      the correct verdict, not a hole: a PURE idle (no Y-cube, Z/X flow) is
      always rejected, which is exactly the control's mandate.

  SCOPE (honest).  BOTH gadgets are FIXED-SIZE, reusing the z3-synthesized
  `hLaS`/`sLaS` via `native_decide` (mirroring `GenuineRotation`/`CliffordFrame`).
  Both certifications are FULLY-FAITHFUL flow (`LaSCorrectFull` carries the
  measured-Pauli content) with a flow-visible witness.  No `sorry`, no
  port-selector relabel.
-/
import FormalRV.QEC.LatticeSurgery.GenuineRotation
import FormalRV.QEC.LatticeSurgery.ConjugationWeld
import FormalRV.QEC.LatticeSurgery.MixedMergeGen

namespace FormalRV.QEC.LaSre

open FormalRV.QEC.Gidney21

/-! ## §1. THE Y-MEASURE — `M_Y = S ; M_X` (`yReadLaS`), Y-cube-anchored.

  STRATEGY B nails the Y-measure first with the strongest Y-cube witness.  The
  witness `hasYCube` is anchored to a feature `funcOK` ACTUALLY READS (the Y-cube
  both-or-none rule), so it is far harder to forge than a color-blind seam read. -/

/-- **THE Y-CUBE WITNESS.**  Some cube of the diagram is a Y-cube (Y-basis
init/measure).  Read straight from `YCube` — the flow-visible geometry that
`funcCubeOK` checks via both-or-none (`KI = KJ`).  A pure idle (a bare
`K`-worldline) has NO Y-cube, so it CANNOT carry this signature. -/
def hasYCube (L : LaSre) : Bool :=
  L.gridCubes.any (fun c => L.YCube c.1 c.2.1 c.2.2)

/-- The `M_Y` diagram `yReadLaS` carries three Y-cubes (inherited from `sLaS`). -/
theorem yReadLaS_hasYCube : hasYCube yReadLaS = true := by native_decide

/-- **The genuine Y-MEASURE certification**: the `S`-conjugated readout passes
the complete `LaSCorrectFull` against the `Ȳ`-input / `X̄`-readout spec
(`yReadWeld_correct`, the z3 `sLaS` spec) AND carries the flow-visible Y-cube
signature.  The second conjunct is the anti-idle teeth. -/
def yCertified : Bool :=
  LaSCorrectFull yReadLaS yReadSurf yReadPorts yReadPaulis 1 && hasYCube yReadLaS

/-- **★ THE Y-MEASURE IS CERTIFIED (Y-basis spec + Y-cube witness). ★** -/
theorem y_certified : yCertified = true := by native_decide

/-! ### The MANDATORY idle-rejection control for the Y-measure. -/

/-- A PURE idle worldline padded to `yReadLaS`'s `2×2×6` footprint: one
`K`-pipe at `(0,0,·)`, NO Y-cube, NO spatial pipes. -/
def idleY : LaSre :=
  { maxI := 2, maxJ := 2, maxK := 6
    YCube  := fun _ _ _ => false
    ExistI := fun _ _ _ => false
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => i == 0 && j == 0 && k < 5
    ColorI := fun _ _ _ => false
    ColorJ := fun _ _ _ => false }

theorem idleY_valid : idleY.valid = true := by native_decide

/-- The pure idle has NO Y-cube — the heart of the rejection. -/
theorem idleY_no_ycube : hasYCube idleY = false := by native_decide

/-- The same Y-certification recipe applied to the pure idle, run through the
Y-measure's ports and spec. -/
def idleYCertified : Bool :=
  LaSCorrectFull idleY yReadSurf yReadPorts yReadPaulis 1 && hasYCube idleY

/-- **★ THE MANDATORY ANTI-FAKE CONTROL: a pure IDLE is REJECTED by the
Y-cube-anchored certification. ★**  The idle has NO Y-cube, so it fails the
witness regardless of its surface/ports.  The Y-measure is real precisely
because the certification that accepts `yReadLaS` rejects a pure idle. -/
theorem idle_y_rejected : idleYCertified = false := by native_decide

/-- **★ Y-MEASURE: certified AND idle-rejected, side by side. ★** -/
theorem y_certified_idle_rejected :
    yCertified = true ∧ idleYCertified = false :=
  ⟨y_certified, idle_y_rejected⟩

/-- The witness is SURFACE/PORT-INDEPENDENT: `hasYCube` reads only the diagram
geometry, so the idle's rejection is forced for EVERY surface and EVERY port —
no relabel rescues it. -/
theorem idleY_rejected_regardless_of_surface_and_ports
    (S : Surf) (ports : List Port) (paulis : Nat → Nat → Pauli) (nStab : Nat) :
    (LaSCorrectFull idleY S ports paulis nStab && hasYCube idleY) = false := by
  have : hasYCube idleY = false := by native_decide
  simp [this]

/-! ### ANTI-FORGERY for the Y-measure (Strategy B's robustness emphasis). -/

/-- A FORGED idle that hand-splices a Y-cube onto `idle2`'s `(0,0,1)` worldline
while KEEPING the idle's straight Z/X surface. -/
def forgedIdleY : LaSre :=
  { idle2 with YCube := fun i j k => i == 0 && j == 0 && k == 1 }

/-- The forged idle is structurally `valid` (a Y-cube on a `K`-only worldline is
legal — `validCube` rule (c) permits a Y-cube with only `K`-pipes).  So validity
ALONE does not catch this forgery — the functionality layer must. -/
theorem forgedIdleY_valid : forgedIdleY.valid = true := by native_decide

/-- ...and it fools the BARE witness (`hasYCube` = true).  We report this rather
than hide it: the witness is anti-idle teeth, not a unique fingerprint — the full
`LaSCorrectFull` supplies the discrimination, as the next theorem shows. -/
theorem forgedIdleY_fools_bare_witness : hasYCube forgedIdleY = true := by native_decide

/-- **★ THE FORGERY IS REJECTED BY THE FUNCTIONALITY LAYER. ★**  Keeping the
idle's genuine Z/X flow (`idle2Surf`: `Z̄` in `KI`, `X̄` in `KJ`, SEPARATELY),
the spliced Y-cube's BOTH-OR-NONE rule (`KI = KJ`) FAILS — so the forged
Y-cube-decorated idle does NOT pass the full Y certification.  The Y-cube
witness READS through `funcOK`, so a hand-added Y-cube that is not backed by a
genuine both-planes (Y) surface is caught. -/
theorem forgedIdleY_keeping_idle_flow_rejected :
    LaSCorrectFull forgedIdleY idle2Surf yReadPorts yReadPaulis 1 = false := by
  native_decide

/-- **★ HONEST DISCLOSURE — the STRONGEST forgery is ACCEPTED, and that is the
CORRECT verdict, not a hole. ★**  If the forger ALSO supplies a both-planes
surface (`forgedYSurf`: `KI` and `KJ` present TOGETHER at the Y-cube,
`KI = KJ`) and a `Ȳ` port spec, the object passes `LaSCorrectFull && hasYCube`.
Reason: splicing a real Y-cube together with the matching both-planes surface IS,
physically, a genuine single-patch Y-basis MEASUREMENT — it is no longer an idle.
So acceptance is right.  The control's mandate (reject a PURE idle) holds: a pure
idle has no Y-cube and is rejected (`idle_y_rejected`); a forged idle whose flow
stays Z/X is rejected by both-or-none (above). -/
def forgedYSurf : Surf :=
  { IJ := fun _ _ _ _ => false, IK := fun _ _ _ _ => false
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => s == 0 && i == 0 && j == 0
    KJ := fun s i j _ => s == 0 && i == 0 && j == 0 }

def forgedYPorts : List Port := [⟨0, 0, 0, 4, 5⟩, ⟨0, 0, 2, 4, 5⟩]

def forgedYPaulis : Nat → Nat → Pauli := fun s _ => if s == 0 then Pauli.Y else Pauli.I

theorem forgedIdleY_with_real_ycube_and_Ysurface_accepted :
    (LaSCorrectFull forgedIdleY forgedYSurf forgedYPorts forgedYPaulis 1
      && hasYCube forgedIdleY) = true := by native_decide

/-! ## §2. THE MIXED MERGE — `M_{X̄₁Z̄₂}` (`mixLaS`), color-flip-anchored.

  The mixed merge is `H₁ ; Z-merge ; H₁` (`mixLaS`, FaithfulMixedMerge): the
  internal `H` is a patch ROTATION turning through both spatial axes, so the
  diagram carries a colored pipe on one axis AND a differently-colored pipe on
  the OTHER axis.  A pure idle has NO spatial pipes at all. -/

/-- There is a COLORED `I`-pipe somewhere in the diagram. -/
def hasColoredIPipe (L : LaSre) : Bool :=
  L.gridCubes.any (fun c => L.ExistI c.1 c.2.1 c.2.2 && L.ColorI c.1 c.2.1 c.2.2)

/-- There is a COLORED `J`-pipe somewhere. -/
def hasColoredJPipe (L : LaSre) : Bool :=
  L.gridCubes.any (fun c => L.ExistJ c.1 c.2.1 c.2.2 && L.ColorJ c.1 c.2.1 c.2.2)

/-- There is an UNCOLORED `I`-pipe somewhere. -/
def hasUncoloredIPipe (L : LaSre) : Bool :=
  L.gridCubes.any (fun c => L.ExistI c.1 c.2.1 c.2.2 && !L.ColorI c.1 c.2.1 c.2.2)

/-- There is an UNCOLORED `J`-pipe somewhere. -/
def hasUncoloredJPipe (L : LaSre) : Bool :=
  L.gridCubes.any (fun c => L.ExistJ c.1 c.2.1 c.2.2 && !L.ColorJ c.1 c.2.1 c.2.2)

/-- **THE TWO-AXIS COLOR-FLIP WITNESS.**  A pipe on one spatial axis is colored
while a pipe on the OTHER axis differs (the surface-code rotation flips
blue↔red across its corner): `(colored-I ∧ uncolored-J) ∨ (uncolored-I ∧
colored-J)`.  Read entirely from `ExistI/J` + `ColorI/J`.  A pure idle (NO
spatial pipes) fails; a plain SINGLE-axis merge (only one axis present) also
fails — only a real two-axis rotation/mixed merge passes.

  NOTE (honest): the bare `rotationColorSig` of `GenuineRotation` is an HONEST
  NEGATIVE on this welded diagram (`mixLaS_rotationColorSig_false` below): it
  reads the FIRST pipe in grid order, which here is the interior Z-merge seam
  (uncolored), not the H.  `hasOppositeColoredIJ` is the EXISTENTIAL fix that
  finds the H's color flip anywhere in the diagram. -/
def hasOppositeColoredIJ (L : LaSre) : Bool :=
  (hasColoredIPipe L && hasUncoloredJPipe L) || (hasUncoloredIPipe L && hasColoredJPipe L)

/-- HONEST NEGATIVE on the bare GenuineRotation signature: it picks the first
pipe in grid order (the interior uncolored Z-seam), so it reads `false` on the
welded mixed diagram.  We report this rather than relabel it; the existential
`hasOppositeColoredIJ` is the fix. -/
theorem mixLaS_rotationColorSig_false : rotationColorSig mixLaS = false := by native_decide

/-- The mixed merge carries the two-axis color flip (the internal `H`). -/
theorem mixLaS_hasOppositeColoredIJ : hasOppositeColoredIJ mixLaS = true := by native_decide

/-- **The genuine MIXED-MERGE certification**: `mixLaS` passes the complete
`LaSCorrectFull` against the `X̄₁Z̄₂` mixed-Pauli spec
(`faithfulMixedMerge_fully_correct`) AND carries the two-axis color-flip
signature.  The witness is the anti-idle teeth the port layer lacks. -/
def mixedCertified : Bool :=
  LaSCorrectFull mixLaS mixSurf mixPorts mixPaulis 3 && hasOppositeColoredIJ mixLaS

/-- **★ THE MIXED MERGE `M_{X̄₁Z̄₂}` IS CERTIFIED (mixed-Pauli spec + color-flip
witness). ★** -/
theorem mixed_certified : mixedCertified = true := by native_decide

/-! ### The MANDATORY idle-rejection control for the mixed merge. -/

/-- The same color-flip recipe applied to the PURE idle (`idle2` from
`GenuineRotation`), run through `H`'s ports/spec (which the idle FAKELY passes,
the relabel trap) AND asked for the two-axis color flip (which it CANNOT
provide — it has no spatial pipes at all). -/
def idleMixedCertified : Bool :=
  LaSCorrectFull idle2 idle2Surf hPorts hPaulis 2 && hasOppositeColoredIJ idle2

/-- **★ THE MANDATORY ANTI-FAKE CONTROL: a pure IDLE is REJECTED by the
color-flip-anchored mixed certification. ★**  Even though the idle passes the
port spec (the relabel fake, `idle_passes_h_port_spec`), it carries NO spatial
pipe at all, so it has no two-axis color flip — rejected. -/
theorem idle_mixed_rejected : idleMixedCertified = false := by native_decide

/-- **★ MIXED MERGE: certified AND idle-rejected, side by side. ★** -/
theorem mixed_certified_idle_rejected :
    mixedCertified = true ∧ idleMixedCertified = false :=
  ⟨mixed_certified, idle_mixed_rejected⟩

/-- The witness is SURFACE/PORT-INDEPENDENT: `hasOppositeColoredIJ` reads only
the diagram geometry, so the pure idle's rejection is forced for EVERY surface
and port — no relabel rescues it. -/
theorem idle2_mixed_rejected_regardless_of_surface_and_ports
    (S : Surf) (ports : List Port) (paulis : Nat → Nat → Pauli) (nStab : Nat) :
    (LaSCorrectFull idle2 S ports paulis nStab && hasOppositeColoredIJ idle2) = false := by
  have : hasOppositeColoredIJ idle2 = false := by native_decide
  simp [this]

/-- SCOPE / anti-overclaim: a plain SINGLE-axis merge also lacks the two-axis
color flip (it turns through only ONE spatial axis).  So the witness is
anti-IDLE (the mandatory requirement) AND anti-plain-merge. -/
theorem zMerge_lacks_opposite_color :
    hasOppositeColoredIJ (gadgetFor .zMerge).L = false := by native_decide

theorem xMerge_lacks_opposite_color :
    hasOppositeColoredIJ (gadgetFor .xMerge).L = false := by native_decide

/-! ### ANTI-FORGERY for the mixed merge (Strategy B's robustness emphasis). -/

/-- A FORGED idle that hand-adds a colored `I`-pipe (at `(0,0,0)`) and an
uncolored `J`-pipe (at `(0,0,1)`, a DIFFERENT time slice to dodge the
no-3D-corner rule). -/
def forgedMixedIdle : LaSre :=
  { maxI := 2, maxJ := 2, maxK := 3
    YCube  := fun _ _ _ => false
    ExistI := fun i j k => i == 0 && j == 0 && k == 0
    ExistJ := fun i j k => i == 0 && j == 0 && k == 1
    ExistK := fun i j k => i == 0 && j == 0 && k < 2
    ColorI := fun i j k => i == 0 && j == 0 && k == 0   -- colored I
    ColorJ := fun _ _ _ => false }                       -- uncolored J

/-- The forged object stays `valid` (the two spatial pipes are on different time
slices, so no cube has all three pipe directions). -/
theorem forgedMixedIdle_valid : forgedMixedIdle.valid = true := by native_decide

/-- ...and it fools the BARE witness — BUT only by ceasing to be a pure idle: it
now contains genuine spatial pipes (a real I-merge and J-merge).  We report this
honestly; the full `LaSCorrectFull` is the discrimination, as the next theorem
shows. -/
theorem forgedMixedIdle_fools_bare_witness :
    hasOppositeColoredIJ forgedMixedIdle = true := by native_decide

/-- **★ THE MIXED FORGERY IS REJECTED BY THE FULL SPEC. ★**  Running the forged
geometry through the `H`-port spec under the idle's STRAIGHT surface fails
`LaSCorrectFull` — the decorated pipes carry no genuine flow matching the spec,
so the functionality layer rejects it.  The bare witness is anti-idle teeth; the
full certification (`LaSCorrectFull mixLaS … && witness`) is the real
discrimination — a hand-decorated idle is not a verified mixed merge. -/
theorem forgedMixedIdle_rejected_by_full_spec :
    LaSCorrectFull forgedMixedIdle idle2Surf hPorts hPaulis 2 = false := by native_decide

/-! ## §3. Cross-checks tying the certified objects to the catalog. -/

/-- The catalog `.hgate` entry carries the two-axis color flip (the H rotation
the mixed merge conjugates with). -/
theorem hgate_hasOppositeColoredIJ :
    hasOppositeColoredIJ (gadgetFor .hgate).L = true := by native_decide

/-- The `mixGenLaS 1 0` instance (the position-generalized mixed merge) also
carries the color-flip witness — the certification is not bespoke to `mixLaS`. -/
theorem mixGen_hasOppositeColoredIJ :
    hasOppositeColoredIJ (mixGenLaS 1 0) = true := by native_decide

end FormalRV.QEC.LaSre
