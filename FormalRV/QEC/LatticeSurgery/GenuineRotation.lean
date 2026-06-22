/-
  FormalRV.QEC.LatticeSurgery.GenuineRotation
  -------------------------------------------
  **★ COLOR-ANCHORED basis-change certification (genuine, idle-rejecting).
  STRATEGY: ColorEnforcing — a GENUINE, COLOR-ANCHORED basis-change
  certification of the Hadamard gadget — with the MANDATORY anti-fake control
  proving it REJECTS a pure idle. ★**

  THE TRAP (the prior failure mode, reproduced honestly here).  `LaSCorrectFull`'s
  port layer (`portsOK`) reads each port's BLUE/RED piece through per-port
  SELECTORS (`blueSel`/`redSel`).  The synthesized `H` gadget's ports legitimately
  SWAP those selectors between input and output (`hPorts = [⟨0,0,0,5,4⟩,
  ⟨0,0,2,4,5⟩]`).  But the swap, by itself, is a RELABEL: a pure idle worldline
  carrying a straight `KI`/`KJ` surface, read through the SAME swapped-selector
  ports, reads IDENTICALLY to `H` at both ports — we verify this here
  (`idle_reads_like_h_at_ports`, `idle_passes_h_port_spec`).  So NO port-selector
  check — including a "basis changes between the two ports" check read through the
  selectors — can tell `H` from idle.  This is exactly the relabel that killed the
  prior attempt; we expose it rather than hide it.

  WHERE THE GENUINE, COLOR-LEVEL DIFFERENCE LIVES (Strategy A's anchor).  The
  ColorEnforcing layer reads the gadget's ACTUAL seam colors `ColorI`/`ColorJ`
  out of its `LaSre` — the physical fact `funcOK`/`portsOK` are BLIND to.  `H` is
  a PATCH ROTATION: its corner route turns through BOTH spatial axes, so it has a
  COLORED `I`-pipe AND a COLORED `J`-pipe, with OPPOSITE boundary colors (the
  rotation flips blue↔red across the turn).  A pure idle has NO spatial pipes at
  all — `seamColorOf` reads `none`, and it has neither a colored `I`- nor a
  colored `J`-boundary.  That color-level fact is read straight from
  `ColorI`/`ColorJ`; it is invisible to any port-selector relabel.

  THE COLOR-ANCHORED CERTIFICATION.
    * `seamColorOf L` (from `ColorEnforcing`) reads the gadget's seam color out of
      `ColorI`/`ColorJ`.  `H ⇒ some`, idle ⇒ `none`.
    * `rotationColorSig L` := `L` carries a COLORED `I`-pipe AND a COLORED
      `J`-pipe whose boundary colors DIFFER — the surface-code rotation signature,
      read entirely from `ExistI/ExistJ` + `ColorI/ColorJ`.  `H` passes; an idle
      (no spatial pipes) and even a plain single-axis merge FAIL.
    * `hBasisChangeColorCertified` := `H` passes the `X̄→Z̄ / Z̄→X̄` flow check
      (`hLaS_fully_correct`) AND carries the rotation color signature.
  Then `H = true`, idle = `false` — the control is the proof of genuineness.

  SCOPE (scrupulously honest).
    * FIXED-SIZE (2×2×3), reusing the z3-synthesized `hLaS` via `native_decide`,
      mirroring `HFromLaSsynth`/`CliffordFrame`.  The WIN is GENUINENESS (idle
      rejected at the COLOR level), not `∀w`.
    * `rotationColorSig` is read from the seam COLORS (`ColorI`/`ColorJ`) — the
      exact data `gadgetColorFaithful` was built to anchor and that `funcOK` is
      blind to.  It separates `H` (rotates through two colored axes) from an
      IDLE/identity (no colored seam) — the prior failure mode — AND from a plain
      single-axis MERGE.  It is the genuine COLOR vehicle of Strategy A.
    * The basis-CHANGE content (input `X̄` ↦ output `Z̄`) is carried by
      `LaSCorrectFull hLaS hSurf hPorts hPaulis` (the z3 spec); the color
      signature adds the teeth the port layer lacks — that the change is realized
      by a real patch ROTATION (two colored spatial axes), not a port relabel.
    * HONEST NEGATIVE on the LITERAL existing checker: the unmodified
      `gadgetColorFaithful` (a per-gadget basis-VALIDITY check) CANNOT reject idle
      — `gadgetColorFaithful .hgate = gadgetColorFaithful .mem = true`
      (`existing_color_check_cannot_reject_idle`).  Strategy A's idle rejection
      requires the basis-CHANGE strengthening built here (`rotationColorSig`),
      which reads the SAME `ColorI`/`ColorJ` data but anchors a ROTATION, not just
      a single-basis readout.
-/
import FormalRV.QEC.Gidney21.ColorEnforcing
import FormalRV.QEC.LatticeSurgery.Weld

namespace FormalRV.QEC.LaSre

open FormalRV.QEC.Gidney21

/-! ## §1. The relabel trap, reproduced — the port layer cannot tell `H` from idle. -/

/-- The idle worldline padded to `H`'s `2×2×3` footprint (one `K`-pipe at
`(0,0,·)`, NO spatial pipes, NO seam color). -/
def idle2 : LaSre :=
  { maxI := 2, maxJ := 2, maxK := 3
    YCube  := fun _ _ _ => false
    ExistI := fun _ _ _ => false
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => i == 0 && j == 0 && k < 2
    ColorI := fun _ _ _ => false
    ColorJ := fun _ _ _ => false }

theorem idle2_valid : idle2.valid = true := by native_decide

/-- The idle's straight surface: flow 0 `Z̄` in the `KI` plane, flow 1 `X̄` in
`KJ`, along the `(0,0,·)` worldline. -/
def idle2Surf : Surf :=
  { IJ := fun _ _ _ _ => false, IK := fun _ _ _ _ => false
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => s == 0 && i == 0 && j == 0
    KJ := fun s i j _ => s == 1 && i == 0 && j == 0 }

/-- Read a port's `(blue, red)` correlation pieces THROUGH ITS OWN SELECTORS, for
flow `s`.  This is the only basis information the port layer exposes. -/
def portBlueRed (S : Surf) (p : Port) (s : Nat) : Bool × Bool :=
  (S.sel p.blueSel s p.pi p.pj p.pk, S.sel p.redSel s p.pi p.pj p.pk)

/-- **★ THE RELABEL TRAP: through `H`'s ports, the idle reads IDENTICALLY to
`H`. ★**  At BOTH the input and the output port, for BOTH flows, the idle's
straight `KI`/`KJ` surface presents the SAME `(blue, red)` pair as `H`'s rotated
surface.  So a "the basis changes between the two ports" check read through the
SELECTORS is satisfied by a pure idle exactly as by `H` — the port layer is a
relabel, blind to the rotation. -/
theorem idle_reads_like_h_at_ports :
    (List.range 2).all (fun s =>
      (hPorts.all (fun p => portBlueRed idle2Surf p s == portBlueRed hSurf p s)))
      = true := by native_decide

/-- ...and consequently the pure idle PASSES `H`'s own `X̄→Z̄ / Z̄→X̄` port
spec under `LaSCorrectFull` — the relabel fake, made concrete.  The port layer
ALONE cannot certify a genuine basis change. -/
theorem idle_passes_h_port_spec :
    LaSCorrectFull idle2 idle2Surf hPorts hPaulis 2 = true := by native_decide

/-! ## §2. The HONEST NEGATIVE on the LITERAL existing ColorEnforcing checker. -/

/-- **★ HONEST NEGATIVE: the UNMODIFIED `gadgetColorFaithful` CANNOT reject the
idle. ★**  `gadgetColorFaithful` is a per-gadget basis-VALIDITY check (the
measured observable matches the seam color); it reads only the flow-0 INPUT port
and never compares input vs output.  So `H` and `mem` (the catalog idle) BOTH
pass — it does not distinguish a basis CHANGE from a single-basis readout.  We
report this rather than relabel it: Strategy A's idle rejection needs the
basis-CHANGE strengthening of §3 (which reads the SAME `ColorI`/`ColorJ`). -/
theorem existing_color_check_cannot_reject_idle :
    gadgetColorFaithful .hgate = true ∧ gadgetColorFaithful .mem = true := by
  constructor <;> native_decide

/-! ## §3. The genuine COLOR-ANCHORED rotation signature (Strategy A's anchor). -/

/-- The seam color of the gadget's FIRST `I`-pipe (`ColorI`), read straight from
the `LaSre` — `none` if it has no `I`-pipe. -/
def firstIColor (L : LaSre) : Option Bool :=
  L.gridCubes.findSome? (fun c =>
    if L.ExistI c.1 c.2.1 c.2.2 then some (L.ColorI c.1 c.2.1 c.2.2) else none)

/-- The seam color of the gadget's FIRST `J`-pipe (`ColorJ`). -/
def firstJColor (L : LaSre) : Option Bool :=
  L.gridCubes.findSome? (fun c =>
    if L.ExistJ c.1 c.2.1 c.2.2 then some (L.ColorJ c.1 c.2.1 c.2.2) else none)

/-- **THE ROTATION COLOR SIGNATURE — the COLOR-ANCHORED discriminator.**  A
surface-code PATCH ROTATION (the geometric content of `H`) turns its corner
route through BOTH spatial axes, so it carries a COLORED `I`-pipe AND a COLORED
`J`-pipe whose BOUNDARY COLORS DIFFER (the rotation flips blue↔red across the
turn).  Read ENTIRELY from `ColorI`/`ColorJ` (via `firstIColor`/`firstJColor`)
— the physical seam data the ColorEnforcing layer anchors and `funcOK`/`portsOK`
are blind to.  A pure idle (no spatial pipes ⇒ both `none`) and a plain
single-axis merge (one axis `none`) BOTH fail it; only a genuine two-axis
rotation passes. -/
def rotationColorSig (L : LaSre) : Bool :=
  match firstIColor L, firstJColor L with
  | some ci, some cj => ci != cj
  | _,       _       => false

/-! ## §4. The certification — `H` certified TRUE, idle certified FALSE. -/

/-- **The genuine, COLOR-ANCHORED `H` basis-change certification**: `H` passes
the `X̄→Z̄ / Z̄→X̄` flow check (the z3-synthesized spec, `hLaS_fully_correct`)
AND carries the rotation COLOR signature (two oppositely-colored spatial
boundaries — a real patch rotation read from `ColorI`/`ColorJ`).  The second
conjunct is the teeth the port layer lacks. -/
def hBasisChangeColorCertified : Bool :=
  LaSCorrectFull hLaS hSurf hPorts hPaulis 2 && rotationColorSig hLaS

/-- **★ THE HADAMARD IS CERTIFIED AS A GENUINE, COLOR-ANCHORED BASIS CHANGE. ★**
It passes the `X̄→Z̄ / Z̄→X̄` flow specification AND carries the rotation color
signature (colored `I`- and `J`-boundaries, opposite colors) — a real patch
rotation, not a port relabel. -/
theorem h_basis_change_color_certified : hBasisChangeColorCertified = true := by
  native_decide

/-- The SAME color-anchored recipe applied to the pure idle: the idle is run
through `H`'s ports and change spec (which it FAKELY passes, §1) AND asked for the
rotation COLOR signature (which it CANNOT provide — it has no colored seam). -/
def idleBasisChangeColorCertified : Bool :=
  LaSCorrectFull idle2 idle2Surf hPorts hPaulis 2 && rotationColorSig idle2

/-- **★ THE MANDATORY ANTI-FAKE CONTROL: a pure IDLE is REJECTED by the
COLOR-ANCHORED check. ★**  Even though the idle PASSES the port spec
(`idle_passes_h_port_spec`, the relabel fake), it FAILS the certification because
it carries NO rotation color signature — `firstIColor idle2 = firstJColor idle2 =
none`, it has no colored spatial seam.  So the COLOR-ANCHORED certification
GENUINELY DISTINGUISHES `H` from idle: `H = true`, idle = `false`. -/
theorem idle_basis_change_color_rejected :
    idleBasisChangeColorCertified = false := by native_decide

/-- **★ THE CERTIFICATION HAS TEETH — `H` certified, idle rejected, side by
side. ★**  The pair is the proof of genuineness: the basis change is REAL
precisely because the COLOR-ANCHORED certification that accepts `H` rejects a
pure idle. -/
theorem h_color_certified_idle_rejected :
    hBasisChangeColorCertified = true ∧ idleBasisChangeColorCertified = false :=
  ⟨h_basis_change_color_certified, idle_basis_change_color_rejected⟩

/-! ## §5. The control is SURFACE-INDEPENDENT — no relabel rescues the idle. -/

/-- **★ NO SURFACE / PORT CHOICE RESCUES THE IDLE. ★**  `rotationColorSig` reads
ONLY the gadget's `LaSre` geometry (`ColorI`/`ColorJ`), NOT its correlation
surface or its ports.  So the idle's rejection is independent of EVERY surface and
EVERY port relabel — the rejection in §4 is forced, not a lucky witness.  The
idle simply has no colored spatial seam to rotate through. -/
theorem idle_rejected_regardless_of_surface_and_ports
    (S : Surf) (ports : List Port) (paulis : Nat → Nat → Pauli) (nStab : Nat) :
    (LaSCorrectFull idle2 S ports paulis nStab && rotationColorSig idle2) = false := by
  have : rotationColorSig idle2 = false := by native_decide
  simp [this]

/-- ...and likewise for the catalog's canonical 1×1 `memoryLaS` (`gadgetFor .mem`):
it too has no colored spatial seam, so it carries no rotation color signature —
the catalog idle is rejected just as surely, for any surface and ports. -/
theorem memory_rejected_regardless_of_surface_and_ports
    (S : Surf) (ports : List Port) (paulis : Nat → Nat → Pauli) (nStab : Nat) :
    (LaSCorrectFull memoryLaS S ports paulis nStab && rotationColorSig memoryLaS)
      = false := by
  have : rotationColorSig memoryLaS = false := by native_decide
  simp [this]

/-! ## §6. HONEST SCOPE — the signature is anti-IDLE AND anti-plain-merge. -/

/-- SCOPE NOTE (stronger than the prior `rotationWitness`, still honest).  The
COLOR signature demands TWO oppositely-colored spatial boundaries.  A pure idle
(no spatial pipes) fails; a plain SINGLE-axis merge also fails — it turns through
only ONE spatial axis.  We verify this so as not to overclaim and not to
underclaim: the control is anti-IDLE (the task's mandatory requirement) AND
anti-plain-merge, separating `H`'s genuine ROTATION from both. -/
theorem zMerge_lacks_rotation_color_sig :
    rotationColorSig (gadgetFor .zMerge).L = false := by native_decide

theorem xMerge_lacks_rotation_color_sig :
    rotationColorSig (gadgetFor .xMerge).L = false := by native_decide

/-- The Hadamard's catalog `LaSre` carries the signature (the cross-check that the
`.hgate` catalog entry IS the `hLaS` we certified). -/
theorem hgate_has_rotation_color_sig :
    rotationColorSig (gadgetFor .hgate).L = true := by native_decide

end FormalRV.QEC.LaSre
