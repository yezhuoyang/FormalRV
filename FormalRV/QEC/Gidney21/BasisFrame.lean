/-
  FormalRV.QEC.Gidney21.BasisFrame
  --------------------------------
  **★ BASIS-AWARE frame/ports — the fix for the Z-merge-centric FrameTracker. ★**

  THE BUG (found while compiling the whole Shor modexp): `FrameTracker.emitPaulis`
  specs every connected component as all-`Z̄`, so a mixed `M_{X̄Z̄}` or a `M_Ȳ`
  readout is silently certified as a joint-`Z̄` — the wrong observable.  Even where
  it "passes", it is checking the gadget against a Z-spec it does not realize.

  THE FIX (ZX-calculus view): in a LaSre the `KI` surface plane carries the
  Z-correlation (the Z/green spider) and `KJ` carries the X-correlation (the X/red
  spider); a `Ȳ` readout lives on BOTH planes.  So the spec a port demands must be
  read from the gadget's ACTUAL measured basis (`gadgetObservable`), NOT assumed
  `Z`.  Here we:

  * `basisFramePorts` — the basis-aware spec: place each placed gadget's REAL
    measured observable (`gadgetObservable`, X/Y/Z per ZX colour) at its qubits.
  * build a genuinely basis-HETEROGENEOUS diagram (a `Z̄`-merge on `{0,1}` welded
    with a `Ȳ` readout on `{2}` — three patches, two different bases) and certify
    it against the basis-aware spec (`bzy_correct`);
  * the ANTI-CHEAT: the OLD all-`Z̄` spec is REJECTED on the same diagram
    (`bzy_allZ_rejected`) — so basis-awareness is load-bearing, not a relabel.
-/
import FormalRV.QEC.Gidney21.ComposedSemantic

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC.LaSre

/-! ## §1. The basis-aware spec emitter (ZX colour per gadget). -/

/-- **The basis-aware frame spec**: each placed gadget contributes its REAL
measured observable (`gadgetObservable` — X/Y/Z per the ZX spider colour) on its
own logical qubits.  (Contrast `FrameTracker.emitPaulis`, which forces `Z̄`.) -/
def basisFramePorts (layer : List PlacedGadget) : List (Nat × Pauli) :=
  layer.flatMap (fun g => g.qubits.zip (gadgetObservable g.kind))

/-- For the heterogeneous layer `[Z-merge {0,1}, Y-readout {2}]` the basis-aware
spec is `Z̄₀ Z̄₁ Ȳ₂` — NOT the Z-centric `Z̄₀ Z̄₁ Z̄₂`. -/
theorem basisFramePorts_zy :
    basisFramePorts [⟨GadgetKind.zMerge, [0, 1]⟩, ⟨GadgetKind.mY1, [2]⟩]
      = [(0, Pauli.Z), (1, Pauli.Z), (2, Pauli.Y)] := by native_decide

/-! ## §2. A genuinely basis-HETEROGENEOUS diagram: `Z̄`-merge {0,1} ⊕ `Ȳ` {2}. -/

/-- Three patches; an I-seam (Z-merge) between patches 0,1; patch 2 a lone
worldline (read in the `Y` basis by the surface below). -/
def bzyLaS : LaSre :=
  { maxI := 3, maxJ := 1, maxK := 3
    YCube  := fun _ _ _ => false
    ExistI := fun i j k => i == 0 && j == 0 && k == 1          -- Z-seam {0,1}
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => (i == 0 || i == 1 || i == 2) && j == 0 && k < 2
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

/-- Flows: `0 = Z̄₀Z̄₁` (blue, joins across the seam), `1 = X̄₀`, `2 = X̄₁` (red),
`3 = Ȳ₂` (BOTH planes on patch 2 — the Y readout). -/
def bzySurf : Surf :=
  { IJ := fun _ _ _ _ => false
    IK := fun s i j k => s == 0 && i == 0 && j == 0 && k == 1          -- joint-Z seam
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => (s == 0 && j == 0 && (i == 0 || i == 1))      -- Z̄₀Z̄₁ (blue)
                       || (s == 3 && i == 2 && j == 0)                  -- Ȳ₂ blue piece
    KJ := fun s i j _ => (s == 1 && i == 0 && j == 0)                   -- X̄₀ (red)
                       || (s == 2 && i == 1 && j == 0)                   -- X̄₁ (red)
                       || (s == 3 && i == 2 && j == 0) }                 -- Ȳ₂ red piece

def bzyPorts : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨0, 0, 2, 4, 5⟩, ⟨1, 0, 0, 4, 5⟩, ⟨1, 0, 2, 4, 5⟩,
   ⟨2, 0, 0, 4, 5⟩, ⟨2, 0, 2, 4, 5⟩]

/-- The BASIS-AWARE spec: flow 0 `Z̄₀Z̄₁` (Z on patches 0,1), flow 3 `Ȳ₂` (Y on
patch 2), the two `X̄` passthroughs. -/
def bzyPaulis : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, 0 => Pauli.Z | 0, 1 => Pauli.Z | 0, 2 => Pauli.Z | 0, 3 => Pauli.Z
  | 1, 0 => Pauli.X | 1, 1 => Pauli.X
  | 2, 2 => Pauli.X | 2, 3 => Pauli.X
  | 3, 4 => Pauli.Y | 3, 5 => Pauli.Y
  | _, _ => Pauli.I

/-- **★ THE BASIS-HETEROGENEOUS DIAGRAM IS CERTIFIED ★** — one welded diagram
carrying a joint `Z̄₀Z̄₁` measurement AND a `Ȳ₂` readout passes the COMPLETE
`LaSCorrectFull` against the BASIS-AWARE spec (Z on {0,1}, Y on {2}). -/
theorem bzy_correct :
    LaSCorrectFull bzyLaS bzySurf bzyPorts bzyPaulis 4 = true := by native_decide

/-! ## §3. THE ANTI-CHEAT — the old all-`Z̄` (Z-centric) spec is REJECTED. -/

/-- The Z-centric spec (`FrameTracker.emitPaulis`-style): patch 2 forced to `Z̄`. -/
def bzyPaulisAllZ : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, 0 => Pauli.Z | 0, 1 => Pauli.Z | 0, 2 => Pauli.Z | 0, 3 => Pauli.Z
  | 1, 0 => Pauli.X | 1, 1 => Pauli.X
  | 2, 2 => Pauli.X | 2, 3 => Pauli.X
  | 3, 4 => Pauli.Z | 3, 5 => Pauli.Z          -- WRONG: patch 2 is Ȳ, not Z̄
  | _, _ => Pauli.I

/-- **★ THE Z-CENTRIC SPEC IS PROVABLY WRONG ★** — the SAME diagram FAILS
`LaSCorrectFull` against the all-`Z̄` spec (the surface genuinely reads `Ȳ` on
patch 2 — both planes — so the `Z̄₂` claim's red piece does not match).  Hence the
basis is LOAD-BEARING: the frame MUST carry each measurement's actual X/Y/Z basis,
exactly the bug behind the whole-Shor composition failure. -/
theorem bzy_allZ_rejected :
    LaSCorrectFull bzyLaS bzySurf bzyPorts bzyPaulisAllZ 4 = false := by native_decide

/-- ...the discriminator is EXACTLY the measurement basis: the two specs AGREE on
the `Z̄`-merge flows (0,1) and disagree precisely on the `Y` patch — basis-aware
says `Ȳ` where the Z-centric spec says `Z̄`. -/
theorem bzy_basis_is_the_discriminator :
    bzyPaulis 3 4 = Pauli.Y ∧ bzyPaulisAllZ 3 4 = Pauli.Z
      ∧ bzyPaulis 0 0 = bzyPaulisAllZ 0 0 ∧ bzyPaulis 1 0 = bzyPaulisAllZ 1 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §4. ALL THREE PAULI BASES in one verified diagram (Z, X, Y).

  The `KI`/`KJ` (Z/X spider) surface genuinely carries DISTINCT bases per patch:
  a `Z̄`-merge on `{0,1}` (blue/`KI` joins), an `X̄` readout on `{2}` (red/`KJ`
  only), a `Ȳ` readout on `{3}` (BOTH planes) — one welded diagram, certified
  against the per-patch basis-aware spec.  This is the two-colour(+Y) surface
  threading all of Z, X, Y at once. -/

def bzxyLaS : LaSre :=
  { maxI := 4, maxJ := 1, maxK := 3
    YCube  := fun _ _ _ => false
    ExistI := fun i j k => i == 0 && j == 0 && k == 1                    -- Z-seam {0,1}
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => (i == 0 || i == 1 || i == 2 || i == 3) && j == 0 && k < 2
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

/-- Flows `0=Z̄₀Z̄₁` (blue), `1=X̄₀`, `2=X̄₁`, `3=X̄₂` (red; the X readout), `4=Ȳ₃`
(both planes). -/
def bzxySurf : Surf :=
  { IJ := fun _ _ _ _ => false
    IK := fun s i j k => s == 0 && i == 0 && j == 0 && k == 1
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => (s == 0 && j == 0 && (i == 0 || i == 1))        -- Z̄₀Z̄₁ blue
                       || (s == 4 && i == 3 && j == 0)                    -- Ȳ₃ blue piece
    KJ := fun s i j _ => (s == 1 && i == 0 && j == 0)                     -- X̄₀
                       || (s == 2 && i == 1 && j == 0)                     -- X̄₁
                       || (s == 3 && i == 2 && j == 0)                     -- X̄₂ (X readout, red)
                       || (s == 4 && i == 3 && j == 0) }                   -- Ȳ₃ red piece

def bzxyPorts : List Port :=
  [⟨0,0,0,4,5⟩,⟨0,0,2,4,5⟩, ⟨1,0,0,4,5⟩,⟨1,0,2,4,5⟩,
   ⟨2,0,0,4,5⟩,⟨2,0,2,4,5⟩, ⟨3,0,0,4,5⟩,⟨3,0,2,4,5⟩]

/-- The basis-aware spec: `Z̄` on {0,1}, `X̄` on {2}, `Ȳ` on {3}. -/
def bzxyPaulis : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0,0 => .Z | 0,1 => .Z | 0,2 => .Z | 0,3 => .Z
  | 1,0 => .X | 1,1 => .X
  | 2,2 => .X | 2,3 => .X
  | 3,4 => .X | 3,5 => .X
  | 4,6 => .Y | 4,7 => .Y
  | _,_ => .I

/-- **★ ALL THREE BASES CERTIFIED IN ONE DIAGRAM ★** — `Z̄₀Z̄₁` + `X̄₂` + `Ȳ₃`. -/
theorem bzxy_correct :
    LaSCorrectFull bzxyLaS bzxySurf bzxyPorts bzxyPaulis 5 = true := by native_decide

/-- The Z-centric spec: patches 2,3 forced to `Z̄`. -/
def bzxyPaulisAllZ : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0,0 => .Z | 0,1 => .Z | 0,2 => .Z | 0,3 => .Z
  | 1,0 => .X | 1,1 => .X
  | 2,2 => .X | 2,3 => .X
  | 3,4 => .Z | 3,5 => .Z       -- WRONG: patch 2 is X̄
  | 4,6 => .Z | 4,7 => .Z       -- WRONG: patch 3 is Ȳ
  | _,_ => .I

/-- **★ THE Z-CENTRIC SPEC IS REJECTED ★** — forcing `Z̄` on the X- and Y-patches
fails `LaSCorrectFull` on the same diagram.  Each of the three bases is genuinely
distinct and load-bearing. -/
theorem bzxy_allZ_rejected :
    LaSCorrectFull bzxyLaS bzxySurf bzxyPorts bzxyPaulisAllZ 5 = false := by native_decide

/-- The basis-aware EMITTER produces exactly this `Z̄ Z̄ X̄ Ȳ` spec from the placed
gadgets — `Z`-merge {0,1}, `X`-readout {2}, `Y`-readout {3} — reading each
gadget's REAL observable, not all-`Z̄`. -/
theorem basisFramePorts_zxy :
    basisFramePorts [⟨GadgetKind.zMerge, [0, 1]⟩, ⟨GadgetKind.mX1, [2]⟩, ⟨GadgetKind.mY1, [3]⟩]
      = [(0, Pauli.Z), (1, Pauli.Z), (2, Pauli.X), (3, Pauli.Y)] := by native_decide

end FormalRV.QEC.Gidney21
