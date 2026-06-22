/-
  FormalRV.QEC.LatticeSurgery.CrossLayerHetero
  --------------------------------------------
  **★ A VERIFIED CROSS-LAYER HETEROGENEOUS lattice-surgery chain ★** — a
  `weldChain` of TWO time-layers in which DIFFERENT measurement bases appear at
  DIFFERENT layers, with the correlation surfaces threading correctly across the
  time-seam and passing the COMPLETE `LaSCorrectFull`.

    * Layer 1 (time-bottom) = a `Z̄₀Z̄₁`-merge (blue/`Z` seam) on cols `{0,1}`,
      col 2 idling;
    * Layer 2 (time-top)    = cols `{0,1}` idling, col 2 read in the `Y` basis
      (`Ȳ₂`, BOTH correlation planes) — a DISJOINT qubit.

  The four stabilizer flows `{Z̄₀Z̄₁, X̄₀, X̄₁, Ȳ₂}` pairwise COMMUTE (the merge
  acts on `{0,1}`, the `Y`-readout on the disjoint col `{2}`), so each threads
  cleanly through the OTHER layer under the chain's IDENTITY flow-map.  This is
  the commuting heterogeneous case: the headline `bzxy_correct`/`bzy_correct`
  diagrams (Gidney21.BasisFrame) carry Z+X+Y in ONE layer; here the SAME
  basis-heterogeneity is spread across TWO welded time-layers.

  HONEST SCOPE.  This is the COMMUTING heterogeneous case (different bases on
  DISJOINT worldlines).  The NON-commuting case — the SAME qubit `Z`-merged at
  layer 1 then read in `X̄` at layer 2 — is genuinely BLOCKED by this single-round
  identity-flow model (the `X̄` membrane anticommutes with the measured `Z̄`, so it
  cannot continue below the Z-layer) and needs the classical Pauli frame; it is
  NOT attempted here.

  Everything is certified via the `weldChain_LaSCorrectFull` gate — per-gadget +
  per-interface checks, NOT a `native_decide` on the whole welded diagram — and is
  axiom-clean (no `sorryAx`).
-/
import FormalRV.QEC.LatticeSurgery.ChainComposition

namespace FormalRV.QEC.LaSre

/-! ## §1. The two heterogeneous time-layers. -/

/-- Layer-1 LaSre: 3 patches, a `Z`-seam (I-pipe) joining cols `{0,1}` at `k=1`,
all three K-worldlines.  Height `h=3`. -/
def hcL1 : LaSre :=
  { maxI := 3, maxJ := 1, maxK := 3
    YCube  := fun _ _ _ => false
    ExistI := fun i j k => i == 0 && j == 0 && k == 1          -- Z-seam {0,1}
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => (i == 0 || i == 1 || i == 2) && j == 0 && k < 2
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

/-- Layer-1 surface: flow 0 `Z̄₀Z̄₁` blue (`KI`) joining across the seam (`IK`
piece); flow 1 `X̄₀`, flow 2 `X̄₁` red (`KJ`); flow 3 `Ȳ₂` BOTH planes on col 2. -/
def hcS1 : Surf :=
  { IJ := fun _ _ _ _ => false
    IK := fun s i j k => s == 0 && i == 0 && j == 0 && k == 1
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => (s == 0 && j == 0 && (i == 0 || i == 1))
                       || (s == 3 && i == 2 && j == 0)
    KJ := fun s i j _ => (s == 1 && i == 0 && j == 0)
                       || (s == 2 && i == 1 && j == 0)
                       || (s == 3 && i == 2 && j == 0) }

/-- Layer-2 LaSre: 3 patches idling — the joint `Z` is already measured below, so
there is NO seam here; col 2 is read in `Y` at the top port.  Height `h=3`. -/
def hcL2 : LaSre :=
  { maxI := 3, maxJ := 1, maxK := 3
    YCube  := fun _ _ _ => false
    ExistI := fun _ _ _ => false
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => (i == 0 || i == 1 || i == 2) && j == 0 && k < 2
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

/-- Layer-2 surface: flow 0 `Z̄₀⊕Z̄₁` blue on cols `{0,1}` (the joint, threaded);
flows 1,2 `X̄₀`,`X̄₁` red; flow 3 `Ȳ₂` BOTH planes on col 2 (the `Y` readout). -/
def hcS2 : Surf :=
  { IJ := fun _ _ _ _ => false
    IK := fun _ _ _ _ => false
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => (s == 0 && j == 0 && (i == 0 || i == 1))
                       || (s == 3 && i == 2 && j == 0)
    KJ := fun s i j _ => (s == 1 && i == 0 && j == 0)
                       || (s == 2 && i == 1 && j == 0)
                       || (s == 3 && i == 2 && j == 0) }

/-- All three worldlines welded across the time-seam. -/
def hcConn : List (Nat × Nat) := [(0, 0), (1, 0), (2, 0)]

def hcGadgets : List LaSre := [hcL1, hcL2]
def hcSurfs : List Surf := [hcS1, hcS2]

/-- Composite ports: bottom of layer 1 (`k=0`) and top of layer 2 (`k=5`), each
reading blue from `KI` (selector 4), red from `KJ` (selector 5). -/
def hcPorts : List Port :=
  [⟨0,0,0,4,5⟩, ⟨0,0,5,4,5⟩, ⟨1,0,0,4,5⟩, ⟨1,0,5,4,5⟩, ⟨2,0,0,4,5⟩, ⟨2,0,5,4,5⟩]

/-- The basis-aware spec: flow 0 `Z̄₀Z̄₁` (Z on cols `{0,1}` = ports 0–3), flow 1
`X̄₀`, flow 2 `X̄₁`, flow 3 `Ȳ₂` (Y on col 2 = ports 4,5). -/
def hcPaulis : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, 0 => Pauli.Z | 0, 1 => Pauli.Z | 0, 2 => Pauli.Z | 0, 3 => Pauli.Z
  | 1, 0 => Pauli.X | 1, 1 => Pauli.X
  | 2, 2 => Pauli.X | 2, 3 => Pauli.X
  | 3, 4 => Pauli.Y | 3, 5 => Pauli.Y
  | _, _ => Pauli.I

/-! ## §2. The certificate, via the chain gate. -/

/-- Per-gadget + per-interface checks (each SMALL): both layers `valid`+`funcOK`,
both seam-interface layers `OK`. -/
theorem hetCross_chainOK :
    chainOK 3 4 hcConn 3 1 hcGadgets hcSurfs = true := by native_decide

/-- The composite ports match the `Z̄₀Z̄₁` / `X̄₀` / `X̄₁` / `Ȳ₂` frame. -/
theorem hetCross_ports :
    portsOK (weldChainSurf 3 hcSurfs) hcPorts hcPaulis 4 = true := by native_decide

/-- **★ CROSS-LAYER HETEROGENEOUS CHAIN CERTIFIED ★** — a 2-time-layer `weldChain`
with a `Z`-merge (blue/`Z` seam) at layer 1 and a `Ȳ`-readout at layer 2 on a
DISJOINT qubit passes the COMPLETE `LaSCorrectFull`, derived from the per-gadget +
per-interface checks via `weldChain_LaSCorrectFull` (NOT a `native_decide` on the
whole welded diagram).  Two time-layers, two distinct measurement bases. -/
theorem hetCross_correct :
    LaSCorrectFull (weldChain 3 hcConn hcGadgets) (weldChainSurf 3 hcSurfs)
      hcPorts hcPaulis 4 = true :=
  weldChain_LaSCorrectFull 3 4 hcConn 3 1 hcGadgets hcSurfs hcPorts hcPaulis
    hetCross_chainOK hetCross_ports

/-! ## §3. TEETH — the heterogeneity is load-bearing, and it is genuinely 2 layers. -/

/-- The Z-centric spec: col 2 forced to `Z̄` instead of `Ȳ`. -/
def hcPaulisAllZ : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, 0 => Pauli.Z | 0, 1 => Pauli.Z | 0, 2 => Pauli.Z | 0, 3 => Pauli.Z
  | 1, 0 => Pauli.X | 1, 1 => Pauli.X
  | 2, 2 => Pauli.X | 2, 3 => Pauli.X
  | 3, 4 => Pauli.Z | 3, 5 => Pauli.Z      -- WRONG: col 2 is Ȳ, not Z̄
  | _, _ => Pauli.I

/-- **★ ANTI-CHEAT ★** — forcing col 2's flow to `Z̄` instead of `Ȳ` FAILS
`LaSCorrectFull`: the `Y` basis is load-bearing across the time-seam (the surface
genuinely reads both planes on col 2, so the `Z̄₂` claim's red piece does not
match).  So the cross-layer heterogeneity is NOT a relabel. -/
theorem hetCross_allZ_rejected :
    LaSCorrectFull (weldChain 3 hcConn hcGadgets) (weldChainSurf 3 hcSurfs)
      hcPorts hcPaulisAllZ 4 = false := by native_decide

/-- **STRUCTURAL** — the welded diagram is genuinely TWO stacked layers (6 tall),
with the `Z`-seam in the LOWER layer (`k=1`) and NO seam in the upper layer
(`k=4`).  So it is not a collapsed single layer. -/
theorem hetCross_two_layers :
    (weldChain 3 hcConn hcGadgets).maxK = 6
      ∧ (weldChain 3 hcConn hcGadgets).ExistI 0 0 1 = true
      ∧ (weldChain 3 hcConn hcGadgets).ExistI 0 0 4 = false := by native_decide

/-- **STRUCTURAL** — the col-2 worldline carries BOTH correlation planes (flow 3 =
`Ȳ₂`) in BOTH layers (`k=0` below the seam, `k=3` above), so the `Y` observable
threads the time-seam. -/
theorem hetCross_Y_threads_seam :
    (weldChainSurf 3 hcSurfs).KI 3 2 0 0 = true ∧ (weldChainSurf 3 hcSurfs).KJ 3 2 0 0 = true
      ∧ (weldChainSurf 3 hcSurfs).KI 3 2 0 3 = true ∧ (weldChainSurf 3 hcSurfs).KJ 3 2 0 3 = true
      := by native_decide

end FormalRV.QEC.LaSre
