/-
  FormalRV.QEC.LatticeSurgery.FaithfulMixedMerge
  ----------------------------------------------
  **★ THE FAITHFUL MIXED MERGE — welding `H₁ ; Z-merge ; H₁` into ONE diagram
  that measures `X̄₁Z̄₂`, color-consistently (no twist). ★**

  The promotion (`ColorEnforcing.lean`) routes a mixed measurement `M_{X₁Z₂}` to
  `[hgate, zMerge, hgate]`.  This file PROVES that the three gadgets WELD into one
  spacetime diagram that (a) passes the complete `LaSCorrectFull`, (b) measures
  exactly `X̄₁Z̄₂`, and (c) is COLOR-FAITHFUL — the interior merge is a pure
  `Z`-seam (`ColorI=false`), and the `H` on `q₁` physically rotates its boundary
  so the `KI` plane the seam joins carries `X̄₁` (not a port relabel).

  Why the `H ; Z-merge` route (and not `H ; X-merge`, the earlier blocker): the
  `H` gadget's OUTPUT port is `z_basis I` (blue=`KI`) — EXACTLY the Z-merge's
  convention — so the H→merge interface is convention-matched with no relabel.
  Placing `q₁`'s `H` at `i=1` (aux at `i=2`, `j=1`) keeps it clear of `q₂` at
  `i=0`, so the two patches share one grid without collision.
-/
import FormalRV.QEC.LatticeSurgery.Weld
import FormalRV.QEC.LatticeSurgery.MixedMergeWeld
import FormalRV.QEC.Gidney21.GadgetToLaS

namespace FormalRV.QEC.LaSre

/-! ## §1. Spatial shift along I (the H-on-q₁ placement operator). -/

/-- Shift a pipe diagram by `di` along the `I` axis (content at `i ≥ di`). -/
def shiftI (di : Nat) (L : LaSre) : LaSre :=
  { maxI := di + L.maxI, maxJ := L.maxJ, maxK := L.maxK
    YCube  := fun i j k => decide (di ≤ i) && L.YCube  (i - di) j k
    ExistI := fun i j k => decide (di ≤ i) && L.ExistI (i - di) j k
    ExistJ := fun i j k => decide (di ≤ i) && L.ExistJ (i - di) j k
    ExistK := fun i j k => decide (di ≤ i) && L.ExistK (i - di) j k
    ColorI := fun i j k => decide (di ≤ i) && L.ColorI (i - di) j k
    ColorJ := fun i j k => decide (di ≤ i) && L.ColorJ (i - di) j k }

/-- Shift a correlation surface by `di` along `I`. -/
def shiftISurf (di : Nat) (S : Surf) : Surf :=
  { IJ := fun s i j k => decide (di ≤ i) && S.IJ s (i - di) j k
    IK := fun s i j k => decide (di ≤ i) && S.IK s (i - di) j k
    JK := fun s i j k => decide (di ≤ i) && S.JK s (i - di) j k
    JI := fun s i j k => decide (di ≤ i) && S.JI s (i - di) j k
    KI := fun s i j k => decide (di ≤ i) && S.KI s (i - di) j k
    KJ := fun s i j k => decide (di ≤ i) && S.KJ s (i - di) j k }

/-! ## §2. LAYER A — `H` on `q₁` (at `i=1`) ∥ idle on `q₂` (at `i=0`).

  `q₂` idles in the MERGE convention (blue=`KI`); `q₁`'s `H` is `hLaS` shifted to
  `i=1`.  Four flows: `Z̄₂, X̄₂` pass on `q₂`; `H` maps `X̄₁→Z̄₁`, `Z̄₁→X̄₁` on `q₁`. -/

/-- `q₂`'s idle worldline at `(0,0)` (3 time steps). -/
def q2idle : LaSre :=
  { maxI := 1, maxJ := 1, maxK := 3
    YCube := fun _ _ _ => false
    ExistI := fun _ _ _ => false, ExistJ := fun _ _ _ => false
    ExistK := fun i j k => i == 0 && j == 0 && k < 2
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

/-- `q₂`'s idle surface in the MERGE convention (blue=`KI`): `Z̄₂` in `KI`, `X̄₂`
in `KJ`. -/
def q2idleSurf : Surf :=
  { IJ := fun _ _ _ _ => false, IK := fun _ _ _ _ => false
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => s == 0 && i == 0 && j == 0
    KJ := fun s i j _ => s == 1 && i == 0 && j == 0 }

/-- Layer A diagram: `q₂` idle ∪ `H`-on-`q₁`(shifted to `i=1`). -/
def layerA : LaSre := unionLaS q2idle (shiftI 1 hLaS)

/-- Layer A surface: flows 0,1 from `q₂` idle; flows 2,3 from the shifted `H`. -/
def layerASurf : Surf :=
  let hS := shiftISurf 1 hSurf
  { IJ := fun s i j k => if s < 2 then q2idleSurf.IJ s i j k else hS.IJ (s - 2) i j k
    IK := fun s i j k => if s < 2 then q2idleSurf.IK s i j k else hS.IK (s - 2) i j k
    JK := fun s i j k => if s < 2 then q2idleSurf.JK s i j k else hS.JK (s - 2) i j k
    JI := fun s i j k => if s < 2 then q2idleSurf.JI s i j k else hS.JI (s - 2) i j k
    KI := fun s i j k => if s < 2 then q2idleSurf.KI s i j k else hS.KI (s - 2) i j k
    KJ := fun s i j k => if s < 2 then q2idleSurf.KJ s i j k else hS.KJ (s - 2) i j k }

/-- Ports: `q₂` in/out at `(0,0)` (blue=`KI` 4); `q₁` in at `(1,0)` (blue=`KJ` 5,
z_basis J) and out at `(1,0)` (blue=`KI` 4, after `H`). -/
def layerAPorts : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨0, 0, 2, 4, 5⟩, ⟨1, 0, 0, 5, 4⟩, ⟨1, 0, 2, 4, 5⟩]

/-- Spec: 0 `Z̄₂`, 1 `X̄₂` (q₂ ports 0,1); 2 `X̄₁→Z̄₁`, 3 `Z̄₁→X̄₁` (q₁ ports 2,3). -/
def layerAPaulis : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, 0 => Pauli.Z | 0, 1 => Pauli.Z   -- Z̄₂
  | 1, 0 => Pauli.X | 1, 1 => Pauli.X   -- X̄₂
  | 2, 2 => Pauli.X | 2, 3 => Pauli.Z   -- X̄₁ → Z̄₁  (H on q₁)
  | 3, 2 => Pauli.Z | 3, 3 => Pauli.X   -- Z̄₁ → X̄₁
  | _, _ => Pauli.I

/-- **★ LAYER A VERIFIED — `H` on `q₁` ∥ idle on `q₂` (merge convention) ★.** -/
theorem layerA_fully_correct :
    LaSCorrectFull layerA layerASurf layerAPorts layerAPaulis 4 = true := by
  native_decide

/-- Debug handle (empty iff correct). -/
theorem layerA_report :
    LaSReport layerA layerASurf layerAPorts layerAPaulis 4 = [] := by
  native_decide

/-! ## §3. THE FULL WELD — `Layer A ; Z-merge ; Layer A` = `M_{X₁Z₂}`.

  Three layers stacked in time: `H₁∥idle` (k∈[0,3)), the pure `Z`-merge
  (k∈[3,6)), `H₁∥idle` (k∈[6,9)).  The composite has 3 stabilizer flows, each the
  `H₁`-conjugate of a Z-merge flow:
    * flow 0 `X̄₁Z̄₂` (joint, MEASURED) = `H(X̄₁→Z̄₁) ; Z̄₁Z̄₂-join ; H(Z̄₁→X̄₁)`;
    * flow 1 `Z̄₁` (passes)            = `H(Z̄₁→X̄₁) ; X̄₁-pass ; H(X̄₁→Z̄₁)`;
    * flow 2 `X̄₂` (passes)            = idle ; `X̄₂`-pass ; idle.
  `q₂` (i=0) is in the merge convention throughout; `q₁` (i=1) input/output is
  z_basis J (the two H's cancel), so `q₁`'s ports read `X̄₁`. -/

/-- The two worldlines welded across each interface. -/
def mixConn : List (Nat × Nat) := [(0, 0), (1, 0)]

/-- Layer A → flow-generator map (composite flow ↦ Layer-A generators).
0`X̄₁Z̄₂`↦{Z̄₂(0), X̄₁→Z̄₁(2)}; 1`Z̄₁`↦{Z̄₁→X̄₁(3)}; 2`X̄₂`↦{X̄₂(1)}. -/
def fmLayer : Nat → List Nat := fun s => if s == 0 then [0, 2] else if s == 1 then [3] else [1]

/-- Z-merge → flow-generator map.
0`X̄₁Z̄₂`↦{Z̄₁Z̄₂ joint(0)}; 1`Z̄₁`↦{X̄₁ pass(2)}; 2`X̄₂`↦{X̄₂ pass(1)}. -/
def fmMerge : Nat → List Nat := fun s => if s == 0 then [0] else if s == 1 then [2] else [1]

/-- The welded diagram: `weldK 6 (weldK 3 layerA merge) layerA`. -/
def mixLaS : LaSre := weldK 6 (weldK 3 layerA FormalRV.QEC.Gidney21.mergeZLaS mixConn) layerA mixConn

/-- The welded surface: thread Layer A's flows up through the merge, then up
through Layer C (= Layer A).  Inner weld uses the per-half flow maps; outer weld
copies the inner composite (`fun s => [s]`) and re-maps the top Layer A. -/
def mixSurf : Surf :=
  weldSurfP 6 (weldSurfP 3 layerASurf FormalRV.QEC.Gidney21.mergeZSurf fmLayer fmMerge) layerASurf
    (fun s => [s]) fmLayer

/-- Ports: `q₂` in/out at `(0,0)` blue=`KI`; `q₁` in/out at `(1,0)` blue=`KJ`
(z_basis J — the two H's cancel, so `q₁` reads `X̄₁`). -/
def mixPorts : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨0, 0, 8, 4, 5⟩, ⟨1, 0, 0, 5, 4⟩, ⟨1, 0, 8, 5, 4⟩]

/-- Spec: flow 0 `X̄₁Z̄₂` (Z on q₂, X on q₁ — the MEASURED joint); flow 1 `Z̄₁`
(passes); flow 2 `X̄₂` (passes). -/
def mixPaulis : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, 0 => Pauli.Z | 0, 1 => Pauli.Z | 0, 2 => Pauli.X | 0, 3 => Pauli.X  -- X̄₁Z̄₂
  | 1, 2 => Pauli.Z | 1, 3 => Pauli.Z                                       -- Z̄₁
  | 2, 0 => Pauli.X | 2, 1 => Pauli.X                                       -- X̄₂
  | _, _ => Pauli.I

/-- Debug handle. -/
theorem mix_report :
    LaSReport mixLaS mixSurf mixPorts mixPaulis 3 = [] := by native_decide

/-- **★ THE FAITHFUL MIXED MERGE IS VERIFIED LATTICE SURGERY ★** — the welded
`H₁ ; Z-merge ; H₁` diagram passes the COMPLETE `LaSCorrectFull` against the
`X̄₁Z̄₂` spec.  The promoted `[hgate, zMerge, hgate]` sequence provably composes
into ONE spacetime diagram realizing the mixed measurement — color-consistently
(the interior seam is a pure `Z`-seam; the `H` makes `q₁`'s joined plane carry
`X̄₁`), no twist, no port relabel.  The promotion's weld is sound. -/
theorem faithfulMixedMerge_fully_correct :
    LaSCorrectFull mixLaS mixSurf mixPorts mixPaulis 3 = true := by native_decide

/-- TEETH: the SAME welded diagram does NOT realize `Z̄₁Z̄₂` (the un-conjugated
joint) — claiming `Z` on `q₁` fails `portsOK`, because the `H` rotated `q₁` so
its joined `KI` plane carries `X̄₁` against its blue=`KJ` port.  So the diagram
genuinely measures `X` on `q₁` (color-anchored by the `H`), not `Z` — the weld
is non-vacuous, and the basis is physical. -/
def mixPaulis_wrongZ : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, 0 => Pauli.Z | 0, 1 => Pauli.Z | 0, 2 => Pauli.Z | 0, 3 => Pauli.Z  -- claim Z̄₁Z̄₂
  | 1, 2 => Pauli.Z | 1, 3 => Pauli.Z
  | 2, 0 => Pauli.X | 2, 1 => Pauli.X
  | _, _ => Pauli.I

theorem faithfulMixedMerge_not_ZZ :
    LaSCorrectFull mixLaS mixSurf mixPorts mixPaulis_wrongZ 3 = false := by native_decide

/-- The welded diagram is 9 time-steps tall (three 3-step layers). -/
theorem mixLaS_maxK : mixLaS.maxK = 9 := by native_decide

/-! ## §4. The faithful mixed merge as a discharged schedule obligation. -/

/-- The welded `H₁ ; Z-merge ; H₁` as a `ScheduleLaS` — the GOLD-STANDARD faithful
realization of `M_{X₁Z₂}`: one verified diagram, basis physically anchored by the
`H`, no port-reinterpretation. -/
def faithfulMxzSchedule : FormalRV.QEC.Gidney21.ScheduleLaS :=
  { L := mixLaS, S := mixSurf, ports := mixPorts, paulis := mixPaulis, nStab := 3 }

/-- **★ THE PROMOTED MIXED MERGE IS A DISCHARGED OBLIGATION ★** — the welded
diagram satisfies `ScheduleImplementsSpec`, so the promotion's
`[hgate, zMerge, hgate]` is realized by ONE verified lattice-surgery schedule
measuring `X̄₁Z̄₂`.  Unlike the flow-level `mxzMerge` (which the color check
rejects), THIS realization is color-consistent — the seam is a pure `Z`-seam and
the `H` supplies the basis change physically. -/
theorem faithfulMxz_implements_spec :
    FormalRV.QEC.Gidney21.ScheduleImplementsSpec faithfulMxzSchedule = true :=
  faithfulMixedMerge_fully_correct

end FormalRV.QEC.LaSre
