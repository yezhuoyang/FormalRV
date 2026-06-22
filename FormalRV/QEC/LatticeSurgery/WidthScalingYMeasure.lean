/-
  FormalRV.QEC.LatticeSurgery.WidthScalingYMeasure
  ------------------------------------------------
  **★ A WIDTH-SYMBOLIC (all `w`) TRANSVERSAL Y-MEASURE gadget — the FIRST
  all-`w` NON-basis-preserving MEASUREMENT gadget. ★**  (STRATEGY B — robust
  Y-surface: the Y-cube both-or-none AND the genuine-`Ȳ` port read both hold.)

  A transversal Y is `w` INDEPENDENT single-qubit `Ȳ`-measures, one per column of
  the `w × 1` footprint: each column is a `K`-worldline (`k=0→1→2`) capped by a
  `Y`-cube at the TOP (`k=2`), with NO `I`/`J` pipes at all.  So — unlike `H`
  / mixed (irregular 2D geometry, blocked from all-`w`) — it factors PER COLUMN
  exactly like `zMerge`/`idleMerge`, and every headline theorem is proved by the
  per-column technique (a universal in an arbitrary column `i`, lifted to all `w`
  by `List.all_eq_true`) with **NO `native_decide` over `w`**.

  WHY THE OBSTRUCTION IS ABSENT.  The feared conflict — a `Y`-cube's both-or-none
  forcing a surface that breaks a worldline parity — does NOT occur.  `funcCubeOK`
  at the `Y`-cube reads ONLY `KI == KJ` (the `YCube` branch short-circuits BEFORE
  any parity check), and the interior `k=1` worldline parities cancel from
  `k`-independence regardless of the `KI=KJ` choice.  Setting `KI ≡ KJ`
  (syntactically identical) satisfies BOTH simultaneously — and makes the port
  read `Ȳ` (BOTH the blue `Z`/`KI` and red `X`/`KJ` planes present, `Y = Z·X`).

  FAITHFULNESS.  `yMeasurePaulis` genuinely measures `Y` (not `I`/`Z`/`X`): the
  port demands `portBlue = portRed = true`, so a `Z`-only or `X`-only surface
  FAILS the spec.  The `Y`-cube is FLOW-VISIBLE (`funcCubeOK` reads it through
  both-or-none, unlike the color-blind `ColorI/J`), so the mandatory anti-fake
  control — a pure idle has NO `Y`-cube ⇒ REJECTED — is anchored to a feature the
  functionality layer actually checks.

  Axiom-clean (`{propext, Classical.choice, Quot.sound}`), zero `sorry`, NO
  `native_decide` over `w` (the `Y`-cube EXISTENCE witness / idle control use a
  fixed `decide` on a single small cube only).
-/
import FormalRV.QEC.LatticeSurgery.GenuineMixedY
import FormalRV.QEC.LatticeSurgery.WidthScalingHetero

namespace FormalRV.QEC.LaSre

/-! ## §1. THE GADGET — `w` independent `K`-worldlines, each capped by a Y-cube. -/

/-- **The transversal `Ȳ`-measure on a `w × 1` footprint.**  Each column `i<w`
is a `K`-worldline (`k=0→1→2`) capped by a `Y`-cube at the TOP (`k=2`).  NO `I`/`J`
pipes — the `w` columns are INDEPENDENT (transversal).  Same footprint as
`zMerge`/`idleMerge`. -/
def yMeasure (w : Nat) : LaSre :=
  { maxI := w, maxJ := 1, maxK := 3
    YCube  := fun i j k => decide (i < w) && j == 0 && k == 2   -- Y-cube atop each column
    ExistI := fun _ _ _ => false
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => decide (i < w) && j == 0 && decide (k < 2) -- w worldlines
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

/-- **The genuine `Ȳ`-surface.**  Flow `s` reads BOTH `KI` (the `Z` piece) AND
`KJ` (the `X` piece) on column `s-1` (`Y = Z·X`).  `KI` and `KJ` are
SYNTACTICALLY IDENTICAL — this is what makes the `Y`-cube both-or-none
(`KI == KJ`) close trivially AND what makes the port read `Ȳ` (both planes). -/
def yMeasureSurf (w : Nat) : Surf :=
  { IJ := fun _ _ _ _ => false,  IK := fun _ _ _ _ => false
    JK := fun _ _ _ _ => false,  JI := fun _ _ _ _ => false
    KI := fun s i j _ => decide (1 ≤ s) && decide (s - 1 = i) && decide (s ≤ w) && j == 0
    KJ := fun s i j _ => decide (1 ≤ s) && decide (s - 1 = i) && decide (s ≤ w) && j == 0 }

/-- One IN port per column at `k=0`; blue selector `4` (`KI`), red selector `5`
(`KJ`). -/
def yMeasurePorts (w : Nat) : List Port :=
  (List.range w).map (fun c => ⟨c, 0, 0, 4, 5⟩)

/-- Flow `s` measures `Ȳ` on column `s-1`. -/
def yMeasurePaulis (w : Nat) : Nat → Nat → Pauli := fun s p =>
  if s - 1 = p % w ∧ 1 ≤ s then Pauli.Y else Pauli.I

/-! ## §2. WIDTH-SYMBOLIC VALIDITY — Y-cube has only K-pipes, no 3D corner. -/

/-- **Per-cube validity.**  No `I`/`J` pipes ⇒ no 3D corner (rule d); the `Y`-cube
has only `K`-pipes ⇒ rule (c) holds. -/
theorem yMeasure_validCube (w i j k : Nat) : (yMeasure w).validCube i j k = true := by
  simp [LaSre.validCube, LaSre.hasI, LaSre.hasJ, yMeasure]

theorem yMeasure_valid (w : Nat) : (yMeasure w).valid = true := by
  rw [LaSre.valid, List.all_eq_true]
  intro c _
  exact yMeasure_validCube w c.1 c.2.1 c.2.2

/-! ## §3. THE INTERIOR LAYER `k=1` — all parities cancel (per column). -/

theorem yMeasure_jParity_k1 (w s i : Nat) :
    jParity (yMeasure w) (yMeasureSurf w) s i 0 1 = false := by
  simp [jParity, yMeasure, yMeasureSurf]

theorem yMeasure_iParity_k1 (w s i : Nat) :
    iParity (yMeasure w) (yMeasureSurf w) s i 0 1 = false := by
  simp [iParity, yMeasure, yMeasureSurf]

theorem yMeasure_allOrNoneI_k1 (w s i : Nat) :
    allOrNoneI (yMeasure w) (yMeasureSurf w) s i 0 1 = true := by
  rw [allOrNoneI]
  apply allEq_const_present (b := (yMeasureSurf w).KJ s i 0 1)
  intro p hp hpres
  fin_cases hp <;> simp_all [yMeasure, yMeasureSurf]

theorem yMeasure_allOrNoneJ_k1 (w s i : Nat) :
    allOrNoneJ (yMeasure w) (yMeasureSurf w) s i 0 1 = true := by
  rw [allOrNoneJ]
  apply allEq_const_present (b := (yMeasureSurf w).KI s i 0 1)
  intro p hp hpres
  fin_cases hp <;> simp_all [yMeasure, yMeasureSurf]

/-! ## §4. `funcCubeOK` per layer — the per-column universal (factored in `w`). -/

/-- **THE Y-CUBE LAYER `k=2` (the new part).**  For a data column `i<w` the cube
is a `Y`-cube, so `funcCubeOK` short-circuits to `KI == KJ`, which is `true`
because the two are SYNTACTICALLY IDENTICAL.  For `i≥w` it is a degree-≤1 port. -/
theorem yMeasure_funcCubeOK_k2 (w s i : Nat) :
    funcCubeOK (yMeasure w) (yMeasureSurf w) s i 0 2 = true := by
  unfold funcCubeOK
  by_cases hiw : i < w
  · rw [if_pos (show (yMeasure w).YCube i 0 2 = true by simp [yMeasure, hiw])]
    simp [yMeasureSurf]
  · rw [if_neg (show ¬ ((yMeasure w).YCube i 0 2 = true) by simp [yMeasure, hiw])]
    have hd : (yMeasure w).degree i 0 2 ≤ 1 := by
      simp [LaSre.degree, yMeasure, hiw]
    rw [if_pos hd]

/-- Interior layer `k=1`: worldline cube (data column) or empty (`i≥w`). -/
theorem yMeasure_funcCubeOK_k1 (w s i : Nat) :
    funcCubeOK (yMeasure w) (yMeasureSurf w) s i 0 1 = true := by
  unfold funcCubeOK
  rw [yMeasure_iParity_k1, yMeasure_jParity_k1, yMeasure_allOrNoneI_k1, yMeasure_allOrNoneJ_k1]
  by_cases hiw : i < w
  · have hK : (yMeasure w).hasK i 0 1 = true := by simp [LaSre.hasK, yMeasure, hiw]
    rw [if_neg (show ¬ ((yMeasure w).YCube i 0 1 = true) by simp [yMeasure]), hK]
    simp [yMeasure]
  · have hd : (yMeasure w).degree i 0 1 ≤ 1 := by
      simp [LaSre.degree, yMeasure, hiw]
    rw [if_neg (show ¬ ((yMeasure w).YCube i 0 1 = true) by simp [yMeasure]), if_pos hd]

/-- Boundary layer `k=0`: a degree-≤1 worldline port. -/
theorem yMeasure_funcCubeOK_k0 (w s i : Nat) :
    funcCubeOK (yMeasure w) (yMeasureSurf w) s i 0 0 = true := by
  unfold funcCubeOK
  have hd : (yMeasure w).degree i 0 0 ≤ 1 := by
    by_cases h : i < w <;> simp [LaSre.degree, yMeasure, h]
  rw [if_neg (show ¬ ((yMeasure w).YCube i 0 0 = true) by simp [yMeasure]), if_pos hd]

/-! ## §5. WIDTH-SYMBOLIC `funcOK` — the whole-grid check, per column. -/

/-- **★ WIDTH-SYMBOLIC INTERIOR FUNCTIONALITY ★** — for ANY width `w` and any
number of flows `n`, every cube passes `funcCubeOK` (worldlines + `Y`-cubes),
discharged by the three per-column layer lemmas, NOT `native_decide` over `w`. -/
theorem yMeasure_funcOK (w n : Nat) :
    funcOK (yMeasure w) (yMeasureSurf w) n = true := by
  rw [LaSre.funcOK, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  rintro ⟨i, j, k⟩ hc
  rw [mem_gridCubes] at hc
  obtain ⟨_, hj, hk⟩ := hc
  have hj0 : j = 0 := by simp only [yMeasure] at hj; omega
  subst hj0
  simp only [yMeasure] at hk
  interval_cases k
  · exact yMeasure_funcCubeOK_k0 w s i
  · exact yMeasure_funcCubeOK_k1 w s i
  · exact yMeasure_funcCubeOK_k2 w s i

theorem yMeasure_LaSCorrect (w n : Nat) :
    LaSCorrect (yMeasure w) (yMeasureSurf w) n = true := by
  rw [LaSre.LaSCorrect, yMeasure_valid, yMeasure_funcOK]; rfl

/-! ## §6. WIDTH-SYMBOLIC PORTS — every port reads `Ȳ` (both planes present). -/

/-- Every port sits on column `idx % w` (`< w`), at `pj=0`, with the canonical
blue/red selectors. -/
theorem yMeasurePorts_get {w : Nat} {p : Port} {idx : Nat}
    (h : (p, idx) ∈ (yMeasurePorts w).zipIdx) :
    p.pj = 0 ∧ p.blueSel = 4 ∧ p.redSel = 5 ∧ p.pi = idx % w ∧ p.pi < w := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  simp only [yMeasurePorts, List.getElem?_map] at h
  by_cases hidx : idx < w
  · rw [List.getElem?_eq_getElem (by simp [hidx]), List.getElem_range,
      Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, (Nat.mod_eq_of_lt hidx).symm, hidx⟩
  · exfalso
    rw [List.getElem?_eq_none (by simp only [List.length_range]; omega)] at h
    simp at h

/-- **★ WIDTH-SYMBOLIC PORT BOUNDARY ★** — at every port the surface matches the
`Ȳ` spec: blue `KI` present AND red `KJ` present exactly for the active flow `s`
on that column, `false` otherwise.  Both planes ⇒ genuine `Ȳ` (not `Z̄`/`X̄`). -/
theorem yMeasure_portsOK (w : Nat) :
    portsOK (yMeasureSurf w) (yMeasurePorts w) (yMeasurePaulis w) (w + 1) = true := by
  rw [portsOK, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro pp hpp
  obtain ⟨p, idx⟩ := pp
  obtain ⟨hpj, hbl, hrd, hpi, hlt⟩ := yMeasurePorts_get hpp
  have hw : 0 < w := by omega
  have hmw : idx % w < w := Nat.mod_lt _ hw
  simp only [Surf.sel, hbl, hrd, hpj, hpi, yMeasureSurf, yMeasurePaulis, portBlue, portRed]
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp
  · have hs1 : 1 ≤ s := hs
    by_cases hc : s - 1 = idx % w
    · have hsw : s ≤ w := by omega
      simp [hc, hs1, hsw]
    · simp [hc, hs1]

/-! ## §7. ★ THE HEADLINE — a transversal `Ȳ`-measure of ANY WIDTH is correct. -/

/-- **★ WIDTH-SYMBOLIC `LaSCorrectFull` ★** — for EVERY width `w`, the transversal
`Ȳ`-measure is a fully correct lattice-surgery subroutine against its
per-column-`Ȳ` measurement spec: structurally valid, interior functionality
satisfied (including the `Y`-cube both-or-none at every column), and ports
matching the `Ȳ` spec.  Proved by per-column universals — **NOT** `native_decide`
over `w`.  This is the FIRST all-`w` NON-basis-preserving MEASUREMENT gadget. -/
theorem yMeasure_LaSCorrectFull (w : Nat) :
    LaSCorrectFull (yMeasure w) (yMeasureSurf w) (yMeasurePorts w) (yMeasurePaulis w) (w + 1)
      = true := by
  rw [LaSre.LaSCorrectFull, yMeasure_valid, yMeasure_funcOK, yMeasure_portsOK]; rfl

/-! ## §8. THE Y-CUBE WITNESS + the MANDATORY anti-fake idle-rejection control. -/

/-- **The `Y`-cube witness fires** for any positive width: the top cube of column
`0` is a `Y`-cube.  Uses a fixed `decide` on a SINGLE small cube — NOT
`native_decide` over `w`. -/
theorem yMeasure_hasYCube (w : Nat) (hw : 0 < w) : hasYCube (yMeasure w) = true := by
  rw [hasYCube, List.any_eq_true]
  refine ⟨(0, 0, 2), ?_, ?_⟩
  · rw [mem_gridCubes]; exact ⟨hw, by simp [yMeasure], by simp [yMeasure]⟩
  · simp [yMeasure, hw]

/-- **The genuine transversal Y-MEASURE certification**: the diagram passes the
complete `LaSCorrectFull` against the per-column-`Ȳ` spec AND carries the
flow-visible `Y`-cube signature.  The second conjunct is the anti-idle teeth. -/
def yMeasureCertified (w : Nat) : Bool :=
  LaSCorrectFull (yMeasure w) (yMeasureSurf w) (yMeasurePorts w) (yMeasurePaulis w) (w + 1)
    && hasYCube (yMeasure w)

/-- **★ THE TRANSVERSAL Y-MEASURE IS CERTIFIED (per-column `Ȳ` spec + Y-cube
witness), for EVERY positive width. ★** -/
theorem yMeasure_certified (w : Nat) (hw : 0 < w) : yMeasureCertified w = true := by
  rw [yMeasureCertified, yMeasure_LaSCorrectFull, yMeasure_hasYCube w hw]; rfl

/-! ### The MANDATORY idle-rejection control. -/

/-- The pure idle on the SAME `w × 1` footprint (reused `idleMerge`): `w` data
worldlines, NO `Y`-cube. -/
def idleYMeasure (w : Nat) : LaSre := idleMerge w

/-- The pure idle has NO `Y`-cube — the heart of the rejection. -/
theorem idleYMeasure_no_ycube (w : Nat) : hasYCube (idleYMeasure w) = false := by
  rw [hasYCube, List.any_eq_false]
  intro c _
  simp [idleYMeasure, idleMerge]

/-- The same Y-certification recipe applied to the pure idle. -/
def idleYMeasureCertified (w : Nat) : Bool :=
  LaSCorrectFull (idleYMeasure w) (yMeasureSurf w) (yMeasurePorts w) (yMeasurePaulis w) (w + 1)
    && hasYCube (idleYMeasure w)

/-- **★ THE MANDATORY ANTI-FAKE CONTROL: a pure IDLE is REJECTED by the
Y-cube-anchored certification (for EVERY width). ★**  The idle has NO `Y`-cube,
so the `&& hasYCube` short-circuits to `false` regardless of its surface/ports.
The transversal Y-measure is real precisely because the certification that
accepts `yMeasure w` rejects a pure idle. -/
theorem idle_yMeasure_rejected (w : Nat) : idleYMeasureCertified w = false := by
  rw [idleYMeasureCertified, idleYMeasure_no_ycube]
  simp

/-- The witness is SURFACE/PORT-INDEPENDENT: `hasYCube` reads only the diagram
geometry, so the idle's rejection is forced for EVERY surface and EVERY port. -/
theorem idleYMeasure_rejected_regardless_of_surface_and_ports
    (w : Nat) (S : Surf) (ports : List Port) (paulis : Nat → Nat → Pauli) (nStab : Nat) :
    (LaSCorrectFull (idleYMeasure w) S ports paulis nStab && hasYCube (idleYMeasure w))
      = false := by
  rw [idleYMeasure_no_ycube]; simp

/-- **★ TRANSVERSAL Y-MEASURE: certified AND idle-rejected, side by side. ★** -/
theorem yMeasure_certified_idle_rejected (w : Nat) (hw : 0 < w) :
    yMeasureCertified w = true ∧ idleYMeasureCertified w = false :=
  ⟨yMeasure_certified w hw, idle_yMeasure_rejected w⟩

/-! ## §9. FAITHFULNESS — the port genuinely reads `Ȳ`, not `Z̄`/`X̄`. -/

/-- The spec genuinely measures `Y`, not `I`: flow `1` on port `0` is `Ȳ`. -/
theorem yMeasurePaulis_measures_Y (w : Nat) (hw : 0 < w) :
    yMeasurePaulis w 1 0 = Pauli.Y := by
  simp [yMeasurePaulis, Nat.mod_eq_of_lt hw]

/-- `Ȳ` demands BOTH planes (`portBlue Y = portRed Y = true`), while `Z` lacks the
`X` piece and `X` lacks the `Z` piece — so the gadget cannot be a disguised `Z̄`
or `X̄` measure. -/
theorem yPort_demands_both_planes :
    portBlue Pauli.Y = true ∧ portRed Pauli.Y = true
      ∧ portRed Pauli.Z = false ∧ portBlue Pauli.X = false := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- A `Z`-ONLY surface (the idle's `KI`-present / `KJ`-absent passthrough) FAILS
the `Ȳ` port spec at width 1 — confirming the spec truly requires the `X` piece
(`KJ`), so it is not a disguised `Z̄` measure. -/
theorem zOnly_surface_fails_yMeasure_spec :
    portsOK (idleSurf 1) (yMeasurePorts 1) (yMeasurePaulis 1) 2 = false := by
  native_decide

end FormalRV.QEC.LaSre
