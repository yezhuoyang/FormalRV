/-
  FormalRV.QEC.LatticeSurgery.WidthScalingYChain
  ----------------------------------------------
  **★ A TERMINAL Y-MEASUREMENT welded into the chain engine — all-`w`, all-`N`,
  via the EXISTING catalog machinery (STRATEGY B). ★**

  `WidthScalingYMeasure` built a width-symbolic transversal `Ȳ`-measure gadget
  `yMeasure w` (a `Y`-cube atop every column).  This file wires it into the
  `weldChain` engine as the TERMINAL (top) link of a depth-`(N+1)` chain whose
  body is `N` `Y`-FLOW IDLES `yIdle w` — `w` worldlines carrying the SAME Y-flow
  surface `yMeasureSurf w` (`KI ≡ KJ`), no `Y`-cube, passing the flow through —
  capped by the terminal `yMeasure w` whose `Y`-cubes sit at the chain TOP.

  HONEST SCOPE — this is a **Y-FLOW chain**, NOT a Z-merge chain with a Y readout.
  `yMeasure` carries the Y-flow (`KI ≡ KJ` per column), not the Z-merge flow
  (`Z` flow0 + `X` passthrough), so it does NOT compose after a `zMerge`; it
  composes after `Y`-flow idles, which share its canonical Y-flow worldline
  boundary.  Because every gadget shares that layer-0 boundary, the chain
  interfaces collapse to each gadget's OWN self-interface cert.

  STRATEGY B (engine reuse) — SUCCEEDED.  Contrary to the scouting fear that the
  catalog could not express a terminal-only measure (because the `yMeasure`
  self-weld puts a `Y`-cube at an interior seam, feared `native_decide`-only), we
  prove `yMeasure`'s self-interface cert WIDTH-SYMBOLICALLY: at the interior seam
  the `Y`-cube's `funcCubeOK` SHORT-CIRCUITS to `KI == KJ` (the two are
  syntactically identical), exactly as in the atomic `yMeasure_funcCubeOK_k2`.
  So both `yIdle` and `yMeasure` become honest `CatalogEntry`s over the shared
  Y-flow bottom, and `catalog_chainOK` discharges the whole terminal chain by
  list induction.  (`yMeasure` is placed LAST, so its self-cert is in fact never
  consumed by the chain — only the `yIdle` prefix gets interface-checked — but it
  is proven anyway, making the entry a first-class catalog citizen.)

  Axiom-clean (`{propext, Classical.choice, Quot.sound}`), zero `sorry`, NO
  `native_decide` over `w` OR `N` for any all-`w`/all-`N` headline.
-/
import FormalRV.QEC.LatticeSurgery.WidthScalingYMeasure

namespace FormalRV.QEC.LaSre

/-! ## §1. `yIdle` — the Y-FLOW idle: `w` worldlines, NO `Y`-cube, Y-flow surface.

  `yIdle w` is the SAME diagram as `idleMerge w` (`w` data `K`-worldlines, no
  `Y`-cube), but PAIRED with the Y-flow surface `yMeasureSurf w` (`KI ≡ KJ`)
  instead of the Z-flow `idleSurf w`.  It carries the Y-flow through, untouched —
  the body link that lets a `Y`-flow thread up to the terminal measure. -/

/-- The Y-flow idle (diagram = `idleMerge`). -/
def yIdle (w : Nat) : LaSre := idleMerge w

/-- The Y-flow idle surface — the SAME Y-flow as `yMeasure` (`KI ≡ KJ`). -/
def yIdleSurf (w : Nat) : Surf := yMeasureSurf w

/-! ### §1a. Interior `k=1` cancellations (per column) against the Y-flow surface. -/

theorem yIdle_jParity_k1 (w s i : Nat) :
    jParity (yIdle w) (yIdleSurf w) s i 0 1 = false := by
  simp [jParity, yIdle, idleMerge, yIdleSurf, yMeasureSurf]

theorem yIdle_iParity_k1 (w s i : Nat) :
    iParity (yIdle w) (yIdleSurf w) s i 0 1 = false := by
  simp [iParity, yIdle, idleMerge, yIdleSurf, yMeasureSurf]

theorem yIdle_allOrNoneI_k1 (w s i : Nat) :
    allOrNoneI (yIdle w) (yIdleSurf w) s i 0 1 = true := by
  rw [allOrNoneI]
  apply allEq_const_present (b := (yIdleSurf w).KJ s i 0 1)
  intro p hp hpres
  fin_cases hp <;> simp_all [yIdle, idleMerge, yIdleSurf, yMeasureSurf]

theorem yIdle_allOrNoneJ_k1 (w s i : Nat) :
    allOrNoneJ (yIdle w) (yIdleSurf w) s i 0 1 = true := by
  rw [allOrNoneJ]
  apply allEq_const_present (b := (yIdleSurf w).KI s i 0 1)
  intro p hp hpres
  fin_cases hp <;> simp_all [yIdle, idleMerge, yIdleSurf, yMeasureSurf]

/-! ### §1b. `funcCubeOK` per layer (no `Y`-cube layer — `k=2` is a degree-≤1 port). -/

theorem yIdle_funcCubeOK_k1 (w s i : Nat) :
    funcCubeOK (yIdle w) (yIdleSurf w) s i 0 1 = true := by
  unfold funcCubeOK
  rw [yIdle_iParity_k1, yIdle_jParity_k1, yIdle_allOrNoneI_k1, yIdle_allOrNoneJ_k1]
  by_cases hiw : i < w
  · have hK : (yIdle w).hasK i 0 1 = true := by simp [LaSre.hasK, yIdle, idleMerge, hiw]
    rw [hK]; simp [yIdle, idleMerge]
  · have hd : (yIdle w).degree i 0 1 ≤ 1 := by
      simp only [LaSre.degree, yIdle, idleMerge]; simp [hiw]
    rw [if_neg (show ¬((yIdle w).YCube i 0 1 = true) by simp [yIdle, idleMerge]), if_pos hd]

theorem yIdle_funcCubeOK_k0 (w s i : Nat) :
    funcCubeOK (yIdle w) (yIdleSurf w) s i 0 0 = true := by
  unfold funcCubeOK
  have hd : (yIdle w).degree i 0 0 ≤ 1 := by
    by_cases h : i < w <;> simp [LaSre.degree, yIdle, idleMerge, h]
  rw [if_neg (show ¬((yIdle w).YCube i 0 0 = true) by simp [yIdle, idleMerge]), if_pos hd]

theorem yIdle_funcCubeOK_k2 (w s i : Nat) :
    funcCubeOK (yIdle w) (yIdleSurf w) s i 0 2 = true := by
  unfold funcCubeOK
  have hd : (yIdle w).degree i 0 2 ≤ 1 := by
    by_cases h : i < w <;> simp [LaSre.degree, yIdle, idleMerge, h]
  rw [if_neg (show ¬((yIdle w).YCube i 0 2 = true) by simp [yIdle, idleMerge]), if_pos hd]

/-! ### §1c. `yIdle` validity + functionality (all-`w`, per-column). -/

/-- `yIdle`'s diagram = `idleMerge`, so structural validity is reused. -/
theorem yIdle_valid (w : Nat) : (yIdle w).valid = true := idle_valid w

/-- **★ `yIdle` is interior-correct against the Y-flow surface, for ALL `w`. ★** -/
theorem yIdle_funcOK (w n : Nat) :
    funcOK (yIdle w) (yIdleSurf w) n = true := by
  rw [LaSre.funcOK, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  rintro ⟨i, j, k⟩ hc
  rw [mem_gridCubes] at hc
  obtain ⟨_, hj, hk⟩ := hc
  have hj0 : j = 0 := by simp only [yIdle, idleMerge] at hj; omega
  subst hj0
  simp only [yIdle, idleMerge] at hk
  interval_cases k
  · exact yIdle_funcCubeOK_k0 w s i
  · exact yIdle_funcCubeOK_k1 w s i
  · exact yIdle_funcCubeOK_k2 w s i

/-! ## §2. `yIdle` SELF-INTERFACE CERTS (width-symbolic).

  `yIdle`'s self-weld diagram is exactly `iSeam w` (`idleMerge` welded to itself),
  so all `ExistK/I/J`/`YCube` seam reductions are the existing `iSeam_*` lemmas.
  Only the SURFACE differs (Y-flow `yIdleSurf` vs Z-flow `idleSurf`), so we redo
  the surface seam reductions + parity cancellations for the Y-flow. -/

/-- The Y-flow stitched self-seam surface. -/
abbrev yiSeamSurf (w : Nat) : Surf := stitchSurf 3 (yIdleSurf w) (yIdleSurf w)

theorem yiSeamSurf_KI1 (w s i : Nat) :
    (yiSeamSurf w).KI s i 0 1 = (yIdleSurf w).KI s i 0 0 := by
  simp only [yiSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem yiSeamSurf_KI2 (w s i : Nat) :
    (yiSeamSurf w).KI s i 0 2 = (yIdleSurf w).KI s i 0 0 := by
  simp only [yiSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem yiSeamSurf_KI3 (w s i : Nat) :
    (yiSeamSurf w).KI s i 0 3 = (yIdleSurf w).KI s i 0 0 := by
  simp only [yiSeamSurf, stitchSurf]; rw [if_neg (by norm_num)]
theorem yiSeamSurf_KJ1 (w s i : Nat) :
    (yiSeamSurf w).KJ s i 0 1 = (yIdleSurf w).KJ s i 0 0 := by
  simp only [yiSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem yiSeamSurf_KJ2 (w s i : Nat) :
    (yiSeamSurf w).KJ s i 0 2 = (yIdleSurf w).KJ s i 0 0 := by
  simp only [yiSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem yiSeamSurf_KJ3 (w s i : Nat) :
    (yiSeamSurf w).KJ s i 0 3 = (yIdleSurf w).KJ s i 0 0 := by
  simp only [yiSeamSurf, stitchSurf]; rw [if_neg (by norm_num)]

theorem yIdle_refValid_sym (w : Nat) :
    weldInterfaceValidOK2 3 (yIdle w) (yIdle w) (zChainConn w) w 1 = true :=
  idle_refValid_sym w

theorem yiSeam_iParity2 (w s i : Nat) :
    iParity (iSeam w) (yiSeamSurf w) s i 0 2 = false := by
  rw [iParity, show (2:Nat)-1=1 from rfl,
    iSeam_ExistJ, iSeam_ExistK2, iSeam_ExistK1, yiSeamSurf_KI2, yiSeamSurf_KI1]
  simp
theorem yiSeam_iParity3 (w s i : Nat) :
    iParity (iSeam w) (yiSeamSurf w) s i 0 3 = false := by
  rw [iParity, show (3:Nat)-1=2 from rfl,
    iSeam_ExistJ, iSeam_ExistK3, iSeam_ExistK2, yiSeamSurf_KI3, yiSeamSurf_KI2]
  simp
theorem yiSeam_jParity2 (w s i : Nat) :
    jParity (iSeam w) (yiSeamSurf w) s i 0 2 = false := by
  rw [jParity, show (2:Nat)-1=1 from rfl]
  simp only [iSeam_ExistI, iSeam_ExistK2, iSeam_ExistK1, yiSeamSurf_KJ2, yiSeamSurf_KJ1]
  simp
theorem yiSeam_jParity3 (w s i : Nat) :
    jParity (iSeam w) (yiSeamSurf w) s i 0 3 = false := by
  rw [jParity, show (3:Nat)-1=2 from rfl]
  simp only [iSeam_ExistI, iSeam_ExistK3, iSeam_ExistK2, yiSeamSurf_KJ3, yiSeamSurf_KJ2]
  simp
theorem yiSeam_allOrNoneI2 (w s i : Nat) :
    allOrNoneI (iSeam w) (yiSeamSurf w) s i 0 2 = true := by
  rw [allOrNoneI, show (2:Nat)-1=1 from rfl,
    iSeam_ExistJ, iSeam_ExistK2, iSeam_ExistK1, yiSeamSurf_KJ2, yiSeamSurf_KJ1]
  apply allEq_const_present (b := (yIdleSurf w).KJ s i 0 0)
  intro p hp hpres; fin_cases hp <;> simp_all
theorem yiSeam_allOrNoneI3 (w s i : Nat) :
    allOrNoneI (iSeam w) (yiSeamSurf w) s i 0 3 = true := by
  rw [allOrNoneI, show (3:Nat)-1=2 from rfl,
    iSeam_ExistJ, iSeam_ExistK3, iSeam_ExistK2, yiSeamSurf_KJ3, yiSeamSurf_KJ2]
  apply allEq_const_present (b := (yIdleSurf w).KJ s i 0 0)
  intro p hp hpres; fin_cases hp <;> simp_all
theorem yiSeam_allOrNoneJ2 (w s i : Nat) :
    allOrNoneJ (iSeam w) (yiSeamSurf w) s i 0 2 = true := by
  rw [allOrNoneJ, show (2:Nat)-1=1 from rfl]
  simp only [iSeam_ExistI, iSeam_ExistK2, iSeam_ExistK1, yiSeamSurf_KI2, yiSeamSurf_KI1]
  apply allEq_const_present (b := (yIdleSurf w).KI s i 0 0)
  intro p hp hpres; fin_cases hp <;> simp_all
theorem yiSeam_allOrNoneJ3 (w s i : Nat) :
    allOrNoneJ (iSeam w) (yiSeamSurf w) s i 0 3 = true := by
  rw [allOrNoneJ, show (3:Nat)-1=2 from rfl]
  simp only [iSeam_ExistI, iSeam_ExistK3, iSeam_ExistK2, yiSeamSurf_KI3, yiSeamSurf_KI2]
  apply allEq_const_present (b := (yIdleSurf w).KI s i 0 0)
  intro p hp hpres; fin_cases hp <;> simp_all

theorem yiSeam_funcCubeOK2 (w s i : Nat) :
    funcCubeOK (iSeam w) (yiSeamSurf w) s i 0 2 = true := by
  unfold funcCubeOK
  rw [yiSeam_iParity2, yiSeam_jParity2, yiSeam_allOrNoneI2, yiSeam_allOrNoneJ2]
  by_cases hiw : i < w
  · rw [show (iSeam w).hasK i 0 2 = true by simp only [LaSre.hasK, iSeam_ExistK2]; simp [hiw]]
    rw [if_neg (show ¬((iSeam w).YCube i 0 2 = true) by rw [iSeam_YCube]; simp)]
    rw [if_neg (show ¬((iSeam w).degree i 0 2 ≤ 1) by
      simp only [LaSre.degree, iSeam_ExistK2, iSeam_ExistI, iSeam_ExistJ,
        show (2:Nat)-1=1 from rfl, iSeam_ExistK1]; simp [hiw])]
    simp
  · rw [if_neg (show ¬((iSeam w).YCube i 0 2 = true) by rw [iSeam_YCube]; simp),
      if_pos (show (iSeam w).degree i 0 2 ≤ 1 by
        simp only [LaSre.degree, iSeam_ExistK2, iSeam_ExistI, iSeam_ExistJ,
          show (2:Nat)-1=1 from rfl, iSeam_ExistK1]; simp [hiw])]

theorem yiSeam_funcCubeOK3 (w s i : Nat) :
    funcCubeOK (iSeam w) (yiSeamSurf w) s i 0 3 = true := by
  unfold funcCubeOK
  rw [yiSeam_iParity3, yiSeam_jParity3, yiSeam_allOrNoneI3, yiSeam_allOrNoneJ3]
  by_cases hiw : i < w
  · rw [show (iSeam w).hasK i 0 3 = true by simp only [LaSre.hasK, iSeam_ExistK3]; simp [hiw]]
    rw [if_neg (show ¬((iSeam w).YCube i 0 3 = true) by rw [iSeam_YCube]; simp)]
    rw [if_neg (show ¬((iSeam w).degree i 0 3 ≤ 1) by
      simp only [LaSre.degree, iSeam_ExistK3, iSeam_ExistI, iSeam_ExistJ,
        show (3:Nat)-1=2 from rfl, iSeam_ExistK2]; simp [hiw])]
    simp
  · rw [if_neg (show ¬((iSeam w).YCube i 0 3 = true) by rw [iSeam_YCube]; simp),
      if_pos (show (iSeam w).degree i 0 3 ≤ 1 by
        simp only [LaSre.degree, iSeam_ExistK3, iSeam_ExistI, iSeam_ExistJ,
          show (3:Nat)-1=2 from rfl, iSeam_ExistK2]; simp [hiw])]

/-- **★ `yIdle`'s width-symbolic FUNCTIONALITY self-interface cert. ★** -/
theorem yIdle_refFunc_sym (w : Nat) :
    weldInterfaceOK2 3 (yIdle w) (yIdle w) (yIdleSurf w) (yIdleSurf w)
      (zChainConn w) (w + 1) w 1 = true := by
  rw [weldInterfaceOK2, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro j hj
  have hj0 : j = 0 := by have := List.mem_range.1 hj; omega
  subst hj0
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [if_pos (by norm_num)]
    show funcCubeOK (iSeam w) (yiSeamSurf w) s i 0 2 = true
    exact yiSeam_funcCubeOK2 w s i
  · show funcCubeOK (iSeam w) (yiSeamSurf w) s i 0 3 = true
    exact yiSeam_funcCubeOK3 w s i

/-! ## §3. `yMeasure` SELF-INTERFACE CERTS (width-symbolic — the KEY STRATEGY-B win).

  The `yMeasure` self-weld `ymSeam w := weldK 3 (yMeasure w) (yMeasure w) conn`
  carries the bottom copy's `Y`-cube at the INTERIOR seam layer `k=2`.  This was
  the feared `native_decide`-only step.  It is NOT: `funcCubeOK` at the `Y`-cube
  SHORT-CIRCUITS to `KI == KJ`, and `yMeasureSurf`'s `KI`/`KJ` are syntactically
  identical, so it closes symbolically for ALL `w` — exactly as in the atomic
  `yMeasure_funcCubeOK_k2`.  At `k=3` (the top copy's `k=0`) there is no `Y`-cube;
  it is a worldline passthrough.  Hence `yMeasure` is a first-class catalog entry. -/

abbrev ymSeam (w : Nat) : LaSre := weldK 3 (yMeasure w) (yMeasure w) (zChainConn w)
abbrev ymSeamSurf (w : Nat) : Surf := stitchSurf 3 (yMeasureSurf w) (yMeasureSurf w)

theorem ymSeam_ExistI (w i j k : Nat) : (ymSeam w).ExistI i j k = false := by
  simp only [ymSeam, weldK, yMeasure]; split <;> rfl
theorem ymSeam_ExistJ (w i j k : Nat) : (ymSeam w).ExistJ i j k = false := by
  simp only [ymSeam, weldK, yMeasure]; split <;> rfl
theorem ymSeam_ExistK1 (w i : Nat) : (ymSeam w).ExistK i 0 1 = decide (i < w) := by
  simp only [ymSeam, weldK]; rw [if_pos (by norm_num)]; simp [yMeasure]
theorem ymSeam_ExistK2 (w i : Nat) : (ymSeam w).ExistK i 0 2 = decide (i < w) := by
  simp only [ymSeam, weldK, zChainConn_contains]; simp [yMeasure]
theorem ymSeam_ExistK3 (w i : Nat) : (ymSeam w).ExistK i 0 3 = decide (i < w) := by
  simp only [ymSeam, weldK]; simp [yMeasure]
/-- At the interior seam `k=2` the bottom copy's `Y`-cube survives (`k < kA`). -/
theorem ymSeam_YCube2 (w i : Nat) : (ymSeam w).YCube i 0 2 = decide (i < w) := by
  simp only [ymSeam, weldK]; rw [if_pos (show (2:Nat)<3 by norm_num)]; simp [yMeasure]
/-- At `k=3` (top copy's `k=0`) there is NO `Y`-cube. -/
theorem ymSeam_YCube3 (w i : Nat) : (ymSeam w).YCube i 0 3 = false := by
  simp only [ymSeam, weldK]; rw [if_neg (by norm_num)]; simp [yMeasure]

theorem ymSeamSurf_KI1 (w s i : Nat) :
    (ymSeamSurf w).KI s i 0 1 = (yMeasureSurf w).KI s i 0 0 := by
  simp only [ymSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem ymSeamSurf_KI2 (w s i : Nat) :
    (ymSeamSurf w).KI s i 0 2 = (yMeasureSurf w).KI s i 0 0 := by
  simp only [ymSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem ymSeamSurf_KI3 (w s i : Nat) :
    (ymSeamSurf w).KI s i 0 3 = (yMeasureSurf w).KI s i 0 0 := by
  simp only [ymSeamSurf, stitchSurf]; rw [if_neg (by norm_num)]
theorem ymSeamSurf_KJ2 (w s i : Nat) :
    (ymSeamSurf w).KJ s i 0 2 = (yMeasureSurf w).KJ s i 0 0 := by
  simp only [ymSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem ymSeamSurf_KJ3 (w s i : Nat) :
    (ymSeamSurf w).KJ s i 0 3 = (yMeasureSurf w).KJ s i 0 0 := by
  simp only [ymSeamSurf, stitchSurf]; rw [if_neg (by norm_num)]

/-- The seam weld has no `I`/`J` pipes ⇒ `validCube` everywhere (even at the
`Y`-cube seam, since the `Y`-cube has only `K`-pipes). -/
theorem ymSeam_validCube (w i j k : Nat) : (ymSeam w).validCube i j k = true := by
  simp only [LaSre.validCube, LaSre.hasI, LaSre.hasJ, ymSeam_ExistI, ymSeam_ExistJ]
  simp

/-- **★ `yMeasure`'s width-symbolic VALIDITY self-interface cert. ★** -/
theorem yMeasure_refValid_sym (w : Nat) :
    weldInterfaceValidOK2 3 (yMeasure w) (yMeasure w) (zChainConn w) w 1 = true := by
  rw [weldInterfaceValidOK2, List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro j _
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [if_pos (by norm_num)]; exact ymSeam_validCube w i j (3 - 1)
  · exact ymSeam_validCube w i j 3

/-- The interior `Y`-cube seam (`k=2`): `funcCubeOK` short-circuits to `KI == KJ`
(syntactically identical) for `i < w`; a degree-≤1 port for `i ≥ w`. -/
theorem ymSeam_funcCubeOK2 (w s i : Nat) :
    funcCubeOK (ymSeam w) (ymSeamSurf w) s i 0 2 = true := by
  unfold funcCubeOK
  by_cases hiw : i < w
  · rw [if_pos (show (ymSeam w).YCube i 0 2 = true by rw [ymSeam_YCube2]; simp [hiw])]
    simp only [ymSeamSurf, stitchSurf]
    rw [if_pos (show (2:Nat) < 3 by norm_num)]
    simp [yMeasureSurf]
  · rw [if_neg (show ¬((ymSeam w).YCube i 0 2 = true) by rw [ymSeam_YCube2]; simp [hiw])]
    rw [if_pos (show (ymSeam w).degree i 0 2 ≤ 1 by
      simp only [LaSre.degree, ymSeam_ExistK2, ymSeam_ExistI, ymSeam_ExistJ,
        show (2:Nat)-1=1 from rfl, ymSeam_ExistK1]; simp [hiw])]

theorem ymSeam_iParity3 (w s i : Nat) :
    iParity (ymSeam w) (ymSeamSurf w) s i 0 3 = false := by
  rw [iParity, show (3:Nat)-1=2 from rfl,
    ymSeam_ExistJ, ymSeam_ExistK3, ymSeam_ExistK2, ymSeamSurf_KI3, ymSeamSurf_KI2]
  simp
theorem ymSeam_jParity3 (w s i : Nat) :
    jParity (ymSeam w) (ymSeamSurf w) s i 0 3 = false := by
  rw [jParity, show (3:Nat)-1=2 from rfl]
  simp only [ymSeam_ExistI, ymSeam_ExistK3, ymSeam_ExistK2, ymSeamSurf_KJ3, ymSeamSurf_KJ2]
  simp
theorem ymSeam_allOrNoneI3 (w s i : Nat) :
    allOrNoneI (ymSeam w) (ymSeamSurf w) s i 0 3 = true := by
  rw [allOrNoneI, show (3:Nat)-1=2 from rfl,
    ymSeam_ExistJ, ymSeam_ExistK3, ymSeam_ExistK2, ymSeamSurf_KJ3, ymSeamSurf_KJ2]
  apply allEq_const_present (b := (yMeasureSurf w).KJ s i 0 0)
  intro p hp hpres; fin_cases hp <;> simp_all
theorem ymSeam_allOrNoneJ3 (w s i : Nat) :
    allOrNoneJ (ymSeam w) (ymSeamSurf w) s i 0 3 = true := by
  rw [allOrNoneJ, show (3:Nat)-1=2 from rfl]
  simp only [ymSeam_ExistI, ymSeam_ExistK3, ymSeam_ExistK2, ymSeamSurf_KI3, ymSeamSurf_KI2]
  apply allEq_const_present (b := (yMeasureSurf w).KI s i 0 0)
  intro p hp hpres; fin_cases hp <;> simp_all

/-- The `k=3` seam (top copy's `k=0`): a plain worldline passthrough, no `Y`-cube. -/
theorem ymSeam_funcCubeOK3 (w s i : Nat) :
    funcCubeOK (ymSeam w) (ymSeamSurf w) s i 0 3 = true := by
  unfold funcCubeOK
  rw [ymSeam_iParity3, ymSeam_jParity3, ymSeam_allOrNoneI3, ymSeam_allOrNoneJ3]
  by_cases hiw : i < w
  · rw [show (ymSeam w).hasK i 0 3 = true by simp only [LaSre.hasK, ymSeam_ExistK3]; simp [hiw]]
    rw [if_neg (show ¬((ymSeam w).YCube i 0 3 = true) by rw [ymSeam_YCube3]; simp)]
    rw [if_neg (show ¬((ymSeam w).degree i 0 3 ≤ 1) by
      simp only [LaSre.degree, ymSeam_ExistK3, ymSeam_ExistI, ymSeam_ExistJ,
        show (3:Nat)-1=2 from rfl, ymSeam_ExistK2]; simp [hiw])]
    simp
  · rw [if_neg (show ¬((ymSeam w).YCube i 0 3 = true) by rw [ymSeam_YCube3]; simp),
      if_pos (show (ymSeam w).degree i 0 3 ≤ 1 by
        simp only [LaSre.degree, ymSeam_ExistK3, ymSeam_ExistI, ymSeam_ExistJ,
          show (3:Nat)-1=2 from rfl, ymSeam_ExistK2]; simp [hiw])]

/-- **★ `yMeasure`'s width-symbolic FUNCTIONALITY self-interface cert ★** — the
interior `Y`-cube at the seam is discharged by the `KI == KJ` short-circuit, for
ALL `w`, with NO `native_decide`.  This is the fact the scout feared impossible. -/
theorem yMeasure_refFunc_sym (w : Nat) :
    weldInterfaceOK2 3 (yMeasure w) (yMeasure w) (yMeasureSurf w) (yMeasureSurf w)
      (zChainConn w) (w + 1) w 1 = true := by
  rw [weldInterfaceOK2, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro j hj
  have hj0 : j = 0 := by have := List.mem_range.1 hj; omega
  subst hj0
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [if_pos (by norm_num)]; exact ymSeam_funcCubeOK2 w s i
  · exact ymSeam_funcCubeOK3 w s i

/-! ## §4. THE Y-FLOW CATALOG — `yIdle` and `yMeasure` over the shared Y-bottom.

  Both gadgets present the SAME layer-0 boundary (`yMeasure w`'s, the canonical
  Y-flow bottom): `yIdle`'s `k=0` worldlines agree with `yMeasure`'s (its top
  `Y`-cube is at `k=2`, not `k=0`), and `yIdleSurf = yMeasureSurf`.  So both are
  `CatalogEntry w (yMeasure w) (yMeasureSurf w)`, and `catalog_chainOK` glues any
  Y-flow sequence by reducing every interface to the head's own self-cert. -/

theorem yIdle_yMeasure_botEqL (w : Nat) : BotEqL (yIdle w) (yMeasure w) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i j <;> simp [yIdle, idleMerge, yMeasure]

theorem yIdle_yMeasure_botEqS (w : Nat) : BotEqS (yIdleSurf w) (yMeasureSurf w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t i j <;> rfl

/-- The Y-flow IDLE catalog entry. -/
def yIdleEntry (w : Nat) : CatalogEntry w (yMeasure w) (yMeasureSurf w) :=
  { g := yIdle w, sg := yIdleSurf w
    hi := rfl, hj := rfl, hk := rfl
    hv := yIdle_valid w, hf := yIdle_funcOK w (w + 1)
    hbL := yIdle_yMeasure_botEqL w
    hbS := yIdle_yMeasure_botEqS w
    rfv := yIdle_refValid_sym w, rff := yIdle_refFunc_sym w }

/-- The terminal Y-MEASURE catalog entry (placed LAST in the chain). -/
def yMeasureEntry (w : Nat) : CatalogEntry w (yMeasure w) (yMeasureSurf w) :=
  { g := yMeasure w, sg := yMeasureSurf w
    hi := rfl, hj := rfl, hk := rfl
    hv := yMeasure_valid w, hf := yMeasure_funcOK w (w + 1)
    hbL := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    hbS := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
            fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    rfv := yMeasure_refValid_sym w, rff := yMeasure_refFunc_sym w }

/-- The terminal entry list: `N` Y-flow idles, capped by the terminal Y-measure. -/
def yEntries (w N : Nat) : List (CatalogEntry w (yMeasure w) (yMeasureSurf w)) :=
  List.replicate N (yIdleEntry w) ++ [yMeasureEntry w]

theorem yEntries_map_g (w N : Nat) :
    (yEntries w N).map (·.g) = List.replicate N (yIdle w) ++ [yMeasure w] := by
  simp [yEntries, yIdleEntry, yMeasureEntry, List.map_replicate]

theorem yEntries_map_sg (w N : Nat) :
    (yEntries w N).map (·.sg) = List.replicate N (yIdleSurf w) ++ [yMeasureSurf w] := by
  simp [yEntries, yIdleEntry, yMeasureEntry, List.map_replicate]

/-! ## §5. THE TERMINAL CHAIN `chainOK` — via `catalog_chainOK` (STRATEGY B). -/

/-- **★ TERMINAL Y-CHAIN `chainOK`, ALL `w`, ALL `N` ★** — the depth-`(N+1)` chain
of `N` Y-flow idles capped by the terminal Y-measure passes the per-gadget +
per-interface chain checker, obtained directly from the generic catalog builder
`catalog_chainOK` by list induction.  NO `native_decide` over `w` OR `N`. -/
theorem yTerminalChain_chainOK (w N : Nat) :
    chainOK 3 (w + 1) (zChainConn w) w 1
      (List.replicate N (yIdle w) ++ [yMeasure w])
      (List.replicate N (yIdleSurf w) ++ [yMeasureSurf w]) = true := by
  have := catalog_chainOK w (yMeasure w) (yMeasureSurf w) (yEntries w N) (by simp [yEntries])
  rwa [yEntries_map_g, yEntries_map_sg] at this

/-! ## §6. THE CHAIN PORTS — `w` IN ports at `k=0` reading `Ȳ` (the flow entering).

  A measurement TERMINATES the flow, so the chain has only the `w` IN ports of
  the entering Y-flow (no OUT ports — the flow is consumed at the terminal
  `Y`-cubes).  The chain surface is HOMOGENEOUS (`yIdleSurf = yMeasureSurf`):
  `replicate N yIdleSurf ++ [yMeasureSurf] = replicate (N+1) yMeasureSurf`, so the
  welded surface is `zChainSurf 3 (yMeasureSurf w) N` and the bottom read collapses
  via `zChainSurf_KI0/KJ0` to `yMeasureSurf w`'s `k`-independent value. -/

/-- The chain ports: `w` IN ports at `k = 0`, reading `Ȳ` (reuse `yMeasure`'s). -/
def yChainPorts (w : Nat) : List Port := yMeasurePorts w
/-- The chain spec: flow `s` measures `Ȳ` on column `s-1` (reuse `yMeasure`'s). -/
def yChainPaulis (w : Nat) : Nat → Nat → Pauli := yMeasurePaulis w

/-- The chain surface list collapses to a homogeneous `Y`-flow replicate. -/
theorem ySurf_list_eq (w N : Nat) :
    List.replicate N (yIdleSurf w) ++ [yMeasureSurf w]
      = List.replicate (N + 1) (yMeasureSurf w) := by
  simp only [yIdleSurf]; rw [List.replicate_succ']

/-- Hence the welded chain surface is exactly `zChainSurf 3 (yMeasureSurf w) N`. -/
theorem yChainSurf_eq (w N : Nat) :
    weldChainSurf 3 (List.replicate N (yIdleSurf w) ++ [yMeasureSurf w])
      = zChainSurf 3 (yMeasureSurf w) N := by
  rw [ySurf_list_eq]

/-- Every chain port: column `idx % w`, `pj = pk = 0`, canonical blue/red. -/
theorem yChainPorts_get {w : Nat} {p : Port} {idx : Nat}
    (h : (p, idx) ∈ (yChainPorts w).zipIdx) :
    p.pj = 0 ∧ p.pk = 0 ∧ p.blueSel = 4 ∧ p.redSel = 5 ∧ p.pi = idx % w ∧ p.pi < w := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  simp only [yChainPorts, yMeasurePorts, List.getElem?_map] at h
  by_cases hidx : idx < w
  · rw [List.getElem?_eq_getElem (by simp [hidx]), List.getElem_range,
      Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl, (Nat.mod_eq_of_lt hidx).symm, hidx⟩
  · exfalso
    rw [List.getElem?_eq_none (by simp only [List.length_range]; omega)] at h
    simp at h

/-- **★ CHAIN PORT BOUNDARY, ALL `w`, ALL `N` ★** — at every IN port the chain
surface matches the `Ȳ` spec (both `KI` and `KJ` planes present for the active
flow on that column).  The bottom read is `N`-independent (`zChainSurf_KI0/KJ0`)
and reduces to `yMeasureSurf w`'s value, then the finite column match closes it. -/
theorem yChain_portsOK (w N : Nat) :
    portsOK (zChainSurf 3 (yMeasureSurf w) N) (yChainPorts w) (yChainPaulis w) (w + 1) = true := by
  rw [portsOK, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro pp hpp
  obtain ⟨p, idx⟩ := pp
  obtain ⟨hpj, hpk, hbl, hrd, hpi, hlt⟩ := yChainPorts_get hpp
  have hw : 0 < w := by omega
  have hmw : idx % w < w := Nat.mod_lt _ hw
  simp only [Surf.sel, hbl, hrd, hpj, hpi, hpk, yChainPaulis]
  rw [zChainSurf_KI0 (by norm_num) N s (idx % w) 0,
      zChainSurf_KJ0 (by norm_num) N s (idx % w) 0]
  simp only [yMeasureSurf, yMeasurePaulis, portBlue, portRed]
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp
  · have hs1 : 1 ≤ s := hs
    by_cases hc : s - 1 = idx % w
    · have hsw : s ≤ w := by omega
      simp [hc, hs1, hsw]
    · simp [hc, hs1]

/-! ## §7. ★ THE HEADLINE — the terminal Y-chain is `LaSCorrectFull`, ALL `w`/`N`. -/

/-- **★ TERMINAL Y-MEASUREMENT CHAIN IS FULLY CORRECT, ALL `w`, ALL `N` ★** — the
welded depth-`(N+1)` chain of `N` Y-flow idles capped by the terminal transversal
`Ȳ`-measure is a fully correct lattice-surgery program: structurally valid,
interior functionality satisfied across every weld seam (INCLUDING the terminal
`Y`-cube layer), and the input ports matching the per-column-`Ȳ` spec.

Built via STRATEGY B — the existing `catalog_chainOK` engine fed a Y-flow catalog
(`yIdleEntry`/`yMeasureEntry`), with `weldChain_LaSCorrectFull` adding the ports.
The chain genuinely ENDS in a Y-measurement (the terminal `yMeasure`'s `Y`-cubes
at the chain top).  Honestly a Y-FLOW chain (every gadget carries `yMeasureSurf`),
NOT a Z-merge chain with a Y readout.  NO `native_decide` over `w` OR `N`. -/
theorem yTerminalChain_LaSCorrectFull (w N : Nat) :
    LaSCorrectFull
      (weldChain 3 (zChainConn w) (List.replicate N (yIdle w) ++ [yMeasure w]))
      (weldChainSurf 3 (List.replicate N (yIdleSurf w) ++ [yMeasureSurf w]))
      (yChainPorts w) (yChainPaulis w) (w + 1) = true := by
  apply weldChain_LaSCorrectFull 3 (w + 1) (zChainConn w) w 1
    (List.replicate N (yIdle w) ++ [yMeasure w])
    (List.replicate N (yIdleSurf w) ++ [yMeasureSurf w])
    (yChainPorts w) (yChainPaulis w)
    (yTerminalChain_chainOK w N)
  rw [yChainSurf_eq]
  exact yChain_portsOK w N

/-! ## §8. THE Y-CUBE WITNESS + the MANDATORY anti-idle-rejection control.

  The chain genuinely contains a `Y`-cube — the terminal `yMeasure`'s top
  `Y`-cube, surviving the welds shifted to `k = N*3 + 2` (the chain top).  An
  ALL-PLAIN-IDLE chain (`idleMerge` body, no `Y`-cube) carries NO `Y`-cube, so the
  same `Y`-cube-anchored certification REJECTS it. -/

/-- The terminal `Y`-cube survives the welds: at the chain top `k = N*3+2`. -/
theorem yChain_YCube_top (w N : Nat) (hw : 0 < w) :
    (weldChain 3 (zChainConn w) (List.replicate N (yIdle w) ++ [yMeasure w])).YCube 0 0 (N * 3 + 2)
      = true := by
  induction N with
  | zero => show (yMeasure w).YCube 0 0 (0 * 3 + 2) = true; simp [yMeasure, hw]
  | succ M ih =>
    rw [List.replicate_succ, List.cons_append]
    cases hL : (List.replicate M (yIdle w) ++ [yMeasure w]) with
    | nil => simp at hL
    | cons a rest =>
      rw [show weldChain 3 (zChainConn w) (yIdle w :: a :: rest)
            = weldK 3 (yIdle w) (weldChain 3 (zChainConn w) (a :: rest)) (zChainConn w) from rfl]
      simp only [weldK]
      rw [if_neg (show ¬ ((M + 1) * 3 + 2 < 3) by omega)]
      rw [show (M + 1) * 3 + 2 - 3 = M * 3 + 2 by omega]
      rw [← hL]; exact ih

theorem yChain_maxI (w N : Nat) :
    (weldChain 3 (zChainConn w) (List.replicate N (yIdle w) ++ [yMeasure w])).maxI = w := by
  induction N with
  | zero => show (yMeasure w).maxI = w; rfl
  | succ M ih =>
    rw [List.replicate_succ, List.cons_append]
    cases hL : (List.replicate M (yIdle w) ++ [yMeasure w]) with
    | nil => simp at hL
    | cons a rest =>
      rw [show weldChain 3 (zChainConn w) (yIdle w :: a :: rest)
            = weldK 3 (yIdle w) (weldChain 3 (zChainConn w) (a :: rest)) (zChainConn w) from rfl]
      simp only [weldK]; rw [← hL, ih]; exact Nat.max_self w

theorem yChain_maxJ (w N : Nat) :
    (weldChain 3 (zChainConn w) (List.replicate N (yIdle w) ++ [yMeasure w])).maxJ = 1 := by
  induction N with
  | zero => show (yMeasure w).maxJ = 1; rfl
  | succ M ih =>
    rw [List.replicate_succ, List.cons_append]
    cases hL : (List.replicate M (yIdle w) ++ [yMeasure w]) with
    | nil => simp at hL
    | cons a rest =>
      rw [show weldChain 3 (zChainConn w) (yIdle w :: a :: rest)
            = weldK 3 (yIdle w) (weldChain 3 (zChainConn w) (a :: rest)) (zChainConn w) from rfl]
      simp only [weldK]; rw [← hL, ih]; exact Nat.max_self 1

theorem yChain_maxK (w N : Nat) :
    (weldChain 3 (zChainConn w) (List.replicate N (yIdle w) ++ [yMeasure w])).maxK = (N + 1) * 3 := by
  induction N with
  | zero => show (yMeasure w).maxK = (0 + 1) * 3; rfl
  | succ M ih =>
    rw [List.replicate_succ, List.cons_append]
    cases hL : (List.replicate M (yIdle w) ++ [yMeasure w]) with
    | nil => simp at hL
    | cons a rest =>
      rw [show weldChain 3 (zChainConn w) (yIdle w :: a :: rest)
            = weldK 3 (yIdle w) (weldChain 3 (zChainConn w) (a :: rest)) (zChainConn w) from rfl]
      simp only [weldK]; rw [← hL, ih]; show 3 + (M + 1) * 3 = (M + 1 + 1) * 3; ring

/-- **★ THE TERMINAL CHAIN CARRIES A `Y`-CUBE, ALL `w`, ALL `N` ★** — the cube
`(0, 0, N*3+2)` at the chain top is the terminal `yMeasure`'s `Y`-cube. -/
theorem yChain_hasYCube (w N : Nat) (hw : 0 < w) :
    hasYCube (weldChain 3 (zChainConn w) (List.replicate N (yIdle w) ++ [yMeasure w])) = true := by
  rw [hasYCube, List.any_eq_true]
  refine ⟨(0, 0, N * 3 + 2), ?_, ?_⟩
  · rw [mem_gridCubes, yChain_maxI, yChain_maxJ, yChain_maxK]
    exact ⟨hw, by norm_num, by omega⟩
  · exact yChain_YCube_top w N hw

/-- **The terminal-Y-chain CERTIFICATION** — the full `LaSCorrectFull` against the
per-column-`Ȳ` spec AND the flow-visible terminal `Y`-cube signature. -/
def yTerminalChainCertified (w N : Nat) : Bool :=
  LaSCorrectFull
    (weldChain 3 (zChainConn w) (List.replicate N (yIdle w) ++ [yMeasure w]))
    (weldChainSurf 3 (List.replicate N (yIdleSurf w) ++ [yMeasureSurf w]))
    (yChainPorts w) (yChainPaulis w) (w + 1)
  && hasYCube (weldChain 3 (zChainConn w) (List.replicate N (yIdle w) ++ [yMeasure w]))

/-- **★ THE TERMINAL Y-CHAIN IS CERTIFIED, ALL `w` (`>0`), ALL `N`. ★** -/
theorem yTerminalChain_certified (w N : Nat) (hw : 0 < w) :
    yTerminalChainCertified w N = true := by
  rw [yTerminalChainCertified, yTerminalChain_LaSCorrectFull, yChain_hasYCube w N hw]; rfl

/-! ### The MANDATORY anti-idle control. -/

/-- The all-plain-idle chain on the SAME footprint has NO `Y`-cube anywhere. -/
theorem idleChain_YCube_false (w N : Nat) (i j k : Nat) :
    (weldChain 3 (zChainConn w) (List.replicate (N + 1) (idleMerge w))).YCube i j k = false := by
  induction N generalizing k with
  | zero => show (idleMerge w).YCube i j k = false; simp [idleMerge]
  | succ M ih =>
    rw [List.replicate_succ]
    rw [show weldChain 3 (zChainConn w) (idleMerge w :: List.replicate (M + 1) (idleMerge w))
          = weldK 3 (idleMerge w)
              (weldChain 3 (zChainConn w) (List.replicate (M + 1) (idleMerge w))) (zChainConn w)
          from rfl]
    simp only [weldK]
    by_cases hk : k < 3
    · rw [if_pos hk]; simp [idleMerge]
    · rw [if_neg hk]; exact ih (k - 3)

theorem idleChain_no_YCube (w N : Nat) :
    hasYCube (weldChain 3 (zChainConn w) (List.replicate (N + 1) (idleMerge w))) = false := by
  rw [hasYCube, List.any_eq_false]
  intro c _
  rw [idleChain_YCube_false w N c.1 c.2.1 c.2.2]
  exact Bool.false_ne_true

/-- The same `Y`-cube-anchored certification recipe applied to the all-idle chain
(for ANY surface/ports — `hasYCube` reads only the diagram geometry). -/
def idleChainCertified (w N : Nat) (S : Surf) (ports : List Port)
    (paulis : Nat → Nat → Pauli) (nStab : Nat) : Bool :=
  LaSCorrectFull (weldChain 3 (zChainConn w) (List.replicate (N + 1) (idleMerge w)))
      S ports paulis nStab
    && hasYCube (weldChain 3 (zChainConn w) (List.replicate (N + 1) (idleMerge w)))

/-- **★ THE MANDATORY ANTI-FAKE CONTROL: an ALL-PLAIN-IDLE chain is REJECTED ★** —
having NO `Y`-cube, the `&& hasYCube` short-circuits to `false`, regardless of its
surface/ports.  The terminal Y-chain is a real measurement precisely because the
certification that accepts it rejects an all-idle chain of the same shape. -/
theorem idleChain_rejected (w N : Nat) (S : Surf) (ports : List Port)
    (paulis : Nat → Nat → Pauli) (nStab : Nat) :
    idleChainCertified w N S ports paulis nStab = false := by
  rw [idleChainCertified, idleChain_no_YCube]; simp

/-- **★ TERMINAL Y-MEASUREMENT CHAIN: certified AND all-idle-rejected, side by
side, ALL `w` (`>0`), ALL `N`. ★** -/
theorem yTerminalChain_certified_idleChain_rejected (w N : Nat) (hw : 0 < w)
    (S : Surf) (ports : List Port) (paulis : Nat → Nat → Pauli) (nStab : Nat) :
    yTerminalChainCertified w N = true ∧ idleChainCertified w N S ports paulis nStab = false :=
  ⟨yTerminalChain_certified w N hw, idleChain_rejected w N S ports paulis nStab⟩

end FormalRV.QEC.LaSre
