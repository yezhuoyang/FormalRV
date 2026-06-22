/-
  FormalRV.QEC.LatticeSurgery.WidthScalingStep2b
  ----------------------------------------------
  **★ STEP 2b — UNIFY WIDTH + DEPTH into ONE symbolic theorem. ★**

  Step 1 (`WidthScaling`) made one `zMerge w` `LaSCorrectFull` for ALL widths `w`
  with no `native_decide` over `w`.  Step 2 (`WidthScalingStep2`) built a
  gadget-generic, length-generic depth engine (`zChain_chainOK_generic`) that
  stacks `N+1` copies welded in time, for ALL `N`, with no `native_decide` over
  `N` — BUT it was instantiated only at the FIXED width `W = 2`, because the two
  reference self-interface certs were proven by `native_decide` at `W = 2`.

  This file removes that last fixed width: it proves the two reference
  self-interface certificates WIDTH-SYMBOLICALLY (for ALL `w`, NO `native_decide`
  over `w`), by the Step-1 PER-COLUMN locality technique applied to the WELDED
  structure `weldK 3 (zMerge w) (zMerge w) (zChainConn w)` at its two seam layers
  `k ∈ {2, 3}`.  Feeding those into the depth engine yields, for ALL `w` AND ALL
  `N`, that the depth-`(N+1)` stack of `zMerge w` is interior-correct
  (`valid`+`funcOK`) and — with the width-symbolic top-boundary ports — fully
  `LaSCorrectFull`.  NO `native_decide` over EITHER `w` OR `N` anywhere.
-/
import FormalRV.QEC.LatticeSurgery.WidthScalingStep2

namespace FormalRV.QEC.LaSre

/-! ## §1. The connection list — weld ALL `w` data columns across the time seam. -/

/-- Weld every data column `0..w-1` (at `j = 0`) across each time seam. -/
def zChainConn (w : Nat) : List (Nat × Nat) := (List.range w).map (fun c => (c, 0))

/-- The connection list contains data column `(i, 0)` exactly when `i < w`. -/
theorem zChainConn_contains (w i : Nat) :
    (zChainConn w).contains (i, 0) = decide (i < w) := by
  rw [List.contains_eq_mem, zChainConn]
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
  congr 1
  apply propext
  constructor
  · rintro ⟨c, hc, rfl, _⟩; exact hc
  · intro hi; exact ⟨i, hi, rfl, trivial⟩

/-! ## §2. The welded self-seam `wSeam w` and its field reductions at `k ∈ {2,3}`.

  `wSeam w := weldK 3 (zMerge w) (zMerge w) (zChainConn w)` is the reference
  self-weld whose two interface layers `k = 2` (`k+1 = kA = 3`) and `k = 3`
  (`k > kA`) the interface certs evaluate.  Because `zMerge`/`zMergeSurf` and the
  conn list are arithmetic, each welded field at the seam reduces to a `decide`
  in `i`, with NO list operations and NO `native_decide` over `w`. -/

/-- The reference self-weld of `zMerge w` (the seam the depth engine certifies). -/
abbrev wSeam (w : Nat) : LaSre := weldK 3 (zMerge w) (zMerge w) (zChainConn w)

/-- The stitched reference surface (used by the functionality interface cert). -/
abbrev wSeamSurf (w : Nat) : Surf := stitchSurf 3 (zMergeSurf w) (zMergeSurf w)

/-- The weld has NO `J`-pipes (neither `zMerge` half does) — so `hasJ ≡ false`
and `validCube` is trivially satisfied at EVERY cube, for ALL widths. -/
theorem wSeam_ExistJ (w i j k : Nat) : (wSeam w).ExistJ i j k = false := by
  simp only [wSeam, weldK, zMerge]; split <;> rfl

theorem wSeam_YCube (w i j k : Nat) : (wSeam w).YCube i j k = false := by
  simp only [wSeam, weldK, zMerge]; split <;> rfl

theorem wSeam_validCube (w i j k : Nat) : (wSeam w).validCube i j k = true := by
  simp only [LaSre.validCube, LaSre.hasJ, wSeam_ExistJ, wSeam_YCube,
    Bool.false_or, Bool.and_false, Bool.not_false, Bool.and_true]
  simp

/-! ## §3. ★ THE WIDTH-SYMBOLIC VALIDITY INTERFACE CERTIFICATE. ★ -/

/-- **★ WIDTH-SYMBOLIC reference VALIDITY interface cert ★** — the self-weld of
`zMerge w` passes the O(N) validity interface check at the seam, for ALL widths
`w`, with NO `native_decide` over `w`.  Every seam cube is `validCube`-true
because the weld has no `J`-pipes and no `Y`-cubes. -/
theorem zMerge_refValid_sym (w : Nat) :
    weldInterfaceValidOK2 3 (zMerge w) (zMerge w) (zChainConn w) w 1 = true := by
  rw [weldInterfaceValidOK2, List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro j _
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [if_pos (by norm_num)]; exact wSeam_validCube w i j (3 - 1)
  · exact wSeam_validCube w i j 3

/-! ## §4. WELDED FIELD REDUCTIONS AT THE SEAM LAYERS (`k ∈ {1,2,3}`).

  All arithmetic, no list ops, no `native_decide` over `w`.  The welded gadget's
  `ExistI`/`ExistK` and the stitched surface's `KI`/`KJ`/`IK` are read by
  `funcCubeOK` at the cube and its lower neighbours; we evaluate each at the three
  relevant `k`-layers `{1,2,3}` directly. -/

-- ExistK at the seam layers.
theorem wSeam_ExistK1 (w i : Nat) : (wSeam w).ExistK i 0 1 = decide (i < w) := by
  simp only [wSeam, weldK]; rw [if_pos (by norm_num)]; simp [zMerge]
theorem wSeam_ExistK2 (w i : Nat) : (wSeam w).ExistK i 0 2 = decide (i < w) := by
  simp only [wSeam, weldK, zChainConn_contains]; simp [zMerge]
theorem wSeam_ExistK3 (w i : Nat) : (wSeam w).ExistK i 0 3 = decide (i < w) := by
  simp only [wSeam, weldK]; simp [zMerge]

-- ExistI is absent at every seam layer (the I-seam lives only at the gadget's k=1,
-- which after weld sits at k=1 of the BOTTOM copy — never a missing-pipe normal we use).
theorem wSeam_ExistI2 (w i : Nat) : (wSeam w).ExistI i 0 2 = false := by
  simp only [wSeam, weldK]; rw [if_pos (by norm_num)]; simp [zMerge]
theorem wSeam_ExistI3 (w i : Nat) : (wSeam w).ExistI i 0 3 = false := by
  simp only [wSeam, weldK]; rw [if_neg (by norm_num)]; simp [zMerge]
theorem wSeam_ExistJany (w i k : Nat) : (wSeam w).ExistJ i 0 k = false :=
  wSeam_ExistJ w i 0 k

-- Stitched surface KI/KJ are the k-independent `zMergeSurf` value at all three layers.
theorem wSeamSurf_KI1 (w s i : Nat) :
    (wSeamSurf w).KI s i 0 1 = (zMergeSurf w).KI s i 0 0 := by
  simp only [wSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem wSeamSurf_KI2 (w s i : Nat) :
    (wSeamSurf w).KI s i 0 2 = (zMergeSurf w).KI s i 0 0 := by
  simp only [wSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem wSeamSurf_KI3 (w s i : Nat) :
    (wSeamSurf w).KI s i 0 3 = (zMergeSurf w).KI s i 0 0 := by
  simp only [wSeamSurf, stitchSurf]; rw [if_neg (by norm_num)]
theorem wSeamSurf_KJ1 (w s i : Nat) :
    (wSeamSurf w).KJ s i 0 1 = (zMergeSurf w).KJ s i 0 0 := by
  simp only [wSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem wSeamSurf_KJ2 (w s i : Nat) :
    (wSeamSurf w).KJ s i 0 2 = (zMergeSurf w).KJ s i 0 0 := by
  simp only [wSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem wSeamSurf_KJ3 (w s i : Nat) :
    (wSeamSurf w).KJ s i 0 3 = (zMergeSurf w).KJ s i 0 0 := by
  simp only [wSeamSurf, stitchSurf]; rw [if_neg (by norm_num)]

/-! ## §5. SEAM PARITY / ALL-OR-NONE CANCELLATIONS — per column, for `k ∈ {2,3}`.

  Mirror of Step 1's `k = 1` analysis, now at the WELD seam.  At each seam layer
  the only incident pipes are the two `K`-worldline pipes (in + out); their two
  surface contributions are EQUAL (the surface is `k`-independent), so every
  parity XORs to `false` and every all-or-none list has equal present values. -/

theorem wSeam_iParity2 (w s i : Nat) :
    iParity (wSeam w) (wSeamSurf w) s i 0 2 = false := by
  rw [iParity, show (2 : Nat) - 1 = 1 from rfl,
    wSeam_ExistJany, wSeam_ExistK2, wSeam_ExistK1, wSeamSurf_KI2, wSeamSurf_KI1]
  simp

theorem wSeam_iParity3 (w s i : Nat) :
    iParity (wSeam w) (wSeamSurf w) s i 0 3 = false := by
  rw [iParity, show (3 : Nat) - 1 = 2 from rfl,
    wSeam_ExistJany, wSeam_ExistK3, wSeam_ExistK2, wSeamSurf_KI3, wSeamSurf_KI2]
  simp

theorem wSeam_jParity2 (w s i : Nat) :
    jParity (wSeam w) (wSeamSurf w) s i 0 2 = false := by
  rw [jParity, show (2 : Nat) - 1 = 1 from rfl]
  simp only [wSeam_ExistI2, wSeam_ExistK2, wSeam_ExistK1, wSeamSurf_KJ2, wSeamSurf_KJ1]
  simp

theorem wSeam_jParity3 (w s i : Nat) :
    jParity (wSeam w) (wSeamSurf w) s i 0 3 = false := by
  rw [jParity, show (3 : Nat) - 1 = 2 from rfl]
  simp only [wSeam_ExistI3, wSeam_ExistK3, wSeam_ExistK2, wSeamSurf_KJ3, wSeamSurf_KJ2]
  simp

theorem wSeam_allOrNoneI2 (w s i : Nat) :
    allOrNoneI (wSeam w) (wSeamSurf w) s i 0 2 = true := by
  rw [allOrNoneI, show (2 : Nat) - 1 = 1 from rfl,
    wSeam_ExistJany, wSeam_ExistK2, wSeam_ExistK1, wSeamSurf_KJ2, wSeamSurf_KJ1]
  apply allEq_const_present (b := (zMergeSurf w).KJ s i 0 0)
  intro p hp hpres
  fin_cases hp <;> simp_all

theorem wSeam_allOrNoneI3 (w s i : Nat) :
    allOrNoneI (wSeam w) (wSeamSurf w) s i 0 3 = true := by
  rw [allOrNoneI, show (3 : Nat) - 1 = 2 from rfl,
    wSeam_ExistJany, wSeam_ExistK3, wSeam_ExistK2, wSeamSurf_KJ3, wSeamSurf_KJ2]
  apply allEq_const_present (b := (zMergeSurf w).KJ s i 0 0)
  intro p hp hpres
  fin_cases hp <;> simp_all

theorem wSeam_allOrNoneJ2 (w s i : Nat) :
    allOrNoneJ (wSeam w) (wSeamSurf w) s i 0 2 = true := by
  rw [allOrNoneJ, show (2 : Nat) - 1 = 1 from rfl]
  simp only [wSeam_ExistI2, wSeam_ExistK2, wSeam_ExistK1, wSeamSurf_KI2, wSeamSurf_KI1]
  apply allEq_const_present (b := (zMergeSurf w).KI s i 0 0)
  intro p hp hpres
  fin_cases hp <;> simp_all

theorem wSeam_allOrNoneJ3 (w s i : Nat) :
    allOrNoneJ (wSeam w) (wSeamSurf w) s i 0 3 = true := by
  rw [allOrNoneJ, show (3 : Nat) - 1 = 2 from rfl]
  simp only [wSeam_ExistI3, wSeam_ExistK3, wSeam_ExistK2, wSeamSurf_KI3, wSeamSurf_KI2]
  apply allEq_const_present (b := (zMergeSurf w).KI s i 0 0)
  intro p hp hpres
  fin_cases hp <;> simp_all

/-! ## §6. ★ THE PER-COLUMN SEAM `funcCubeOK` (the heart of the symbolic cert). ★

  For a DATA column `i < w` the seam cube is a worldline passthrough (the weld's
  `K`-pipe in + worldline out give `hasK`); with no `I`/`J` pipes the only
  obligations are the parity/all-or-none cancellations of §5.  For `i ≥ w` the
  seam cube has degree `0` (a port), trivially `funcCubeOK`.  Both `k = 2` and
  `k = 3`, for ALL `w`, `s`, `i` — NO `native_decide` over `w`. -/

/-- `hasK` at the seam: a data column `i < w` has the welded worldline `K`-pipe. -/
theorem wSeam_hasK2 (w i : Nat) (hiw : i < w) : (wSeam w).hasK i 0 2 = true := by
  simp only [LaSre.hasK, wSeam_ExistK2]; simp [hiw]

theorem wSeam_hasK3 (w i : Nat) (hiw : i < w) : (wSeam w).hasK i 0 3 = true := by
  simp only [LaSre.hasK, wSeam_ExistK3]; simp [hiw]

/-- `degree ≤ 1` at the seam for an out-of-range column `i ≥ w` (a port). -/
theorem wSeam_degree2_port (w i : Nat) (hiw : ¬ i < w) :
    (wSeam w).degree i 0 2 ≤ 1 := by
  simp only [LaSre.degree, wSeam_ExistK2, wSeam_ExistI2, wSeam_ExistJany,
    show (2 : Nat) - 1 = 1 from rfl, wSeam_ExistK1]
  simp [hiw]

theorem wSeam_degree3_port (w i : Nat) (hiw : ¬ i < w) :
    (wSeam w).degree i 0 3 ≤ 1 := by
  simp only [LaSre.degree, wSeam_ExistK3, wSeam_ExistI3, wSeam_ExistJany,
    show (3 : Nat) - 1 = 2 from rfl, wSeam_ExistK2]
  simp [hiw]

theorem wSeam_funcCubeOK2 (w s i : Nat) :
    funcCubeOK (wSeam w) (wSeamSurf w) s i 0 2 = true := by
  unfold funcCubeOK
  rw [wSeam_iParity2, wSeam_jParity2, wSeam_allOrNoneI2, wSeam_allOrNoneJ2]
  by_cases hiw : i < w
  · rw [wSeam_hasK2 w i hiw]
    rw [if_neg (show ¬((wSeam w).YCube i 0 2 = true) by rw [wSeam_YCube]; simp)]
    rw [if_neg (show ¬((wSeam w).degree i 0 2 ≤ 1) by
      simp only [LaSre.degree, wSeam_ExistK2, wSeam_ExistI2, wSeam_ExistJany,
        show (2 : Nat) - 1 = 1 from rfl, wSeam_ExistK1]; simp [hiw])]
    simp
  · rw [if_neg (show ¬((wSeam w).YCube i 0 2 = true) by rw [wSeam_YCube]; simp),
      if_pos (wSeam_degree2_port w i hiw)]

theorem wSeam_funcCubeOK3 (w s i : Nat) :
    funcCubeOK (wSeam w) (wSeamSurf w) s i 0 3 = true := by
  unfold funcCubeOK
  rw [wSeam_iParity3, wSeam_jParity3, wSeam_allOrNoneI3, wSeam_allOrNoneJ3]
  by_cases hiw : i < w
  · rw [wSeam_hasK3 w i hiw]
    rw [if_neg (show ¬((wSeam w).YCube i 0 3 = true) by rw [wSeam_YCube]; simp)]
    rw [if_neg (show ¬((wSeam w).degree i 0 3 ≤ 1) by
      simp only [LaSre.degree, wSeam_ExistK3, wSeam_ExistI3, wSeam_ExistJany,
        show (3 : Nat) - 1 = 2 from rfl, wSeam_ExistK2]; simp [hiw])]
    simp
  · rw [if_neg (show ¬((wSeam w).YCube i 0 3 = true) by rw [wSeam_YCube]; simp),
      if_pos (wSeam_degree3_port w i hiw)]

/-! ## §7. ★ THE WIDTH-SYMBOLIC FUNCTIONALITY INTERFACE CERTIFICATE. ★ -/

/-- **★ WIDTH-SYMBOLIC reference FUNCTIONALITY interface cert ★** — the self-weld
of `zMerge w` passes the O(N) functionality interface check at the seam, for ALL
widths `w` and `w+1` flows, with NO `native_decide` over `w`.  Discharged by the
two per-column seam `funcCubeOK` lemmas (`k ∈ {2,3}`), `List.all_eq_true` lifting
them to all columns and flows. -/
theorem zMerge_refFunc_sym (w : Nat) :
    weldInterfaceOK2 3 (zMerge w) (zMerge w) (zMergeSurf w) (zMergeSurf w)
      (zChainConn w) (w + 1) w 1 = true := by
  rw [weldInterfaceOK2, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro j hj
  have hj0 : j = 0 := by
    have := List.mem_range.1 hj; omega
  subst hj0
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [if_pos (by norm_num)]; exact wSeam_funcCubeOK2 w s i
  · exact wSeam_funcCubeOK3 w s i

/-! ## §8. ★ THE UNIFIED ∀w ∀N `chainOK` — width-symbolic AND depth-generic. ★

  Instantiate the gadget-generic, length-generic depth engine
  `zChain_chainOK_generic` with the two WIDTH-SYMBOLIC interface certs above.  The
  result is the per-gadget + per-interface chain checker passing for the
  depth-`(N+1)` stack of `zMerge w` — for ALL `w` AND ALL `N`, with NO
  `native_decide` over EITHER. -/

/-- **★ UNIFIED WIDTH+DEPTH `chainOK` ★** — for EVERY width `w` and EVERY chain
length `N`, the depth-`(N+1)` stack of `zMerge w`s welded across all `w` data
columns passes `chainOK`.  By `chainOK_sound` this gives the welded chain's
`valid` ∧ `funcOK` (interior correctness) for all `w`, `N`. -/
theorem zMerge_stack_chainOK (w N : Nat) :
    chainOK 3 (w + 1) (zChainConn w) w 1
      (List.replicate (N + 1) (zMerge w)) (List.replicate (N + 1) (zMergeSurf w)) = true :=
  zChain_chainOK_generic (h := 3) (conn := zChainConn w) (g := zMerge w) (s := zMergeSurf w)
    (by norm_num) (w + 1) w 1
    rfl rfl rfl (zMerge_valid w) (zMerge_funcOK w (w + 1))
    (zMerge_refValid_sym w) (zMerge_refFunc_sym w) N

/-- **★ UNIFIED WIDTH+DEPTH INTERIOR CORRECTNESS ★** — for EVERY width `w` and
EVERY chain length `N`, the welded depth-`(N+1)` stack of `zMerge w`s is
structurally `valid` AND satisfies the interior functionality check `funcOK`
across every weld seam.  This is `LaSCorrectFull` minus the port-boundary clause,
holding for ALL `w` AND ALL `N` with NO `native_decide` over either. -/
theorem zMerge_stack_LaSCorrect (w N : Nat) :
    LaSCorrect (weldChain 3 (zChainConn w) (List.replicate (N + 1) (zMerge w)))
      (weldChainSurf 3 (List.replicate (N + 1) (zMergeSurf w))) (w + 1) = true := by
  obtain ⟨hv, hf, _, _⟩ :=
    chainOK_sound 3 (w + 1) (zChainConn w) w 1
      (List.replicate (N + 1) (zMerge w)) (List.replicate (N + 1) (zMergeSurf w))
      (zMerge_stack_chainOK w N)
  rw [LaSre.LaSCorrect, hv, hf]; rfl

/-! ## §9. ★ WIDTH-SYMBOLIC + TOP-BOUNDARY PORTS — the unified composite boundary. ★

  The depth-`(N+1)` stack's ports: `w` IN ports at `k = 0` and `w` OUT ports at
  the chain TOP `k = topK3 N = (N+1)·3 − 1`, one per data column, canonical
  blue=`KI`(4)/red=`KJ`(5).  The spec is `zMergePaulis w` (flow 0 = joint `Z̄`,
  flow `s∈[1,w]` = `X̄` on column `s−1`).  Both boundary surface reads are
  `N`-independent (bottom via `zChainSurf_KI0/KJ0`, top via `zChainSurf_KI_top/
  KJ_top`) and collapse to `zMergeSurf w`'s `k`-independent value, so the proof is
  Step-1's width-symbolic column match, uniform in `N`. -/

/-- The chain's TOP time layer (height `3` per gadget, `N+1` gadgets). -/
abbrev topK3 (N : Nat) : Nat := (N + 1) * 3 - 1

/-- Composite ports: `w` IN ports at `k = 0`, `w` OUT ports at `k = topK3 N`. -/
def zStackPorts (w N : Nat) : List Port :=
  (List.range w).map (fun c => ⟨c, 0, 0, 4, 5⟩)
    ++ (List.range w).map (fun c => ⟨c, 0, topK3 N, 4, 5⟩)

/-- The chain surface as the `zChainSurf` abbreviation (DEFINITIONAL). -/
theorem stackSurf_eq (w N : Nat) :
    weldChainSurf 3 (List.replicate (N + 1) (zMergeSurf w))
      = zChainSurf 3 (zMergeSurf w) N := rfl

/-- Every stack port sits on column `idx % w` (`< w`), `pj = 0`, canonical
selectors; the IN ports (`idx < w`) at `pk = 0`, the OUT ports at `pk = topK3 N`. -/
theorem zStackPorts_get {w N : Nat} {p : Port} {idx : Nat}
    (h : (p, idx) ∈ (zStackPorts w N).zipIdx) :
    p.pj = 0 ∧ p.blueSel = 4 ∧ p.redSel = 5 ∧ p.pi = idx % w ∧ p.pi < w
      ∧ (p.pk = 0 ∨ p.pk = topK3 N) := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  simp only [zStackPorts, List.getElem?_append, List.getElem?_map,
    List.length_map, List.length_range] at h
  by_cases hidx : idx < w
  · rw [if_pos hidx, List.getElem?_eq_getElem (by simp [hidx]), List.getElem_range,
      Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, (Nat.mod_eq_of_lt hidx).symm, hidx, Or.inl rfl⟩
  · rw [if_neg hidx] at h
    by_cases hidx2 : idx - w < w
    · rw [List.getElem?_eq_getElem (by simp [hidx2]), List.getElem_range,
        Option.map_some, Option.some.injEq] at h
      subst h
      have hmod : idx % w = idx - w := by
        conv_lhs => rw [show idx = (idx - w) + w from by omega]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hidx2]
      exact ⟨rfl, rfl, rfl, hmod.symm, hidx2, Or.inr rfl⟩
    · exfalso
      rw [List.getElem?_eq_none (by simp only [List.length_range]; omega)] at h
      simp at h

/-- The stack surface's `KI` plane is `N`-independent at BOTH boundaries (the
chain bottom `k=0` via `zChainSurf_KI0`, the chain top `k=topK3 N` via
`zChainSurf_KI_top`), equal to `zMergeSurf w`'s `k`-independent value. -/
theorem zStackSurf_KI_bdry (w N s i k : Nat) (hk : k = 0 ∨ k = topK3 N) :
    (zChainSurf 3 (zMergeSurf w) N).KI s i 0 k = (zMergeSurf w).KI s i 0 0 := by
  rcases hk with hk | hk
  · subst hk; exact zChainSurf_KI0 (by norm_num) N s i 0
  · subst hk
    rw [zChainSurf_KI_top (by norm_num) N s i 0]
    rfl

theorem zStackSurf_KJ_bdry (w N s i k : Nat) (hk : k = 0 ∨ k = topK3 N) :
    (zChainSurf 3 (zMergeSurf w) N).KJ s i 0 k = (zMergeSurf w).KJ s i 0 0 := by
  rcases hk with hk | hk
  · subst hk; exact zChainSurf_KJ0 (by norm_num) N s i 0
  · subst hk
    rw [zChainSurf_KJ_top (by norm_num) N s i 0]
    rfl

/-- **★ WIDTH-SYMBOLIC + TOP-BOUNDARY PORT MATCH, FOR ALL `N` ★** — at every
composite port of the depth-`(N+1)` stack of `zMerge w`s, the chain surface
matches the spec Pauli (blue `KI` = joint `Z̄`, red `KJ` = the per-column `X̄`),
for ALL widths `w` AND all chain lengths `N`.  Both boundary reads reduce to
`zMergeSurf w`'s `k`-independent value, then Step-1's finite column match closes
it — NO `native_decide` over `w` OR `N`. -/
theorem zMerge_stack_portsOK (w N : Nat) :
    portsOK (zChainSurf 3 (zMergeSurf w) N) (zStackPorts w N) (zMergePaulis w) (w + 1) = true := by
  rw [portsOK, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro pp hpp
  obtain ⟨p, idx⟩ := pp
  obtain ⟨hpj, hbl, hrd, hpi, hlt, hpk⟩ := zStackPorts_get hpp
  have hw : 0 < w := by omega
  have hmw : idx % w < w := Nat.mod_lt _ hw
  simp only [Surf.sel, hbl, hrd, hpj, hpi]
  rw [zStackSurf_KI_bdry w N s (idx % w) p.pk hpk,
      zStackSurf_KJ_bdry w N s (idx % w) p.pk hpk]
  simp only [zMergeSurf, zMergePaulis, portBlue, portRed]
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp [hmw]
  · have hs0 : ¬ s = 0 := by omega
    by_cases hc : s - 1 = idx % w
    · have hsw : s ≤ w := by omega
      simp [hs0, hc, hmw, hsw]
      omega
    · simp [hs0, hc, hmw]

/-! ## §10. ★ THE UNIFIED HEADLINE — ∀w ∀N `LaSCorrectFull`. ★ -/

/-- **★ UNIFIED WIDTH-SYMBOLIC + DEPTH-GENERIC `LaSCorrectFull` ★** — for EVERY
width `w` and EVERY chain length `N`, the welded depth-`(N+1)` stack of contiguous
`Z̄`-merges (each measuring the same joint `Z̄` on all `w` data qubits) is a FULLY
CORRECT lattice-surgery program: structurally valid, interior functionality
satisfied across every weld seam, and the composite ports (IN at the bottom, OUT
at the chain top) matching the joint-`Z̄` / per-column-`X̄` spec.

This is the time–space UNIFICATION of Steps 1 and 2: "cost one tile, compose"
made rigorous in BOTH the width AND the depth directions at once.  NO
`native_decide` over EITHER the width `w` OR the chain length `N` — both are
handled symbolically (the width via the per-column locality of `funcCubeOK`/
`validCube`, the depth via the `N`-independence of the seam interface checks). -/
theorem zMerge_stack_LaSCorrectFull (w N : Nat) :
    LaSCorrectFull
      (weldChain 3 (zChainConn w) (List.replicate (N + 1) (zMerge w)))
      (weldChainSurf 3 (List.replicate (N + 1) (zMergeSurf w)))
      (zStackPorts w N) (zMergePaulis w) (w + 1) = true :=
  weldChain_LaSCorrectFull 3 (w + 1) (zChainConn w) w 1
    (List.replicate (N + 1) (zMerge w)) (List.replicate (N + 1) (zMergeSurf w))
    (zStackPorts w N) (zMergePaulis w)
    (zMerge_stack_chainOK w N) (zMerge_stack_portsOK w N)

end FormalRV.QEC.LaSre
