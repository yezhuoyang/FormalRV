/-
  FormalRV.QEC.LatticeSurgery.WidthScalingXMerge
  ----------------------------------------------
  **★ THE X-MERGE — the joint-X̄ measurement, dual of the Z-merge, WIDTH+DEPTH
  symbolic, reusing the depth engine. ★**

  An X-merge measures the joint `X̄` over the `w` data qubits and leaves each `Z̄`
  as a passthrough — the exact DUAL of `zMerge` (`WidthScaling`), which measures
  the joint `Z̄` and passes through each `X̄`.

  THE FAITHFUL DUAL = the 90° axis swap `I ↔ J`.  `zMerge` runs its `Z`-seam
  along the `I`-axis (`ExistI` at `k=1`), with the joint `Z̄` on the `KI` plane of
  the data worldlines and the `X̄` passthrough on `KJ`.  The dual `xMerge` runs an
  `X`-seam along the `J`-axis (`ExistJ` at `k=1`), with the joint `X̄` on the `KJ`
  plane and the `Z̄` passthrough on `KI` — and the seam-correlation piece in the
  `J`-pipe is `JK` (the dual of `zMerge`'s `IK`).  `ColorJ := true` records the
  `X`-basis boundary (`funcCubeOK` is color-blind, so this is documentation that a
  `ColorEnforcing` layer would check; it does not affect any proof here).

  WHY THE AXIS SWAP IS THE RIGHT DUAL (and the naive `KI/KJ` swap is NOT): the
  interior `funcCubeOK` at a seam cube checks ONLY the missing-pipe normal.  In
  `zMerge` the seam cube has `hasI` (vacuous I-normal) + `hasK` (vacuous K-normal),
  leaving the **J-normal** live — whose all-or-none `allOrNoneJ` binds the seam
  piece `IK` to the worldline plane `KI`, so BOTH must carry the joint value.  If
  one only swaps `KI ↔ KJ` keeping the `I`-seam, `allOrNoneJ` then binds the `IK`
  seam to the `KI` PASSTHROUGH worldlines — values disagree, the check FAILS.  The
  axis swap fixes this: the seam cube now has `hasJ` + `hasK`, leaving the
  **I-normal** live, whose `allOrNoneI` binds the seam `JK` to the joint-`X̄` plane
  `KJ` (both `s==0`) ✓, while the `Z̄` passthrough on `KI` is read only by the
  vacuous J-normal — exactly mirroring `zMerge`.

  TARGETS (all ∀w, NO `native_decide` over `w`; then ∀w∀N via the engine, NO
  `native_decide` over `N` either):
    `xMerge_valid` / `xMerge_funcOK` / `xMerge_portsOK` / `xMerge_LaSCorrectFull`
    (single gadget, ∀w); `xMerge_refValid_sym` / `xMerge_refFunc_sym` (the
    width-symbolic self-interface certs); `xMerge_stack_chainOK` (the depth-`N`
    stack via `zChain_chainOK_generic`); and the HEADLINE
    `xMerge_stack_LaSCorrectFull`.
-/
import FormalRV.QEC.LatticeSurgery.WidthScalingStep2b

namespace FormalRV.QEC.LaSre

/-! ## §1. The contiguous width-`w` `X̄`-merge — the `I ↔ J` dual of `zMerge`. -/

/-- The width-`w` `X̄`-merge: the `w` data columns `0..w-1` laid along the `J`-axis
(`maxI = 1`, `maxJ = w`), joined by a single `X`-seam (`J`-pipe spanning `0..w-2`
at time `k=1`); every column carries a data worldline.  Flow `0` is the joint
`X̄`; flow `s∈[1,w]` is `Z̄` on column `s-1` (the passthrough).  `ColorJ := true`
marks the `X`-basis boundary (color-blind to `funcCubeOK`). -/
def xMerge (w : Nat) : LaSre :=
  { maxI := 1, maxJ := w, maxK := 3
    YCube  := fun _ _ _ => false
    ExistI := fun _ _ _ => false
    ExistJ := fun i j k => i == 0 && decide (j + 1 < w) && k == 1   -- X-seam 0..w-2 along J
    ExistK := fun i j k => i == 0 && decide (j < w) && decide (k < 2) -- all w worldlines
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => true }

/-- The dual surface: the joint `X̄` (flow 0) on the `KJ` plane of every data
worldline, threaded by the `JK` seam pieces; the `Z̄` passthrough (flow `s∈[1,w]`)
on the `KI` plane of column `s-1`. -/
def xMergeSurf (w : Nat) : Surf :=
  { IJ := fun _ _ _ _ => false
    IK := fun _ _ _ _ => false
    JK := fun s i j k => s == 0 && i == 0 && decide (j + 1 < w) && k == 1   -- seam (joint X)
    JI := fun _ _ _ _ => false
    KI := fun s i j _ => decide (1 ≤ s) && decide (s - 1 = j) && decide (s ≤ w) && i == 0  -- Z passthrough on col j
    KJ := fun s i j _ => s == 0 && i == 0 && decide (j < w) }              -- joint X on all data

/-! ## §2. WIDTH-SYMBOLIC VALIDITY — no `I`-pipes ⇒ no 3D corner, at every cube. -/

theorem xMerge_validCube (w i j k : Nat) : (xMerge w).validCube i j k = true := by
  simp [LaSre.validCube, LaSre.hasI, xMerge]

theorem xMerge_valid (w : Nat) : (xMerge w).valid = true := by
  rw [LaSre.valid, List.all_eq_true]
  intro c _
  exact xMerge_validCube w c.1 c.2.1 c.2.2

/-! ## §3. The interior time-layer `k=1`: all parities cancel, all all-or-none hold.

  At the seam cube `(0,j,1)` the live normal is the **I-normal** (`hasJ` from the
  seam pipe and `hasK` from the worldline make the J- and K-normals vacuous).  Its
  `allOrNoneI` binds the `JK` seam piece to the joint-`X̄` `KJ` worldline plane
  (both `s==0`); the `Z̄` passthrough on `KI` is read only by the vacuous J-normal.
  Mirror of Step 1's `k=1` analysis, with `I ↔ J` swapped. -/

theorem xMerge_iParity_k1 (w s j : Nat) :
    iParity (xMerge w) (xMergeSurf w) s 0 j 1 = false := by
  simp [iParity, xMerge, xMergeSurf]

theorem xMerge_jParity_k1 (w s j : Nat) :
    jParity (xMerge w) (xMergeSurf w) s 0 j 1 = false := by
  simp [jParity, xMerge, xMergeSurf]

theorem xMerge_allOrNoneI_k1 (w s j : Nat) :
    allOrNoneI (xMerge w) (xMergeSurf w) s 0 j 1 = true := by
  rw [allOrNoneI]
  apply allEq_const_present (b := s == 0)
  intro p hp hpres
  fin_cases hp <;> simp_all [xMerge, xMergeSurf]

theorem xMerge_allOrNoneJ_k1 (w s j : Nat) :
    allOrNoneJ (xMerge w) (xMergeSurf w) s 0 j 1 = true := by
  rw [allOrNoneJ]
  apply allEq_const_present (b := (decide (1 ≤ s) && decide (s - 1 = j) && decide (s ≤ w)))
  intro p hp hpres
  fin_cases hp <;> simp_all [xMerge, xMergeSurf]

/-! ### `funcCubeOK` at every cube — the per-column universal (factored in width). -/

/-- Interior layer `k=1`: `funcCubeOK` holds at EVERY column `j` and flow `s`.  For
a data column `j<w` the worldline supplies `hasK`, so the only nontrivial
(missing-`I`) obligation is the parity/all-or-none cancellation proved above; for
`j≥w` the cube is empty (degree-0 port). -/
theorem xMerge_funcCubeOK_k1 (w s j : Nat) :
    funcCubeOK (xMerge w) (xMergeSurf w) s 0 j 1 = true := by
  unfold funcCubeOK
  rw [xMerge_iParity_k1, xMerge_jParity_k1, xMerge_allOrNoneI_k1, xMerge_allOrNoneJ_k1]
  by_cases hjw : j < w
  · have hK : (xMerge w).hasK 0 j 1 = true := by simp [LaSre.hasK, xMerge, hjw]
    rw [hK]
    simp [xMerge]
  · have hd : (xMerge w).degree 0 j 1 ≤ 1 := by
      simp only [LaSre.degree, xMerge]
      have h1 : ¬ j + 1 < w := by omega
      have h3 : ¬ (j - 1) + 1 < w := by omega
      simp [hjw, h1, h3]
    rw [if_neg (show ¬((xMerge w).YCube 0 j 1 = true) by simp [xMerge]), if_pos hd]

/-- Boundary layers `k∈{0,2}`: only a worldline `K`-pipe can touch the cube, so its
degree is `≤1` — a port, trivially `funcCubeOK`. -/
theorem xMerge_funcCubeOK_k0 (w s j : Nat) :
    funcCubeOK (xMerge w) (xMergeSurf w) s 0 j 0 = true := by
  unfold funcCubeOK
  have hd : (xMerge w).degree 0 j 0 ≤ 1 := by
    by_cases h : j < w <;> simp [LaSre.degree, xMerge, h]
  rw [if_neg (show ¬((xMerge w).YCube 0 j 0 = true) by simp [xMerge]), if_pos hd]

theorem xMerge_funcCubeOK_k2 (w s j : Nat) :
    funcCubeOK (xMerge w) (xMergeSurf w) s 0 j 2 = true := by
  unfold funcCubeOK
  have hd : (xMerge w).degree 0 j 2 ≤ 1 := by
    by_cases h : j < w <;> simp [LaSre.degree, xMerge, h]
  rw [if_neg (show ¬((xMerge w).YCube 0 j 2 = true) by simp [xMerge]), if_pos hd]

/-! ### WIDTH-SYMBOLIC `funcOK` — the whole-grid check, factored per column. -/

/-- **★ WIDTH-SYMBOLIC INTERIOR FUNCTIONALITY ★** — the contiguous `X̄`-merge's
correlation surfaces satisfy the interior functionality check for ANY width `w`
and ANY number of flows `n`, with NO `native_decide` over the width.  The grid is
`1 × w × 3`, so `gridCubes` ranges `i=0`, `j<w`, `k∈{0,1,2}`. -/
theorem xMerge_funcOK (w n : Nat) :
    funcOK (xMerge w) (xMergeSurf w) n = true := by
  rw [LaSre.funcOK, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  rintro ⟨i, j, k⟩ hc
  rw [mem_gridCubes] at hc
  obtain ⟨hi, _, hk⟩ := hc
  have hi0 : i = 0 := by simp only [xMerge] at hi; omega
  subst hi0
  simp only [xMerge] at hk
  interval_cases k
  · exact xMerge_funcCubeOK_k0 w s j
  · exact xMerge_funcCubeOK_k1 w s j
  · exact xMerge_funcCubeOK_k2 w s j

/-- **★ WIDTH-SYMBOLIC INTERIOR CORRECTNESS ★** — `valid` ∧ `funcOK`, ∀w∀n. -/
theorem xMerge_LaSCorrect (w n : Nat) :
    LaSCorrect (xMerge w) (xMergeSurf w) n = true := by
  rw [LaSre.LaSCorrect, xMerge_valid, xMerge_funcOK]; rfl

/-! ## §4. WIDTH-SYMBOLIC PORTS — the boundary matches the joint-`X̄` / `Z̄` spec.

  Ports: each data column `c` has an IN port (`k=0`) and an OUT port (`k=2`), at
  `(0, c, k)`, blue selector `4` (`KI`, the `Z` piece) and red selector `5`
  (`KJ`, the `X` piece).  Spec flow `0` is the joint `X̄` (red on all ports); flow
  `s∈[1,w]` is `Z̄` on column `s-1` (blue).  The list is `ins ++ outs`, so a port
  at `zipIdx` index `p` sits on column `p % w`. -/

def xMergePorts (w : Nat) : List Port :=
  (List.range w).map (fun c => ⟨0, c, 0, 4, 5⟩) ++ (List.range w).map (fun c => ⟨0, c, 2, 4, 5⟩)

def xMergePaulis (w : Nat) : Nat → Nat → Pauli := fun s p =>
  if s = 0 then Pauli.X else if s - 1 = p % w then Pauli.Z else Pauli.I

/-- Every port sits on column `idx % w` (`< w`), at `pi=0`, with the canonical
blue/red selectors — the structural invariant of the `ins ++ outs` port list. -/
theorem xMergePorts_get {w : Nat} {p : Port} {idx : Nat}
    (h : (p, idx) ∈ (xMergePorts w).zipIdx) :
    p.pi = 0 ∧ p.blueSel = 4 ∧ p.redSel = 5 ∧ p.pj = idx % w ∧ p.pj < w := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  simp only [xMergePorts, List.getElem?_append, List.getElem?_map,
    List.length_map, List.length_range] at h
  by_cases hidx : idx < w
  · rw [if_pos hidx, List.getElem?_eq_getElem (by simp [hidx]), List.getElem_range,
      Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, (Nat.mod_eq_of_lt hidx).symm, hidx⟩
  · rw [if_neg hidx] at h
    by_cases hidx2 : idx - w < w
    · rw [List.getElem?_eq_getElem (by simp [hidx2]), List.getElem_range,
        Option.map_some, Option.some.injEq] at h
      subst h
      have hmod : idx % w = idx - w := by
        conv_lhs => rw [show idx = (idx - w) + w from by omega]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hidx2]
      exact ⟨rfl, rfl, rfl, hmod.symm, hidx2⟩
    · exfalso
      rw [List.getElem?_eq_none (by simp only [List.length_range]; omega)] at h
      simp at h

/-- **★ WIDTH-SYMBOLIC PORT BOUNDARY ★** — at every port the correlation surface
matches the spec Pauli (red `KJ` = joint `X̄`, blue `KI` = the per-column `Z̄`),
for ANY width.  The `(s≤w)` factor in `KI` is automatic because a port's column
`idx % w < w`, so a flow `s` with `s-1` on that column has `s ≤ w`. -/
theorem xMerge_portsOK (w : Nat) :
    portsOK (xMergeSurf w) (xMergePorts w) (xMergePaulis w) (w + 1) = true := by
  rw [portsOK, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro pp hpp
  obtain ⟨p, idx⟩ := pp
  obtain ⟨hpi, hbl, hrd, hpj, hlt⟩ := xMergePorts_get hpp
  have hw : 0 < w := by omega
  have hmw : idx % w < w := Nat.mod_lt _ hw
  simp only [Surf.sel, hbl, hrd, hpi, hpj, xMergeSurf, xMergePaulis, portBlue, portRed]
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp [hmw]
  · have hs0 : ¬ s = 0 := by omega
    by_cases hc : s - 1 = idx % w
    · have hsw : s ≤ w := by omega
      simp [hs0, hc, hmw, hsw]
      omega
    · simp [hs0, hc, hmw]

/-! ## §5. ★ THE HEADLINE (single gadget) — an `X̄`-merge of ANY WIDTH is `LaSCorrectFull`. -/

/-- **★ WIDTH-SYMBOLIC `LaSCorrectFull` ★** — for EVERY width `w`, the contiguous
`X̄`-merge is a fully correct lattice-surgery subroutine against its joint-`X̄` /
per-column-`Z̄` measurement spec.  The `I ↔ J` dual of `zMerge_LaSCorrectFull`,
proven by per-column universals — NOT by `native_decide` over the width. -/
theorem xMerge_LaSCorrectFull (w : Nat) :
    LaSCorrectFull (xMerge w) (xMergeSurf w) (xMergePorts w) (xMergePaulis w) (w + 1) = true := by
  rw [LaSre.LaSCorrectFull, xMerge_valid, xMerge_funcOK, xMerge_portsOK]; rfl

/-! ## §6. THE DEPTH STACK — width-symbolic self-interface certs at `xConn w`. -/

/-- Weld every data column `0..w-1` (at `i = 0`) across each time seam. -/
def xConn (w : Nat) : List (Nat × Nat) := (List.range w).map (fun c => (0, c))

/-- The connection list contains data column `(0, j)` exactly when `j < w`. -/
theorem xConn_contains (w j : Nat) :
    (xConn w).contains (0, j) = decide (j < w) := by
  rw [List.contains_eq_mem, xConn]
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
  congr 1
  apply propext
  constructor
  · rintro ⟨c, hc, _, rfl⟩; exact hc
  · intro hj; exact ⟨j, hj, trivial, rfl⟩

/-- The reference self-weld of `xMerge w` (the seam the depth engine certifies). -/
abbrev xSeam (w : Nat) : LaSre := weldK 3 (xMerge w) (xMerge w) (xConn w)

/-- The stitched reference surface (used by the functionality interface cert). -/
abbrev xSeamSurf (w : Nat) : Surf := stitchSurf 3 (xMergeSurf w) (xMergeSurf w)

/-- The weld has NO `I`-pipes (neither `xMerge` half does) — so `hasI ≡ false` and
`validCube` is trivially satisfied at EVERY cube, for ALL widths. -/
theorem xSeam_ExistI (w i j k : Nat) : (xSeam w).ExistI i j k = false := by
  simp only [xSeam, weldK, xMerge]; split <;> rfl

theorem xSeam_YCube (w i j k : Nat) : (xSeam w).YCube i j k = false := by
  simp only [xSeam, weldK, xMerge]; split <;> rfl

theorem xSeam_validCube (w i j k : Nat) : (xSeam w).validCube i j k = true := by
  simp only [LaSre.validCube, LaSre.hasI, xSeam_ExistI, xSeam_YCube,
    Bool.false_or, Bool.and_false, Bool.not_false]
  simp

/-- **★ WIDTH-SYMBOLIC reference VALIDITY interface cert ★** — the self-weld of
`xMerge w` passes the O(N) validity interface check at the seam, for ALL widths
`w`, with NO `native_decide`.  Every seam cube is `validCube`-true (no `I`-pipes,
no `Y`-cubes).  Footprint `w=1`, `wj=w` (the `xMerge` grid is `1 × w`). -/
theorem xMerge_refValid_sym (w : Nat) :
    weldInterfaceValidOK2 3 (xMerge w) (xMerge w) (xConn w) 1 w = true := by
  rw [weldInterfaceValidOK2, List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro j _
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [if_pos (by norm_num)]; exact xSeam_validCube w i j (3 - 1)
  · exact xSeam_validCube w i j 3

/-! ### Welded field reductions at the seam layers `k ∈ {1,2,3}`. -/

theorem xSeam_ExistK1 (w j : Nat) : (xSeam w).ExistK 0 j 1 = decide (j < w) := by
  simp only [xSeam, weldK]; rw [if_pos (by norm_num)]; simp [xMerge]
theorem xSeam_ExistK2 (w j : Nat) : (xSeam w).ExistK 0 j 2 = decide (j < w) := by
  simp only [xSeam, weldK, xConn_contains]; simp [xMerge]
theorem xSeam_ExistK3 (w j : Nat) : (xSeam w).ExistK 0 j 3 = decide (j < w) := by
  simp only [xSeam, weldK]; simp [xMerge]

-- ExistJ (the seam pipe) is absent at every seam layer (it lives only at the
-- gadget's k=1, which after weld sits at k=1 of the BOTTOM copy).
theorem xSeam_ExistJ2 (w j : Nat) : (xSeam w).ExistJ 0 j 2 = false := by
  simp only [xSeam, weldK]; rw [if_pos (by norm_num)]; simp [xMerge]
theorem xSeam_ExistJ3 (w j : Nat) : (xSeam w).ExistJ 0 j 3 = false := by
  simp only [xSeam, weldK]; rw [if_neg (by norm_num)]; simp [xMerge]
theorem xSeam_ExistIany (w j k : Nat) : (xSeam w).ExistI 0 j k = false :=
  xSeam_ExistI w 0 j k

-- Stitched surface KI/KJ are the k-independent `xMergeSurf` value at all three layers.
theorem xSeamSurf_KI1 (w s j : Nat) :
    (xSeamSurf w).KI s 0 j 1 = (xMergeSurf w).KI s 0 j 0 := by
  simp only [xSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem xSeamSurf_KI2 (w s j : Nat) :
    (xSeamSurf w).KI s 0 j 2 = (xMergeSurf w).KI s 0 j 0 := by
  simp only [xSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem xSeamSurf_KI3 (w s j : Nat) :
    (xSeamSurf w).KI s 0 j 3 = (xMergeSurf w).KI s 0 j 0 := by
  simp only [xSeamSurf, stitchSurf]; rw [if_neg (by norm_num)]
theorem xSeamSurf_KJ1 (w s j : Nat) :
    (xSeamSurf w).KJ s 0 j 1 = (xMergeSurf w).KJ s 0 j 0 := by
  simp only [xSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem xSeamSurf_KJ2 (w s j : Nat) :
    (xSeamSurf w).KJ s 0 j 2 = (xMergeSurf w).KJ s 0 j 0 := by
  simp only [xSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem xSeamSurf_KJ3 (w s j : Nat) :
    (xSeamSurf w).KJ s 0 j 3 = (xMergeSurf w).KJ s 0 j 0 := by
  simp only [xSeamSurf, stitchSurf]; rw [if_neg (by norm_num)]

/-! ### Seam parity / all-or-none cancellations — per column, for `k ∈ {2,3}`.

  At each seam layer the only incident pipes are the two `K`-worldline pipes (in +
  out); their two surface contributions are EQUAL (the surface is `k`-independent),
  so every parity XORs to `false` and every all-or-none list has equal present
  values.  Mirror of Step 2b's `k ∈ {2,3}` analysis with `I ↔ J` swapped. -/

theorem xSeam_jParity2 (w s j : Nat) :
    jParity (xSeam w) (xSeamSurf w) s 0 j 2 = false := by
  rw [jParity, show (2 : Nat) - 1 = 1 from rfl,
    xSeam_ExistIany, xSeam_ExistK2, xSeam_ExistK1, xSeamSurf_KJ2, xSeamSurf_KJ1]
  simp

theorem xSeam_jParity3 (w s j : Nat) :
    jParity (xSeam w) (xSeamSurf w) s 0 j 3 = false := by
  rw [jParity, show (3 : Nat) - 1 = 2 from rfl,
    xSeam_ExistIany, xSeam_ExistK3, xSeam_ExistK2, xSeamSurf_KJ3, xSeamSurf_KJ2]
  simp

theorem xSeam_iParity2 (w s j : Nat) :
    iParity (xSeam w) (xSeamSurf w) s 0 j 2 = false := by
  rw [iParity, show (2 : Nat) - 1 = 1 from rfl]
  simp only [xSeam_ExistJ2, xSeam_ExistK2, xSeam_ExistK1, xSeamSurf_KI2, xSeamSurf_KI1]
  simp

theorem xSeam_iParity3 (w s j : Nat) :
    iParity (xSeam w) (xSeamSurf w) s 0 j 3 = false := by
  rw [iParity, show (3 : Nat) - 1 = 2 from rfl]
  simp only [xSeam_ExistJ3, xSeam_ExistK3, xSeam_ExistK2, xSeamSurf_KI3, xSeamSurf_KI2]
  simp

theorem xSeam_allOrNoneJ2 (w s j : Nat) :
    allOrNoneJ (xSeam w) (xSeamSurf w) s 0 j 2 = true := by
  rw [allOrNoneJ, show (2 : Nat) - 1 = 1 from rfl,
    xSeam_ExistIany, xSeam_ExistK2, xSeam_ExistK1, xSeamSurf_KI2, xSeamSurf_KI1]
  apply allEq_const_present (b := (xMergeSurf w).KI s 0 j 0)
  intro p hp hpres
  fin_cases hp <;> simp_all

theorem xSeam_allOrNoneJ3 (w s j : Nat) :
    allOrNoneJ (xSeam w) (xSeamSurf w) s 0 j 3 = true := by
  rw [allOrNoneJ, show (3 : Nat) - 1 = 2 from rfl,
    xSeam_ExistIany, xSeam_ExistK3, xSeam_ExistK2, xSeamSurf_KI3, xSeamSurf_KI2]
  apply allEq_const_present (b := (xMergeSurf w).KI s 0 j 0)
  intro p hp hpres
  fin_cases hp <;> simp_all

theorem xSeam_allOrNoneI2 (w s j : Nat) :
    allOrNoneI (xSeam w) (xSeamSurf w) s 0 j 2 = true := by
  rw [allOrNoneI, show (2 : Nat) - 1 = 1 from rfl]
  simp only [xSeam_ExistJ2, xSeam_ExistK2, xSeam_ExistK1, xSeamSurf_KJ2, xSeamSurf_KJ1]
  apply allEq_const_present (b := (xMergeSurf w).KJ s 0 j 0)
  intro p hp hpres
  fin_cases hp <;> simp_all

theorem xSeam_allOrNoneI3 (w s j : Nat) :
    allOrNoneI (xSeam w) (xSeamSurf w) s 0 j 3 = true := by
  rw [allOrNoneI, show (3 : Nat) - 1 = 2 from rfl]
  simp only [xSeam_ExistJ3, xSeam_ExistK3, xSeam_ExistK2, xSeamSurf_KJ3, xSeamSurf_KJ2]
  apply allEq_const_present (b := (xMergeSurf w).KJ s 0 j 0)
  intro p hp hpres
  fin_cases hp <;> simp_all

/-! ### The per-column seam `funcCubeOK` (the heart of the symbolic cert). -/

theorem xSeam_hasK2 (w j : Nat) (hjw : j < w) : (xSeam w).hasK 0 j 2 = true := by
  simp only [LaSre.hasK, xSeam_ExistK2]; simp [hjw]

theorem xSeam_hasK3 (w j : Nat) (hjw : j < w) : (xSeam w).hasK 0 j 3 = true := by
  simp only [LaSre.hasK, xSeam_ExistK3]; simp [hjw]

theorem xSeam_degree2_port (w j : Nat) (hjw : ¬ j < w) :
    (xSeam w).degree 0 j 2 ≤ 1 := by
  simp only [LaSre.degree, xSeam_ExistK2, xSeam_ExistJ2, xSeam_ExistIany,
    show (2 : Nat) - 1 = 1 from rfl, xSeam_ExistK1]
  simp [hjw]

theorem xSeam_degree3_port (w j : Nat) (hjw : ¬ j < w) :
    (xSeam w).degree 0 j 3 ≤ 1 := by
  simp only [LaSre.degree, xSeam_ExistK3, xSeam_ExistJ3, xSeam_ExistIany,
    show (3 : Nat) - 1 = 2 from rfl, xSeam_ExistK2]
  simp [hjw]

theorem xSeam_funcCubeOK2 (w s j : Nat) :
    funcCubeOK (xSeam w) (xSeamSurf w) s 0 j 2 = true := by
  unfold funcCubeOK
  rw [xSeam_iParity2, xSeam_jParity2, xSeam_allOrNoneI2, xSeam_allOrNoneJ2]
  by_cases hjw : j < w
  · rw [xSeam_hasK2 w j hjw]
    rw [if_neg (show ¬((xSeam w).YCube 0 j 2 = true) by rw [xSeam_YCube]; simp)]
    rw [if_neg (show ¬((xSeam w).degree 0 j 2 ≤ 1) by
      simp only [LaSre.degree, xSeam_ExistK2, xSeam_ExistJ2, xSeam_ExistIany,
        show (2 : Nat) - 1 = 1 from rfl, xSeam_ExistK1]; simp [hjw])]
    simp
  · rw [if_neg (show ¬((xSeam w).YCube 0 j 2 = true) by rw [xSeam_YCube]; simp),
      if_pos (xSeam_degree2_port w j hjw)]

theorem xSeam_funcCubeOK3 (w s j : Nat) :
    funcCubeOK (xSeam w) (xSeamSurf w) s 0 j 3 = true := by
  unfold funcCubeOK
  rw [xSeam_iParity3, xSeam_jParity3, xSeam_allOrNoneI3, xSeam_allOrNoneJ3]
  by_cases hjw : j < w
  · rw [xSeam_hasK3 w j hjw]
    rw [if_neg (show ¬((xSeam w).YCube 0 j 3 = true) by rw [xSeam_YCube]; simp)]
    rw [if_neg (show ¬((xSeam w).degree 0 j 3 ≤ 1) by
      simp only [LaSre.degree, xSeam_ExistK3, xSeam_ExistJ3, xSeam_ExistIany,
        show (3 : Nat) - 1 = 2 from rfl, xSeam_ExistK2]; simp [hjw])]
    simp
  · rw [if_neg (show ¬((xSeam w).YCube 0 j 3 = true) by rw [xSeam_YCube]; simp),
      if_pos (xSeam_degree3_port w j hjw)]

/-- **★ WIDTH-SYMBOLIC reference FUNCTIONALITY interface cert ★** — the self-weld
of `xMerge w` passes the O(N) functionality interface check at the seam, for ALL
widths `w` and `w+1` flows, with NO `native_decide`.  Footprint `w=1`, `wj=w`. -/
theorem xMerge_refFunc_sym (w : Nat) :
    weldInterfaceOK2 3 (xMerge w) (xMerge w) (xMergeSurf w) (xMergeSurf w)
      (xConn w) (w + 1) 1 w = true := by
  rw [weldInterfaceOK2, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro i hi
  have hi0 : i = 0 := by
    have := List.mem_range.1 hi; omega
  subst hi0
  rw [List.all_eq_true]
  intro j _
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [if_pos (by norm_num)]; exact xSeam_funcCubeOK2 w s j
  · exact xSeam_funcCubeOK3 w s j

/-! ## §7. ★ THE UNIFIED ∀w ∀N `chainOK` — width-symbolic AND depth-generic. ★ -/

/-- **★ UNIFIED WIDTH+DEPTH `chainOK` ★** — for EVERY width `w` and EVERY chain
length `N`, the depth-`(N+1)` stack of `xMerge w`s welded across all `w` data
columns passes `chainOK`.  Instantiates the gadget-generic depth engine
`zChain_chainOK_generic` with the two WIDTH-SYMBOLIC interface certs above. -/
theorem xMerge_stack_chainOK (w N : Nat) :
    chainOK 3 (w + 1) (xConn w) 1 w
      (List.replicate (N + 1) (xMerge w)) (List.replicate (N + 1) (xMergeSurf w)) = true :=
  zChain_chainOK_generic (h := 3) (conn := xConn w) (g := xMerge w) (s := xMergeSurf w)
    (by norm_num) (w + 1) 1 w
    rfl rfl rfl (xMerge_valid w) (xMerge_funcOK w (w + 1))
    (xMerge_refValid_sym w) (xMerge_refFunc_sym w) N

/-- **★ UNIFIED WIDTH+DEPTH INTERIOR CORRECTNESS ★** — the welded depth-`(N+1)`
stack of `xMerge w`s is `valid` AND `funcOK` across every weld seam, for ALL `w`
AND ALL `N` with NO `native_decide` over either. -/
theorem xMerge_stack_LaSCorrect (w N : Nat) :
    LaSCorrect (weldChain 3 (xConn w) (List.replicate (N + 1) (xMerge w)))
      (weldChainSurf 3 (List.replicate (N + 1) (xMergeSurf w))) (w + 1) = true := by
  obtain ⟨hv, hf, _, _⟩ :=
    chainOK_sound 3 (w + 1) (xConn w) 1 w
      (List.replicate (N + 1) (xMerge w)) (List.replicate (N + 1) (xMergeSurf w))
      (xMerge_stack_chainOK w N)
  rw [LaSre.LaSCorrect, hv, hf]; rfl

/-! ## §8. ★ WIDTH-SYMBOLIC + TOP-BOUNDARY PORTS — the unified composite boundary. ★ -/

/-- Composite ports: `w` IN ports at `k = 0`, `w` OUT ports at `k = topK3 N`,
columns `(0, c)`, canonical blue=`KI`(4)/red=`KJ`(5). -/
def xStackPorts (w N : Nat) : List Port :=
  (List.range w).map (fun c => ⟨0, c, 0, 4, 5⟩)
    ++ (List.range w).map (fun c => ⟨0, c, topK3 N, 4, 5⟩)

/-- Every stack port sits on column `idx % w` (`< w`), `pi = 0`, canonical
selectors; the IN ports (`idx < w`) at `pk = 0`, the OUT ports at `pk = topK3 N`. -/
theorem xStackPorts_get {w N : Nat} {p : Port} {idx : Nat}
    (h : (p, idx) ∈ (xStackPorts w N).zipIdx) :
    p.pi = 0 ∧ p.blueSel = 4 ∧ p.redSel = 5 ∧ p.pj = idx % w ∧ p.pj < w
      ∧ (p.pk = 0 ∨ p.pk = topK3 N) := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  simp only [xStackPorts, List.getElem?_append, List.getElem?_map,
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

/-- The stack surface's `KI` plane is `N`-independent at BOTH boundaries (chain
bottom `k=0` via `zChainSurf_KI0`, chain top `k=topK3 N` via `zChainSurf_KI_top`),
equal to `xMergeSurf w`'s `k`-independent value. -/
theorem xStackSurf_KI_bdry (w N s j k : Nat) (hk : k = 0 ∨ k = topK3 N) :
    (zChainSurf 3 (xMergeSurf w) N).KI s 0 j k = (xMergeSurf w).KI s 0 j 0 := by
  rcases hk with hk | hk
  · subst hk; exact zChainSurf_KI0 (by norm_num) N s 0 j
  · subst hk
    rw [zChainSurf_KI_top (by norm_num) N s 0 j]
    rfl

theorem xStackSurf_KJ_bdry (w N s j k : Nat) (hk : k = 0 ∨ k = topK3 N) :
    (zChainSurf 3 (xMergeSurf w) N).KJ s 0 j k = (xMergeSurf w).KJ s 0 j 0 := by
  rcases hk with hk | hk
  · subst hk; exact zChainSurf_KJ0 (by norm_num) N s 0 j
  · subst hk
    rw [zChainSurf_KJ_top (by norm_num) N s 0 j]
    rfl

/-- **★ WIDTH-SYMBOLIC + TOP-BOUNDARY PORT MATCH, FOR ALL `N` ★** — at every
composite port of the depth-`(N+1)` stack of `xMerge w`s, the chain surface matches
the spec Pauli (red `KJ` = joint `X̄`, blue `KI` = the per-column `Z̄`), for ALL
widths `w` AND all chain lengths `N` — NO `native_decide` over `w` OR `N`. -/
theorem xMerge_stack_portsOK (w N : Nat) :
    portsOK (zChainSurf 3 (xMergeSurf w) N) (xStackPorts w N) (xMergePaulis w) (w + 1) = true := by
  rw [portsOK, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro pp hpp
  obtain ⟨p, idx⟩ := pp
  obtain ⟨hpi, hbl, hrd, hpj, hlt, hpk⟩ := xStackPorts_get hpp
  have hw : 0 < w := by omega
  have hmw : idx % w < w := Nat.mod_lt _ hw
  simp only [Surf.sel, hbl, hrd, hpi, hpj]
  rw [xStackSurf_KI_bdry w N s (idx % w) p.pk hpk,
      xStackSurf_KJ_bdry w N s (idx % w) p.pk hpk]
  simp only [xMergeSurf, xMergePaulis, portBlue, portRed]
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp [hmw]
  · have hs0 : ¬ s = 0 := by omega
    by_cases hc : s - 1 = idx % w
    · have hsw : s ≤ w := by omega
      simp [hs0, hc, hmw, hsw]
      omega
    · simp [hs0, hc, hmw]

/-! ## §9. ★ THE UNIFIED HEADLINE — ∀w ∀N `LaSCorrectFull` for the `X̄`-merge stack. ★ -/

/-- **★ UNIFIED WIDTH-SYMBOLIC + DEPTH-GENERIC `LaSCorrectFull` (X-MERGE) ★** — for
EVERY width `w` and EVERY chain length `N`, the welded depth-`(N+1)` stack of
contiguous `X̄`-merges (each measuring the same joint `X̄` on all `w` data qubits) is
a FULLY CORRECT lattice-surgery program: structurally valid, interior functionality
satisfied across every weld seam, and the composite ports (IN at the bottom, OUT at
the chain top) matching the joint-`X̄` / per-column-`Z̄` spec.

The `I ↔ J` time–space dual of `zMerge_stack_LaSCorrectFull`.  NO `native_decide`
over EITHER the width `w` OR the chain length `N` — the width via the per-column
locality of `funcCubeOK`/`validCube`, the depth via the `N`-independence of the seam
interface checks (the gadget-generic engine `zChain_chainOK_generic`). -/
theorem xMerge_stack_LaSCorrectFull (w N : Nat) :
    LaSCorrectFull
      (weldChain 3 (xConn w) (List.replicate (N + 1) (xMerge w)))
      (weldChainSurf 3 (List.replicate (N + 1) (xMergeSurf w)))
      (xStackPorts w N) (xMergePaulis w) (w + 1) = true :=
  weldChain_LaSCorrectFull 3 (w + 1) (xConn w) 1 w
    (List.replicate (N + 1) (xMerge w)) (List.replicate (N + 1) (xMergeSurf w))
    (xStackPorts w N) (xMergePaulis w)
    (xMerge_stack_chainOK w N) (xMerge_stack_portsOK w N)

end FormalRV.QEC.LaSre
