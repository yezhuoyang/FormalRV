/-
  FormalRV.QEC.LatticeSurgery.WeldComposition
  -------------------------------------------
  **★ THE GENERAL WELD-COMPOSITION THEOREM — `weldK` preserves `funcOK`
  MODULARLY, so a program chain is certified gadget-by-gadget (LINEAR), not by
  one exponential `native_decide`. ★**

  `funcCubeOK L S s i j k` reads `L`/`S` only at the cube `(i,j,k)` and its LOWER
  neighbours `(i-1,j,k)`, `(i,j-1,k)`, `(i,j,k-1)` — all at k-coordinate `k` or
  `k-1`.  So for a cube with `k+1 < kA`, the welded diagram agrees with `A`
  everywhere `funcCubeOK` looks; for `k ≥ kA+1`, it agrees with (shifted) `B`.
  The only NEW obligations are the two interface layers `k ∈ {kA-1, kA}` — a
  small decidable check (`weldInterfaceOK`).  Hence:

      `A.funcOK SA n ∧ B.funcOK SB n ∧ weldInterfaceOK …
          → (weldK kA A B conn).funcOK (stitchSurf kA SA SB) n`

  is proven WITHOUT deciding the whole welded grid (`weldK_funcOK`).  A length-`n`
  chain then follows by induction on `weldChain`.
-/
import FormalRV.QEC.LatticeSurgery.Weld

namespace FormalRV.QEC.LaSre

/-! ## §1. The stitched surface (the `weldSurfP` composite, products pre-baked). -/

/-- Piecewise stitch of two surfaces along time `kA` (the identity-flow-map weld).
`weldSurfP` is exactly this on the `surfCombine`d halves. -/
def stitchSurf (kA : Nat) (SA SB : Surf) : Surf :=
  { IJ := fun s i j k => if k < kA then SA.IJ s i j k else SB.IJ s i j (k - kA)
    IK := fun s i j k => if k < kA then SA.IK s i j k else SB.IK s i j (k - kA)
    JK := fun s i j k => if k < kA then SA.JK s i j k else SB.JK s i j (k - kA)
    JI := fun s i j k => if k < kA then SA.JI s i j k else SB.JI s i j (k - kA)
    KI := fun s i j k => if k < kA then SA.KI s i j k else SB.KI s i j (k - kA)
    KJ := fun s i j k => if k < kA then SA.KJ s i j k else SB.KJ s i j (k - kA) }

/-! ## §2. Field-agreement lemmas (welded diagram vs `A`, below the interface). -/

variable (kA : Nat) (A B : LaSre) (SA SB : Surf) (conn : List (Nat × Nat))

theorem wk_YCube {i j k} (h : k < kA) :
    (weldK kA A B conn).YCube i j k = A.YCube i j k := if_pos h
theorem wk_ExistI {i j k} (h : k < kA) :
    (weldK kA A B conn).ExistI i j k = A.ExistI i j k := if_pos h
theorem wk_ExistJ {i j k} (h : k < kA) :
    (weldK kA A B conn).ExistJ i j k = A.ExistJ i j k := if_pos h
theorem wk_ExistK {i j k} (h : k + 1 < kA) :
    (weldK kA A B conn).ExistK i j k = A.ExistK i j k := if_pos h
theorem st_IJ {i j k} (h : k < kA) :
    (stitchSurf kA SA SB).IJ s i j k = SA.IJ s i j k := if_pos h
theorem st_IK {i j k} (h : k < kA) :
    (stitchSurf kA SA SB).IK s i j k = SA.IK s i j k := if_pos h
theorem st_JK {i j k} (h : k < kA) :
    (stitchSurf kA SA SB).JK s i j k = SA.JK s i j k := if_pos h
theorem st_JI {i j k} (h : k < kA) :
    (stitchSurf kA SA SB).JI s i j k = SA.JI s i j k := if_pos h
theorem st_KI {i j k} (h : k < kA) :
    (stitchSurf kA SA SB).KI s i j k = SA.KI s i j k := if_pos h
theorem st_KJ {i j k} (h : k < kA) :
    (stitchSurf kA SA SB).KJ s i j k = SA.KJ s i j k := if_pos h

/-! ## §3. THE LOWER-CUBE CONGRUENCE — `funcCubeOK` agrees with `A` when `k+1<kA`. -/

theorem funcCubeOK_lower (s i j k : Nat) (h : k + 1 < kA) :
    (weldK kA A B conn).funcCubeOK (stitchSurf kA SA SB) s i j k
      = A.funcCubeOK SA s i j k := by
  have hk : k < kA := by omega
  have hkm : k - 1 < kA := by omega
  have hkk : k - 1 + 1 < kA := by omega
  simp only [LaSre.funcCubeOK, LaSre.degree, LaSre.hasI, LaSre.hasJ, LaSre.hasK,
    LaSre.iParity, LaSre.jParity, LaSre.kParity,
    LaSre.allOrNoneI, LaSre.allOrNoneJ, LaSre.allOrNoneK,
    wk_YCube kA A B conn hk, wk_ExistI kA A B conn hk, wk_ExistJ kA A B conn hk,
    wk_ExistK kA A B conn h, wk_ExistK kA A B conn hkk,
    st_IJ kA SA SB hk, st_IK kA SA SB hk, st_JK kA SA SB hk,
    st_JI kA SA SB hk, st_KI kA SA SB hk, st_KJ kA SA SB hk,
    st_IJ kA SA SB hkm, st_IK kA SA SB hkm, st_JK kA SA SB hkm,
    st_JI kA SA SB hkm, st_KI kA SA SB hkm, st_KJ kA SA SB hkm,
    wk_ExistI kA A B conn hkm, wk_ExistJ kA A B conn hkm]

/-! ## §4. Field-agreement lemmas ABOVE the interface (welded vs shifted `B`). -/

theorem wk_YCube_hi {i j k} (h : ¬ k < kA) :
    (weldK kA A B conn).YCube i j k = B.YCube i j (k - kA) := if_neg h
theorem wk_ExistI_hi {i j k} (h : ¬ k < kA) :
    (weldK kA A B conn).ExistI i j k = B.ExistI i j (k - kA) := if_neg h
theorem wk_ExistJ_hi {i j k} (h : ¬ k < kA) :
    (weldK kA A B conn).ExistJ i j k = B.ExistJ i j (k - kA) := if_neg h
theorem wk_ExistK_hi {i j k} (h1 : ¬ k + 1 < kA) (h2 : ¬ (k + 1 == kA) = true) :
    (weldK kA A B conn).ExistK i j k = B.ExistK i j (k - kA) := by
  simp only [weldK]; rw [if_neg h1, if_neg h2]
theorem st_IJ_hi {i j k} (h : ¬ k < kA) :
    (stitchSurf kA SA SB).IJ s i j k = SB.IJ s i j (k - kA) := if_neg h
theorem st_IK_hi {i j k} (h : ¬ k < kA) :
    (stitchSurf kA SA SB).IK s i j k = SB.IK s i j (k - kA) := if_neg h
theorem st_JK_hi {i j k} (h : ¬ k < kA) :
    (stitchSurf kA SA SB).JK s i j k = SB.JK s i j (k - kA) := if_neg h
theorem st_JI_hi {i j k} (h : ¬ k < kA) :
    (stitchSurf kA SA SB).JI s i j k = SB.JI s i j (k - kA) := if_neg h
theorem st_KI_hi {i j k} (h : ¬ k < kA) :
    (stitchSurf kA SA SB).KI s i j k = SB.KI s i j (k - kA) := if_neg h
theorem st_KJ_hi {i j k} (h : ¬ k < kA) :
    (stitchSurf kA SA SB).KJ s i j k = SB.KJ s i j (k - kA) := if_neg h

/-! ## §5. THE UPPER-CUBE CONGRUENCE — `funcCubeOK` agrees with shifted `B`. -/

theorem funcCubeOK_upper (s i j k : Nat) (h : kA < k) :
    (weldK kA A B conn).funcCubeOK (stitchSurf kA SA SB) s i j k
      = B.funcCubeOK SB s i j (k - kA) := by
  -- write k = kA + 1 + m so every shifted coordinate simplifies cleanly
  obtain ⟨m, rfl⟩ : ∃ m, k = kA + 1 + m := ⟨k - kA - 1, by omega⟩
  have e1 : kA + 1 + m - kA = m + 1 := by omega
  have e2 : kA + 1 + m - 1 = kA + m := by omega
  have e3 : kA + m - kA = m := by omega
  have h1 : ¬ kA + 1 + m < kA := by omega
  have h3 : ¬ kA + m < kA := by omega
  have hK1 : ¬ kA + 1 + m + 1 < kA := by omega
  have hK2 : ¬ (kA + 1 + m + 1 == kA) = true := by intro hc; have := eq_of_beq hc; omega
  have hK3 : ¬ kA + m + 1 < kA := by omega
  have hK4 : ¬ (kA + m + 1 == kA) = true := by intro hc; have := eq_of_beq hc; omega
  have p1 : (0 < kA + 1 + m) = True := eq_true (by omega)
  have p2 : (0 < m + 1) = True := eq_true (by omega)
  simp only [LaSre.funcCubeOK, LaSre.degree, LaSre.hasI, LaSre.hasJ, LaSre.hasK,
    LaSre.iParity, LaSre.jParity, LaSre.kParity,
    LaSre.allOrNoneI, LaSre.allOrNoneJ, LaSre.allOrNoneK,
    e2,
    wk_YCube_hi kA A B conn h1, wk_ExistI_hi kA A B conn h1,
    wk_ExistJ_hi kA A B conn h1, wk_ExistK_hi kA A B conn hK1 hK2,
    wk_ExistI_hi kA A B conn h3, wk_ExistJ_hi kA A B conn h3,
    wk_ExistK_hi kA A B conn hK3 hK4,
    st_IJ_hi kA SA SB h1, st_IK_hi kA SA SB h1, st_JK_hi kA SA SB h1,
    st_JI_hi kA SA SB h1, st_KI_hi kA SA SB h1, st_KJ_hi kA SA SB h1,
    st_IJ_hi kA SA SB h3, st_IK_hi kA SA SB h3, st_JK_hi kA SA SB h3,
    st_JI_hi kA SA SB h3, st_KI_hi kA SA SB h3, st_KJ_hi kA SA SB h3,
    e1, e3, p1, p2, Nat.add_sub_cancel]

/-! ## §6. Cube-membership, the interface check, and the MAIN theorem. -/

theorem mem_gridCubes {L : LaSre} {i j k : Nat} :
    (i, j, k) ∈ L.gridCubes ↔ i < L.maxI ∧ j < L.maxJ ∧ k < L.maxK := by
  simp only [LaSre.gridCubes, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, rfl, rfl, rfl⟩; exact ⟨ha, hb, hc⟩
  · rintro ⟨hi, hj, hk⟩; exact ⟨i, hi, j, hj, k, hk, rfl, rfl, rfl⟩

/-- **The interface obligation** — `funcCubeOK` at the TWO interface layers
`k = kA-1` (`k+1=kA`) and `k = kA`, which were degree-1 PORTS in `A`/`B` (skipped
by their `funcOK`) and become interior on welding.  A SMALL decidable check
(only two `k`-layers), independent of the rest of the chain. -/
def weldInterfaceOK (kA : Nat) (A B : LaSre) (SA SB : Surf)
    (conn : List (Nat × Nat)) (n : Nat) : Bool :=
  (List.range n).all (fun s =>
    (weldK kA A B conn).gridCubes.all (fun c =>
      if c.2.2 + 1 = kA ∨ c.2.2 = kA then
        (weldK kA A B conn).funcCubeOK (stitchSurf kA SA SB) s c.1 c.2.1 c.2.2
      else true))

/-- **★ THE O(N) INTERFACE CHECK ★** — the SAME obligation as `weldInterfaceOK`,
but iterating ONLY the two interface layers `k ∈ {kA-1, kA}`, and only over a
GIVEN spatial footprint `w × wj` (the chain's known constant width), never the
whole (chain-growing) welded grid and never even computing the welded `maxI`/
`maxJ` (which would itself fold the spine).  So a length-`N` chain's per-weld cost
is O(w·wj), genuinely independent of `N` ⇒ O(N) total interface work instead of
O(N²).  (It is *stronger* than `weldInterfaceOK` whenever `w ≥ maxI`, `wj ≥ maxJ`:
it demands the check at the layer-`kA` cube unconditionally, which for a real weld
`maxK = kA + B.maxK > kA` is always a genuine cube, so gadget certificates still
pass.) -/
def weldInterfaceOK2 (kA : Nat) (A B : LaSre) (SA SB : Surf)
    (conn : List (Nat × Nat)) (n w wj : Nat) : Bool :=
  (List.range n).all (fun s =>
    (List.range w).all (fun i =>
      (List.range wj).all (fun j =>
        (if 0 < kA then
            (weldK kA A B conn).funcCubeOK (stitchSurf kA SA SB) s i j (kA - 1)
          else true)
          && (weldK kA A B conn).funcCubeOK (stitchSurf kA SA SB) s i j kA)))

/-- The O(N) interface check implies the original whole-grid-filtered one (when
the supplied footprint `w × wj` covers the weld), so `weldK_funcOK` applies
unchanged. -/
theorem weldInterfaceOK_of_2 (n w wj : Nat)
    (hw : (weldK kA A B conn).maxI ≤ w) (hwj : (weldK kA A B conn).maxJ ≤ wj)
    (h : weldInterfaceOK2 kA A B SA SB conn n w wj = true) :
    weldInterfaceOK kA A B SA SB conn n = true := by
  rw [weldInterfaceOK2, List.all_eq_true] at h
  rw [weldInterfaceOK, List.all_eq_true]
  intro s hs
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨i, j, k⟩ := c
  by_cases hcond : k + 1 = kA ∨ k = kA
  · rw [if_pos hcond]
    rw [mem_gridCubes] at hc
    obtain ⟨hi, hj, hk⟩ := hc
    have h2 := h s hs
    rw [List.all_eq_true] at h2
    have h3 := h2 i (List.mem_range.2 (by omega))
    rw [List.all_eq_true] at h3
    have h4 := h3 j (List.mem_range.2 (by omega))
    rw [Bool.and_eq_true] at h4
    rcases hcond with hc1 | hc1
    · have hkeq : k = kA - 1 := by omega
      have hk0 : 0 < kA := by omega
      have hf := h4.1
      rw [if_pos hk0] at hf
      rw [hkeq]; exact hf
    · rw [hc1]; exact h4.2
  · rw [if_neg hcond]

/-- Extract one cube's check from `funcOK`. -/
theorem funcOK_apply {L : LaSre} {S : Surf} {n s i j k : Nat}
    (h : L.funcOK S n = true) (hs : s < n) (hc : (i, j, k) ∈ L.gridCubes) :
    L.funcCubeOK S s i j k = true := by
  rw [LaSre.funcOK, List.all_eq_true] at h
  have h2 := h s (List.mem_range.2 hs)
  rw [List.all_eq_true] at h2
  exact h2 (i, j, k) hc

/-- **★ THE GENERAL WELD-COMPOSITION THEOREM (interior functionality) ★** — if
`A` and `B` (same spatial footprint, `A` filling `[0,kA)`) each satisfy `funcOK`,
and the two interface layers pass, then the WELD satisfies `funcOK` — proven
WITHOUT deciding the whole welded grid.  The `A`-region cubes reduce to `A`'s
check (`funcCubeOK_lower`), the `B`-region to `B`'s (`funcCubeOK_upper`), and only
the interface is new. -/
theorem weldK_funcOK (n : Nat)
    (hI : A.maxI = B.maxI) (hJ : A.maxJ = B.maxJ) (hMaxK : A.maxK = kA)
    (hA : A.funcOK SA n = true) (hB : B.funcOK SB n = true)
    (hIf : weldInterfaceOK kA A B SA SB conn n = true) :
    (weldK kA A B conn).funcOK (stitchSurf kA SA SB) n = true := by
  rw [LaSre.funcOK, List.all_eq_true]
  intro s hs
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨i, j, k⟩ := c
  have hsn : s < n := List.mem_range.1 hs
  rw [mem_gridCubes] at hc
  obtain ⟨hi, hj, hk⟩ := hc
  simp only [weldK] at hi hj hk
  by_cases hlo : k + 1 < kA
  · rw [funcCubeOK_lower kA A B SA SB conn s i j k hlo]
    exact funcOK_apply hA hsn (mem_gridCubes.2 ⟨by omega, by omega, by omega⟩)
  · by_cases hmid : k + 1 = kA ∨ k = kA
    · rw [weldInterfaceOK, List.all_eq_true] at hIf
      have h2 := hIf s hs
      rw [List.all_eq_true] at h2
      have h3 := h2 (i, j, k) (mem_gridCubes.2 ⟨hi, hj, hk⟩)
      rwa [if_pos hmid] at h3
    · have hgt : kA < k := by omega
      rw [funcCubeOK_upper kA A B SA SB conn s i j k hgt]
      exact funcOK_apply hB hsn (mem_gridCubes.2 ⟨by omega, by omega, by omega⟩)

/-! ## §7. The SAME for structural validity (`validCube` is also local). -/

theorem validCube_lower (i j k : Nat) (h : k + 1 < kA) :
    (weldK kA A B conn).validCube i j k = A.validCube i j k := by
  have hk : k < kA := by omega
  have hkm : k - 1 < kA := by omega
  have hkk : k - 1 + 1 < kA := by omega
  simp only [LaSre.validCube, LaSre.hasI, LaSre.hasJ, LaSre.hasK,
    wk_YCube kA A B conn hk, wk_ExistI kA A B conn hk, wk_ExistJ kA A B conn hk,
    wk_ExistK kA A B conn h, wk_ExistK kA A B conn hkk,
    wk_ExistI kA A B conn hkm, wk_ExistJ kA A B conn hkm]

theorem validCube_upper (i j k : Nat) (h : kA < k) :
    (weldK kA A B conn).validCube i j k = B.validCube i j (k - kA) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = kA + 1 + m := ⟨k - kA - 1, by omega⟩
  have e1 : kA + 1 + m - kA = m + 1 := by omega
  have e2 : kA + 1 + m - 1 = kA + m := by omega
  have e3 : kA + m - kA = m := by omega
  have h1 : ¬ kA + 1 + m < kA := by omega
  have h3 : ¬ kA + m < kA := by omega
  have hK1 : ¬ kA + 1 + m + 1 < kA := by omega
  have hK2 : ¬ (kA + 1 + m + 1 == kA) = true := by intro hc; have := eq_of_beq hc; omega
  have hK3 : ¬ kA + m + 1 < kA := by omega
  have hK4 : ¬ (kA + m + 1 == kA) = true := by intro hc; have := eq_of_beq hc; omega
  have p1 : (0 < kA + 1 + m) = True := eq_true (by omega)
  have p2 : (0 < m + 1) = True := eq_true (by omega)
  simp only [LaSre.validCube, LaSre.hasI, LaSre.hasJ, LaSre.hasK, e2,
    wk_YCube_hi kA A B conn h1, wk_ExistI_hi kA A B conn h1,
    wk_ExistJ_hi kA A B conn h1, wk_ExistK_hi kA A B conn hK1 hK2,
    wk_ExistI_hi kA A B conn h3, wk_ExistJ_hi kA A B conn h3,
    wk_ExistK_hi kA A B conn hK3 hK4, e1, e3, p1, p2, Nat.add_sub_cancel]

theorem validCube_apply {L : LaSre} {i j k : Nat}
    (h : L.valid = true) (hc : (i, j, k) ∈ L.gridCubes) : L.validCube i j k = true := by
  rw [LaSre.valid, List.all_eq_true] at h
  exact h (i, j, k) hc

/-- Interface validity at the two welded layers. -/
def weldInterfaceValidOK (kA : Nat) (A B : LaSre) (conn : List (Nat × Nat)) : Bool :=
  (weldK kA A B conn).gridCubes.all (fun c =>
    if c.2.2 + 1 = kA ∨ c.2.2 = kA then
      (weldK kA A B conn).validCube c.1 c.2.1 c.2.2 else true)

/-- **★ THE O(N) VALIDITY INTERFACE CHECK ★** — `weldInterfaceValidOK` over only
the two interface layers `k ∈ {kA-1, kA}` and a GIVEN footprint `w × wj`, never
the whole welded grid nor the welded `maxI`/`maxJ` (O(w·wj) per weld ⇒ O(N)
total). -/
def weldInterfaceValidOK2 (kA : Nat) (A B : LaSre) (conn : List (Nat × Nat))
    (w wj : Nat) : Bool :=
  (List.range w).all (fun i =>
    (List.range wj).all (fun j =>
      (if 0 < kA then (weldK kA A B conn).validCube i j (kA - 1) else true)
        && (weldK kA A B conn).validCube i j kA))

/-- The O(N) validity check implies the original (when `w × wj` covers the weld),
so `weldK_valid` applies. -/
theorem weldInterfaceValidOK_of_2 (w wj : Nat)
    (hw : (weldK kA A B conn).maxI ≤ w) (hwj : (weldK kA A B conn).maxJ ≤ wj)
    (h : weldInterfaceValidOK2 kA A B conn w wj = true) :
    weldInterfaceValidOK kA A B conn = true := by
  rw [weldInterfaceValidOK2, List.all_eq_true] at h
  rw [weldInterfaceValidOK, List.all_eq_true]
  intro c hc
  obtain ⟨i, j, k⟩ := c
  by_cases hcond : k + 1 = kA ∨ k = kA
  · rw [if_pos hcond]
    rw [mem_gridCubes] at hc
    obtain ⟨hi, hj, hk⟩ := hc
    have h2 := h i (List.mem_range.2 (by omega))
    rw [List.all_eq_true] at h2
    have h3 := h2 j (List.mem_range.2 (by omega))
    rw [Bool.and_eq_true] at h3
    rcases hcond with hc1 | hc1
    · have hkeq : k = kA - 1 := by omega
      have hk0 : 0 < kA := by omega
      have hf := h3.1
      rw [if_pos hk0] at hf
      rw [hkeq]; exact hf
    · rw [hc1]; exact h3.2
  · rw [if_neg hcond]

theorem weldK_valid (hI : A.maxI = B.maxI) (hJ : A.maxJ = B.maxJ) (hMaxK : A.maxK = kA)
    (hA : A.valid = true) (hB : B.valid = true)
    (hIf : weldInterfaceValidOK kA A B conn = true) :
    (weldK kA A B conn).valid = true := by
  rw [LaSre.valid, List.all_eq_true]
  intro c hc
  obtain ⟨i, j, k⟩ := c
  rw [mem_gridCubes] at hc
  obtain ⟨hi, hj, hk⟩ := hc
  simp only [weldK] at hi hj hk
  by_cases hlo : k + 1 < kA
  · rw [validCube_lower kA A B conn i j k hlo]
    exact validCube_apply hA (mem_gridCubes.2 ⟨by omega, by omega, by omega⟩)
  · by_cases hmid : k + 1 = kA ∨ k = kA
    · rw [weldInterfaceValidOK, List.all_eq_true] at hIf
      have h3 := hIf (i, j, k) (mem_gridCubes.2 ⟨hi, hj, hk⟩)
      rwa [if_pos hmid] at h3
    · have hgt : kA < k := by omega
      rw [validCube_upper kA A B conn i j k hgt]
      exact validCube_apply hB (mem_gridCubes.2 ⟨by omega, by omega, by omega⟩)

/-! ## §8. THE FULL `LaSCorrectFull` COMPOSITION — the modular weld certificate. -/

/-- **★ THE MODULAR WELD CERTIFICATE ★** — a welded diagram is `LaSCorrectFull`
once each half is (`valid`+`funcOK`), the two interface layers pass, and the
composite ports match.  Every hypothesis is a SMALL check (per-gadget, or only
the two interface layers, or the few ports) — so a program chain is certified in
LINEAR work, never deciding the whole welded grid. -/
theorem weldK_LaSCorrectFull (n : Nat) (ports : List Port) (paulis : Nat → Nat → Pauli)
    (hI : A.maxI = B.maxI) (hJ : A.maxJ = B.maxJ) (hMaxK : A.maxK = kA)
    (hAv : A.valid = true) (hBv : B.valid = true)
    (hAf : A.funcOK SA n = true) (hBf : B.funcOK SB n = true)
    (hIfv : weldInterfaceValidOK kA A B conn = true)
    (hIff : weldInterfaceOK kA A B SA SB conn n = true)
    (hPorts : portsOK (stitchSurf kA SA SB) ports paulis n = true) :
    LaSCorrectFull (weldK kA A B conn) (stitchSurf kA SA SB) ports paulis n = true := by
  simp only [LaSre.LaSCorrectFull,
    weldK_valid kA A B conn hI hJ hMaxK hAv hBv hIfv,
    weldK_funcOK kA A B SA SB conn n hI hJ hMaxK hAf hBf hIff, hPorts,
    Bool.and_self, Bool.and_true]

/-! ## §9. DEMONSTRATION — a real weld certified MODULARLY (no whole-grid decide).

  `memWeld = weldK 3 memoryLaS memoryLaS [(0,0)]` was proven correct by a
  `native_decide` on the WHOLE 6-step diagram (`memWeld_fully_correct`).  Here the
  SAME result is obtained from `weldK_LaSCorrectFull`: every hypothesis is a check
  on a SINGLE memory cell, the two interface layers, or the ports — none touches
  the whole weld.  For a 2-gadget weld the saving is nil; for a length-`n` program
  chain it is exponential → linear (each gadget + interface certified once). -/

theorem memWeldSurf_is_stitch : memWeldSurf = stitchSurf 3 idSurf idSurf := rfl

theorem memWeld_via_modular_composition :
    LaSCorrectFull memWeld (stitchSurf 3 idSurf idSurf) memWeldPorts idPaulis 2 = true :=
  weldK_LaSCorrectFull 3 memoryLaS memoryLaS idSurf idSurf [(0, 0)] 2 memWeldPorts idPaulis
    rfl rfl rfl memoryLaS_valid memoryLaS_valid
    (by native_decide) (by native_decide)   -- per-gadget funcOK (one memory)
    (by native_decide) (by native_decide)   -- the two interface layers
    (by native_decide)                       -- the ports

end FormalRV.QEC.LaSre
