/-
  FormalRV.QEC.LatticeSurgery.WidthScaling
  ----------------------------------------
  **★ STEP 1 — WIDTH-SYMBOLIC correctness of the catalog Z-merge. ★**

  The scalability program (Gidney's "cost a tile, multiply" made rigorous) needs
  the per-gadget correctness to hold for ANY width WITHOUT `native_decide` over
  the width.  `funcCubeOK`/`validCube` are LOCAL (each reads only a cube and its
  lower neighbours), so the whole-grid check factors into a PER-COLUMN universal:
  prove the cube predicate for an arbitrary column index `i`, and the
  `List.all` over `range maxI` follows for every width by `List.all_eq_true`.

  This file proves the long-range multi-data `Z̄`-merge (`lrMergeMulti cols`,
  the catalog pure-`Z` gadget) is `valid` for ANY column set, by the structural
  observation that it has NO `J`-pipes (so no 3D corner can ever form).  This is
  the validity half of `LaSCorrectFull`, established symbolically in the width.
-/
import FormalRV.QEC.LatticeSurgery.Routing

namespace FormalRV.QEC.LaSre

/-! ## §1. WIDTH-SYMBOLIC VALIDITY — no `J`-pipes ⇒ no 3D corner, at every cube. -/

/-- **Per-cube** validity of a multi-data `Z̄`-merge, for an ARBITRARY column
`i` and ANY column set `cols` — the local check, with no quantifier over width.
Because `ExistJ ≡ false`, `hasJ ≡ false`, so the no-3D-corner rule
`!(hasI ∧ hasJ ∧ hasK)` holds and the `Y`-rule is vacuous. -/
theorem lrMergeMulti_validCube (cols : List Nat) (i j k : Nat) :
    (lrMergeMulti cols).validCube i j k = true := by
  simp [LaSre.validCube, LaSre.hasJ, lrMergeMulti]

/-- **★ WIDTH-SYMBOLIC VALIDITY ★** — the long-range `Z̄`-merge over ANY data
columns is structurally valid.  The `List.all` over `range maxI` is discharged
by the per-column universal `lrMergeMulti_validCube`, NOT by `native_decide`
over the (arbitrary) width. -/
theorem lrMergeMulti_valid (cols : List Nat) : (lrMergeMulti cols).valid = true := by
  rw [LaSre.valid, List.all_eq_true]
  intro c _
  exact lrMergeMulti_validCube cols c.1 c.2.1 c.2.2

/-! ## §2. A CONTIGUOUS width-`w` `Z̄`-merge — arithmetic fields, no list ops.

  `zMerge w` joins the `w` adjacent data columns `0..w-1` with a single `Z`-seam
  (the `I`-pipe spans `0..w-2` at time `k=1`; every column carries a data
  worldline).  Flow `0` is the joint `Z̄`; flow `s∈[1,w]` is `X̄` on column
  `s-1` (the passthrough).  Identical SHAPE to the catalog `lrMergeMulti`, but
  with arithmetic-only fields so the width-symbolic proof needs no list lemmas. -/

def zMerge (w : Nat) : LaSre :=
  { maxI := w, maxJ := 1, maxK := 3
    YCube  := fun _ _ _ => false
    ExistI := fun i j k => decide (i + 1 < w) && j == 0 && k == 1   -- Z-seam 0..w-2
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => decide (i < w) && j == 0 && decide (k < 2) -- all w worldlines
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

def zMergeSurf (w : Nat) : Surf :=
  { IJ := fun _ _ _ _ => false
    IK := fun s i j k => s == 0 && decide (i + 1 < w) && j == 0 && k == 1
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => s == 0 && j == 0 && decide (i < w)          -- joint Z on all data
    KJ := fun s i j _ => decide (1 ≤ s) && decide (s - 1 = i) && decide (s ≤ w) && j == 0 }

theorem zMerge_validCube (w i j k : Nat) : (zMerge w).validCube i j k = true := by
  simp [LaSre.validCube, LaSre.hasJ, zMerge]

theorem zMerge_valid (w : Nat) : (zMerge w).valid = true := by
  rw [LaSre.valid, List.all_eq_true]
  intro c _
  exact zMerge_validCube w c.1 c.2.1 c.2.2

/-! ### The interior time-layer `k=1`: all parities cancel, all all-or-none hold.

  At `k=1` the two `K`-pipe contributions to each parity are equal (the surface
  is `k`-independent), so every parity `XOR`s to `false`; and every all-or-none
  list has equal present values.  These hold for ALL columns `i` and flows `s`
  — the per-column universals that the whole-grid `funcOK` factors into. -/

/-- **All-or-none from a common present value.**  If every entry of an `allEq`
list, WHEN present, carries the same value `b`, then `allEq` holds — the head is
`b` and all present values equal it.  This is the structural reason the merge's
surfaces pass all-or-none at the interior layer (all present pieces share the
flow's value `s==0`, resp. the joint-`Z` value). -/
theorem allEq_const_present {b : Bool} {xs : List (Bool × Bool)}
    (h : ∀ p ∈ xs, p.1 = true → p.2 = b) : allEq xs = true := by
  unfold allEq
  generalize hL : (xs.filter (·.1)).map (·.2) = L
  have key : ∀ x ∈ L, x = b := by
    intro x hx
    rw [← hL, List.mem_map] at hx
    obtain ⟨p, hpf, rfl⟩ := hx
    rw [List.mem_filter] at hpf
    exact h p hpf.1 (by simpa using hpf.2)
  cases L with
  | nil => rfl
  | cons y ys =>
    rw [List.all_eq_true]
    intro x hx
    have hxb : x = b := key x hx
    have hyb : y = b := key y (by simp)
    simp [List.headD, hxb, hyb]

theorem zMerge_jParity_k1 (w s i : Nat) :
    jParity (zMerge w) (zMergeSurf w) s i 0 1 = false := by
  simp [jParity, zMerge, zMergeSurf]

theorem zMerge_iParity_k1 (w s i : Nat) :
    iParity (zMerge w) (zMergeSurf w) s i 0 1 = false := by
  simp [iParity, zMerge, zMergeSurf]

theorem zMerge_allOrNoneI_k1 (w s i : Nat) :
    allOrNoneI (zMerge w) (zMergeSurf w) s i 0 1 = true := by
  rw [allOrNoneI]
  apply allEq_const_present (b := (zMergeSurf w).KJ s i 0 1)
  intro p hp hpres
  fin_cases hp <;> simp_all [zMerge, zMergeSurf]

theorem zMerge_allOrNoneJ_k1 (w s i : Nat) :
    allOrNoneJ (zMerge w) (zMergeSurf w) s i 0 1 = true := by
  rw [allOrNoneJ]
  apply allEq_const_present (b := s == 0)
  intro p hp hpres
  fin_cases hp <;> simp_all [zMerge, zMergeSurf]

/-! ### `funcCubeOK` at every cube — the per-column universal (factored in width). -/

/-- Interior layer `k=1`: `funcCubeOK` holds at EVERY column `i` and flow `s`.
For a data column `i<w` the worldline supplies `hasK`, so the only nontrivial
(missing-`J`) obligation is the parity/all-or-none cancellation proved above; for
`i≥w` the cube is empty (degree-0 port). -/
theorem zMerge_funcCubeOK_k1 (w s i : Nat) :
    funcCubeOK (zMerge w) (zMergeSurf w) s i 0 1 = true := by
  unfold funcCubeOK
  rw [zMerge_iParity_k1, zMerge_jParity_k1, zMerge_allOrNoneI_k1, zMerge_allOrNoneJ_k1]
  by_cases hiw : i < w
  · have hK : (zMerge w).hasK i 0 1 = true := by simp [LaSre.hasK, zMerge, hiw]
    rw [hK]
    simp [zMerge]
  · have hd : (zMerge w).degree i 0 1 ≤ 1 := by
      simp only [LaSre.degree, zMerge]
      have h1 : ¬ i + 1 < w := by omega
      have h3 : ¬ (i - 1) + 1 < w := by omega
      simp [hiw, h1, h3]
    rw [if_neg (show ¬((zMerge w).YCube i 0 1 = true) by simp [zMerge]), if_pos hd]

/-- Boundary layers `k∈{0,2}`: only a worldline `K`-pipe can touch the cube, so
its degree is `≤1` — a port, trivially `funcCubeOK`. -/
theorem zMerge_funcCubeOK_k0 (w s i : Nat) :
    funcCubeOK (zMerge w) (zMergeSurf w) s i 0 0 = true := by
  unfold funcCubeOK
  have hd : (zMerge w).degree i 0 0 ≤ 1 := by
    by_cases h : i < w <;> simp [LaSre.degree, zMerge, h]
  rw [if_neg (show ¬((zMerge w).YCube i 0 0 = true) by simp [zMerge]), if_pos hd]

theorem zMerge_funcCubeOK_k2 (w s i : Nat) :
    funcCubeOK (zMerge w) (zMergeSurf w) s i 0 2 = true := by
  unfold funcCubeOK
  have hd : (zMerge w).degree i 0 2 ≤ 1 := by
    by_cases h : i < w <;> simp [LaSre.degree, zMerge, h]
  rw [if_neg (show ¬((zMerge w).YCube i 0 2 = true) by simp [zMerge]), if_pos hd]

/-! ### §3. WIDTH-SYMBOLIC `funcOK` — the whole-grid check, factored per column. -/

/-- **★ WIDTH-SYMBOLIC INTERIOR FUNCTIONALITY ★** — the contiguous `Z̄`-merge's
correlation surfaces satisfy the interior functionality check for ANY width `w`
and ANY number of flows `n`.  The `List.all` over `gridCubes` (size `3w`) is
discharged by the three per-column cube lemmas (`k∈{0,1,2}`), NOT by
`native_decide` over the width. -/
theorem zMerge_funcOK (w n : Nat) :
    funcOK (zMerge w) (zMergeSurf w) n = true := by
  rw [LaSre.funcOK, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  rintro ⟨i, j, k⟩ hc
  rw [mem_gridCubes] at hc
  obtain ⟨_, hj, hk⟩ := hc
  have hj0 : j = 0 := by simp only [zMerge] at hj; omega
  subst hj0
  simp only [zMerge] at hk
  interval_cases k
  · exact zMerge_funcCubeOK_k0 w s i
  · exact zMerge_funcCubeOK_k1 w s i
  · exact zMerge_funcCubeOK_k2 w s i

/-- **★ WIDTH-SYMBOLIC INTERIOR CORRECTNESS ★** — `valid` ∧ `funcOK`, for ANY
width and any number of flows, with NO `native_decide` over the width. -/
theorem zMerge_LaSCorrect (w n : Nat) :
    LaSCorrect (zMerge w) (zMergeSurf w) n = true := by
  rw [LaSre.LaSCorrect, zMerge_valid, zMerge_funcOK]; rfl

/-! ### §4. WIDTH-SYMBOLIC PORTS — the boundary matches the joint-`Z̄` / `X̄` spec.

  Ports: each data column `c` has an IN port (`k=0`) and an OUT port (`k=2`),
  blue selector `4` (`KI`, the `Z` piece) and red selector `5` (`KJ`, the `X`
  piece).  Spec flow `0` is the joint `Z̄`; flow `s∈[1,w]` is `X̄` on column
  `s-1`.  The list is `ins ++ outs`, so a port at `zipIdx` index `p` sits on
  column `p % w` — matching the surface, which is the boundary condition. -/

def zMergePorts (w : Nat) : List Port :=
  (List.range w).map (fun c => ⟨c, 0, 0, 4, 5⟩) ++ (List.range w).map (fun c => ⟨c, 0, 2, 4, 5⟩)

def zMergePaulis (w : Nat) : Nat → Nat → Pauli := fun s p =>
  if s = 0 then Pauli.Z else if s - 1 = p % w then Pauli.X else Pauli.I

/-- Every port sits on column `idx % w` (`< w`), at `pj=0`, with the canonical
blue/red selectors — the structural invariant of the `ins ++ outs` port list. -/
theorem zMergePorts_get {w : Nat} {p : Port} {idx : Nat}
    (h : (p, idx) ∈ (zMergePorts w).zipIdx) :
    p.pj = 0 ∧ p.blueSel = 4 ∧ p.redSel = 5 ∧ p.pi = idx % w ∧ p.pi < w := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  simp only [zMergePorts, List.getElem?_append, List.getElem?_map,
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
matches the spec Pauli (blue `KI` = joint `Z̄`, red `KJ` = the per-column `X̄`),
for ANY width.  The `(s≤w)` factor in `KJ` is automatic because a port's column
`idx % w < w`, so a flow `s` with `s-1` on that column has `s ≤ w`. -/
theorem zMerge_portsOK (w : Nat) :
    portsOK (zMergeSurf w) (zMergePorts w) (zMergePaulis w) (w + 1) = true := by
  rw [portsOK, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro pp hpp
  obtain ⟨p, idx⟩ := pp
  obtain ⟨hpj, hbl, hrd, hpi, hlt⟩ := zMergePorts_get hpp
  have hw : 0 < w := by omega
  have hmw : idx % w < w := Nat.mod_lt _ hw
  simp only [Surf.sel, hbl, hrd, hpj, hpi, zMergeSurf, zMergePaulis, portBlue, portRed]
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp [hmw]
  · have hs0 : ¬ s = 0 := by omega
    by_cases hc : s - 1 = idx % w
    · have hsw : s ≤ w := by omega
      simp [hs0, hc, hmw, hsw]
      omega
    · simp [hs0, hc, hmw]

/-! ### §5. ★ THE HEADLINE — a `Z̄`-merge of ANY WIDTH passes `LaSCorrectFull`. -/

/-- **★ WIDTH-SYMBOLIC `LaSCorrectFull` ★** — for EVERY width `w`, the contiguous
long-range `Z̄`-merge is a fully correct lattice-surgery subroutine against its
joint-`Z̄`/per-column-`X̄` measurement spec: structurally valid, interior
functionality satisfied, and ports matching the spec.  Proven by per-column
universals (locality of `funcCubeOK`/`validCube`) — **NOT** by `native_decide`
over the width.  This is Step 1 of the scalable-Shor program: one concrete
lattice-surgery construction, verified symbolically in its width. -/
theorem zMerge_LaSCorrectFull (w : Nat) :
    LaSCorrectFull (zMerge w) (zMergeSurf w) (zMergePorts w) (zMergePaulis w) (w + 1) = true := by
  rw [LaSre.LaSCorrectFull, zMerge_valid, zMerge_funcOK, zMerge_portsOK]; rfl

end FormalRV.QEC.LaSre
