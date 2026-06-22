/-
  FormalRV.QEC.LatticeSurgery.WidthScalingStep2
  ---------------------------------------------
  **★ STEP 2 — DEPTH-GENERIC (LENGTH-GENERIC) correctness of a Z-merge stack. ★**

  Step 1 (`WidthScaling`) proved one `zMerge w` is `LaSCorrectFull` for ANY width,
  with no `native_decide` over the width.  Step 2 proves the DEPTH (time) mirror:
  a stack of `N+1` identical `zMerge W`s, welded in time by `weldChain`, passes the
  full `LaSCorrectFull` for ALL `N`, BY INDUCTION ON `N`, with NO `native_decide`
  over the chain length `N`.

  The KEY (Scout 3): `funcCubeOK` / `validCube` are LOCAL — at the two interface
  layers `k ∈ {h-1, h}` they read the upper gadget `B` ONLY at layer 0.  Because
  the chain `weldChain h conn (g :: rest)` agrees with `g` below the interface and
  with the chain's bottom (always `g`'s layer 0) at layer `h`, the interface
  obligation between `g` and the chain is INDEPENDENT of `N`.  So ONE interface
  certificate — proven once at the fixed width `W=2` — discharges every induction
  step.  No per-`N` decision is ever run.
-/
import FormalRV.QEC.LatticeSurgery.WidthScaling
import FormalRV.QEC.LatticeSurgery.ChainComposition

namespace FormalRV.QEC.LaSre

/-! ## §0. Fixed concrete width `W = 2`. -/

/-- The connection list welding both data columns `0,1` across each time seam. -/
def zConn2 : List (Nat × Nat) := [(0, 0), (1, 0)]

/-! ## §1. The depth-`N` chain and its surface (replicate of one gadget). -/

/-- The depth-`(N+1)` stack of identical gadgets `g`, welded in time by `weldK`. -/
abbrev zChain (h : Nat) (conn : List (Nat × Nat)) (g : LaSre) (N : Nat) : LaSre :=
  weldChain h conn (List.replicate (N + 1) g)

abbrev zChainSurf (h : Nat) (s : Surf) (N : Nat) : Surf :=
  weldChainSurf h (List.replicate (N + 1) s)

/-- Base: a single-element chain is the gadget itself. -/
theorem zChain_zero (h : Nat) (conn : List (Nat × Nat)) (g : LaSre) :
    zChain h conn g 0 = g := rfl

/-- Step: the depth-`(N+2)` chain is `g` welded onto the depth-`(N+1)` chain. -/
theorem zChain_succ (h : Nat) (conn : List (Nat × Nat)) (g : LaSre) (N : Nat) :
    zChain h conn g (N + 1) = weldK h g (zChain h conn g N) conn := by
  show weldChain h conn (g :: List.replicate (N + 1) g) = _
  rw [List.replicate_succ]
  rfl

theorem zChainSurf_zero (h : Nat) (s : Surf) : zChainSurf h s 0 = s := rfl

theorem zChainSurf_succ (h : Nat) (s : Surf) (N : Nat) :
    zChainSurf h s (N + 1) = weldSurf h s (zChainSurf h s N) (fun x => (x, x)) := by
  show weldChainSurf h (s :: List.replicate (N + 1) s) = _
  rw [List.replicate_succ]
  rfl

/-! ## §2. LAYER-0 FIELD CONGRUENCE — the chain's BOTTOM is always `g` (resp. `s`).

  These are the heart of `N`-independence: `funcCubeOK`/`validCube` at the two
  interface layers read the upper gadget `B` ONLY at layer 0, so the interface
  obligation only sees the chain's bottom — which is ALWAYS `g`'s/`s`'s layer 0,
  for EVERY `N`.  Provided `2 ≤ h` (so layer 0 is strictly below the seam). -/

variable {h : Nat} {conn : List (Nat × Nat)} {g : LaSre} {s : Surf}

theorem zChain_YCube0 (hh : 2 ≤ h) (N : Nat) (i j : Nat) :
    (zChain h conn g N).YCube i j 0 = g.YCube i j 0 := by
  cases N with
  | zero => rfl
  | succ M => rw [zChain_succ]; simp only [weldK]; rw [if_pos (by omega)]

theorem zChain_ExistI0 (hh : 2 ≤ h) (N : Nat) (i j : Nat) :
    (zChain h conn g N).ExistI i j 0 = g.ExistI i j 0 := by
  cases N with
  | zero => rfl
  | succ M => rw [zChain_succ]; simp only [weldK]; rw [if_pos (by omega)]

theorem zChain_ExistJ0 (hh : 2 ≤ h) (N : Nat) (i j : Nat) :
    (zChain h conn g N).ExistJ i j 0 = g.ExistJ i j 0 := by
  cases N with
  | zero => rfl
  | succ M => rw [zChain_succ]; simp only [weldK]; rw [if_pos (by omega)]

theorem zChain_ExistK0 (hh : 2 ≤ h) (N : Nat) (i j : Nat) :
    (zChain h conn g N).ExistK i j 0 = g.ExistK i j 0 := by
  cases N with
  | zero => rfl
  | succ M =>
    rw [zChain_succ]; simp only [weldK]
    rw [if_pos (show (0 : Nat) + 1 < h by omega)]

theorem zChainSurf_KI0 (hh : 2 ≤ h) (N : Nat) (t i j : Nat) :
    (zChainSurf h s N).KI t i j 0 = s.KI t i j 0 := by
  cases N with
  | zero => rfl
  | succ M => rw [zChainSurf_succ]; simp only [weldSurf]; rw [if_pos (by omega)]

theorem zChainSurf_KJ0 (hh : 2 ≤ h) (N : Nat) (t i j : Nat) :
    (zChainSurf h s N).KJ t i j 0 = s.KJ t i j 0 := by
  cases N with
  | zero => rfl
  | succ M => rw [zChainSurf_succ]; simp only [weldSurf]; rw [if_pos (by omega)]

theorem zChainSurf_IJ0 (hh : 2 ≤ h) (N : Nat) (t i j : Nat) :
    (zChainSurf h s N).IJ t i j 0 = s.IJ t i j 0 := by
  cases N with
  | zero => rfl
  | succ M => rw [zChainSurf_succ]; simp only [weldSurf]; rw [if_pos (by omega)]

theorem zChainSurf_IK0 (hh : 2 ≤ h) (N : Nat) (t i j : Nat) :
    (zChainSurf h s N).IK t i j 0 = s.IK t i j 0 := by
  cases N with
  | zero => rfl
  | succ M => rw [zChainSurf_succ]; simp only [weldSurf]; rw [if_pos (by omega)]

theorem zChainSurf_JK0 (hh : 2 ≤ h) (N : Nat) (t i j : Nat) :
    (zChainSurf h s N).JK t i j 0 = s.JK t i j 0 := by
  cases N with
  | zero => rfl
  | succ M => rw [zChainSurf_succ]; simp only [weldSurf]; rw [if_pos (by omega)]

theorem zChainSurf_JI0 (hh : 2 ≤ h) (N : Nat) (t i j : Nat) :
    (zChainSurf h s N).JI t i j 0 = s.JI t i j 0 := by
  cases N with
  | zero => rfl
  | succ M => rw [zChainSurf_succ]; simp only [weldSurf]; rw [if_pos (by omega)]

/-! ## §3. CHAIN FOOTPRINT — `maxI`/`maxJ` are `N`-independent (`= g`'s). -/

theorem zChain_maxI (N : Nat) : (zChain h conn g N).maxI = g.maxI := by
  induction N with
  | zero => rfl
  | succ M ih => rw [zChain_succ]; simp only [weldK]; rw [ih, Nat.max_self]

theorem zChain_maxJ (N : Nat) : (zChain h conn g N).maxJ = g.maxJ := by
  induction N with
  | zero => rfl
  | succ M ih => rw [zChain_succ]; simp only [weldK]; rw [ih, Nat.max_self]

theorem zChain_maxK (N : Nat) (hg : g.maxK = h) :
    (zChain h conn g N).maxK = (N + 1) * h := by
  induction N with
  | zero => simpa using hg
  | succ M ih => rw [zChain_succ]; simp only [weldK]; rw [ih]; ring

/-! ## §4. INTERFACE-LAYER FIELD EQUALITY — the welded chain-seam equals the
    welded single-gadget seam on EVERY field, at every layer `k ≤ h`.

  `funcCubeOK`/`validCube` at the seam layers `k ∈ {h-1, h}` read the welded
  diagram only at layers `≤ h`.  At those layers `weldK h g (zChain N) conn`
  agrees field-by-field with the reference `weldK h g g conn`: below `h` both
  read `g`; at `k = h` both read the upper gadget's layer 0, and the chain's
  layer 0 IS `g`'s (§2).  So the two welds are interchangeable for the interface
  obligation — the source of `N`-independence. -/

/-- The reference seam: `g` welded onto a single copy of `g` (i.e. `N = 1`). -/
abbrev refWeld (h : Nat) (conn : List (Nat × Nat)) (g : LaSre) : LaSre :=
  weldK h g g conn

abbrev refWeldSurf (h : Nat) (s : Surf) : Surf :=
  stitchSurf h s s

theorem seam_YCube_eq (hh : 2 ≤ h) (N : Nat) (i j k : Nat) (hk : k ≤ h) :
    (weldK h g (zChain h conn g N) conn).YCube i j k = (refWeld h conn g).YCube i j k := by
  simp only [weldK, refWeld]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, zChain_YCube0 hh]

theorem seam_ExistI_eq (hh : 2 ≤ h) (N : Nat) (i j k : Nat) (hk : k ≤ h) :
    (weldK h g (zChain h conn g N) conn).ExistI i j k = (refWeld h conn g).ExistI i j k := by
  simp only [weldK, refWeld]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, zChain_ExistI0 hh]

theorem seam_ExistJ_eq (hh : 2 ≤ h) (N : Nat) (i j k : Nat) (hk : k ≤ h) :
    (weldK h g (zChain h conn g N) conn).ExistJ i j k = (refWeld h conn g).ExistJ i j k := by
  simp only [weldK, refWeld]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, zChain_ExistJ0 hh]

theorem seam_ExistK_eq (hh : 2 ≤ h) (N : Nat) (i j k : Nat) (hk : k ≤ h) :
    (weldK h g (zChain h conn g N) conn).ExistK i j k = (refWeld h conn g).ExistK i j k := by
  simp only [weldK, refWeld]
  by_cases hk1 : k + 1 < h
  · rw [if_pos hk1, if_pos hk1]
  · by_cases hk2 : (k + 1 == h) = true
    · rw [if_neg hk1, if_pos hk2, if_neg hk1, if_pos hk2]
    · -- k + 1 > h, but k ≤ h forces k = h, so k - h = 0
      have hkh : k = h := by
        rcases Nat.lt_or_ge (k + 1) h with hlt | hge
        · exact absurd hlt hk1
        · have : ¬ (k + 1 = h) := by intro hc; exact hk2 (by simp [hc])
          omega
      subst hkh
      rw [if_neg hk1, if_neg hk2, if_neg hk1, if_neg hk2, Nat.sub_self, zChain_ExistK0 hh]

theorem seam_KI_eq (hh : 2 ≤ h) (N : Nat) (t i j k : Nat) (hk : k ≤ h) :
    (stitchSurf h s (zChainSurf h s N)).KI t i j k = (refWeldSurf h s).KI t i j k := by
  simp only [stitchSurf, refWeldSurf]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, zChainSurf_KI0 hh]

theorem seam_KJ_eq (hh : 2 ≤ h) (N : Nat) (t i j k : Nat) (hk : k ≤ h) :
    (stitchSurf h s (zChainSurf h s N)).KJ t i j k = (refWeldSurf h s).KJ t i j k := by
  simp only [stitchSurf, refWeldSurf]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, zChainSurf_KJ0 hh]

theorem seam_IJ_eq (hh : 2 ≤ h) (N : Nat) (t i j k : Nat) (hk : k ≤ h) :
    (stitchSurf h s (zChainSurf h s N)).IJ t i j k = (refWeldSurf h s).IJ t i j k := by
  simp only [stitchSurf, refWeldSurf]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, zChainSurf_IJ0 hh]

theorem seam_IK_eq (hh : 2 ≤ h) (N : Nat) (t i j k : Nat) (hk : k ≤ h) :
    (stitchSurf h s (zChainSurf h s N)).IK t i j k = (refWeldSurf h s).IK t i j k := by
  simp only [stitchSurf, refWeldSurf]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, zChainSurf_IK0 hh]

theorem seam_JK_eq (hh : 2 ≤ h) (N : Nat) (t i j k : Nat) (hk : k ≤ h) :
    (stitchSurf h s (zChainSurf h s N)).JK t i j k = (refWeldSurf h s).JK t i j k := by
  simp only [stitchSurf, refWeldSurf]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, zChainSurf_JK0 hh]

theorem seam_JI_eq (hh : 2 ≤ h) (N : Nat) (t i j k : Nat) (hk : k ≤ h) :
    (stitchSurf h s (zChainSurf h s N)).JI t i j k = (refWeldSurf h s).JI t i j k := by
  simp only [stitchSurf, refWeldSurf]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, zChainSurf_JI0 hh]

/-! ## §5. `funcCubeOK` / `validCube` AGREE at the interface layers.

  `funcCubeOK L S t i j k` reads `L`,`S` only at the cube `(i,j,k)` and its lower
  neighbours `(i-1,j,k)`, `(i,j-1,k)`, `(i,j,k-1)` — all at `k`-coordinate `k` or
  `k-1`.  At the two seam layers `k ∈ {h-1, h}` every such read is at a layer
  `≤ h`, where the chain-seam and the reference-seam fields coincide (§4).  So the
  obligation value is the SAME for the chain (any `N`) as for the reference. -/

theorem funcCubeOK_seam_eq (hh : 2 ≤ h) (N : Nat) (t i j k : Nat) (hk : k ≤ h) :
    (weldK h g (zChain h conn g N) conn).funcCubeOK
        (stitchSurf h s (zChainSurf h s N)) t i j k
      = (refWeld h conn g).funcCubeOK (refWeldSurf h s) t i j k := by
  have hkm : k - 1 ≤ h := by omega
  simp only [LaSre.funcCubeOK, LaSre.degree, LaSre.hasI, LaSre.hasJ, LaSre.hasK,
    LaSre.iParity, LaSre.jParity, LaSre.kParity,
    LaSre.allOrNoneI, LaSre.allOrNoneJ, LaSre.allOrNoneK,
    seam_YCube_eq hh N i j k hk,
    seam_ExistI_eq hh N i j k hk, seam_ExistI_eq hh N (i - 1) j k hk,
    seam_ExistJ_eq hh N i j k hk, seam_ExistJ_eq hh N i (j - 1) k hk,
    seam_ExistK_eq hh N i j k hk, seam_ExistK_eq hh N i j (k - 1) hkm,
    seam_KI_eq hh N t i j k hk, seam_KI_eq hh N t i j (k - 1) hkm,
    seam_KJ_eq hh N t i j k hk, seam_KJ_eq hh N t i j (k - 1) hkm,
    seam_IJ_eq hh N t i j k hk, seam_IJ_eq hh N t (i - 1) j k hk,
    seam_IK_eq hh N t i j k hk, seam_IK_eq hh N t (i - 1) j k hk,
    seam_JK_eq hh N t i j k hk, seam_JK_eq hh N t i (j - 1) k hk,
    seam_JI_eq hh N t i j k hk, seam_JI_eq hh N t i (j - 1) k hk]

theorem validCube_seam_eq (hh : 2 ≤ h) (N : Nat) (i j k : Nat) (hk : k ≤ h) :
    (weldK h g (zChain h conn g N) conn).validCube i j k
      = (refWeld h conn g).validCube i j k := by
  have hkm : k - 1 ≤ h := by omega
  simp only [LaSre.validCube, LaSre.hasI, LaSre.hasJ, LaSre.hasK,
    seam_YCube_eq hh N i j k hk,
    seam_ExistI_eq hh N i j k hk, seam_ExistI_eq hh N (i - 1) j k hk,
    seam_ExistJ_eq hh N i j k hk, seam_ExistJ_eq hh N i (j - 1) k hk,
    seam_ExistK_eq hh N i j k hk, seam_ExistK_eq hh N i j (k - 1) hkm]

/-! ## §6. THE INTERFACE CHECKS ARE `N`-INDEPENDENT.

  The O(N) interface checks `weldInterfaceOK2` / `weldInterfaceValidOK2` evaluate
  `funcCubeOK` / `validCube` of the weld ONLY at the two seam layers `k ∈ {h-1,h}`
  and over the fixed footprint `w × wj`.  Both layers are `≤ h`, so by §5 every
  evaluated value equals the reference seam's — hence the WHOLE check value equals
  the reference's, for EVERY `N`.  This is the single fact that lets ONE interface
  certificate (proven once at the reference) discharge every induction step. -/

theorem weldInterfaceOK2_N_eq (hh : 2 ≤ h) (N : Nat) (n w wj : Nat) :
    weldInterfaceOK2 h g (zChain h conn g N) s (zChainSurf h s N) conn n w wj
      = weldInterfaceOK2 h g g s s conn n w wj := by
  have hh0 : 0 < h := by omega
  simp only [weldInterfaceOK2]
  congr 1
  funext t
  congr 1
  funext i
  congr 1
  funext j
  rw [if_pos hh0, if_pos hh0]
  have e1 := funcCubeOK_seam_eq (g := g) (s := s) (conn := conn) hh N t i j (h - 1) (by omega)
  have e2 := funcCubeOK_seam_eq (g := g) (s := s) (conn := conn) hh N t i j h (le_refl h)
  simp only [refWeld, refWeldSurf] at e1 e2
  rw [e1, e2]

theorem weldInterfaceValidOK2_N_eq (hh : 2 ≤ h) (N : Nat) (w wj : Nat) :
    weldInterfaceValidOK2 h g (zChain h conn g N) conn w wj
      = weldInterfaceValidOK2 h g g conn w wj := by
  have hh0 : 0 < h := by omega
  simp only [weldInterfaceValidOK2]
  congr 1
  funext i
  congr 1
  funext j
  rw [if_pos hh0, if_pos hh0]
  have e1 := validCube_seam_eq (g := g) (conn := conn) hh N i j (h - 1) (by omega)
  have e2 := validCube_seam_eq (g := g) (conn := conn) hh N i j h (le_refl h)
  simp only [refWeld] at e1 e2
  rw [e1, e2]

/-! ## §7. ★ THE DEPTH INDUCTION — `chainOK` of the `N`-fold replicate, for ALL `N`.

  The induction step reuses, at EVERY `N`:
    * the per-gadget facts `g.valid` / `g.funcOK` — proven ONCE (Step 1);
    * the TWO interface certificates at the REFERENCE seam `weldK h g g conn` —
      proven ONCE (a single `native_decide` at the fixed width), transported to
      the chain seam by the `N`-independence lemmas of §6.
  No check whose size grows with `N` is ever run. -/

/-- **★ GENERIC DEPTH INDUCTION ★** — given a gadget `g`/surface `s` that is
self-consistent (`valid`+`funcOK`+footprint) and whose REFERENCE self-weld passes
the two interface checks, the depth-`(N+1)` replicate chain passes `chainOK` for
ALL `N`, by induction — the interface obligations are `N`-independent (§6) so the
two reference certificates discharge every step. -/
theorem zChain_chainOK_generic (hh : 2 ≤ h) (n w wj : Nat)
    (hg_i : g.maxI = w) (hg_j : g.maxJ = wj) (hg_k : g.maxK = h)
    (hg_v : g.valid = true) (hg_f : g.funcOK s n = true)
    (href_v : weldInterfaceValidOK2 h g g conn w wj = true)
    (href_f : weldInterfaceOK2 h g g s s conn n w wj = true)
    (N : Nat) :
    chainOK h n conn w wj (List.replicate (N + 1) g) (List.replicate (N + 1) s) = true := by
  induction N with
  | zero =>
    -- `replicate 1 g = [g]`, base case of `chainOK`
    rw [List.replicate_succ, List.replicate_zero, List.replicate_succ, List.replicate_zero]
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨⟨hg_i, hg_j⟩, hg_k⟩, hg_v⟩, hg_f⟩
  | succ M ih =>
    -- `replicate (M+2) g = g :: g :: replicate M g` — the step case of `chainOK`
    rw [show M + 1 + 1 = (M + 1) + 1 from rfl]
    rw [List.replicate_succ (n := M + 1), List.replicate_succ (n := M + 1)]
    rw [List.replicate_succ (n := M), List.replicate_succ (n := M)]
    -- now the lists are `g :: g :: replicate M g` and `s :: s :: replicate M s`
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq]
    -- the tail `weldChain h conn (g :: replicate M g) = zChain h conn g M`
    have hTail : weldChain h conn (g :: List.replicate M g) = zChain h conn g M := by
      show weldChain h conn (List.replicate (M + 1) g) = _
      rfl
    have hTailS : weldChainSurf h (s :: List.replicate M s) = zChainSurf h s M := by
      show weldChainSurf h (List.replicate (M + 1) s) = _
      rfl
    refine ⟨⟨⟨⟨⟨⟨⟨hg_i, hg_j⟩, hg_k⟩, hg_v⟩, hg_f⟩, ?_⟩, ?_⟩, ?_⟩
    · -- validity interface, transported from the reference cert
      rw [hTail, weldInterfaceValidOK2_N_eq hh M w wj]
      exact href_v
    · -- functionality interface, transported from the reference cert
      rw [hTail, hTailS, weldInterfaceOK2_N_eq hh M n w wj]
      exact href_f
    · -- the recursive tail: the IH, after folding `g :: replicate M g = replicate (M+1) g`
      rw [show g :: List.replicate M g = List.replicate (M + 1) g from (List.replicate_succ).symm,
          show s :: List.replicate M s = List.replicate (M + 1) s from (List.replicate_succ).symm]
      exact ih

/-! ## §7½. TOP-LAYER SURFACE — the chain's TOP mirrors `s`'s top, for all `N`.

  For the OUT ports (top boundary, `k = (N+1)·h − 1`) the chain surface reads the
  LAST gadget's top layer.  `weldSurf` puts `SB` (the rest of the chain) at layers
  `≥ h`, so by induction the top reads `s` at layer `h−1` — the same surface piece
  for EVERY `N`.  (Only the `KI`/`KJ` planes are needed for the canonical Z/X
  boundary ports.) -/

theorem zChainSurf_KI_top (hh : 1 ≤ h) (N : Nat) (t i j : Nat) :
    (zChainSurf h s N).KI t i j ((N + 1) * h - 1) = s.KI t i j (h - 1) := by
  induction N with
  | zero =>
    show s.KI t i j ((0 + 1) * h - 1) = s.KI t i j (h - 1)
    rw [Nat.zero_add, Nat.one_mul]
  | succ M ih =>
    rw [zChainSurf_succ]
    simp only [weldSurf]
    have hp : (M + 1) * h + h = (M + 1 + 1) * h := by ring
    have hp1 : 1 ≤ (M + 1) * h := Nat.le_trans hh (Nat.le_mul_of_pos_left h (by omega))
    have harith : (M + 1 + 1) * h - 1 = (M + 1) * h - 1 + h := by omega
    rw [harith]
    rw [if_neg (by omega)]
    rw [show (M + 1) * h - 1 + h - h = (M + 1) * h - 1 from by omega]
    exact ih

theorem zChainSurf_KJ_top (hh : 1 ≤ h) (N : Nat) (t i j : Nat) :
    (zChainSurf h s N).KJ t i j ((N + 1) * h - 1) = s.KJ t i j (h - 1) := by
  induction N with
  | zero =>
    show s.KJ t i j ((0 + 1) * h - 1) = s.KJ t i j (h - 1)
    rw [Nat.zero_add, Nat.one_mul]
  | succ M ih =>
    rw [zChainSurf_succ]
    simp only [weldSurf]
    have hp : (M + 1) * h + h = (M + 1 + 1) * h := by ring
    have hp1 : 1 ≤ (M + 1) * h := Nat.le_trans hh (Nat.le_mul_of_pos_left h (by omega))
    have harith : (M + 1 + 1) * h - 1 = (M + 1) * h - 1 + h := by omega
    rw [harith]
    rw [if_neg (by omega)]
    rw [show (M + 1) * h - 1 + h - h = (M + 1) * h - 1 from by omega]
    exact ih

/-! ## §8. ★ FIXED WIDTH `W = 2` — the depth-`N` `Z̄`-merge stack, for ALL `N`. -/

/-- The ONE reference validity interface certificate at `W = 2` — a SINGLE
`native_decide` at the FIXED width (reused, via §6, at every induction step; it is
NOT re-run per `N`). -/
theorem zMerge2_refValidInterface :
    weldInterfaceValidOK2 3 (zMerge 2) (zMerge 2) zConn2 2 1 = true := by native_decide

/-- The ONE reference functionality interface certificate at `W = 2` — a SINGLE
`native_decide` at the FIXED width.  `n = 3` flows suffice for `W = 2`
(`zMerge` has flows `0..w`).  Reused at every step via §6. -/
theorem zMerge2_refFuncInterface :
    weldInterfaceOK2 3 (zMerge 2) (zMerge 2) (zMergeSurf 2) (zMergeSurf 2) zConn2 3 2 1 = true := by
  native_decide

/-- **★ DEPTH-GENERIC `chainOK` AT `W = 2` ★** — the depth-`(N+1)` stack of
`zMerge 2`s passes the per-gadget + per-interface chain checker for ALL `N`, by
induction.  The per-gadget facts come from Step 1 (`zMerge_valid`/`zMerge_funcOK`)
and the two interfaces from the SINGLE reference certificates above — NO
`native_decide` over the chain length `N`. -/
theorem zChain2_chainOK (N : Nat) :
    chainOK 3 3 zConn2 2 1
      (List.replicate (N + 1) (zMerge 2)) (List.replicate (N + 1) (zMergeSurf 2)) = true :=
  zChain_chainOK_generic (h := 3) (conn := zConn2) (g := zMerge 2) (s := zMergeSurf 2)
    (by norm_num) 3 2 1
    rfl rfl rfl (zMerge_valid 2) (zMerge_funcOK 2 3)
    zMerge2_refValidInterface zMerge2_refFuncInterface N

/-! ## §9. ★ THE N-FOLD CHAIN PORTS — composite boundary, for ALL `N`. -/

/-- The top time layer of the depth-`(N+1)` stack at `W = 2` (height `3` each). -/
abbrev topK2 (N : Nat) : Nat := (N + 1) * 3 - 1

/-- Composite ports: the two data IN ports at `k = 0` and the two OUT ports at the
top layer `k = topK2 N`, columns `0,1`, canonical blue=`KI`(4)/red=`KJ`(5). -/
def zChain2Ports (N : Nat) : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨1, 0, 0, 4, 5⟩,
   ⟨0, 0, topK2 N, 4, 5⟩, ⟨1, 0, topK2 N, 4, 5⟩]

/-- Spec: flow `0` is the joint `Z̄₁Z̄₂` (measured at both ends); flow `t∈{1,2}`
is `X̄` on column `t-1`.  Column of port `p` is `p % 2` (ins then outs). -/
def zChain2Paulis : Nat → Nat → Pauli := fun t p =>
  if t = 0 then Pauli.Z else if t - 1 = p % 2 then Pauli.X else Pauli.I

/-- The chain surface's `KI` plane is `N`-independent at BOTH boundaries (and is
exactly `zMergeSurf 2`'s `k`-independent value). -/
theorem zChain2Surf_KI_bdry (N t i j : Nat) (k : Nat) (hk : k = 0 ∨ k = topK2 N) :
    (zChainSurf 3 (zMergeSurf 2) N).KI t i j k = (zMergeSurf 2).KI t i j 0 := by
  rcases hk with hk | hk
  · subst hk; exact zChainSurf_KI0 (by norm_num) N t i j
  · subst hk
    rw [zChainSurf_KI_top (by norm_num) N t i j]
    rfl

theorem zChain2Surf_KJ_bdry (N t i j : Nat) (k : Nat) (hk : k = 0 ∨ k = topK2 N) :
    (zChainSurf 3 (zMergeSurf 2) N).KJ t i j k = (zMergeSurf 2).KJ t i j 0 := by
  rcases hk with hk | hk
  · subst hk; exact zChainSurf_KJ0 (by norm_num) N t i j
  · subst hk
    rw [zChainSurf_KJ_top (by norm_num) N t i j]
    rfl

/-- **★ N-FOLD CHAIN PORT BOUNDARY ★** — for EVERY `N`, the welded depth-`(N+1)`
`Z̄`-merge stack's surface matches the joint-`Z̄₁Z̄₂` / per-column-`X̄` spec at all
four composite ports.  The two surface reads (IN at `k=0`, OUT at `k=topK2 N`) are
`N`-independent (§7, §7½) and reduce to `zMergeSurf 2`'s `k`-independent boundary,
so the proof is the same finite column match for all `N`. -/
theorem zChain2_portsOK (N : Nat) :
    portsOK (zChainSurf 3 (zMergeSurf 2) N) (zChain2Ports N) zChain2Paulis 3 = true := by
  rw [portsOK, List.all_eq_true]
  intro t ht
  have htlt : t < 3 := List.mem_range.1 ht
  rw [List.all_eq_true]
  intro pp hpp
  -- enumerate the four ports
  simp only [zChain2Ports, List.zipIdx, List.zipIdx_cons,
    List.mem_cons, List.not_mem_nil, or_false] at hpp
  -- a uniform finisher once both boundary reads are reduced to `zMergeSurf 2`'s
  -- `k`-independent value: the four ports are a finite column match in `t < 3`.
  have hbK : ∀ i k, (k = 0 ∨ k = topK2 N) →
      (zChainSurf 3 (zMergeSurf 2) N).KI t i 0 k = (zMergeSurf 2).KI t i 0 0 :=
    fun i k hk => zChain2Surf_KI_bdry N t i 0 k hk
  have hbJ : ∀ i k, (k = 0 ∨ k = topK2 N) →
      (zChainSurf 3 (zMergeSurf 2) N).KJ t i 0 k = (zMergeSurf 2).KJ t i 0 0 :=
    fun i k hk => zChain2Surf_KJ_bdry N t i 0 k hk
  rcases hpp with rfl | rfl | rfl | rfl <;>
    -- step 1: collapse the boundary surface reads to `zMergeSurf 2`'s value
    simp only [Surf.sel,
      hbK 0 0 (Or.inl rfl), hbK 1 0 (Or.inl rfl),
      hbJ 0 0 (Or.inl rfl), hbJ 1 0 (Or.inl rfl),
      hbK 0 (topK2 N) (Or.inr rfl), hbK 1 (topK2 N) (Or.inr rfl),
      hbJ 0 (topK2 N) (Or.inr rfl), hbJ 1 (topK2 N) (Or.inr rfl)] <;>
    -- step 2: now unfold the spec/surface and finish by the finite column match
    · simp only [zChain2Paulis, zMergeSurf, portBlue, portRed]
      interval_cases t <;> simp

/-! ## §10. ★ THE HEADLINE — a depth-`N` `Z̄`-merge stack passes `LaSCorrectFull`
    for ALL `N`. -/

/-- **★ DEPTH-GENERIC `LaSCorrectFull` AT `W = 2`, FOR ALL `N` ★** — the welded
depth-`(N+1)` stack of contiguous `Z̄`-merges (each measuring the same joint
`Z̄₁Z̄₂` on the two data qubits) is a FULLY CORRECT lattice-surgery program for
EVERY chain length `N`: structurally valid, interior functionality satisfied
across every weld seam, and the composite ports matching the joint-`Z̄₁Z̄₂` /
per-column-`X̄` spec.

Obtained from `weldChain_LaSCorrectFull` (the generic chain bridge) fed the
depth-generic `chainOK` (§8, proven by INDUCTION on `N`, reusing ONE fixed-width
interface certificate) and the N-fold ports (§9).  This is "cost one tile,
compose" made rigorous in the DEPTH direction — the time-axis mirror of the
width-symbolic Step 1.  NO `native_decide` over the chain length `N`. -/
theorem zChain2_LaSCorrectFull (N : Nat) :
    LaSCorrectFull
      (weldChain 3 zConn2 (List.replicate (N + 1) (zMerge 2)))
      (weldChainSurf 3 (List.replicate (N + 1) (zMergeSurf 2)))
      (zChain2Ports N) zChain2Paulis 3 = true :=
  weldChain_LaSCorrectFull 3 3 zConn2 2 1
    (List.replicate (N + 1) (zMerge 2)) (List.replicate (N + 1) (zMergeSurf 2))
    (zChain2Ports N) zChain2Paulis
    (zChain2_chainOK N) (zChain2_portsOK N)

end FormalRV.QEC.LaSre
