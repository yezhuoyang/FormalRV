import FormalRV.QEC.Gidney21.FoldPPMProg
import FormalRV.QEC.LatticeSurgery.WidthScalingHeteroPorts

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC.LaSre

/-! ## Bridge: the GadgetToLaS Z-merge IS the width-symbolic `zMerge 2`. -/

theorem mergeZLaS_eq : mergeZLaS = zMerge 2 := by
  unfold mergeZLaS zMerge
  congr 1
  · funext i j k; cases i <;> rfl
  · funext i j k; cases i with
    | zero => rfl
    | succ n => cases n <;> rfl

theorem mergeZSurf_eq : mergeZSurf = zMergeSurf 2 := by
  unfold mergeZSurf zMergeSurf
  congr 1
  · funext s i j k; cases i <;> rfl                                   -- IK (seam)
  · funext s i j k; rcases i with _|_|i <;> rfl                        -- KI (worldlines)
  · funext s i j k; rcases s with _|_|_|s <;> rcases i with _|_|i <;> simp  -- KJ

theorem measConn_eq : measConn = zChainConn 2 := rfl

/-! ## A real ∀-N family of programs: `N` joint `Z̄₁Z̄₂` measurements. -/

open FormalRV.PPM.Prog (PPMStmt PPMProg PFactor PKind)

/-- One statement: `c_dst = Measure Z[0]Z[1]`. -/
def zMeasStmt (dst : Nat) : PPMStmt :=
  PPMStmt.measure dst [{ qubit := 0, kind := PKind.z }, { qubit := 1, kind := PKind.z }]

/-- The program: `N` joint-`Z̄₁Z̄₂` measurements, slots `c0 … c_{N-1}` in order
(so `PPMProg.wf` holds — a genuine well-formed program of unbounded length). -/
def zMeasProg (N : Nat) : PPMProg := (List.range N).map zMeasStmt

/-- The catalog routing of ONE statement is a single Z-merge (independent of the
classical slot). -/
theorem stmtGadgets_zMeas (d : Nat) : stmtGadgets (zMeasStmt d) = [GadgetKind.zMerge] := rfl

/-- The whole program routes to `N` Z-merges — by induction on the statement list. -/
theorem progGadgets_zMeas_list (l : List Nat) :
    progGadgets (l.map zMeasStmt) = List.replicate l.length GadgetKind.zMerge := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.length_cons, List.replicate_succ]
    show stmtGadgets (zMeasStmt a) ++ progGadgets (t.map zMeasStmt) = _
    rw [stmtGadgets_zMeas, ih]; rfl

theorem zMeasProg_gadgets (N : Nat) :
    progGadgets (zMeasProg N) = List.replicate N GadgetKind.zMerge := by
  rw [zMeasProg, progGadgets_zMeas_list, List.length_range]

/-! ## The fold of `zMeasProg N` IS the width-2 catalog chain `replicate N (zMerge 2)`. -/

theorem foldLaSList_zMeas (N : Nat) :
    foldLaSList (zMeasProg N) = List.replicate N (zMerge 2) := by
  rw [foldLaSList, zMeasProg_gadgets, List.map_replicate,
      show (gadgetFor GadgetKind.zMerge).L = mergeZLaS from rfl, mergeZLaS_eq]

theorem foldSurfList_zMeas (N : Nat) :
    foldSurfList (zMeasProg N) = List.replicate N (zMergeSurf 2) := by
  rw [foldSurfList, zMeasProg_gadgets, List.map_replicate,
      show (gadgetFor GadgetKind.zMerge).S = mergeZSurf from rfl, mergeZSurf_eq]

/-- The engine's kind-chain at `w = 2`, `ks = replicate N true`, has the SAME
diagram list `replicate N (zMerge 2)`. -/
theorem kindChain_g_replicate (N : Nat) :
    ((List.replicate N true).map (kindEntry 2)).map (·.g) = List.replicate N (zMerge 2) := by
  rw [List.map_replicate, List.map_replicate]; rfl

theorem kindChain_sg_replicate (N : Nat) :
    ((List.replicate N true).map (kindEntry 2)).map (·.sg) = List.replicate N (zMergeSurf 2) := by
  rw [List.map_replicate, List.map_replicate]; rfl

/-! ## §HEADLINE — the whole ∀-N family auto-certifies (no native_decide on N). -/

/-- **★ A WHOLE UNBOUNDED-LENGTH PPM PROGRAM FAMILY FOLDS TO ONE VERIFIED LATTICE-
SURGERY DIAGRAM — FOR ALL `N`, BY INDUCTION ★.**  For every `N > 0`, the program
`zMeasProg N` (`N` joint `Z̄₁Z̄₂` measurements) is folded through the SYNTAX
(`progGadgets`/`gadgetFor` → `foldPPMProgLaS`) and the WHOLE welded diagram passes
the COMPLETE global `LaSCorrectFull`, realizing the joint `Z̄₁Z̄₂` + per-qubit `X̄`
spec — obtained from the ∀-N chain engine (`kindChain_LaSCorrectFull`, list
induction + per-column `List.all_eq_true`), NOT from a `native_decide` on the
length-`N` diagram.  So `foldPPMProg`'s `chainOK`/`portsOK` obligations discharge
AUTOMATICALLY for this entire program family. -/
theorem foldPPMProg_zMeas_scales (N : Nat) (hN : 0 < N) :
    LaSCorrectFull
      (foldPPMProgLaS 3 (zChainConn 2) (zMeasProg N))
      (weldChainSurf 3 (foldSurfList (zMeasProg N)))
      (heteroStackPorts 2 (List.replicate N true)) (zMergePaulis 2) 3 = true := by
  have hne : (List.replicate N true) ≠ [] := by
    rw [Ne, List.replicate_eq_nil_iff]; omega
  have hL : foldPPMProgLaS 3 (zChainConn 2) (zMeasProg N)
      = weldChain 3 (zChainConn 2) (((List.replicate N true).map (kindEntry 2)).map (·.g)) := by
    rw [foldPPMProgLaS, foldLaSList_zMeas, kindChain_g_replicate]
  have hS : weldChainSurf 3 (foldSurfList (zMeasProg N))
      = weldChainSurf 3 (((List.replicate N true).map (kindEntry 2)).map (·.sg)) := by
    rw [foldSurfList_zMeas, kindChain_sg_replicate]
  rw [hL, hS]
  exact kindChain_LaSCorrectFull 2 (List.replicate N true) hne

/-! ## §MIXED — the genuinely mixed-basis `M_{X̄₁Z̄₂}` family, ∀-N.

  The mixed merge is the SAME spacetime diagram + surface as the Z-merge
  (`mxzScheduleLaS.L = mergeZLaS`, `.S = mergeZSurf`) read with patch-1 in the
  X-boundary convention (blue↔red swapped ports).  So the chain `valid`/`funcOK`
  is IDENTICAL to the Z case (reused via `replicate_chainOK`); only the PORTS
  differ — and the chain surface's KI/KJ being `k`-constant
  (`weldChainSurf_KI_const`/`KJ_const`) reduces the ∀-N port check to the same
  per-flow reading `mxzMerge_fully_correct` discharges at one gadget. -/

/-- One mixed statement: `c_dst = Measure X[0]Z[1]`. -/
def mxzMeasStmt (dst : Nat) : PPMStmt :=
  PPMStmt.measure dst [{ qubit := 0, kind := PKind.x }, { qubit := 1, kind := PKind.z }]

/-- The program: `N` joint `X̄₁Z̄₂` measurements. -/
def mxzMeasProg (N : Nat) : PPMProg := (List.range N).map mxzMeasStmt

theorem stmtGadgets_mxz (d : Nat) : stmtGadgets (mxzMeasStmt d) = [GadgetKind.mxzMerge] := rfl

theorem progGadgets_mxz_list (l : List Nat) :
    progGadgets (l.map mxzMeasStmt) = List.replicate l.length GadgetKind.mxzMerge := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.length_cons, List.replicate_succ]
    show stmtGadgets (mxzMeasStmt a) ++ progGadgets (t.map mxzMeasStmt) = _
    rw [stmtGadgets_mxz, ih]; rfl

theorem mxzMeasProg_gadgets (N : Nat) :
    progGadgets (mxzMeasProg N) = List.replicate N GadgetKind.mxzMerge := by
  rw [mxzMeasProg, progGadgets_mxz_list, List.length_range]

/-- The mixed fold IS the same diagram/surface as the Z fold (`mxzMerge.L = mergeZLaS`). -/
theorem foldLaSList_mxz (N : Nat) :
    foldLaSList (mxzMeasProg N) = List.replicate N (zMerge 2) := by
  rw [foldLaSList, mxzMeasProg_gadgets, List.map_replicate,
      show (gadgetFor GadgetKind.mxzMerge).L = mergeZLaS from rfl, mergeZLaS_eq]

theorem foldSurfList_mxz (N : Nat) :
    foldSurfList (mxzMeasProg N) = List.replicate N (zMergeSurf 2) := by
  rw [foldSurfList, mxzMeasProg_gadgets, List.map_replicate,
      show (gadgetFor GadgetKind.mxzMerge).S = mergeZSurf from rfl, mergeZSurf_eq]

/-- The chain's `chainOK` (valid+funcOK+interfaces) — SHARED with the Z case
(same diagram/surface). -/
theorem replicate_chainOK (N : Nat) (hN : 0 < N) :
    chainOK 3 3 (zChainConn 2) 2 1
      (List.replicate N (zMerge 2)) (List.replicate N (zMergeSurf 2)) = true := by
  have hne : (List.replicate N true) ≠ [] := by rw [Ne, List.replicate_eq_nil_iff]; omega
  have h := kindChain_chainOK 2 (List.replicate N true) hne
  rwa [kindChain_g_replicate, kindChain_sg_replicate] at h

/-- The mixed ports: patch-1 (col 0) in the X-convention (blue=`KJ` 5, red=`KI`
4); patch-2 (col 1) normal — at the bottom (`k=0`) and top (`k=3N-1`) of the
`N`-tall chain. -/
def mxzStackPorts (N : Nat) : List Port :=
  [⟨0, 0, 0, 5, 4⟩, ⟨0, 0, 3 * N - 1, 5, 4⟩, ⟨1, 0, 0, 4, 5⟩, ⟨1, 0, 3 * N - 1, 4, 5⟩]

/-- **★ THE ∀-N MIXED PORT CHECK ★** — the chain surface's `KI`/`KJ` are
`k`-constant, so every port (bottom or top, any `N`) reads the bottom
`zMergeSurf 2` value, which matches the `X̄₁Z̄₂` spec for all three flows. -/
theorem mxzStack_portsOK (N : Nat) (hN : 0 < N) :
    portsOK (weldChainSurf 3 (List.replicate N (zMergeSurf 2)))
      (mxzStackPorts N) mxzPaulis 3 = true := by
  have hne : (List.replicate N (zMergeSurf 2)) ≠ [] := by
    rw [Ne, List.replicate_eq_nil_iff]; omega
  have hKI : ∀ t i j k,
      (weldChainSurf 3 (List.replicate N (zMergeSurf 2))).KI t i j k = (zMergeSurf 2).KI t i j 0 :=
    fun t i j k => weldChainSurf_KI_const (zMergeSurf 2).KI (fun _ _ _ _ => rfl) _ hne
      (fun sg hsg => by rw [List.eq_of_mem_replicate hsg]) t i j k
  have hKJ : ∀ t i j k,
      (weldChainSurf 3 (List.replicate N (zMergeSurf 2))).KJ t i j k = (zMergeSurf 2).KJ t i j 0 :=
    fun t i j k => weldChainSurf_KJ_const (zMergeSurf 2).KJ (fun _ _ _ _ => rfl) _ hne
      (fun sg hsg => by rw [List.eq_of_mem_replicate hsg]) t i j k
  rw [portsOK, List.all_eq_true]
  intro s hs
  simp only [List.mem_range] at hs
  rw [List.all_eq_true]
  intro pp hpp
  fin_cases hpp <;>
    simp only [Surf.sel, hKI, hKJ] <;>
    interval_cases s <;> decide

/-- **★ THE GENUINELY MIXED-BASIS PROGRAM FAMILY FOLDS TO ONE VERIFIED DIAGRAM,
∀-N ★** — for every `N > 0`, the program `mxzMeasProg N` (`N` joint `X̄₁Z̄₂`
measurements) folds through the SYNTAX into one welded diagram passing the
COMPLETE global `LaSCorrectFull` against the `X̄₁Z̄₂` spec (`mxzPaulis`), for ALL
`N` — `chainOK` reused from the Z case (same diagram), the mixed PORTS proved
`k`-constant.  No `native_decide` on `N`.  (Flow-level mixed merge, per the
`mxzMerge` color-blind scope note — the color-faithful weld is a separate
refinement.) -/
theorem foldPPMProg_mxz_scales (N : Nat) (hN : 0 < N) :
    LaSCorrectFull
      (foldPPMProgLaS 3 (zChainConn 2) (mxzMeasProg N))
      (weldChainSurf 3 (foldSurfList (mxzMeasProg N)))
      (mxzStackPorts N) mxzPaulis 3 = true := by
  rw [foldPPMProgLaS, foldLaSList_mxz, foldSurfList_mxz]
  exact weldChain_LaSCorrectFull 3 3 (zChainConn 2) 2 1
    (List.replicate N (zMerge 2)) (List.replicate N (zMergeSurf 2))
    (mxzStackPorts N) mxzPaulis (replicate_chainOK N hN) (mxzStack_portsOK N hN)

/-! ## A reusable program-routing helper (any constant-kind statement family). -/

theorem progGadgets_map_const {k : GadgetKind} {f : Nat → PPMStmt}
    (hf : ∀ d, stmtGadgets (f d) = [k]) (l : List Nat) :
    progGadgets (l.map f) = List.replicate l.length k := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.length_cons, List.replicate_succ]
    show stmtGadgets (f a) ++ progGadgets (t.map f) = _
    rw [hf a, ih]; rfl

/-! ## §X-MERGE — the I↔J dual: the joint `X̄₁X̄₂` family, ∀-N. -/

/-- Bridge: the GadgetToLaS X-merge IS the width-symbolic `xMerge 2`. -/
theorem mergeXLaS_eq : mergeXLaS = xMerge 2 := by
  unfold mergeXLaS xMerge
  congr 1
  · funext i j k; cases j <;> rfl                       -- ExistJ (seam)
  · funext i j k; rcases j with _|_|j <;> rfl            -- ExistK (worldlines)

theorem mergeXSurf_eq : mergeXSurf = xMergeSurf 2 := by
  unfold mergeXSurf xMergeSurf
  congr 1
  · funext s i j k; cases j <;> rfl                                  -- JK (seam, joint X)
  · funext s i j k; rcases s with _|_|_|s <;> rcases j with _|_|j <;> simp  -- KI (Z passthrough)
  · funext s i j k; rcases j with _|_|j <;> rfl                       -- KJ (joint X)

/-- One X statement: `c_dst = Measure X[0]X[1]`. -/
def xMeasStmt (dst : Nat) : PPMStmt :=
  PPMStmt.measure dst [{ qubit := 0, kind := PKind.x }, { qubit := 1, kind := PKind.x }]

def xMeasProg (M : Nat) : PPMProg := (List.range M).map xMeasStmt

theorem stmtGadgets_xMeas (d : Nat) : stmtGadgets (xMeasStmt d) = [GadgetKind.xMerge] := rfl

theorem xMeasProg_gadgets (M : Nat) :
    progGadgets (xMeasProg M) = List.replicate M GadgetKind.xMerge := by
  rw [xMeasProg, progGadgets_map_const stmtGadgets_xMeas, List.length_range]

theorem foldLaSList_xMerge (M : Nat) :
    foldLaSList (xMeasProg M) = List.replicate M (xMerge 2) := by
  rw [foldLaSList, xMeasProg_gadgets, List.map_replicate,
      show (gadgetFor GadgetKind.xMerge).L = mergeXLaS from rfl, mergeXLaS_eq]

theorem foldSurfList_xMerge (M : Nat) :
    foldSurfList (xMeasProg M) = List.replicate M (xMergeSurf 2) := by
  rw [foldSurfList, xMeasProg_gadgets, List.map_replicate,
      show (gadgetFor GadgetKind.xMerge).S = mergeXSurf from rfl, mergeXSurf_eq]

/-- **★ THE JOINT-`X̄₁X̄₂` PROGRAM FAMILY FOLDS TO ONE VERIFIED DIAGRAM, ∀-N ★** —
the I↔J dual of the Z case: for every `N`, `xMeasProg (N+1)` (`N+1` joint `X̄₁X̄₂`
measurements) folds through the syntax into one welded diagram passing the
COMPLETE `LaSCorrectFull` against the joint-`X̄` / per-column-`Z̄` spec, via the
∀w∀N `xMerge_stack_LaSCorrectFull` engine.  No `native_decide` over `N`. -/
theorem foldPPMProg_xMerge_scales (N : Nat) :
    LaSCorrectFull
      (foldPPMProgLaS 3 (xConn 2) (xMeasProg (N + 1)))
      (weldChainSurf 3 (foldSurfList (xMeasProg (N + 1))))
      (xStackPorts 2 N) (xMergePaulis 2) 3 = true := by
  rw [foldPPMProgLaS, foldLaSList_xMerge, foldSurfList_xMerge]
  exact xMerge_stack_LaSCorrectFull 2 N

/-! ## §MIRROR — the `M_{Z̄₁X̄₂}` family, ∀-N (same Z-diagram, X-convention on col 1). -/

/-- One mirror statement: `c_dst = Measure Z[0]X[1]`. -/
def mzxMeasStmt (dst : Nat) : PPMStmt :=
  PPMStmt.measure dst [{ qubit := 0, kind := PKind.z }, { qubit := 1, kind := PKind.x }]

def mzxMeasProg (M : Nat) : PPMProg := (List.range M).map mzxMeasStmt

theorem stmtGadgets_mzx (d : Nat) : stmtGadgets (mzxMeasStmt d) = [GadgetKind.mzxMerge] := rfl

theorem mzxMeasProg_gadgets (M : Nat) :
    progGadgets (mzxMeasProg M) = List.replicate M GadgetKind.mzxMerge := by
  rw [mzxMeasProg, progGadgets_map_const stmtGadgets_mzx, List.length_range]

theorem foldLaSList_mzx (M : Nat) :
    foldLaSList (mzxMeasProg M) = List.replicate M (zMerge 2) := by
  rw [foldLaSList, mzxMeasProg_gadgets, List.map_replicate,
      show (gadgetFor GadgetKind.mzxMerge).L = mergeZLaS from rfl, mergeZLaS_eq]

theorem foldSurfList_mzx (M : Nat) :
    foldSurfList (mzxMeasProg M) = List.replicate M (zMergeSurf 2) := by
  rw [foldSurfList, mzxMeasProg_gadgets, List.map_replicate,
      show (gadgetFor GadgetKind.mzxMerge).S = mergeZSurf from rfl, mergeZSurf_eq]

/-- The mirror ports: patch-1 (col 0) normal (Z), patch-2 (col 1) in X-convention. -/
def mzxStackPorts (N : Nat) : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨0, 0, 3 * N - 1, 4, 5⟩, ⟨1, 0, 0, 5, 4⟩, ⟨1, 0, 3 * N - 1, 5, 4⟩]

theorem mzxStack_portsOK (N : Nat) (hN : 0 < N) :
    portsOK (weldChainSurf 3 (List.replicate N (zMergeSurf 2)))
      (mzxStackPorts N) mzxPaulis 3 = true := by
  have hne : (List.replicate N (zMergeSurf 2)) ≠ [] := by
    rw [Ne, List.replicate_eq_nil_iff]; omega
  have hKI : ∀ t i j k,
      (weldChainSurf 3 (List.replicate N (zMergeSurf 2))).KI t i j k = (zMergeSurf 2).KI t i j 0 :=
    fun t i j k => weldChainSurf_KI_const (zMergeSurf 2).KI (fun _ _ _ _ => rfl) _ hne
      (fun sg hsg => by rw [List.eq_of_mem_replicate hsg]) t i j k
  have hKJ : ∀ t i j k,
      (weldChainSurf 3 (List.replicate N (zMergeSurf 2))).KJ t i j k = (zMergeSurf 2).KJ t i j 0 :=
    fun t i j k => weldChainSurf_KJ_const (zMergeSurf 2).KJ (fun _ _ _ _ => rfl) _ hne
      (fun sg hsg => by rw [List.eq_of_mem_replicate hsg]) t i j k
  rw [portsOK, List.all_eq_true]
  intro s hs
  simp only [List.mem_range] at hs
  rw [List.all_eq_true]
  intro pp hpp
  fin_cases hpp <;>
    simp only [Surf.sel, hKI, hKJ] <;>
    interval_cases s <;> decide

/-- **★ THE `M_{Z̄₁X̄₂}` MIRROR FAMILY FOLDS TO ONE VERIFIED DIAGRAM, ∀-N ★** — the
same Z-merge diagram, patch-2 read in the X-convention; `chainOK` reused, mirror
ports proved `k`-constant.  No `native_decide` over `N`. -/
theorem foldPPMProg_mzx_scales (N : Nat) (hN : 0 < N) :
    LaSCorrectFull
      (foldPPMProgLaS 3 (zChainConn 2) (mzxMeasProg N))
      (weldChainSurf 3 (foldSurfList (mzxMeasProg N)))
      (mzxStackPorts N) mzxPaulis 3 = true := by
  rw [foldPPMProgLaS, foldLaSList_mzx, foldSurfList_mzx]
  exact weldChain_LaSCorrectFull 3 3 (zChainConn 2) 2 1
    (List.replicate N (zMerge 2)) (List.replicate N (zMergeSurf 2))
    (mzxStackPorts N) mzxPaulis (replicate_chainOK N hN) (mzxStack_portsOK N hN)

/-! ## §Y — the weight-1 single-patch `M_Y` family, ∀-N (completes X/Y/Z).

  A genuinely single-flow (nStab = 1) readout: `mY1`'s diagram is `memoryLaS`
  (one worldline), and `mY1Surf` carries BOTH planes (`KI`=`KJ`= the worldline) so
  it reads `Ȳ`.  A reusable single-gadget ∀-N chain lemma `rep_chainOK` (the
  generic catalog induction specialized to ONE repeated gadget at arbitrary
  `nStab`) certifies the chain; the `k`-constant ports give the Y readout. -/

/-- **A repeated-gadget ∀-N `chainOK`** — for ANY single catalog gadget `(g, s)`
with its own per-gadget checks and self-interface certs, the depth-`N` chain of
identical gadgets passes `chainOK`, by induction, each interface reduced to the
gadget's own self-cert (`chain_*_reduce_to_self`).  No `native_decide` over `N`. -/
theorem rep_chainOK (g : LaSre) (s : Surf) (n w wj : Nat) (conn : List (Nat × Nat))
    (hi : g.maxI = w) (hj : g.maxJ = wj) (hk : g.maxK = 3)
    (hv : g.valid = true) (hf : g.funcOK s n = true)
    (rfv : weldInterfaceValidOK2 3 g g conn w wj = true)
    (rff : weldInterfaceOK2 3 g g s s conn n w wj = true)
    (hbL : BotEqL g g) (hbS : BotEqS s s) :
    ∀ N, 0 < N → chainOK 3 n conn w wj (List.replicate N g) (List.replicate N s) = true := by
  intro N
  induction N with
  | zero => intro h; exact absurd h (by omega)
  | succ p ih =>
    cases p with
    | zero =>
      intro _
      simp only [List.replicate, chainOK, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨hi, hj⟩, hk⟩, hv⟩, hf⟩
    | succ q =>
      intro _
      simp only [List.replicate_succ, chainOK, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, hk⟩, hv⟩, hf⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [chain_validInterface_reduce_to_self (by norm_num) g (List.replicate q g) hbL]
        exact rfv
      · rw [chain_interface_reduce_to_self (by norm_num) g (List.replicate q g) s
              (List.replicate q s) hbL hbS]
        exact rff
      · have hrec := ih (Nat.succ_pos q)
        simpa only [List.replicate_succ, chainOK, Bool.and_eq_true, beq_iff_eq] using hrec

theorem mY1_funcOK : memoryLaS.funcOK mY1Surf 1 = true := by native_decide
theorem yRead_refValid : weldInterfaceValidOK2 3 memoryLaS memoryLaS [(0, 0)] 1 1 = true := by
  native_decide
theorem yRead_refFunc :
    weldInterfaceOK2 3 memoryLaS memoryLaS mY1Surf mY1Surf [(0, 0)] 1 1 1 = true := by native_decide

def botEqL_mem : BotEqL memoryLaS memoryLaS :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
def botEqS_mY1 : BotEqS mY1Surf mY1Surf :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
   fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- The single-patch `M_Y` chain passes `chainOK` for all `N`. -/
theorem yReadout_chainOK (N : Nat) (hN : 0 < N) :
    chainOK 3 1 [(0, 0)] 1 1 (List.replicate N memoryLaS) (List.replicate N mY1Surf) = true :=
  rep_chainOK memoryLaS mY1Surf 1 1 1 [(0, 0)] rfl rfl rfl memoryLaS_valid mY1_funcOK
    yRead_refValid yRead_refFunc botEqL_mem botEqS_mY1 N hN

/-- One Y statement: `c_dst = Measure Y[0]`. -/
def yMeasStmt (dst : Nat) : PPMStmt :=
  PPMStmt.measure dst [{ qubit := 0, kind := PKind.y }]

def yMeasProg (M : Nat) : PPMProg := (List.range M).map yMeasStmt

theorem stmtGadgets_yMeas (d : Nat) : stmtGadgets (yMeasStmt d) = [GadgetKind.mY1] := rfl

theorem yMeasProg_gadgets (M : Nat) :
    progGadgets (yMeasProg M) = List.replicate M GadgetKind.mY1 := by
  rw [yMeasProg, progGadgets_map_const stmtGadgets_yMeas, List.length_range]

theorem foldLaSList_yMeas (M : Nat) :
    foldLaSList (yMeasProg M) = List.replicate M memoryLaS := by
  rw [foldLaSList, yMeasProg_gadgets, List.map_replicate]; rfl

theorem foldSurfList_yMeas (M : Nat) :
    foldSurfList (yMeasProg M) = List.replicate M mY1Surf := by
  rw [foldSurfList, yMeasProg_gadgets, List.map_replicate]; rfl

/-- The Y readout ports: one patch, bottom (`k=0`) and top (`k=3N-1`), normal
convention (blue=`KI`, red=`KJ`); the `Ȳ` spec reads BOTH planes. -/
def yStackPorts (N : Nat) : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨0, 0, 3 * N - 1, 4, 5⟩]

theorem yReadout_portsOK (N : Nat) (hN : 0 < N) :
    portsOK (weldChainSurf 3 (List.replicate N mY1Surf)) (yStackPorts N) mY1Paulis 1 = true := by
  have hne : (List.replicate N mY1Surf) ≠ [] := by rw [Ne, List.replicate_eq_nil_iff]; omega
  have hKI : ∀ t i j k,
      (weldChainSurf 3 (List.replicate N mY1Surf)).KI t i j k = mY1Surf.KI t i j 0 :=
    fun t i j k => weldChainSurf_KI_const mY1Surf.KI (fun _ _ _ _ => rfl) _ hne
      (fun sg hsg => by rw [List.eq_of_mem_replicate hsg]) t i j k
  have hKJ : ∀ t i j k,
      (weldChainSurf 3 (List.replicate N mY1Surf)).KJ t i j k = mY1Surf.KJ t i j 0 :=
    fun t i j k => weldChainSurf_KJ_const mY1Surf.KJ (fun _ _ _ _ => rfl) _ hne
      (fun sg hsg => by rw [List.eq_of_mem_replicate hsg]) t i j k
  rw [portsOK, List.all_eq_true]
  intro s hs
  simp only [List.mem_range] at hs
  rw [List.all_eq_true]
  intro pp hpp
  fin_cases hpp <;>
    simp only [Surf.sel, hKI, hKJ] <;>
    interval_cases s <;> decide

/-- **★ THE WEIGHT-1 `M_Y` PROGRAM FAMILY FOLDS TO ONE VERIFIED DIAGRAM, ∀-N ★** —
for every `N > 0`, `yMeasProg N` (`N` single-qubit `Ȳ` measurements) folds through
the syntax into one welded single-patch worldline passing the COMPLETE
`LaSCorrectFull` against the `Ȳ` spec (`mY1Paulis`), for ALL `N` — genuine
single-flow (nStab = 1) readout, `chainOK` by induction (`rep_chainOK`), ports
`k`-constant.  No `native_decide` over `N`.  Completes the single-patch X/Y/Z
readout set (flow-level Y, per the `mY1` §3½ caveat). -/
theorem foldPPMProg_yMeas_scales (N : Nat) (hN : 0 < N) :
    LaSCorrectFull
      (foldPPMProgLaS 3 [(0, 0)] (yMeasProg N))
      (weldChainSurf 3 (foldSurfList (yMeasProg N)))
      (yStackPorts N) mY1Paulis 1 = true := by
  rw [foldPPMProgLaS, foldLaSList_yMeas, foldSurfList_yMeas]
  exact weldChain_LaSCorrectFull 3 1 [(0, 0)] 1 1
    (List.replicate N memoryLaS) (List.replicate N mY1Surf)
    (yStackPorts N) mY1Paulis (yReadout_chainOK N hN) (yReadout_portsOK N hN)

/-! ## §WEIGHT-3 — the 3-patch joins (Toffoli/adder merges), ∀-N.

  The width-symbolic `kindChain` engine is `∀w`; the weight-3 Z-merge family lives
  at `w = 3`.  Generic-`w` bridge helpers connect any `zMerge w`/`zMergeSurf w`
  replicate-chain to `foldPPMProg`. -/

theorem kindChain_g_repl (w N : Nat) :
    ((List.replicate N true).map (kindEntry w)).map (·.g) = List.replicate N (zMerge w) := by
  rw [List.map_replicate, List.map_replicate]; rfl

theorem kindChain_sg_repl (w N : Nat) :
    ((List.replicate N true).map (kindEntry w)).map (·.sg) = List.replicate N (zMergeSurf w) := by
  rw [List.map_replicate, List.map_replicate]; rfl

theorem replicate_chainOK_w (w N : Nat) (hN : 0 < N) :
    chainOK 3 (w + 1) (zChainConn w) w 1
      (List.replicate N (zMerge w)) (List.replicate N (zMergeSurf w)) = true := by
  have hne : (List.replicate N true) ≠ [] := by rw [Ne, List.replicate_eq_nil_iff]; omega
  have h := kindChain_chainOK w (List.replicate N true) hne
  rwa [kindChain_g_repl, kindChain_sg_repl] at h

/-- Bridge: the weight-3 Z-merge IS the width-symbolic `zMerge 3`. -/
theorem mergeZ3LaS_eq : mergeZ3LaS = zMerge 3 := by
  unfold mergeZ3LaS zMerge
  congr 1
  · funext i j k; rcases i with _|_|i <;> rfl          -- ExistI (2 seams)
  · funext i j k; rcases i with _|_|_|i <;> rfl         -- ExistK (3 worldlines)

theorem mergeZ3Surf_eq : mergeZ3Surf = zMergeSurf 3 := by
  unfold mergeZ3Surf zMergeSurf
  congr 1
  · funext s i j k; rcases i with _|_|i <;> rfl                           -- IK
  · funext s i j k; rcases i with _|_|_|i <;> rfl                         -- KI
  · funext s i j k; rcases s with _|_|_|_|s <;> rcases i with _|_|_|i <;> simp  -- KJ

/-- One weight-3 Z statement: `c_dst = Measure Z[0]Z[1]Z[2]`. -/
def z3MeasStmt (dst : Nat) : PPMStmt :=
  PPMStmt.measure dst
    [{ qubit := 0, kind := PKind.z }, { qubit := 1, kind := PKind.z }, { qubit := 2, kind := PKind.z }]

def z3MeasProg (M : Nat) : PPMProg := (List.range M).map z3MeasStmt

theorem stmtGadgets_z3 (d : Nat) : stmtGadgets (z3MeasStmt d) = [GadgetKind.mZ3] := rfl

theorem z3MeasProg_gadgets (M : Nat) :
    progGadgets (z3MeasProg M) = List.replicate M GadgetKind.mZ3 := by
  rw [z3MeasProg, progGadgets_map_const stmtGadgets_z3, List.length_range]

theorem foldLaSList_z3 (M : Nat) :
    foldLaSList (z3MeasProg M) = List.replicate M (zMerge 3) := by
  rw [foldLaSList, z3MeasProg_gadgets, List.map_replicate,
      show (gadgetFor GadgetKind.mZ3).L = mergeZ3LaS from rfl, mergeZ3LaS_eq]

theorem foldSurfList_z3 (M : Nat) :
    foldSurfList (z3MeasProg M) = List.replicate M (zMergeSurf 3) := by
  rw [foldSurfList, z3MeasProg_gadgets, List.map_replicate,
      show (gadgetFor GadgetKind.mZ3).S = mergeZ3Surf from rfl, mergeZ3Surf_eq]

/-- **★ THE WEIGHT-3 JOINT-`Z̄₁Z̄₂Z̄₃` FAMILY FOLDS TO ONE VERIFIED DIAGRAM, ∀-N ★** —
the 3-patch Toffoli/adder join, for all `N`, via the `∀w` `kindChain` engine at
`w = 3`.  No `native_decide` over `N`. -/
theorem foldPPMProg_z3Meas_scales (N : Nat) (hN : 0 < N) :
    LaSCorrectFull
      (foldPPMProgLaS 3 (zChainConn 3) (z3MeasProg N))
      (weldChainSurf 3 (foldSurfList (z3MeasProg N)))
      (heteroStackPorts 3 (List.replicate N true)) (zMergePaulis 3) 4 = true := by
  have hne : (List.replicate N true) ≠ [] := by rw [Ne, List.replicate_eq_nil_iff]; omega
  have hL : foldPPMProgLaS 3 (zChainConn 3) (z3MeasProg N)
      = weldChain 3 (zChainConn 3) (((List.replicate N true).map (kindEntry 3)).map (·.g)) := by
    rw [foldPPMProgLaS, foldLaSList_z3, kindChain_g_repl]
  have hS : weldChainSurf 3 (foldSurfList (z3MeasProg N))
      = weldChainSurf 3 (((List.replicate N true).map (kindEntry 3)).map (·.sg)) := by
    rw [foldSurfList_z3, kindChain_sg_repl]
  rw [hL, hS]
  exact kindChain_LaSCorrectFull 3 (List.replicate N true) hne

/-! ## §WEIGHT-3 MIXED — `X̄₁Z̄₂Z̄₃` (same `mergeZ3` diagram, col-1 in X-convention). -/

/-- One mixed weight-3 statement: `c_dst = Measure X[0]Z[1]Z[2]`. -/
def mxzz3MeasStmt (dst : Nat) : PPMStmt :=
  PPMStmt.measure dst
    [{ qubit := 0, kind := PKind.x }, { qubit := 1, kind := PKind.z }, { qubit := 2, kind := PKind.z }]

def mxzz3MeasProg (M : Nat) : PPMProg := (List.range M).map mxzz3MeasStmt

theorem stmtGadgets_mxzz3 (d : Nat) : stmtGadgets (mxzz3MeasStmt d) = [GadgetKind.mxzz3] := rfl

theorem mxzz3MeasProg_gadgets (M : Nat) :
    progGadgets (mxzz3MeasProg M) = List.replicate M GadgetKind.mxzz3 := by
  rw [mxzz3MeasProg, progGadgets_map_const stmtGadgets_mxzz3, List.length_range]

theorem foldLaSList_mxzz3 (M : Nat) :
    foldLaSList (mxzz3MeasProg M) = List.replicate M (zMerge 3) := by
  rw [foldLaSList, mxzz3MeasProg_gadgets, List.map_replicate,
      show (gadgetFor GadgetKind.mxzz3).L = mergeZ3LaS from rfl, mergeZ3LaS_eq]

theorem foldSurfList_mxzz3 (M : Nat) :
    foldSurfList (mxzz3MeasProg M) = List.replicate M (zMergeSurf 3) := by
  rw [foldSurfList, mxzz3MeasProg_gadgets, List.map_replicate,
      show (gadgetFor GadgetKind.mxzz3).S = mergeZ3Surf from rfl, mergeZ3Surf_eq]

/-- The mixed weight-3 ports: patch-1 (col 0) X-convention, patches 2,3 normal —
bottom (`k=0`) and top (`k=3N-1`) of the chain. -/
def mxzz3StackPorts (N : Nat) : List Port :=
  [⟨0, 0, 0, 5, 4⟩, ⟨0, 0, 3 * N - 1, 5, 4⟩,
   ⟨1, 0, 0, 4, 5⟩, ⟨1, 0, 3 * N - 1, 4, 5⟩,
   ⟨2, 0, 0, 4, 5⟩, ⟨2, 0, 3 * N - 1, 4, 5⟩]

theorem mxzz3Stack_portsOK (N : Nat) (hN : 0 < N) :
    portsOK (weldChainSurf 3 (List.replicate N (zMergeSurf 3)))
      (mxzz3StackPorts N) mxzz3Paulis 4 = true := by
  have hne : (List.replicate N (zMergeSurf 3)) ≠ [] := by rw [Ne, List.replicate_eq_nil_iff]; omega
  have hKI : ∀ t i j k,
      (weldChainSurf 3 (List.replicate N (zMergeSurf 3))).KI t i j k = (zMergeSurf 3).KI t i j 0 :=
    fun t i j k => weldChainSurf_KI_const (zMergeSurf 3).KI (fun _ _ _ _ => rfl) _ hne
      (fun sg hsg => by rw [List.eq_of_mem_replicate hsg]) t i j k
  have hKJ : ∀ t i j k,
      (weldChainSurf 3 (List.replicate N (zMergeSurf 3))).KJ t i j k = (zMergeSurf 3).KJ t i j 0 :=
    fun t i j k => weldChainSurf_KJ_const (zMergeSurf 3).KJ (fun _ _ _ _ => rfl) _ hne
      (fun sg hsg => by rw [List.eq_of_mem_replicate hsg]) t i j k
  rw [portsOK, List.all_eq_true]
  intro s hs
  simp only [List.mem_range] at hs
  rw [List.all_eq_true]
  intro pp hpp
  fin_cases hpp <;>
    simp only [Surf.sel, hKI, hKJ] <;>
    interval_cases s <;> decide

/-- **★ THE WEIGHT-3 MIXED `X̄₁Z̄₂Z̄₃` FAMILY FOLDS TO ONE VERIFIED DIAGRAM, ∀-N ★** —
same `mergeZ3` diagram (`chainOK` reused via `replicate_chainOK_w 3`), col-1 read
in the X-convention; ports `k`-constant.  No `native_decide` over `N`. -/
theorem foldPPMProg_mxzz3_scales (N : Nat) (hN : 0 < N) :
    LaSCorrectFull
      (foldPPMProgLaS 3 (zChainConn 3) (mxzz3MeasProg N))
      (weldChainSurf 3 (foldSurfList (mxzz3MeasProg N)))
      (mxzz3StackPorts N) mxzz3Paulis 4 = true := by
  rw [foldPPMProgLaS, foldLaSList_mxzz3, foldSurfList_mxzz3]
  exact weldChain_LaSCorrectFull 3 4 (zChainConn 3) 3 1
    (List.replicate N (zMerge 3)) (List.replicate N (zMergeSurf 3))
    (mxzz3StackPorts N) mxzz3Paulis (replicate_chainOK_w 3 N hN) (mxzz3Stack_portsOK N hN)

/-! ## §HETEROGENEOUS SCHEDULE — a genuinely MULTI-DIAGRAM chain, ∀ schedule.

  The previous families are HOMOGENEOUS (one repeated diagram).  A real schedule
  on a fixed board interleaves TWO distinct diagrams in TIME: a `Z`-merge
  (`zMerge 2`, an I-seam at k=1) when the patches measure, and an idle
  (`idleMerge 2`, NO seam) when they just hold.  `kindChain_LaSCorrectFull` proves
  ANY such merge/idle schedule `ks : List Bool` (∀ length, native_decide-free).
  Here we expose it at the fold API, prove a schedule is GENUINELY heterogeneous
  (the welded diagram really has both a merge-seam layer AND a seam-free idle
  layer), and show it SUBSUMES the homogeneous `foldPPMProg` (all-merge = the
  `zMeasProg` family).

  SCOPE (honest): "multi-diagram" here = merge ⊕ idle (two diagrams sharing the
  i-axis worldline bottom — `BotEqL idle zMerge`).  Mixing a Z-merge and an
  X-merge in one TIME chain is NOT meaningful in this model (their worldlines lie
  on transposed axes — `BotEqL zMerge xMerge` fails; physically a fixed pair of
  patches measures one boundary type).  Per-layer DIFFERENT merge SUBSETS (e.g.
  merge {0,1} then {1,2} on a 3-patch board) is the FrameTracker connected-
  components frontier. -/

/-- The fold of a merge/idle SCHEDULE `t` (true = `Z̄₁Z̄₂` merge, false = idle). -/
def foldTimedLaS (t : List Bool) : LaSre :=
  weldChain 3 (zChainConn 2) ((t.map (kindEntry 2)).map (·.g))
def foldTimedSurf (t : List Bool) : Surf :=
  weldChainSurf 3 ((t.map (kindEntry 2)).map (·.sg))

/-- **★ ANY MERGE/IDLE SCHEDULE FOLDS TO ONE VERIFIED MULTI-DIAGRAM CHAIN, ∀ ★** —
for every nonempty schedule `t`, the welded chain (freely interleaving `zMerge 2`
and `idleMerge 2` diagrams) passes the COMPLETE `LaSCorrectFull` against the joint
`Z̄₁Z̄₂` + per-qubit `X̄` spec, for ALL schedules and lengths.  No `native_decide`
over the schedule.  (Directly the `∀ks` chain engine.) -/
theorem foldTimed_LaSCorrectFull (t : List Bool) (ht : t ≠ []) :
    LaSCorrectFull (foldTimedLaS t) (foldTimedSurf t)
      (heteroStackPorts 2 t) (zMergePaulis 2) 3 = true := by
  unfold foldTimedLaS foldTimedSurf
  exact kindChain_LaSCorrectFull 2 t ht

/-- The engine SUBSUMES the homogeneous fold: the all-merge schedule IS the
`zMeasProg` diagram. -/
theorem foldTimed_allMerge_eq_zMeas (N : Nat) :
    foldTimedLaS (List.replicate N true) = foldPPMProgLaS 3 (zChainConn 2) (zMeasProg N) := by
  rw [foldTimedLaS, kindChain_g_repl, foldPPMProgLaS, foldLaSList_zMeas]

/-! ### A GENUINELY heterogeneous worked schedule: merge ; idle ; merge ; idle ; merge. -/

def demoSched : List Bool := [true, false, true, false, true]

/-- It is genuinely mixed — 3 merges and 2 idles (not secretly homogeneous). -/
theorem demoSched_genuinely_mixed :
    demoSched.count true = 3 ∧ demoSched.count false = 2 := by decide

/-- The whole heterogeneous schedule certifies. -/
theorem demoSched_correct :
    LaSCorrectFull (foldTimedLaS demoSched) (foldTimedSurf demoSched)
      (heteroStackPorts 2 demoSched) (zMergePaulis 2) 3 = true :=
  foldTimed_LaSCorrectFull demoSched (by decide)

/-- The welded diagram REALLY interleaves two diagrams: a merge-seam at the first
(merge) layer `k=1`... -/
theorem demoSched_has_merge_layer : (foldTimedLaS demoSched).ExistI 0 0 1 = true := by
  native_decide

/-- ...and NO seam at the second (idle) layer's seam slot `k=4` — so it is not the
all-merge diagram; the heterogeneity is real, not a relabel. -/
theorem demoSched_has_idle_layer : (foldTimedLaS demoSched).ExistI 0 0 4 = false := by
  native_decide

end FormalRV.QEC.Gidney21
