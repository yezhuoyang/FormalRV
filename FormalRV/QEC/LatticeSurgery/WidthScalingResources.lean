import FormalRV.QEC.LatticeSurgery.WidthScalingHeteroPorts

namespace FormalRV.QEC.LaSre

/-! ## Counter defs (fresh, tiny — avoids importing heavy CompileReport). -/

def cubeCount (g : Nat → Nat → Nat → Bool) (mi mj mk : Nat) : Nat :=
  ((List.range mi).flatMap (fun i => (List.range mj).flatMap (fun j =>
    (List.range mk).map (fun k => if g i j k then 1 else 0)))).foldl (· + ·) 0

def physSeams (L : LaSre) : Nat := cubeCount L.ExistI L.maxI L.maxJ L.maxK
def physWorldlineSegs (L : LaSre) : Nat := cubeCount L.ExistK L.maxI L.maxJ L.maxK

-- foldl → sum, with accumulator
theorem foldl_add_acc (l : List Nat) (z : Nat) : l.foldl (·+·) z = z + l.sum := by
  induction l generalizing z with
  | nil => simp
  | cons a t ih => simp only [List.foldl_cons, List.sum_cons, ih]; omega

theorem foldl_add_eq_sum (l : List Nat) : l.foldl (·+·) 0 = l.sum := by
  rw [foldl_add_acc]; simp

-- flatMap-sum helper
theorem sum_flatMap (l : List Nat) (f : Nat → List Nat) :
    (l.flatMap f).sum = (l.map (fun x => (f x).sum)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.sum_append, ih]

-- cubeCount as a nested sum
theorem cubeCount_eq_sum (g : Nat → Nat → Nat → Bool) (mi mj mk : Nat) :
    cubeCount g mi mj mk =
      ((List.range mi).map (fun i => ((List.range mj).map (fun j =>
        ((List.range mk).map (fun k => if g i j k then 1 else 0)).sum)).sum)).sum := by
  rw [cubeCount, foldl_add_eq_sum, sum_flatMap]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [sum_flatMap]

-- the core combinatorial count: sum over i<w of [i+1<w] = w-1
theorem sum_range_succ_lt (w : Nat) :
    ((List.range w).map (fun i => if i + 1 < w then 1 else 0)).sum = w - 1 := by
  induction w with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [List.map_congr_left (g := fun _ => 1)
      (fun i hi => by simp only [List.mem_range] at hi; rw [if_pos (by omega)])]
    rw [if_neg (by omega : ¬ n + 1 < n + 1)]; simp

-- the innermost k-sum splits over a + b (via List.range_add).
theorem ksum_add (f : Nat → Bool) (a b : Nat) :
    ((List.range (a + b)).map (fun k => if f k then 1 else 0)).sum
      = ((List.range a).map (fun k => if f k then 1 else 0)).sum
        + ((List.range b).map (fun k => if f (k + a) then 1 else 0)).sum := by
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  congr 1
  rw [show ((fun k => if f k then 1 else 0) ∘ fun x => a + x)
        = (fun k => if f (k + a) then 1 else 0) from ?_]
  funext k
  simp only [Function.comp_apply, Nat.add_comm]

-- the j-sum is the inner k-sum, lifted pointwise.
-- additivity over the k-range (the KEY lemma): split mk = a + b.
theorem cubeCount_add (g : Nat → Nat → Nat → Bool) (mi mj a b : Nat) :
    cubeCount g mi mj (a + b)
      = cubeCount g mi mj a + cubeCount (fun i j k => g i j (k + a)) mi mj b := by
  simp only [cubeCount_eq_sum]
  rw [← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro j _
  exact ksum_add (g i j) a b

/-- For the `w × 1 × 3` footprint, `cubeCount` collapses to a sum over the `w`
columns of the three time-layer indicators. -/
theorem cubeCount_w_1_3 (g : Nat → Nat → Nat → Bool) (w : Nat) :
    cubeCount g w 1 3 =
      ((List.range w).map (fun i =>
        (if g i 0 0 then 1 else 0) + (if g i 0 1 then 1 else 0)
          + (if g i 0 2 then 1 else 0))).sum := by
  rw [cubeCount_eq_sum]
  simp only [List.range_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [show (List.range 3) = [0,1,2] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-! ## §3. PER-GADGET resource counts (all `w`). -/

/-- The `Z̄`-merge has exactly `w − 1` merge-seam I-pipes (the seam spans
columns `0..w-2` at time `k = 1`). -/
theorem zMerge_physSeams (w : Nat) : physSeams (zMerge w) = w - 1 := by
  show cubeCount (zMerge w).ExistI (zMerge w).maxI (zMerge w).maxJ (zMerge w).maxK = w - 1
  show cubeCount (zMerge w).ExistI w 1 3 = w - 1
  rw [cubeCount_w_1_3]
  simp only [zMerge, Bool.and_true, show ((0:Nat)==1)=false from rfl,
    show ((1:Nat)==1)=true from rfl, show ((2:Nat)==1)=false from rfl,
    show ((0:Nat)==0)=true from rfl, Bool.and_false, Bool.false_eq_true, if_false,
    Nat.zero_add, Nat.add_zero, decide_eq_true_eq]
  exact sum_range_succ_lt w

/-- The idle gadget has NO merge-seam I-pipes. -/
theorem idleMerge_physSeams (w : Nat) : physSeams (idleMerge w) = 0 := by
  show cubeCount (idleMerge w).ExistI w 1 3 = 0
  rw [cubeCount_w_1_3]
  simp [idleMerge]

/-- The `Z̄`-merge carries exactly `2w` worldline K-segments (each of the `w`
columns has a segment at `k ∈ {0,1}`). -/
theorem zMerge_physWorldlineSegs (w : Nat) : physWorldlineSegs (zMerge w) = 2 * w := by
  show cubeCount (zMerge w).ExistK w 1 3 = 2 * w
  rw [cubeCount_w_1_3]
  simp only [zMerge, Bool.and_true, show ((0:Nat)==0)=true from rfl,
    show (decide (0 < 2)) = true from rfl, show (decide (1 < 2)) = true from rfl,
    show (decide (2 < 2)) = false from rfl, Bool.and_false, Bool.false_eq_true, if_false,
    Nat.add_zero, decide_eq_true_eq]
  rw [List.map_congr_left (g := fun _ => 2)
    (fun i hi => by simp only [List.mem_range] at hi; rw [if_pos hi])]
  simp [List.map_const', List.sum_replicate, List.length_range, Nat.mul_comm]

/-- The idle gadget carries the SAME `2w` worldline K-segments as the merge
(its `ExistK` is identical to the merge's). -/
theorem idleMerge_physWorldlineSegs (w : Nat) : physWorldlineSegs (idleMerge w) = 2 * w := by
  show cubeCount (idleMerge w).ExistK w 1 3 = 2 * w
  rw [show (idleMerge w).ExistK = (zMerge w).ExistK from rfl]
  exact zMerge_physWorldlineSegs w

/-- The `Z̄`-merge occupies a `w × 1 × 3` spacetime box: volume `3w`. -/
theorem zMerge_volume (w : Nat) : (zMerge w).volume = 3 * w := by
  show w * 1 * 3 = 3 * w
  ring

/-- The idle gadget occupies the same `w × 1 × 3` box. -/
theorem idleMerge_volume (w : Nat) : (idleMerge w).volume = 3 * w := by
  show w * 1 * 3 = 3 * w
  ring

/-! ## §4. CHAIN WIDTH/DEPTH bounding-box: `maxI`, `maxJ` constant under welding. -/

/-- A welded chain of width-`w` gadgets keeps width `w`. -/
theorem weldChain_maxI_const (conn : List (Nat × Nat)) (gs : List LaSre)
    (hgs : gs ≠ []) (w : Nat) (hg : ∀ g ∈ gs, g.maxI = w) :
    (weldChain 3 conn gs).maxI = w := by
  induction gs with
  | nil => exact absurd rfl hgs
  | cons g rest ih =>
    cases rest with
    | nil => exact hg g (by simp)
    | cons g2 rest' =>
      show (weldK 3 g (weldChain 3 conn (g2 :: rest')) conn).maxI = w
      simp only [weldK]
      rw [ih (by simp) (fun gg hgg => hg gg (by simp [hgg])), hg g (by simp), Nat.max_self]

/-- A welded chain of `maxJ = 1` gadgets keeps `maxJ = 1`. -/
theorem weldChain_maxJ_const (conn : List (Nat × Nat)) (gs : List LaSre)
    (hgs : gs ≠ []) (hg : ∀ g ∈ gs, g.maxJ = 1) :
    (weldChain 3 conn gs).maxJ = 1 := by
  induction gs with
  | nil => exact absurd rfl hgs
  | cons g rest ih =>
    cases rest with
    | nil => exact hg g (by simp)
    | cons g2 rest' =>
      show (weldK 3 g (weldChain 3 conn (g2 :: rest')) conn).maxJ = 1
      simp only [weldK]
      rw [ih (by simp) (fun gg hgg => hg gg (by simp [hgg])), hg g (by simp), Nat.max_self]

/-! ## §5. THE WELD-SEAM SPLIT — additivity of `physSeams` across one weld.

`weldK 3 A B conn` has `ExistI i j k = A.ExistI` for `k < 3` and `B.ExistI (k-3)`
for `k ≥ 3` (NO `conn` injection on `ExistI` — seams are purely piecewise).  So
the seam count splits into the bottom `A`-region (over `k < 3`) plus the entire
`B`-region.  We use `cubeCount_add` with `a = 3`, `b = B.maxK`. -/

/-- The bottom `k < 3` region of the welded `ExistI` over a `w × 1` cross-section
counts EXACTLY `A`'s own seam tally (here `A` has footprint `w × 1 × 3`). -/
theorem weldK_botSeams (A B : LaSre) (conn : List (Nat × Nat)) (w : Nat) :
    cubeCount (weldK 3 A B conn).ExistI w 1 3 = cubeCount A.ExistI w 1 3 := by
  -- the welded `ExistI` at every `k ∈ {0,1,2}` is `A.ExistI` (since `k < 3`).
  rw [cubeCount_w_1_3, cubeCount_w_1_3]
  congr 1

/-- The `k ≥ 3` region of the welded `ExistI` is exactly `B`'s `ExistI`, so the
shifted count over `B.maxK` layers equals `physSeams B` (when `B` has width `w`,
`maxJ = 1`). -/
theorem weldK_topSeams (A B : LaSre) (conn : List (Nat × Nat)) (w : Nat)
    (hBi : B.maxI = w) (hBj : B.maxJ = 1) :
    cubeCount (fun i j k => (weldK 3 A B conn).ExistI i j (k + 3)) w 1 B.maxK
      = physSeams B := by
  rw [physSeams, hBi, hBj]
  apply congrArg (cubeCount · w 1 B.maxK)
  funext i j k
  simp only [weldK]
  rw [if_neg (by omega : ¬ k + 3 < 3), Nat.add_sub_cancel]

/-- **★ PER-WELD SEAM ADDITIVITY ★** — across one weld, `physSeams` is additive:
the bottom gadget `A`'s seam tally plus the entire chain-tail `B`'s, for
width-`w`, `maxJ = 1` gadgets.  Proven via `cubeCount_add` (NO `native_decide`). -/
theorem weldK_physSeams (A B : LaSre) (conn : List (Nat × Nat)) (w : Nat)
    (hA : A.maxI = w) (hAj : A.maxJ = 1) (_hAk : A.maxK = 3)
    (hBi : B.maxI = w) (hBj : B.maxJ = 1) :
    physSeams (weldK 3 A B conn) = cubeCount A.ExistI w 1 3 + physSeams B := by
  have hMi : (weldK 3 A B conn).maxI = w := by simp only [weldK]; rw [hA, hBi, Nat.max_self]
  have hMj : (weldK 3 A B conn).maxJ = 1 := by simp only [weldK]; rw [hAj, hBj, Nat.max_self]
  have hMk : (weldK 3 A B conn).maxK = 3 + B.maxK := by simp only [weldK]
  show cubeCount (weldK 3 A B conn).ExistI (weldK 3 A B conn).maxI
        (weldK 3 A B conn).maxJ (weldK 3 A B conn).maxK = _
  rw [hMi, hMj, hMk, cubeCount_add (a := 3) (b := B.maxK),
    weldK_botSeams A B conn w, weldK_topSeams A B conn w hBi hBj]

/-- For a `w × 1 × 3` gadget, `physSeams g = cubeCount g.ExistI w 1 3`. -/
theorem physSeams_w_1_3 (g : LaSre) (w : Nat)
    (hi : g.maxI = w) (hj : g.maxJ = 1) (hk : g.maxK = 3) :
    physSeams g = cubeCount g.ExistI w 1 3 := by
  rw [physSeams, hi, hj, hk]

/-! ## §6. ★ THE CHAIN SEAM COUNT = FORMULA (by induction, NO native_decide). ★ -/

/-- **★ GENERIC CHAIN SEAM ADDITIVITY ★** — for ANY nonempty list of `w × 1 × 3`
gadgets, the welded chain's actual merge-seam count is the SUM of the per-gadget
seam counts.  Proven BY INDUCTION on the list, each weld discharged by
`weldK_physSeams` (which itself is the `cubeCount_add` k-range split).  NO
`native_decide` over the width OR the chain length. -/
theorem weldChain_physSeams (conn : List (Nat × Nat)) (w : Nat) (gs : List LaSre)
    (hgs : gs ≠ [])
    (hi : ∀ g ∈ gs, g.maxI = w) (hj : ∀ g ∈ gs, g.maxJ = 1) (hk : ∀ g ∈ gs, g.maxK = 3) :
    physSeams (weldChain 3 conn gs) = (gs.map physSeams).sum := by
  induction gs with
  | nil => exact absurd rfl hgs
  | cons g rest ih =>
    cases rest with
    | nil => show physSeams g = _; simp
    | cons g2 rest' =>
      show physSeams (weldK 3 g (weldChain 3 conn (g2 :: rest')) conn) = _
      have hBi : (weldChain 3 conn (g2 :: rest')).maxI = w :=
        weldChain_maxI_const conn _ (by simp) w (fun gg hgg => hi gg (by simp [hgg]))
      have hBj : (weldChain 3 conn (g2 :: rest')).maxJ = 1 :=
        weldChain_maxJ_const conn _ (by simp) (fun gg hgg => hj gg (by simp [hgg]))
      rw [weldK_physSeams g _ conn w (hi g (by simp)) (hj g (by simp)) (hk g (by simp)) hBi hBj]
      rw [← physSeams_w_1_3 g w (hi g (by simp)) (hj g (by simp)) (hk g (by simp))]
      rw [ih (by simp) (fun gg hgg => hi gg (by simp [hgg]))
        (fun gg hgg => hj gg (by simp [hgg])) (fun gg hgg => hk gg (by simp [hgg]))]
      simp [List.map_cons, List.sum_cons]

/-! ### §6a. HOMOGENEOUS chain — `N+1` copies of the `Z̄`-merge. -/

/-- **★ HOMOGENEOUS SEAM COUNT = FORMULA ★** — a depth-`(N+1)` stack of the
width-`w` `Z̄`-merge has EXACTLY `(N+1)·(w−1)` merge-seam I-pipes.  Proven by the
generic chain additivity + per-gadget count, BY INDUCTION, NO `native_decide`. -/
theorem replicate_zMerge_physSeams (w N : Nat) :
    physSeams (weldChain 3 (zChainConn w) (List.replicate (N + 1) (zMerge w)))
      = (N + 1) * (w - 1) := by
  rw [weldChain_physSeams (zChainConn w) w _
    (by simp) (by intro g hg; rw [List.eq_of_mem_replicate hg]; rfl)
    (by intro g hg; rw [List.eq_of_mem_replicate hg]; rfl)
    (by intro g hg; rw [List.eq_of_mem_replicate hg]; rfl)]
  rw [List.map_replicate, zMerge_physSeams, List.sum_replicate, smul_eq_mul]

/-! ### §6b. HETEROGENEOUS chain — ANY merge/idle sequence. -/

/-- A `kindEntry` gadget has the canonical `w × 1 × 3` footprint. -/
theorem kindEntry_g_maxI (w : Nat) (b : Bool) : (kindEntry w b).g.maxI = w := by cases b <;> rfl
theorem kindEntry_g_maxJ (w : Nat) (b : Bool) : (kindEntry w b).g.maxJ = 1 := by cases b <;> rfl

/-- The per-gadget seam tally of a `kindEntry`: `w−1` for a merge, `0` for idle. -/
theorem kindEntry_g_physSeams (w : Nat) (b : Bool) :
    physSeams (kindEntry w b).g = if b then w - 1 else 0 := by
  cases b with
  | true => exact zMerge_physSeams w
  | false => exact idleMerge_physSeams w

/-- The sum of the per-layer indicator `if b then (w−1) else 0` over a kind list
equals `(ks.count true)·(w−1)`. -/
theorem sum_kind_indicator (w : Nat) (ks : List Bool) :
    (ks.map (fun b => if b then w - 1 else 0)).sum = ks.count true * (w - 1) := by
  induction ks with
  | nil => simp
  | cons b t ih =>
    rw [List.map_cons, List.sum_cons, List.count_cons, ih]
    cases b with
    | true => simp; ring
    | false => simp

/-- **★ HETEROGENEOUS SEAM COUNT = FORMULA ★** — for ANY merge/idle sequence
`ks : List Bool`, the welded catalog chain has EXACTLY `(ks.count true)·(w−1)`
merge-seam I-pipes: only MERGE layers contribute a seam, idle layers contribute
0.  Proven via the generic chain additivity, BY INDUCTION, NO `native_decide`
over `w` OR the chain length/composition. -/
theorem kindChain_physSeams (w : Nat) (ks : List Bool) (hk : ks ≠ []) :
    physSeams (weldChain 3 (zChainConn w) ((ks.map (kindEntry w)).map (·.g)))
      = ks.count true * (w - 1) := by
  rw [weldChain_physSeams (zChainConn w) w _
    (by simp only [ne_eq, List.map_eq_nil_iff]; exact hk)
    (by intro g hg; simp only [List.mem_map] at hg; obtain ⟨e, he, rfl⟩ := hg
        obtain ⟨b, _, rfl⟩ := he; exact kindEntry_g_maxI w b)
    (by intro g hg; simp only [List.mem_map] at hg; obtain ⟨e, he, rfl⟩ := hg
        obtain ⟨b, _, rfl⟩ := he; exact kindEntry_g_maxJ w b)
    (by intro g hg; simp only [List.mem_map] at hg; obtain ⟨e, he, rfl⟩ := hg
        obtain ⟨b, _, rfl⟩ := he; exact kindEntry_g_maxK w b)]
  -- ((ks.map (kindEntry w)).map (·.g)).map physSeams = ks.map (fun b => if b then w-1 else 0)
  rw [List.map_map, List.map_map,
    List.map_congr_left (g := fun b => if b then w - 1 else 0)
      (fun b _ => by simp only [Function.comp_apply]; exact kindEntry_g_physSeams w b),
    sum_kind_indicator]

/-! ## §7. CHAIN DEPTH and VOLUME = FORMULA (∀w, ∀ ks, NO native_decide). -/

/-- **★ HETEROGENEOUS CHAIN DEPTH ★** — the welded catalog chain is exactly
`ks.length · 3` time-steps tall.  (Re-export of `kindChain_maxK`.) -/
theorem kindChain_depth (w : Nat) (ks : List Bool) (hk : ks ≠ []) :
    (weldChain 3 (zChainConn w) ((ks.map (kindEntry w)).map (·.g))).maxK = ks.length * 3 :=
  kindChain_maxK w ks hk

/-- **★ HETEROGENEOUS CHAIN VOLUME = FORMULA ★** — the welded catalog chain's
spacetime bounding box is `w · 1 · (ks.length · 3) = 3 · w · ks.length`.  Width
from `weldChain_maxI_const`, depth from `kindChain_maxK`; NO `native_decide`. -/
theorem kindChain_volume (w : Nat) (ks : List Bool) (hk : ks ≠ []) :
    (weldChain 3 (zChainConn w) ((ks.map (kindEntry w)).map (·.g))).volume
      = 3 * w * ks.length := by
  have hne : ((ks.map (kindEntry w)).map (·.g)) ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff]; exact hk
  rw [LaSre.volume,
    weldChain_maxI_const (zChainConn w) _ hne w
      (by intro g hg; simp only [List.mem_map] at hg; obtain ⟨e, he, rfl⟩ := hg
          obtain ⟨b, _, rfl⟩ := he; exact kindEntry_g_maxI w b),
    weldChain_maxJ_const (zChainConn w) _ hne
      (by intro g hg; simp only [List.mem_map] at hg; obtain ⟨e, he, rfl⟩ := hg
          obtain ⟨b, _, rfl⟩ := he; exact kindEntry_g_maxJ w b),
    kindChain_maxK w ks hk]
  ring

/-- **★ HOMOGENEOUS CHAIN DEPTH ★** — `N+1` welded copies are `(N+1)·3` tall. -/
theorem replicate_zMerge_depth (w N : Nat) :
    (weldChain 3 (zChainConn w) (List.replicate (N + 1) (zMerge w))).maxK = (N + 1) * 3 := by
  rw [weldChain_maxK_const (zChainConn w) _ (by simp)
    (by intro g hg; rw [List.eq_of_mem_replicate hg]; rfl)]
  rw [List.length_replicate]

/-- **★ HOMOGENEOUS CHAIN VOLUME = FORMULA ★** — `w · 1 · ((N+1)·3) = 3w(N+1)`. -/
theorem replicate_zMerge_volume (w N : Nat) :
    (weldChain 3 (zChainConn w) (List.replicate (N + 1) (zMerge w))).volume
      = 3 * w * (N + 1) := by
  rw [LaSre.volume,
    weldChain_maxI_const (zChainConn w) _ (by simp) w
      (by intro g hg; rw [List.eq_of_mem_replicate hg]; rfl),
    weldChain_maxJ_const (zChainConn w) _ (by simp)
      (by intro g hg; rw [List.eq_of_mem_replicate hg]; rfl),
    replicate_zMerge_depth]
  ring

/-! ## §8. STRETCH — the WORLDLINE-SEGMENT chain formula.

Unlike seams, the welded `ExistK` gets a `conn`-injection at each weld's seam
layer (local `k = 2`): worldlines CONNECT across gadgets.  For our `w` data
columns welded by `zChainConn w` (which contains exactly `(i,0)` for `i < w`),
each gadget's own `ExistK i 0 2 = false` (its block is only 2 layers tall), so the
seam layer contributes a FRESH `w` connection segments at every weld.  Hence a
chain of `m` gadgets carries `m · 2w` in-block segments PLUS `(m−1) · w` seam
connections — exactly `(3m − 1)·w`.  We prove this precisely, by induction. -/

/-- The shared `ExistK` of both catalog gadgets, at the seam layer `k = 2`, is
`false` (each block is only 2 layers of worldline). -/
theorem catalog_ExistK_k2 (w i : Nat) : (zMerge w).ExistK i 0 2 = false := by
  simp [zMerge]

/-- The bottom `k < 3` region of the welded `ExistK`, for a bottom gadget `A` whose
`ExistK` is the canonical catalog one, welded by `zChainConn w`: the two in-block
layers (`k = 0,1`) give `2w`, and the seam layer (`k = 2`) gives a FRESH `w` from
the connection — total `3w`. -/
theorem weldK_botWorldline (A B : LaSre) (w : Nat)
    (hA : A.ExistK = (zMerge w).ExistK) :
    cubeCount (weldK 3 A B (zChainConn w)).ExistK w 1 3 = 3 * w := by
  rw [cubeCount_w_1_3]
  -- at k=0,1: zMerge.ExistK = decide(i<w); at k=2: false || conn.contains (i,0) = decide(i<w)
  have hmap : ∀ i ∈ List.range w,
      ((if (weldK 3 A B (zChainConn w)).ExistK i 0 0 then 1 else 0) +
        (if (weldK 3 A B (zChainConn w)).ExistK i 0 1 then 1 else 0)
        + (if (weldK 3 A B (zChainConn w)).ExistK i 0 2 then 1 else 0)) = 3 := by
    intro i hi
    simp only [List.mem_range] at hi
    simp only [weldK, zChainConn_contains, hA, zMerge,
      if_pos (show (0:Nat) + 1 < 3 by norm_num), if_pos (show (1:Nat) + 1 < 3 by norm_num),
      if_neg (show ¬ (2:Nat) + 1 < 3 by norm_num), if_pos (show (2:Nat) + 1 == 3 by norm_num)]
    simp [hi]
  rw [List.map_congr_left hmap]
  simp [List.map_const', List.sum_replicate, List.length_range, Nat.mul_comm]

/-- The `k ≥ 3` region of the welded `ExistK` is exactly `B`'s `ExistK` (the conn
injection lives only at the seam layer `k = 2`, never `k ≥ 3`), so the shifted
count equals `physWorldlineSegs B`. -/
theorem weldK_topWorldline (A B : LaSre) (conn : List (Nat × Nat)) (w : Nat)
    (hBi : B.maxI = w) (hBj : B.maxJ = 1) :
    cubeCount (fun i j k => (weldK 3 A B conn).ExistK i j (k + 3)) w 1 B.maxK
      = physWorldlineSegs B := by
  rw [physWorldlineSegs, hBi, hBj]
  apply congrArg (cubeCount · w 1 B.maxK)
  funext i j k
  simp only [weldK]
  rw [if_neg (by omega : ¬ k + 3 + 1 < 3), if_neg (by simp : ¬ (k + 3 + 1 == 3) = true),
    Nat.add_sub_cancel]

/-- **★ PER-WELD WORLDLINE COUNT ★** — across one weld of a catalog gadget onto a
width-`w` tail `B`, the worldline-segment count is `3w` (two in-block layers +
one seam connection) plus the tail `B`'s own segments. -/
theorem weldK_physWorldlineSegs (A B : LaSre) (w : Nat)
    (hA : A.ExistK = (zMerge w).ExistK) (hAi : A.maxI = w) (hAj : A.maxJ = 1)
    (hBi : B.maxI = w) (hBj : B.maxJ = 1) :
    physWorldlineSegs (weldK 3 A B (zChainConn w))
      = 3 * w + physWorldlineSegs B := by
  have hMi : (weldK 3 A B (zChainConn w)).maxI = w := by
    simp only [weldK]; rw [hBi, hAi, Nat.max_self]
  have hMj : (weldK 3 A B (zChainConn w)).maxJ = 1 := by
    simp only [weldK]; rw [hBj, hAj, Nat.max_self]
  have hMk : (weldK 3 A B (zChainConn w)).maxK = 3 + B.maxK := by simp only [weldK]
  show cubeCount (weldK 3 A B (zChainConn w)).ExistK _ _ _ = _
  rw [hMi, hMj, hMk, cubeCount_add (a := 3) (b := B.maxK),
    weldK_botWorldline A B w hA, weldK_topWorldline A B (zChainConn w) w hBi hBj]

/-- **★ HOMOGENEOUS WORLDLINE COUNT = FORMULA ★** — a depth-`(N+1)` `Z̄`-merge
stack carries EXACTLY `(3·(N+1) − 1)·w` worldline K-segments: `(N+1)·2w` in-block
segments plus `N·w` seam connections.  Proven BY INDUCTION, NO `native_decide`. -/
theorem replicate_zMerge_physWorldlineSegs (w N : Nat) :
    physWorldlineSegs (weldChain 3 (zChainConn w) (List.replicate (N + 1) (zMerge w)))
      = (3 * (N + 1) - 1) * w := by
  induction N with
  | zero =>
    show physWorldlineSegs (weldChain 3 (zChainConn w) [zMerge w]) = _
    show physWorldlineSegs (zMerge w) = _
    rw [zMerge_physWorldlineSegs]
  | succ n ih =>
    have hwc : (weldChain 3 (zChainConn w) (List.replicate (n + 1 + 1) (zMerge w)))
        = weldK 3 (zMerge w) (weldChain 3 (zChainConn w) (List.replicate (n + 1) (zMerge w)))
            (zChainConn w) := by
      rw [show List.replicate (n + 1 + 1) (zMerge w)
            = zMerge w :: List.replicate (n + 1) (zMerge w) from rfl]
      rw [show List.replicate (n + 1) (zMerge w)
            = zMerge w :: List.replicate n (zMerge w) from rfl]
      rfl
    rw [hwc, weldK_physWorldlineSegs _ _ w rfl rfl rfl
      (weldChain_maxI_const (zChainConn w) _ (by simp) w
        (by intro g hg; rw [List.eq_of_mem_replicate hg]; rfl))
      (weldChain_maxJ_const (zChainConn w) _ (by simp)
        (by intro g hg; rw [List.eq_of_mem_replicate hg]; rfl)),
      ih]
    -- 3w + (3(n+1)-1)w = (3(n+2)-1)w
    rw [show 3 * (n + 1) - 1 = 3 * n + 2 by omega,
        show 3 * (n + 1 + 1) - 1 = 3 * n + 5 by omega]
    ring

/-! ### §8a. HETEROGENEOUS worldline formula — ANY merge/idle sequence.

Worldlines are present in BOTH catalog kinds (idle only zeroed the I-SEAM, not the
K-worldlines), and the conn is `zChainConn w` at every weld, so the worldline
count does NOT depend on the merge/idle content — only the LENGTH: `(3m − 1)·w`
for an `m`-gadget chain.  Proven by induction on a list of gadgets that each
present the catalog `ExistK` and the `w × 1 × 3` footprint. -/

/-- For a `w × 1 × 3` gadget, `physWorldlineSegs g = cubeCount g.ExistK w 1 3`. -/
theorem physWorldlineSegs_w_1_3 (g : LaSre) (w : Nat)
    (hi : g.maxI = w) (hj : g.maxJ = 1) (hk : g.maxK = 3) :
    physWorldlineSegs g = cubeCount g.ExistK w 1 3 := by
  rw [physWorldlineSegs, hi, hj, hk]

/-- A catalog-`ExistK` `w × 1 × 3` gadget carries exactly `2w` worldline segments. -/
theorem worldlineSegs_of_catalog (g : LaSre) (w : Nat)
    (hi : g.maxI = w) (hj : g.maxJ = 1) (hk : g.maxK = 3)
    (hK : g.ExistK = (zMerge w).ExistK) :
    physWorldlineSegs g = 2 * w := by
  rw [physWorldlineSegs_w_1_3 g w hi hj hk, hK, ← physWorldlineSegs_w_1_3 (zMerge w) w rfl rfl rfl,
    zMerge_physWorldlineSegs]

/-- Generic worldline chain count for any nonempty list of width-`w` gadgets that
all share the catalog `ExistK` (welded by `zChainConn w`): `(3·len − 1)·w`. -/
theorem weldChain_physWorldlineSegs (w : Nat) (gs : List LaSre) (hgs : gs ≠ [])
    (hK : ∀ g ∈ gs, g.ExistK = (zMerge w).ExistK)
    (hi : ∀ g ∈ gs, g.maxI = w) (hj : ∀ g ∈ gs, g.maxJ = 1) (hk : ∀ g ∈ gs, g.maxK = 3) :
    physWorldlineSegs (weldChain 3 (zChainConn w) gs) = (3 * gs.length - 1) * w := by
  induction gs with
  | nil => exact absurd rfl hgs
  | cons g rest ih =>
    cases rest with
    | nil =>
      show physWorldlineSegs g = _
      rw [worldlineSegs_of_catalog g w (hi g (by simp)) (hj g (by simp)) (hk g (by simp))
          (hK g (by simp))]
      simp
    | cons g2 rest' =>
      show physWorldlineSegs (weldK 3 g (weldChain 3 (zChainConn w) (g2 :: rest'))
        (zChainConn w)) = _
      have hBi : (weldChain 3 (zChainConn w) (g2 :: rest')).maxI = w :=
        weldChain_maxI_const _ _ (by simp) w (fun gg hgg => hi gg (by simp [hgg]))
      have hBj : (weldChain 3 (zChainConn w) (g2 :: rest')).maxJ = 1 :=
        weldChain_maxJ_const _ _ (by simp) (fun gg hgg => hj gg (by simp [hgg]))
      rw [weldK_physWorldlineSegs g _ w (hK g (by simp)) (hi g (by simp)) (hj g (by simp))
        hBi hBj,
        ih (by simp) (fun gg hgg => hK gg (by simp [hgg])) (fun gg hgg => hi gg (by simp [hgg]))
          (fun gg hgg => hj gg (by simp [hgg])) (fun gg hgg => hk gg (by simp [hgg]))]
      simp only [List.length_cons]
      rw [show 3 * (rest'.length + 1) - 1 = 3 * rest'.length + 2 by omega,
          show 3 * (rest'.length + 1 + 1) - 1 = 3 * rest'.length + 5 by omega]
      ring

/-- **★ HETEROGENEOUS WORLDLINE COUNT = FORMULA ★** — for ANY merge/idle sequence
`ks : List Bool`, the welded catalog chain carries EXACTLY `(3·ks.length − 1)·w`
worldline K-segments — INDEPENDENT of the merge/idle content (worldlines persist
through both kinds).  Proven by induction, NO `native_decide`. -/
theorem kindChain_physWorldlineSegs (w : Nat) (ks : List Bool) (hk : ks ≠ []) :
    physWorldlineSegs (weldChain 3 (zChainConn w) ((ks.map (kindEntry w)).map (·.g)))
      = (3 * ks.length - 1) * w := by
  rw [weldChain_physWorldlineSegs w _
    (by simp only [ne_eq, List.map_eq_nil_iff]; exact hk)
    (by intro g hg; simp only [List.mem_map] at hg; obtain ⟨e, he, rfl⟩ := hg
        obtain ⟨b, _, rfl⟩ := he; cases b <;> rfl)
    (by intro g hg; simp only [List.mem_map] at hg; obtain ⟨e, he, rfl⟩ := hg
        obtain ⟨b, _, rfl⟩ := he; exact kindEntry_g_maxI w b)
    (by intro g hg; simp only [List.mem_map] at hg; obtain ⟨e, he, rfl⟩ := hg
        obtain ⟨b, _, rfl⟩ := he; exact kindEntry_g_maxJ w b)
    (by intro g hg; simp only [List.mem_map] at hg; obtain ⟨e, he, rfl⟩ := hg
        obtain ⟨b, _, rfl⟩ := he; exact kindEntry_g_maxK w b)]
  simp only [List.length_map]

end FormalRV.QEC.LaSre
