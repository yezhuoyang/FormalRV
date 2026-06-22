/-
  FormalRV.PauliRotation.Compiler.SchedulerK
  ─────────────────────────────────
  **THE HARDWARE-BOUNDED COMPILER: ≤ K joint Pauli rotations per layer.**

  Lattice-surgery hardware executes at most `K` joint Pauli measurements
  in parallel (QianXu-style: `K = 5`).  `scheduleListK K` is the greedy
  ASAP parallelizer CONSTRAINED to layers of at most `K` rotations — a
  verified COMPILER from arbitrary rotation sequences to hardware-valid
  layered programs:

    • `scheduleListK_denote`     — the layered program denotes EXACTLY the
                                   input sequence (matrix equality);
    • `scheduleListK_layers_le`  — every layer has ≤ K rotations (validity
                                   against the hardware bound);
    • `scheduleListK_countAngle` — per-angle counts on the nose (T-count
                                   survives compilation);
    • `countRot_le_K_mul_depth`  — THE UNIVERSAL LOWER BOUND: any K-valid
                                   program needs ≥ ⌈N/K⌉ layers;
    • `scheduleListK_depth_optimal_of_commuting` — for PAIRWISE-COMMUTING
                                   sequences (phase polynomials: CCZ/adder
                                   layers) the compiler ACHIEVES ⌈N/K⌉ —
                                   verified optimality, not heuristics.

  Correct-BY-CONSTRUCTION: unlike the certificate lane (Optimizer.lean),
  this compiler's output needs no per-run checking — one theorem covers
  every invocation.
-/
import FormalRV.PauliRotation.Compiler.Scheduler

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource
open Matrix

/-! ## §1. The K-bounded insertion. -/

/-- ASAP insertion with the hardware cap: a layer accepts only if it has
ROOM (`< K`) and `r` commutes with it and with everything after. -/
def insertASAPK (K : Nat) (r : Rot) : RotProg → RotProg
  | [] => [[r]]
  | L :: rest =>
      if decide (L.length < K) && passes r L && passesAll r rest
      then (L ++ [r]) :: rest
      else L :: insertASAPK K r rest

/-- **The K-bounded compiler**: fold the sequence through K-capped ASAP
insertion. -/
def scheduleListK (K : Nat) (rs : List Rot) : RotProg :=
  rs.foldl (fun acc r => insertASAPK K r acc) []

/-! ## §2. Semantic preservation (mirrors the unbounded scheduler). -/

theorem insertASAPK_denote (K : Nat) (n : Nat) (r : Rot) (p : RotProg)
    (hb : RotsBounded n p) :
    RotProg.denote n (insertASAPK K r p)
      = Rot.denote n r * RotProg.denote n p := by
  induction p with
  | nil =>
      show RotProg.denote n [[r]] = _
      show RotProg.denote n [] * RotLayer.denote n [r] = _
      simp [RotLayer.denote, RotProg.denote]
  | cons L rest ih =>
      show RotProg.denote n
          (if decide (L.length < K) && passes r L && passesAll r rest
           then (L ++ [r]) :: rest
           else L :: insertASAPK K r rest) = _
      by_cases hpass : (decide (L.length < K) && passes r L
          && passesAll r rest) = true
      · rw [if_pos hpass]
        simp only [Bool.and_eq_true] at hpass
        show RotProg.denote n rest * RotLayer.denote n (L ++ [r])
            = Rot.denote n r * (RotProg.denote n rest * RotLayer.denote n L)
        have hL : RotLayer.denote n (L ++ [r])
            = RotLayer.denote n L * Rot.denote n r := by
          show ((L ++ [r]).map (Rot.denote n)).prod = _
          rw [List.map_append, List.prod_append]
          simp [RotLayer.denote]
        rw [hL]
        have hcomm : Commute (Rot.denote n r) (RotProg.denote n rest) :=
          commute_denote_prog n r rest
            (fun L' hL' s hs => hb L' (List.mem_cons_of_mem _ hL') s hs)
            hpass.2
        have hcommL : Commute (Rot.denote n r) (RotLayer.denote n L) :=
          commute_denote_layer n r L
            (fun s hs => hb L (List.mem_cons_self) s hs) hpass.1.2
        calc RotProg.denote n rest * (RotLayer.denote n L * Rot.denote n r)
            = RotProg.denote n rest
                * (Rot.denote n r * RotLayer.denote n L) := by
              rw [hcommL.eq]
          _ = (RotProg.denote n rest * Rot.denote n r)
                * RotLayer.denote n L := by
              rw [Matrix.mul_assoc]
          _ = (Rot.denote n r * RotProg.denote n rest)
                * RotLayer.denote n L := by
              rw [hcomm.eq]
          _ = Rot.denote n r
                * (RotProg.denote n rest * RotLayer.denote n L) := by
              rw [Matrix.mul_assoc]
      · rw [if_neg hpass]
        show RotProg.denote n (insertASAPK K r rest) * RotLayer.denote n L
            = Rot.denote n r
                * (RotProg.denote n rest * RotLayer.denote n L)
        rw [ih (fun L' hL' s hs => hb L' (List.mem_cons_of_mem _ hL') s hs),
            Matrix.mul_assoc]

theorem insertASAPK_bounded (K n : Nat) (r : Rot)
    (hr : sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ n)
    (p : RotProg) (hb : RotsBounded n p) :
    RotsBounded n (insertASAPK K r p) := by
  induction p with
  | nil =>
      intro L hL s hs
      simp only [insertASAPK, List.mem_cons, List.not_mem_nil, or_false]
        at hL
      subst hL
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      exact hr
  | cons L rest ih =>
      intro L' hL' s hs
      unfold insertASAPK at hL'
      split at hL'
      · rcases List.mem_cons.mp hL' with rfl | hmem
        · rcases List.mem_append.mp hs with hsl | hsr
          · exact hb L (List.mem_cons_self) s hsl
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hsr
            subst hsr
            exact hr
        · exact hb L' (List.mem_cons_of_mem _ hmem) s hs
      · rcases List.mem_cons.mp hL' with rfl | hmem
        · exact hb L' (List.mem_cons_self) s hs
        · exact ih (fun L'' h'' s' hs' =>
            hb L'' (List.mem_cons_of_mem _ h'') s' hs') L' hmem s hs

private theorem scheduleListK_denote_aux (K n : Nat) :
    ∀ (rs : List Rot) (acc : RotProg),
      (∀ r ∈ rs, sortedStrict r.axis = true
        ∧ PauliProduct.width r.axis ≤ n) →
      RotsBounded n acc →
      RotProg.denote n (rs.foldl (fun a r => insertASAPK K r a) acc)
        = seqDenote n rs * RotProg.denote n acc
  | [], acc, _, _ => by
      show RotProg.denote n acc = seqDenote n [] * RotProg.denote n acc
      show RotProg.denote n acc = 1 * RotProg.denote n acc
      rw [Matrix.one_mul]
  | r :: rs, acc, hrs, hacc => by
      show RotProg.denote n
          (rs.foldl (fun a r => insertASAPK K r a) (insertASAPK K r acc))
        = seqDenote n (r :: rs) * RotProg.denote n acc
      rw [scheduleListK_denote_aux K n rs (insertASAPK K r acc)
            (fun s hs => hrs s (List.mem_cons_of_mem _ hs))
            (insertASAPK_bounded K n r (hrs r List.mem_cons_self) acc hacc),
          insertASAPK_denote K n r acc hacc]
      show seqDenote n rs * (Rot.denote n r * RotProg.denote n acc)
          = (seqDenote n rs * Rot.denote n r) * RotProg.denote n acc
      rw [Matrix.mul_assoc]

/-- **SEMANTIC PRESERVATION**: the K-bounded compiler's layered program
denotes EXACTLY the input sequence. -/
theorem scheduleListK_denote (K n : Nat) (rs : List Rot)
    (hrs : ∀ r ∈ rs, sortedStrict r.axis = true
      ∧ PauliProduct.width r.axis ≤ n) :
    RotProg.denote n (scheduleListK K rs) = seqDenote n rs := by
  unfold scheduleListK
  rw [scheduleListK_denote_aux K n rs [] hrs (fun L hL => by cases hL)]
  show seqDenote n rs * 1 = seqDenote n rs
  rw [Matrix.mul_one]

/-! ## §3. Hardware validity: every layer within the cap. -/

/-- Layer sizes of a program all within `K`. -/
def layersLE (K : Nat) (p : RotProg) : Bool :=
  p.all (fun L => decide (L.length ≤ K))

theorem insertASAPK_layers (K : Nat) (hK : 1 ≤ K) (r : Rot) (p : RotProg)
    (hp : layersLE K p = true) :
    layersLE K (insertASAPK K r p) = true := by
  induction p with
  | nil =>
      simp [insertASAPK, layersLE]
      omega
  | cons L rest ih =>
      simp only [layersLE, List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] at hp
      show layersLE K
          (if _ then (L ++ [r]) :: rest else L :: insertASAPK K r rest)
        = true
      split
      next hpass =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hpass
        simp only [layersLE, List.all_cons, Bool.and_eq_true,
          decide_eq_true_eq, List.length_append, List.length_cons,
          List.length_nil]
        constructor
        · omega
        · exact hp.2
      next =>
        simp only [layersLE, List.all_cons, Bool.and_eq_true,
          decide_eq_true_eq]
        exact ⟨hp.1, ih hp.2⟩

/-- **HARDWARE VALIDITY**: every layer of the compiled program has at most
`K` rotations. -/
theorem scheduleListK_layers (K : Nat) (hK : 1 ≤ K) (rs : List Rot) :
    layersLE K (scheduleListK K rs) = true := by
  unfold scheduleListK
  generalize hacc : ([] : RotProg) = acc
  have hacc' : layersLE K acc = true := by
    rw [← hacc]
    rfl
  clear hacc
  induction rs generalizing acc with
  | nil => exact hacc'
  | cons r rs ih =>
      exact ih (insertASAPK K r acc) (insertASAPK_layers K hK r acc hacc')

/-! ## §4. Counts on the nose. -/

theorem insertASAPK_countAngle (K : Nat) (a : RAngle) (r : Rot)
    (p : RotProg) :
    countAngle a (insertASAPK K r p)
      = countAngle a p + (if r.angle == a then 1 else 0) := by
  induction p with
  | nil =>
      simp [insertASAPK, countAngle, countAngleL, List.countP_cons]
  | cons L rest ih =>
      show countAngle a
          (if _ then (L ++ [r]) :: rest else L :: insertASAPK K r rest) = _
      split
      · show countAngleL a (L ++ [r]) + countAngle a rest = _
        unfold countAngleL
        rw [List.countP_append]
        show countAngleL a L + _ + countAngle a rest = _
        simp only [List.countP_cons, List.countP_nil]
        show countAngleL a L + (0 + _) + countAngle a rest
            = countAngleL a L + countAngle a rest + _
        omega
      · show countAngleL a L + countAngle a (insertASAPK K r rest) = _
        rw [ih]
        show _ = countAngleL a L + countAngle a rest + _
        omega

private theorem foldl_countAngle (K : Nat) (a : RAngle) :
    ∀ (rs : List Rot) (acc : RotProg),
      countAngle a (rs.foldl (fun acc r => insertASAPK K r acc) acc)
        = countAngle a acc + rs.countP (fun r => r.angle == a)
  | [], acc => by simp
  | r :: rs, acc => by
      show countAngle a
          (rs.foldl (fun acc r => insertASAPK K r acc) (insertASAPK K r acc))
        = _
      rw [foldl_countAngle K a rs (insertASAPK K r acc),
          insertASAPK_countAngle, List.countP_cons]
      omega

/-- **Per-angle counts survive K-bounded compilation on the nose.** -/
theorem scheduleListK_countAngle (K : Nat) (a : RAngle) (rs : List Rot) :
    countAngle a (scheduleListK K rs)
      = rs.countP (fun r => r.angle == a) := by
  unfold scheduleListK
  rw [foldl_countAngle K a rs []]
  show 0 + _ = _
  omega

/-- **The T-count survives K-bounded compilation.** -/
theorem scheduleListK_countPi8 (K : Nat) (rs : List Rot) :
    countPi8 (scheduleListK K rs)
      = rs.countP (fun r => r.angle == RAngle.piEighth) :=
  scheduleListK_countAngle K .piEighth rs

/-! ## §5. THE OPTIMALITY SANDWICH. -/

/-- Total rotations of a program = sum of layer sizes. -/
theorem countRot_eq_sum (p : RotProg) :
    countRot p = (p.map List.length).sum := by
  induction p with
  | nil => rfl
  | cons L rest ih =>
      show countRotL L + countRot rest = L.length + (rest.map _).sum
      rw [ih]
      rfl

/-- **THE UNIVERSAL LOWER BOUND**: any K-valid layered program packs at
most `K` rotations per layer, so `N ≤ K · depth` — i.e. depth ≥ ⌈N/K⌉ for
EVERY compiler respecting the hardware cap. -/
theorem countRot_le_K_mul_depth (K : Nat) (p : RotProg)
    (hv : layersLE K p = true) :
    countRot p ≤ K * rotDepth p := by
  induction p with
  | nil => simp [countRot, rotDepth]
  | cons L rest ih =>
      simp only [layersLE, List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] at hv
      obtain ⟨h1, h2⟩ := hv
      have ht := ih h2
      show L.length + countRot rest ≤ K * (rest.length + 1)
      unfold rotDepth at ht
      rw [Nat.mul_succ]
      omega

/-- The number of layers the greedy K-compiler produces never exceeds
the sequence length. -/
theorem scheduleListK_depth_le (K : Nat) (rs : List Rot) :
    rotDepth (scheduleListK K rs) ≤ rs.length := by
  unfold scheduleListK
  generalize hacc : ([] : RotProg) = acc
  have hlen : ∀ (r : Rot) (p : RotProg),
      rotDepth (insertASAPK K r p) ≤ rotDepth p + 1 := by
    intro r p
    induction p with
    | nil => simp [insertASAPK, rotDepth]
    | cons L rest ih =>
        show rotDepth (if _ then (L ++ [r]) :: rest
            else L :: insertASAPK K r rest) ≤ _
        split
        · simp [rotDepth]
        · show (insertASAPK K r rest).length + 1 ≤ rest.length + 1 + 1
          have := ih
          unfold rotDepth at this
          omega
  have hgen : ∀ (rs : List Rot) (acc : RotProg),
      rotDepth (rs.foldl (fun a r => insertASAPK K r a) acc)
        ≤ rotDepth acc + rs.length := by
    intro rs
    induction rs with
    | nil => intro acc; simp
    | cons r t ih =>
        intro acc
        show rotDepth (t.foldl _ (insertASAPK K r acc)) ≤ _
        have h1 := ih (insertASAPK K r acc)
        have h2 := hlen r acc
        show rotDepth (t.foldl _ (insertASAPK K r acc))
            ≤ rotDepth acc + (t.length + 1)
        omega
  have := hgen rs acc
  rw [← hacc] at this
  have h0 : rotDepth ([] : RotProg) = 0 := rfl
  rw [← hacc]
  omega

/-! ## §6. VERIFIED OPTIMALITY for commuting sequences. -/

theorem countRot_insertASAPK (K : Nat) (r : Rot) (p : RotProg) :
    countRot (insertASAPK K r p) = countRot p + 1 := by
  induction p with
  | nil => rfl
  | cons L rest ih =>
      show countRot (if _ then (L ++ [r]) :: rest
          else L :: insertASAPK K r rest) = _
      split
      · show countRotL (L ++ [r]) + countRot rest = _
        show (L ++ [r]).length + countRot rest
            = L.length + countRot rest + 1
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · show countRotL L + countRot (insertASAPK K r rest) = _
        rw [ih]
        show L.length + (countRot rest + 1) = L.length + countRot rest + 1
        omega

theorem countRot_scheduleListK (K : Nat) (rs : List Rot) :
    countRot (scheduleListK K rs) = rs.length := by
  unfold scheduleListK
  have hgen : ∀ (rs : List Rot) (acc : RotProg),
      countRot (rs.foldl (fun a r => insertASAPK K r a) acc)
        = countRot acc + rs.length := by
    intro rs
    induction rs with
    | nil => intro acc; simp
    | cons r t ih =>
        intro acc
        show countRot (t.foldl _ (insertASAPK K r acc)) = _
        rw [ih (insertASAPK K r acc), countRot_insertASAPK]
        show countRot acc + 1 + t.length = countRot acc + (t.length + 1)
        omega
  rw [hgen rs []]
  show 0 + rs.length = rs.length
  omega

/-- The greedy-fill shape: every layer FULL (`= K`) except possibly the
last, which is nonempty and within the cap. -/
def packed (K : Nat) : RotProg → Bool
  | [] => true
  | [L] => decide (1 ≤ L.length) && decide (L.length ≤ K)
  | L :: rest => decide (L.length = K) && packed K rest

/-- Every element placed by K-bounded insertion is an old element or the
inserted rotation. -/
theorem insertASAPK_mem (K : Nat) (r : Rot) :
    ∀ (p : RotProg) (L : RotLayer) (s : Rot),
      L ∈ insertASAPK K r p → s ∈ L →
      (∃ L' ∈ p, s ∈ L') ∨ s = r := by
  intro p
  induction p with
  | nil =>
      intro L s hL hs
      simp only [insertASAPK, List.mem_cons, List.not_mem_nil, or_false]
        at hL
      subst hL
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      right
      exact hs
  | cons L0 rest ih =>
      intro L s hL hs
      unfold insertASAPK at hL
      split at hL
      · rcases List.mem_cons.mp hL with rfl | hmem
        · rcases List.mem_append.mp hs with hsl | hsr
          · exact Or.inl ⟨L0, List.mem_cons_self, hsl⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hsr
            exact Or.inr hsr
        · exact Or.inl ⟨L, List.mem_cons_of_mem _ hmem, hs⟩
      · rcases List.mem_cons.mp hL with rfl | hmem
        · exact Or.inl ⟨L, List.mem_cons_self, hs⟩
        · rcases ih L s hmem hs with ⟨L', hL', hs'⟩ | hr
          · exact Or.inl ⟨L', List.mem_cons_of_mem _ hL', hs'⟩
          · exact Or.inr hr

theorem insertASAPK_ne_nil (K : Nat) (r : Rot) :
    ∀ (p : RotProg), insertASAPK K r p ≠ []
  | [] => by simp [insertASAPK]
  | L :: rest => by
      unfold insertASAPK
      split <;> simp

/-- **The greedy-fill lemma**: when the inserted rotation commutes with
everything placed, K-bounded insertion preserves the packed shape. -/
theorem insertASAPK_packed (K : Nat) (hK : 1 ≤ K) (r : Rot) :
    ∀ (acc : RotProg),
      (∀ L ∈ acc, ∀ s ∈ L, commF s.axis r.axis = true) →
      packed K acc = true →
      packed K (insertASAPK K r acc) = true := by
  intro acc
  induction acc with
  | nil =>
      intro _ _
      show packed K [[r]] = true
      simp only [packed, List.length_cons, List.length_nil,
        Bool.and_eq_true, decide_eq_true_eq]
      omega
  | cons L rest ih =>
      intro hcomm hp
      have hpassL : passes r L = true := by
        unfold passes
        rw [List.all_eq_true]
        intro s hs
        exact hcomm L List.mem_cons_self s hs
      have hpassAll : passesAll r rest = true := by
        unfold passesAll
        rw [List.all_eq_true]
        intro L' hL'
        unfold passes
        rw [List.all_eq_true]
        intro s hs
        exact hcomm L' (List.mem_cons_of_mem _ hL') s hs
      cases rest with
      | nil =>
          simp only [packed, Bool.and_eq_true, decide_eq_true_eq] at hp
          show packed K
              (if decide (L.length < K) && passes r L && passesAll r []
               then (L ++ [r]) :: []
               else L :: insertASAPK K r []) = true
          rw [hpassL, hpassAll]
          by_cases hlen : L.length < K
          · rw [if_pos (by simp [hlen])]
            simp only [packed, List.length_append, List.length_cons,
              List.length_nil, Bool.and_eq_true, decide_eq_true_eq]
            omega
          · rw [if_neg (by simp [hlen])]
            show packed K (L :: [[r]]) = true
            simp only [packed, List.length_cons, List.length_nil,
              Bool.and_eq_true, decide_eq_true_eq]
            omega
      | cons L1 rest1 =>
          simp only [packed, Bool.and_eq_true, decide_eq_true_eq] at hp
          show packed K
              (if decide (L.length < K) && passes r L
                  && passesAll r (L1 :: rest1)
               then (L ++ [r]) :: L1 :: rest1
               else L :: insertASAPK K r (L1 :: rest1)) = true
          rw [hpassL, hpassAll]
          rw [if_neg (by simp [hp.1])]
          have hrec := ih
            (fun L' hL' s hs => hcomm L' (List.mem_cons_of_mem _ hL') s hs)
            hp.2
          rcases hX : insertASAPK K r (L1 :: rest1) with _ | ⟨Y, ys⟩
          · exact absurd hX (insertASAPK_ne_nil K r _)
          · rw [hX] at hrec
            show (decide (L.length = K) && packed K (Y :: ys)) = true
            rw [hrec]
            simp [hp.1]

/-- Packed programs have depth EXACTLY ⌈count/K⌉. -/
theorem packed_depth (K : Nat) (hK : 1 ≤ K) :
    ∀ (p : RotProg), packed K p = true →
      rotDepth p = (countRot p + K - 1) / K := by
  intro p
  induction p with
  | nil =>
      intro _
      show 0 = (0 + K - 1) / K
      rw [Nat.div_eq_of_lt (by omega)]
  | cons L rest ih =>
      intro hp
      cases rest with
      | nil =>
          simp only [packed, Bool.and_eq_true, decide_eq_true_eq] at hp
          show 1 = (countRotL L + 0 + K - 1) / K
          show 1 = (L.length + 0 + K - 1) / K
          exact (Nat.div_eq_of_lt_le (by omega) (by omega)).symm
      | cons L1 rest1 =>
          simp only [packed, Bool.and_eq_true, decide_eq_true_eq] at hp
          have ht := ih (by
            show packed K (L1 :: rest1) = true
            exact hp.2)
          show (L1 :: rest1).length + 1
              = (countRotL L + countRot (L1 :: rest1) + K - 1) / K
          rw [show countRotL L + countRot (L1 :: rest1) + K - 1
                = (countRot (L1 :: rest1) + K - 1) + K from by
              show L.length + countRot (L1 :: rest1) + K - 1 = _
              omega,
              Nat.add_div_right _ (by omega : 0 < K)]
          unfold rotDepth at ht
          omega

/-- The pairwise-commuting hypothesis, decidable on the flat sequence
(`a` before `b` ⇒ `commF a.axis b.axis`). -/
def allCommB : List Rot → Bool
  | [] => true
  | r :: t => t.all (fun s => commF r.axis s.axis) && allCommB t

private theorem foldl_packed (K : Nat) (hK : 1 ≤ K) :
    ∀ (rs : List Rot) (acc : RotProg),
      allCommB rs = true →
      (∀ L ∈ acc, ∀ s ∈ L, ∀ r' ∈ rs, commF s.axis r'.axis = true) →
      packed K acc = true →
      packed K (rs.foldl (fun a r => insertASAPK K r a) acc) = true
  | [], _, _, _, hp => hp
  | r :: rs, acc, hcomm, hsub, hp => by
      simp only [allCommB, Bool.and_eq_true, List.all_eq_true] at hcomm
      show packed K
          (rs.foldl (fun a r => insertASAPK K r a) (insertASAPK K r acc))
        = true
      refine foldl_packed K hK rs (insertASAPK K r acc) hcomm.2 ?_ ?_
      · intro L hL s hs r' hr'
        rcases insertASAPK_mem K r acc L s hL hs with ⟨L', hL', hs'⟩ | rfl
        · exact hsub L' hL' s hs' r' (List.mem_cons_of_mem _ hr')
        · exact hcomm.1 r' hr'
      · exact insertASAPK_packed K hK r acc
          (fun L hL s hs => hsub L hL s hs r List.mem_cons_self) hp

/-- **VERIFIED OPTIMALITY (achievability)**: for a pairwise-commuting
sequence — a PHASE POLYNOMIAL, e.g. the CCZ/adder layers of QianXu-style
circuits — the K-bounded compiler achieves depth EXACTLY ⌈N/K⌉. -/
theorem scheduleListK_depth_eq (K : Nat) (hK : 1 ≤ K) (rs : List Rot)
    (hcomm : allCommB rs = true) :
    rotDepth (scheduleListK K rs) = (rs.length + K - 1) / K := by
  have hpacked : packed K (scheduleListK K rs) = true := by
    unfold scheduleListK
    exact foldl_packed K hK rs [] hcomm
      (fun L hL => by cases hL) rfl
  rw [packed_depth K hK _ hpacked, countRot_scheduleListK]

/-- **VERIFIED OPTIMALITY (no compiler can beat it)**: any K-valid layered
program implementing the same rotation count needs at least as many layers
— the ⌈N/K⌉ sandwich closes. -/
theorem scheduleListK_optimal (K : Nat) (hK : 1 ≤ K) (rs : List Rot)
    (hcomm : allCommB rs = true)
    (q : RotProg) (hqv : layersLE K q = true)
    (hqc : countRot q = rs.length) :
    rotDepth (scheduleListK K rs) ≤ rotDepth q := by
  rw [scheduleListK_depth_eq K hK rs hcomm]
  have hlb := countRot_le_K_mul_depth K q hqv
  rw [hqc] at hlb
  calc (rs.length + K - 1) / K
      ≤ (K * rotDepth q + (K - 1)) / K := by
        apply Nat.div_le_div_right
        omega
    _ = rotDepth q + (K - 1) / K := by
        rw [Nat.mul_add_div (by omega : 0 < K)]
    _ = rotDepth q := by
        rw [Nat.div_eq_of_lt (by omega), Nat.add_zero]

end FormalRV.PauliRotation
