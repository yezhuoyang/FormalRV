/-
  FormalRV.PauliRotation.Compiler.Scheduler
  ────────────────────────────────
  THE VERIFIED PARALLELIZER: greedy ASAP (as-soon-as-possible) scheduling of
  a rotation sequence into parallel layers, with full semantic preservation.

  ## The parallelism target (John's question 1)

  The optimum reachable by commutation alone is the CRITICAL PATH of the
  anticommutation DAG (nodes = rotations; edge `i → j` for `i < j` iff the
  axes anticommute): no valid layering can be shallower than the longest
  anticommuting chain, and greedy ASAP attains it — each rotation settles in
  the EARLIEST layer such that (a) it commutes with that whole layer and
  (b) it commutes with everything scheduled after it (so dragging it back is
  a chain of legal exchanges).

  ## The mechanical correctness recipe (John's question 2)

  One micro-lemma + one macro-lemma + induction — the standard verified-
  scheduler pattern (same shape as list-scheduling proofs in verified
  compilers):

    1. EXCHANGE (`CommBridge.Rot.denote_swap`): adjacent rotations with
       syntactically commuting axes (`commF`) swap, semantics unchanged.
    2. INSERTION (`insertASAP_denote`): if `r` commutes with everything
       after its landing spot, inserting it there equals appending it at the
       end — proved by lifting EXCHANGE through products
       (`Commute.list_prod_right`).
    3. INDUCTION (`scheduleList_denote`): fold INSERTION over the input.

  Nothing here is semantically ad hoc: every step is the exchange lemma,
  applied through the algebra of `Commute`.

  Counters are preserved on the nose (`scheduleList_countAngle` — scheduling
  moves rotations, never makes or destroys them), well-formedness is
  preserved, and depth never exceeds the sequential length.
-/
import FormalRV.PauliRotation.Semantics.CommBridge
import FormalRV.PauliRotation.Compiler.GateDictionary
import FormalRV.Resource.RotationCount

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource

/-! ## §1. The scheduler. -/

/-- `r` commutes with every rotation of the layer (syntactic test; guard
orientation `commF s.axis r.axis` so the bridge applies with `s` canonical). -/
def passes (r : Rot) (L : RotLayer) : Bool :=
  L.all (fun s => commF s.axis r.axis)

/-- `r` commutes with every rotation of every layer. -/
def passesAll (r : Rot) (p : RotProg) : Bool := p.all (passes r)

/-- **ASAP insertion**: `r` settles in the first layer it commutes with,
provided it also commutes with everything after (the legality of dragging it
back); otherwise it walks right; if nothing accepts it, a fresh layer. -/
def insertASAP (r : Rot) : RotProg → RotProg
  | [] => [[r]]
  | L :: rest =>
      if passes r L && passesAll r rest
      then (L ++ [r]) :: rest
      else L :: insertASAP r rest

/-- **The scheduler**: fold a rotation sequence (execution order) into
parallel layers. -/
def scheduleList (rs : List Rot) : RotProg :=
  rs.foldl (fun acc r => insertASAP r acc) []

/-- Sequential denotation of a rotation list (the naive gate-by-gate
compilation's meaning; later rotations act on the left). -/
noncomputable def seqDenote (n : Nat) : List Rot → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | []      => 1
  | r :: rs => seqDenote n rs * Rot.denote n r

/-- A singleton-layer program means exactly the sequence. -/
theorem denote_singletons (n : Nat) (rs : List Rot) :
    RotProg.denote n (rs.map (fun r => [r])) = seqDenote n rs := by
  induction rs with
  | nil => rfl
  | cons r t ih =>
      show RotProg.denote n (t.map _) * RotLayer.denote n [r]
          = seqDenote n t * Rot.denote n r
      rw [ih]
      congr 1
      simp [RotLayer.denote]

/-! ## §2. Commutation lifts (the exchange lemma through products). -/

/-- Per-rotation side conditions the bridge needs: canonical axis, in width. -/
def RotsBounded (n : Nat) (p : RotProg) : Prop :=
  ∀ L ∈ p, ∀ s ∈ L, sortedStrict s.axis = true ∧ PauliProduct.width s.axis ≤ n

theorem commute_denote_layer (n : Nat) (r : Rot) (L : RotLayer)
    (hb : ∀ s ∈ L, sortedStrict s.axis = true ∧ PauliProduct.width s.axis ≤ n)
    (hp : passes r L = true) :
    Commute (Rot.denote n r) (RotLayer.denote n L) := by
  unfold RotLayer.denote
  apply Commute.list_prod_right
  intro y hy
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
  have hcomm := List.all_eq_true.mp hp s hs
  exact Rot.denote_swap n r s (hb s hs).1 (hb s hs).2 hcomm

theorem commute_denote_prog (n : Nat) (r : Rot) (p : RotProg)
    (hb : RotsBounded n p) (hp : passesAll r p = true) :
    Commute (Rot.denote n r) (RotProg.denote n p) := by
  induction p with
  | nil => exact Commute.one_right _
  | cons L t ih =>
      simp only [passesAll, List.all_cons, Bool.and_eq_true] at hp
      show Commute _ (RotProg.denote n t * RotLayer.denote n L)
      exact Commute.mul_right
        (ih (fun M hM => hb M (List.mem_cons_of_mem _ hM))
          (by simp [passesAll, hp.2]))
        (commute_denote_layer n r L (hb L (List.mem_cons_self ..)) hp.1)

/-! ## §3. The insertion lemma (the macro-step). -/

/-- **Insertion is append, semantically**: wherever ASAP lands `r`, the
program denotes exactly `⟦r⟧ · ⟦p⟧` — i.e. the same as running `p` then `r`. -/
theorem insertASAP_denote (n : Nat) (r : Rot) (p : RotProg)
    (hb : RotsBounded n p) :
    RotProg.denote n (insertASAP r p) = Rot.denote n r * RotProg.denote n p := by
  induction p with
  | nil =>
      show RotProg.denote n [] * RotLayer.denote n [r] = _
      simp [RotLayer.denote, RotProg.denote]
  | cons L rest ih =>
      by_cases hc : (passes r L && passesAll r rest) = true
      · rw [show insertASAP r (L :: rest) = (L ++ [r]) :: rest from by
            simp [insertASAP, hc]]
        show RotProg.denote n rest * RotLayer.denote n (L ++ [r]) = _
        have hlay : RotLayer.denote n (L ++ [r])
            = RotLayer.denote n L * Rot.denote n r := by
          simp [RotLayer.denote]
        simp only [Bool.and_eq_true] at hc
        have c1 : Commute (Rot.denote n r) (RotProg.denote n rest) :=
          commute_denote_prog n r rest
            (fun M hM => hb M (List.mem_cons_of_mem _ hM)) hc.2
        have c2 : Commute (Rot.denote n r) (RotLayer.denote n L) :=
          commute_denote_layer n r L (hb L (List.mem_cons_self ..)) hc.1
        rw [hlay, ← Matrix.mul_assoc]
        exact (Commute.mul_right c1 c2).eq.symm
      · rw [show insertASAP r (L :: rest) = L :: insertASAP r rest from by
            simp [insertASAP, hc]]
        show RotProg.denote n (insertASAP r rest) * RotLayer.denote n L = _
        rw [ih (fun M hM => hb M (List.mem_cons_of_mem _ hM)), Matrix.mul_assoc]
        rfl

theorem insertASAP_bounded (n : Nat) (r : Rot)
    (hr : sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ n)
    (p : RotProg) (hb : RotsBounded n p) : RotsBounded n (insertASAP r p) := by
  induction p with
  | nil =>
      intro L hL s hs
      simp only [insertASAP, List.mem_cons, List.not_mem_nil, or_false] at hL
      subst hL
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      exact hr
  | cons L rest ih =>
      intro M hM s hs
      by_cases hc : (passes r L && passesAll r rest) = true
      · rw [show insertASAP r (L :: rest) = (L ++ [r]) :: rest from by
            simp [insertASAP, hc]] at hM
        rcases List.mem_cons.mp hM with rfl | hM
        · rcases List.mem_append.mp hs with hs | hs
          · exact hb L (List.mem_cons_self ..) s hs
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
            subst hs; exact hr
        · exact hb M (List.mem_cons_of_mem _ hM) s hs
      · rw [show insertASAP r (L :: rest) = L :: insertASAP r rest from by
            simp [insertASAP, hc]] at hM
        rcases List.mem_cons.mp hM with rfl | hM
        · exact hb M (List.mem_cons_self ..) s hs
        · exact ih (fun K hK => hb K (List.mem_cons_of_mem _ hK)) M hM s hs

/-! ## §4. The scheduler theorems. -/

private theorem scheduleList_denote_aux (n : Nat) (rs : List Rot) (acc : RotProg)
    (hrs : ∀ r ∈ rs, sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ n)
    (hacc : RotsBounded n acc) :
    RotProg.denote n (rs.foldl (fun a r => insertASAP r a) acc)
      = seqDenote n rs * RotProg.denote n acc := by
  induction rs generalizing acc with
  | nil => show RotProg.denote n acc = 1 * _; rw [Matrix.one_mul]
  | cons r t ih =>
      show RotProg.denote n (t.foldl _ (insertASAP r acc)) = _
      rw [ih (insertASAP r acc)
            (fun s hs => hrs s (List.mem_cons_of_mem _ hs))
            (insertASAP_bounded n r (hrs r (List.mem_cons_self ..)) acc hacc),
          insertASAP_denote n r acc hacc, ← Matrix.mul_assoc]
      rfl

/-- **THE SCHEDULER CORRECTNESS THEOREM**: ASAP parallelization preserves the
denotation exactly — for every rotation sequence (canonical axes, in width),
the layered program means the same operator as the sequence. -/
theorem scheduleList_denote (n : Nat) (rs : List Rot)
    (hrs : ∀ r ∈ rs, sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ n) :
    RotProg.denote n (scheduleList rs) = seqDenote n rs := by
  unfold scheduleList
  rw [scheduleList_denote_aux n rs [] hrs (fun L hL => nomatch hL)]
  show seqDenote n rs * 1 = seqDenote n rs
  rw [Matrix.mul_one]

/-- Scheduling never creates or destroys rotations: every angle count is
preserved on the nose. -/
theorem insertASAP_countAngle (a : RAngle) (r : Rot) (p : RotProg) :
    countAngle a (insertASAP r p)
      = countAngle a p + (if r.angle == a then 1 else 0) := by
  induction p with
  | nil => simp [insertASAP, countAngle, countAngleL]
  | cons L rest ih =>
      by_cases hc : (passes r L && passesAll r rest) = true
      · rw [show insertASAP r (L :: rest) = (L ++ [r]) :: rest from by
            simp [insertASAP, hc]]
        show countAngleL a (L ++ [r]) + countAngle a rest = _
        simp only [countAngleL, List.countP_append, List.countP_cons,
          List.countP_nil]
        show List.countP _ L + (0 + _) + countAngle a rest
            = List.countP _ L + countAngle a rest + _
        omega
      · rw [show insertASAP r (L :: rest) = L :: insertASAP r rest from by
            simp [insertASAP, hc]]
        show countAngleL a L + countAngle a (insertASAP r rest) = _
        rw [ih]
        show countAngleL a L + (countAngle a rest + _)
            = countAngleL a L + countAngle a rest + _
        omega

theorem scheduleList_countAngle (a : RAngle) (rs : List Rot) :
    countAngle a (scheduleList rs) = rs.countP (fun r => r.angle == a) := by
  suffices h : ∀ acc, countAngle a (rs.foldl (fun p r => insertASAP r p) acc)
      = countAngle a acc + rs.countP (fun r => r.angle == a) by
    have := h []
    simpa [scheduleList, countAngle] using this
  induction rs with
  | nil => intro acc; simp
  | cons r t ih =>
      intro acc
      show countAngle a (t.foldl _ (insertASAP r acc)) = _
      rw [ih, insertASAP_countAngle, List.countP_cons]
      omega

/-- In particular the T-count survives parallelization untouched. -/
theorem scheduleList_countPi8 (rs : List Rot) :
    countPi8 (scheduleList rs) = rs.countP (fun r => r.angle == RAngle.piEighth) :=
  scheduleList_countAngle .piEighth rs

/-- Insertion adds at most one layer … -/
theorem insertASAP_depth_le (r : Rot) (p : RotProg) :
    rotDepth (insertASAP r p) ≤ rotDepth p + 1 := by
  induction p with
  | nil => simp [insertASAP, rotDepth]
  | cons L rest ih =>
      by_cases hc : (passes r L && passesAll r rest) = true
      · rw [show insertASAP r (L :: rest) = (L ++ [r]) :: rest from by
            simp [insertASAP, hc]]
        simp [rotDepth]
      · rw [show insertASAP r (L :: rest) = L :: insertASAP r rest from by
            simp [insertASAP, hc]]
        simp only [rotDepth, List.length_cons] at ih ⊢
        omega

/-- … so the parallel depth never exceeds the sequential length. -/
theorem scheduleList_depth_le (rs : List Rot) :
    rotDepth (scheduleList rs) ≤ rs.length := by
  suffices h : ∀ acc, rotDepth (rs.foldl (fun p r => insertASAP r p) acc)
      ≤ rotDepth acc + rs.length by
    simpa [scheduleList, rotDepth] using h []
  induction rs with
  | nil => intro acc; simp
  | cons r t ih =>
      intro acc
      show rotDepth (t.foldl _ (insertASAP r acc)) ≤ _
      calc rotDepth (t.foldl (fun p r => insertASAP r p) (insertASAP r acc))
          ≤ rotDepth (insertASAP r acc) + t.length := ih (insertASAP r acc)
        _ ≤ (rotDepth acc + 1) + t.length := by
              have := insertASAP_depth_le r acc; omega
        _ = rotDepth acc + (r :: t).length := by simp; omega

/-! ## §5. The scheduler in action (kernel-checked). -/

open FormalRV.PPM.Prog in
/-- The serialized CCZ (depth 7) reschedules to EXACTLY the single parallel
layer — the optimizer discovers `cczLayer` on its own. -/
example : scheduleList ((cczGate 0 1 2).flatten) = cczLayer 0 1 2 := by decide

/-- The serialized CNOT (depth 3) reschedules to one layer. -/
example : rotDepth (scheduleList ((cnotGate 0 1).flatten)) = 1 := by decide

/-- Anticommuting rotations stay sequential — no false parallelism. -/
example : rotDepth (scheduleList
    [⟨false, .piEighth, [⟨0, .x⟩]⟩, ⟨false, .piEighth, [⟨0, .z⟩]⟩]) = 2 := by decide

/-- Two CCZs on disjoint triples: 14 rotations, depth 1. -/
example : rotDepth (scheduleList
    ((cczGate 0 1 2).flatten ++ (cczGate 3 4 5).flatten)) = 1 := by decide

end FormalRV.PauliRotation
