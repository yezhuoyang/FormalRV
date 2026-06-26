/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth.Scheduler
  ──────────────────────────────────────────────────────
  Submodule of `ParallelDepth` (split out for per-file compile memory).
  Contains §1–§5: the gate support `supp`, the ASAP scheduler (`tick`/`sched`),
  `maxOver` algebra, the headline disjoint-`seq` law `parallelDepth_seq_disjoint`,
  and the sanity bound `parallelDepth_le_depth`.

  Re-exported VERBATIM from the original `ParallelDepth.lean`; the declarations,
  statements, names, namespace and `open`s are unchanged.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional

namespace FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional

/-! ## §1. Support and the ASAP scheduler. -/

/-- The (syntactic) support of a gate: the list of qubits it touches. -/
def supp : Gate → List Nat
  | Gate.I          => []
  | Gate.X q        => [q]
  | Gate.CX a b     => [a, b]
  | Gate.CCX a b c  => [a, b, c]
  | Gate.seq g₁ g₂  => supp g₁ ++ supp g₂

/-- Advance the ready-time map `s` by scheduling ONE gate acting on `qs`:
    it runs at `τ = 1 + max_{q∈qs} s q`, after which every `q ∈ qs` is ready
    at `τ`; all other qubits keep their old ready-time. -/
def tick (qs : List Nat) (s : Nat → Nat) : Nat → Nat :=
  let τ := (qs.foldl (fun m q => max m (s q)) 0) + 1
  fun x => if x ∈ qs then τ else s x

/-- ASAP schedule: thread the ready-time map through the gate list. -/
def sched : Gate → (Nat → Nat) → (Nat → Nat)
  | Gate.I,          s => s
  | Gate.X q,        s => tick [q] s
  | Gate.CX a b,     s => tick [a, b] s
  | Gate.CCX a b c,  s => tick [a, b, c] s
  | Gate.seq g₁ g₂,  s => sched g₂ (sched g₁ s)

/-- `max` of `f` over a qubit list (fold, identity `0`). -/
def maxOver (qs : List Nat) (f : Nat → Nat) : Nat :=
  qs.foldl (fun m q => max m (f q)) 0

/-- **ASAP critical-path depth.**  Schedule from the all-zero ready map, then
    take the max finish-time over the gate's support. -/
def parallelDepth (g : Gate) : Nat :=
  maxOver (supp g) (sched g (fun _ => 0))

/-! ## §2. `tick` / `sched` frame, monotonicity, locality. -/

/-- Off its qubit set, `tick` leaves the ready-time unchanged. -/
theorem tick_frame (qs : List Nat) (s : Nat → Nat) (x : Nat) (hx : x ∉ qs) :
    tick qs s x = s x := by
  unfold tick; simp [hx]

/-- A `foldl`-max is at least its seed. -/
theorem foldl_max_ge_init (qs : List Nat) (s : Nat → Nat) (init : Nat) :
    init ≤ qs.foldl (fun m q => max m (s q)) init := by
  induction qs generalizing init with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldl_cons]
      exact le_trans (le_max_left init (s a)) (ih (max init (s a)))

/-- The `foldl`-max over `qs` dominates `s x` for every member `x ∈ qs`
    (with any seed `init`). -/
theorem foldl_max_ge_mem (qs : List Nat) (s : Nat → Nat) (x : Nat)
    (hx : x ∈ qs) :
    ∀ init : Nat, s x ≤ qs.foldl (fun m q => max m (s q)) init := by
  induction qs with
  | nil => simp at hx
  | cons a l ih =>
      intro init
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hx with h | h
      · subst h
        exact le_trans (le_max_right init (s x)) (foldl_max_ge_init l s _)
      · exact ih h _

/-- `tick` only increases ready-times. -/
theorem tick_mono (qs : List Nat) (s : Nat → Nat) (x : Nat) :
    s x ≤ tick qs s x := by
  unfold tick
  by_cases hx : x ∈ qs
  · simp only [hx, if_pos]
    have := foldl_max_ge_mem qs s x hx 0
    omega
  · simp [hx]

/-- `sched` only increases ready-times. -/
theorem sched_mono (g : Gate) (s : Nat → Nat) (x : Nat) :
    s x ≤ sched g s x := by
  induction g generalizing s with
  | I => exact le_refl _
  | X q => exact tick_mono _ _ _
  | CX a b => exact tick_mono _ _ _
  | CCX a b c => exact tick_mono _ _ _
  | seq g₁ g₂ ih₁ ih₂ => exact le_trans (ih₁ s) (ih₂ (sched g₁ s))

/-- Off the support of `g`, `sched g` leaves the ready-time unchanged. -/
theorem sched_frame (g : Gate) (s : Nat → Nat) (x : Nat) (hx : x ∉ supp g) :
    sched g s x = s x := by
  induction g generalizing s with
  | I => rfl
  | X q =>
      apply tick_frame; simpa [supp] using hx
  | CX a b =>
      apply tick_frame; simpa [supp] using hx
  | CCX a b c =>
      apply tick_frame; simpa [supp] using hx
  | seq g₁ g₂ ih₁ ih₂ =>
      simp only [supp, List.mem_append, not_or] at hx
      rw [show sched (Gate.seq g₁ g₂) s x = sched g₂ (sched g₁ s) x from rfl]
      rw [ih₂ (sched g₁ s) hx.2, ih₁ s hx.1]

/-- `tick` is LOCAL: its action on a support member depends only on the values
    of `s` over the qubit set `qs`. -/
theorem tick_local (qs : List Nat) (s s' : Nat → Nat)
    (h : ∀ q, q ∈ qs → s q = s' q) (x : Nat) (hx : x ∈ qs) :
    tick qs s x = tick qs s' x := by
  unfold tick
  simp only [hx, if_pos]
  -- the two folds agree because `s = s'` on every element of `qs`.
  have hfold : ∀ (l : List Nat) (init : Nat), (∀ q, q ∈ l → s q = s' q) →
      l.foldl (fun m q => max m (s q)) init
        = l.foldl (fun m q => max m (s' q)) init := by
    intro l
    induction l with
    | nil => intro init _; rfl
    | cons a t ih =>
        intro init hl
        simp only [List.foldl_cons]
        rw [hl a (by simp), ih (max init (s' a))
          (fun q hq => hl q (by simp [hq]))]
  rw [hfold qs 0 h]

/-- `sched g` is LOCAL on `supp g`: its action on a support qubit depends only
    on the input ready-times restricted to `supp g`. -/
theorem sched_local (g : Gate) (s s' : Nat → Nat)
    (h : ∀ q, q ∈ supp g → s q = s' q) :
    ∀ q, q ∈ supp g → sched g s q = sched g s' q := by
  induction g generalizing s s' with
  | I => intro q hq; simp [supp] at hq
  | X a => intro q hq; exact tick_local _ s s' h q hq
  | CX a b => intro q hq; exact tick_local _ s s' h q hq
  | CCX a b c => intro q hq; exact tick_local _ s s' h q hq
  | seq g₁ g₂ ih₁ ih₂ =>
      intro q hq
      simp only [supp, List.mem_append] at h hq
      -- The two prefixes agree on supp g₁, hence sched g₁ s = sched g₁ s' on supp g₁.
      have hg1 : ∀ p, p ∈ supp g₁ → sched g₁ s p = sched g₁ s' p :=
        ih₁ s s' (fun p hp => h p (Or.inl hp))
      -- `sched g₁ s` and `sched g₁ s'` agree on supp g₂.
      have hagree2 : ∀ p, p ∈ supp g₂ → sched g₁ s p = sched g₁ s' p := by
        intro p hp
        by_cases hp1 : p ∈ supp g₁
        · exact hg1 p hp1
        · rw [sched_frame g₁ s p hp1, sched_frame g₁ s' p hp1]
          exact h p (Or.inr hp)
      show sched g₂ (sched g₁ s) q = sched g₂ (sched g₁ s') q
      rcases hq with hq | hq
      · -- q ∈ supp g₁; if also in supp g₂ use ih₂, else frame both down to sched g₁.
        by_cases hq2 : q ∈ supp g₂
        · exact ih₂ (sched g₁ s) (sched g₁ s') hagree2 q hq2
        · rw [sched_frame g₂ _ q hq2, sched_frame g₂ _ q hq2]
          exact hg1 q hq
      · exact ih₂ (sched g₁ s) (sched g₁ s') hagree2 q hq

/-! ## §3. `maxOver` algebra. -/

/-- `maxOver` over an append splits as a `max`. -/
theorem maxOver_append (l₁ l₂ : List Nat) (f : Nat → Nat) :
    maxOver (l₁ ++ l₂) f = max (maxOver l₁ f) (maxOver l₂ f) := by
  unfold maxOver
  rw [List.foldl_append]
  -- foldl over l₂ starting at (foldl over l₁ from 0) = max (foldl l₁) (foldl l₂ from 0)
  have key : ∀ (l : List Nat) (init : Nat),
      l.foldl (fun m q => max m (f q)) init
        = max init (l.foldl (fun m q => max m (f q)) 0) := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons a t ih =>
        intro init
        simp only [List.foldl_cons]
        rw [ih (max init (f a)), ih (max 0 (f a))]
        omega
  rw [key l₂ _]

/-- `maxOver` only depends on `f`'s values over the list. -/
theorem maxOver_congr (l : List Nat) (f g : Nat → Nat)
    (h : ∀ q, q ∈ l → f q = g q) :
    maxOver l f = maxOver l g := by
  unfold maxOver
  have key : ∀ (t : List Nat) (init : Nat), (∀ q, q ∈ t → f q = g q) →
      t.foldl (fun m q => max m (f q)) init
        = t.foldl (fun m q => max m (g q)) init := by
    intro t
    induction t with
    | nil => intro init _; rfl
    | cons a u ih =>
        intro init hu
        simp only [List.foldl_cons]
        rw [hu a (by simp), ih (max init (g a))
          (fun q hq => hu q (by simp [hq]))]
  exact key l 0 h

/-! ## §4. THE CRUX: disjoint `seq` runs in parallel. -/

/-- **`parallelDepth` of a `seq` of qubit-DISJOINT gates is the `max`, not the
    sum.**  Two gates touching no common qubit do not delay each other, so the
    sequential composition's ASAP depth is the larger of the two — the structural
    fact that underlies every parallel-depth win. -/
theorem parallelDepth_seq_disjoint (g₁ g₂ : Gate)
    (hdisj : ∀ x, x ∈ supp g₁ → x ∉ supp g₂) :
    parallelDepth (Gate.seq g₁ g₂)
      = max (parallelDepth g₁) (parallelDepth g₂) := by
  unfold parallelDepth
  -- supp (seq) = supp g₁ ++ supp g₂; sched (seq) 0 = sched g₂ (sched g₁ 0).
  show maxOver (supp g₁ ++ supp g₂) (sched g₂ (sched g₁ (fun _ => 0)))
      = max (maxOver (supp g₁) (sched g₁ (fun _ => 0)))
            (maxOver (supp g₂) (sched g₂ (fun _ => 0)))
  rw [maxOver_append]
  congr 1
  · -- On supp g₁: those qubits ∉ supp g₂, so sched g₂ fixes them.
    apply maxOver_congr
    intro q hq
    exact sched_frame g₂ (sched g₁ (fun _ => 0)) q (hdisj q hq)
  · -- On supp g₂: sched g₁ fixes them (q ∉ supp g₁), so sched g₁ 0 = 0 there;
    -- then sched g₂ on supp g₂ depends only on those values (sched_local).
    apply maxOver_congr
    intro q hq
    apply sched_local g₂ (sched g₁ (fun _ => 0)) (fun _ => 0) _ q hq
    intro p hp
    -- p ∈ supp g₂ ⇒ p ∉ supp g₁ (by disjointness, contrapositive) ⇒ sched g₁ 0 p = 0.
    have hp1 : p ∉ supp g₁ := fun hpg1 => hdisj p hpg1 hp
    rw [sched_frame g₁ (fun _ => 0) p hp1]

/-! ## §5. Sanity: `parallelDepth` is a genuine depth. -/

-- Same qubit ⇒ serial ⇒ depth 2.
example : parallelDepth (Gate.seq (Gate.X 0) (Gate.X 0)) = 2 := by decide
-- Disjoint qubits ⇒ parallel ⇒ depth 1.
example : parallelDepth (Gate.seq (Gate.X 0) (Gate.X 1)) = 1 := by decide

/-- `maxOver` of a `≤`-dominated function is `≤` the dominating `maxOver`. -/
theorem maxOver_mono (l : List Nat) (f g : Nat → Nat)
    (h : ∀ q, q ∈ l → f q ≤ g q) :
    maxOver l f ≤ maxOver l g := by
  unfold maxOver
  have key : ∀ (t : List Nat) (i j : Nat), i ≤ j → (∀ q, q ∈ t → f q ≤ g q) →
      t.foldl (fun m q => max m (f q)) i ≤ t.foldl (fun m q => max m (g q)) j := by
    intro t
    induction t with
    | nil => intro i j hij _; simpa using hij
    | cons a u ih =>
        intro i j hij hu
        simp only [List.foldl_cons]
        apply ih
        · have := hu a (by simp)
          omega
        · intro q hq; exact hu q (by simp [hq])
  exact key l 0 0 (le_refl 0) h

/-- A `foldl`-max over `qs` is bounded by `B` once the seed and every `s q` are. -/
theorem foldl_max_le (qs : List Nat) (s : Nat → Nat) (B : Nat)
    (hq : ∀ q, q ∈ qs → s q ≤ B) :
    ∀ init, init ≤ B → qs.foldl (fun m q => max m (s q)) init ≤ B := by
  induction qs with
  | nil => intro init h; simpa using h
  | cons a t ih =>
      intro init hinit
      simp only [List.foldl_cons]
      exact ih (fun q hq' => hq q (by simp [hq'])) (max init (s a))
        (by have := hq a (by simp); omega)

/-- `tick` finish-time everywhere is bounded by `B + 1` once `s` is `≤ B`
    everywhere. -/
theorem tick_le_of_bound (qs : List Nat) (s : Nat → Nat) (B : Nat)
    (hB : ∀ y, s y ≤ B) (x : Nat) :
    tick qs s x ≤ B + 1 := by
  unfold tick
  by_cases hxin : x ∈ qs
  · simp only [hxin, if_pos]
    have := foldl_max_le qs s B (fun q _ => hB q) 0 (by omega)
    omega
  · simp only [hxin, if_neg, not_false_iff]
    have := hB x; omega

/-- **Uniform-bound scheduling bound.**  If every ready-time in `s` is `≤ B`,
    then every scheduled finish-time is `≤ B + Gate.depth g`. -/
theorem sched_le_of_bound (g : Gate) :
    ∀ (s : Nat → Nat) (B : Nat), (∀ y, s y ≤ B) → ∀ x, sched g s x ≤ B + Gate.depth g := by
  induction g with
  | I => intro s B hB x; simpa [sched, Gate.depth] using hB x
  | X a =>
      intro s B hB x
      show tick [a] s x ≤ B + 1
      exact tick_le_of_bound _ s B hB x
  | CX a b =>
      intro s B hB x
      show tick [a, b] s x ≤ B + 1
      exact tick_le_of_bound _ s B hB x
  | CCX a b c =>
      intro s B hB x
      show tick [a, b, c] s x ≤ B + 1
      exact tick_le_of_bound _ s B hB x
  | seq g₁ g₂ ih₁ ih₂ =>
      intro s B hB x
      show sched g₂ (sched g₁ s) x ≤ B + (Gate.depth g₁ + Gate.depth g₂)
      -- after g₁, the ready-times are ≤ B + depth g₁.
      have hmid : ∀ y, sched g₁ s y ≤ B + Gate.depth g₁ := fun y => ih₁ s B hB y
      have := ih₂ (sched g₁ s) (B + Gate.depth g₁) hmid x
      omega

/-- **`parallelDepth ≤ Gate.depth`.**  The achievable parallel (ASAP) depth never
    exceeds the sequential gate count — `parallelDepth` is a genuine depth. -/
theorem parallelDepth_le_depth (g : Gate) : parallelDepth g ≤ Gate.depth g := by
  unfold parallelDepth
  -- every finish-time on supp g is ≤ 0 + depth g.
  calc maxOver (supp g) (sched g (fun _ => 0))
      ≤ maxOver (supp g) (fun _ => Gate.depth g) := by
        apply maxOver_mono
        intro q _
        have := sched_le_of_bound g (fun _ => 0) 0 (fun _ => le_refl 0) q
        simpa using this
    _ ≤ Gate.depth g := by
        -- maxOver of a constant is ≤ that constant.
        unfold maxOver
        have key : ∀ (t : List Nat) (init : Nat), init ≤ Gate.depth g →
            t.foldl (fun m _ => max m (Gate.depth g)) init ≤ Gate.depth g := by
          intro t
          induction t with
          | nil => intro init h; simpa using h
          | cons a u ih =>
              intro init h
              simp only [List.foldl_cons]
              exact ih (max init (Gate.depth g)) (by omega)
        exact key (supp g) 0 (by omega)

end FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth
