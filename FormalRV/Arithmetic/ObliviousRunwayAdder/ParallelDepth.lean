/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth
  ──────────────────────────────────────────────────────
  A **PARALLEL (ASAP critical-path) depth** measure on the `Gate` IR, and the
  oblivious-carry-runway adder's depth advantage proved against it.

  `Gate.depth` (in `Core/Gate.lean`) SUMS over `seq`, so it is the SEQUENTIAL
  gate count: a `seq` of `k` disjoint segments costs `k ×` one segment — it can
  never show a parallelism win.  `parallelDepth` here instead schedules every
  gate As-Soon-As-Possible: a gate on qubits `Q` runs at time
  `1 + max (ready-time of its qubits)`, after which those qubits' ready-times
  become that.  Two gates on DISJOINT qubits do not delay each other, so

      parallelDepth (seq g₁ g₂) = max (parallelDepth g₁) (parallelDepth g₂)
        whenever  supp g₁ ∩ supp g₂ = ∅                 (`parallelDepth_seq_disjoint`)

  The runway adder `runwayAddK gSep k` is a `seq` of `k` Cuccaro adds over
  PAIRWISE-DISJOINT qubit blocks (segment `j` lives in `[segBase j, …)`).  By the
  disjoint-seq law its parallel depth equals ONE segment's, INDEPENDENT of `k`:

      parallelDepth (runwayAddK gSep k) = parallelDepth (one segment)
                                                          (`parallelDepth_runwayAddK_eq`)

  This is the realized oblivious-carry depth advantage: `O(gSep)` parallel depth
  for the runway adder vs `O(n)` for a plain `n`-bit Cuccaro add (whose carry
  chain serializes).  See the `#eval` table in `Example.lean`.

  HONEST SCOPE.  `parallelDepth` is a SCHEDULING / depth MODEL on the gate list:
  it assumes gates on disjoint qubits MAY run concurrently (the standard notion
  of circuit depth).  It does NOT change the `Gate` — `runwayAddK` is still a
  `seq` and its `Gate.depth` (sequential count) still grows with `k`.  What this
  file adds is a faithful measure of the ACHIEVABLE parallel depth, and a proof
  that for the runway adder that depth is constant in the number of segments.
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

/-! ## §6. Support of the Cuccaro circuit lies in its block. -/

open FormalRV.BQAlgo in
/-- A two-sided support bound: every qubit of `cuccaro_maj_chain n q` lies in
    `[q, q + 2n + 1)` (= `[q, q + span n)`). -/
theorem supp_cuccaro_maj_chain (n q : Nat) :
    ∀ p, p ∈ supp (cuccaro_maj_chain n q) → q ≤ p ∧ p < q + 2 * n + 1 := by
  induction n generalizing q with
  | zero => intro p hp; simp [cuccaro_maj_chain, supp] at hp
  | succ k ih =>
      intro p hp
      -- chain (k+1) q = seq (MAJ q (q+1) (q+2)) (chain k (q+2))
      rw [show cuccaro_maj_chain (k + 1) q
            = Gate.seq (cuccaro_MAJ q (q + 1) (q + 2)) (cuccaro_maj_chain k (q + 2))
          from rfl] at hp
      simp only [supp, List.mem_append] at hp
      rcases hp with hp | hp
      · -- MAJ q (q+1) (q+2) = seq (CX (q+2) (q+1)) (seq (CX (q+2) q) (CCX q (q+1) (q+2)))
        unfold cuccaro_MAJ at hp
        simp only [supp, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hp
        omega
      · have := ih (q + 2) p hp; omega

open FormalRV.BQAlgo in
/-- Every qubit of `cuccaro_uma_chain_reverse n q` lies in `[q, q + 2n + 1)`. -/
theorem supp_cuccaro_uma_chain_reverse (n q : Nat) :
    ∀ p, p ∈ supp (cuccaro_uma_chain_reverse n q) → q ≤ p ∧ p < q + 2 * n + 1 := by
  induction n generalizing q with
  | zero => intro p hp; simp [cuccaro_uma_chain_reverse, supp] at hp
  | succ k ih =>
      intro p hp
      rw [show cuccaro_uma_chain_reverse (k + 1) q
            = Gate.seq (cuccaro_uma_chain_reverse k (q + 2))
                       (cuccaro_UMA q (q + 1) (q + 2))
          from rfl] at hp
      simp only [supp, List.mem_append] at hp
      rcases hp with hp | hp
      · have := ih (q + 2) p hp; omega
      · unfold cuccaro_UMA at hp
        simp only [supp, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hp
        omega

open FormalRV.BQAlgo in
/-- **Support of the Cuccaro `n`-bit adder is contained in its block.**
    Every qubit it touches lies in `[base, base + (2n+1)) = [base, base + span n)`. -/
theorem supp_cuccaro_subset (n base : Nat) :
    ∀ p, p ∈ supp (cuccaroAdder.circuit n base) → base ≤ p ∧ p < base + (2 * n + 1) := by
  intro p hp
  -- circuit n base = cuccaro_n_bit_adder_full n base = seq maj_chain uma_chain_reverse
  rw [show cuccaroAdder.circuit n base = cuccaro_n_bit_adder_full n base from rfl] at hp
  rw [show cuccaro_n_bit_adder_full n base
        = Gate.seq (cuccaro_maj_chain n base) (cuccaro_uma_chain_reverse n base)
      from rfl] at hp
  simp only [supp, List.mem_append] at hp
  rcases hp with hp | hp
  · have := supp_cuccaro_maj_chain n base p hp; omega
  · have := supp_cuccaro_uma_chain_reverse n base p hp; omega

/-! ## §7. Runway-segment support & disjointness. -/

/-- `segAdd gSep m` (a width-`(gSep+1)` Cuccaro at `segBase gSep m`) touches only
    qubits in its segment block `[segBase m, segBase m + (2·gSep+3))`. -/
theorem supp_segAdd_subset (gSep m : Nat) :
    ∀ p, p ∈ supp (segAdd gSep m) →
      segBase gSep m ≤ p ∧ p < segBase gSep m + (2 * gSep + 3) := by
  intro p hp
  unfold segAdd at hp
  have := supp_cuccaro_subset (gSep + 1) (segBase gSep m) p hp
  -- 2*(gSep+1)+1 = 2*gSep+3.
  constructor
  · exact this.1
  · have h2 : 2 * (gSep + 1) + 1 = 2 * gSep + 3 := by ring
    omega

/-- `runwayAddK gSep k` (segments `0…k-1`) touches only qubits strictly below
    `segBase gSep k = k·stride`. -/
theorem supp_runwayAddK_lt (gSep : Nat) :
    ∀ (k : Nat) p, p ∈ supp (runwayAddK gSep k) → p < segBase gSep k := by
  intro k
  induction k with
  | zero => intro p hp; simp [runwayAddK, supp] at hp
  | succ m ih =>
      intro p hp
      rw [show runwayAddK gSep (m + 1)
            = Gate.seq (runwayAddK gSep m) (segAdd gSep m) from rfl] at hp
      simp only [supp, List.mem_append] at hp
      have hbase : segBase gSep (m + 1) = segBase gSep m + (2 * gSep + 3) := by
        unfold segBase segStride; ring
      rcases hp with hp | hp
      · have := ih p hp
        -- segBase m ≤ segBase (m+1).
        have hmono : segBase gSep m ≤ segBase gSep (m + 1) := by omega
        omega
      · have := supp_segAdd_subset gSep m p hp; omega

/-- **Segment disjointness.**  `runwayAddK gSep k` and `segAdd gSep k` touch no
    common qubit: the former lives below `segBase k`, the latter at or above it. -/
theorem runwayAddK_segAdd_disjoint (gSep k : Nat) :
    ∀ x, x ∈ supp (runwayAddK gSep k) → x ∉ supp (segAdd gSep k) := by
  intro x hx hxseg
  have h1 := supp_runwayAddK_lt gSep k x hx
  have h2 := supp_segAdd_subset gSep k x hxseg
  omega

/-! ## §8. Shift invariance of `parallelDepth`.

A uniform qubit relabelling `q ↦ q + d` does not change the achievable parallel
depth: the gate-connectivity structure (which gates share which qubits) is
unchanged.  We use this to show every segment add has the SAME parallel depth as
the base-`0` segment, independent of its position. -/

/-- Relabel every qubit of `g` by `· + d`. -/
def shiftGate (d : Nat) : Gate → Gate
  | Gate.I          => Gate.I
  | Gate.X q        => Gate.X (q + d)
  | Gate.CX a b     => Gate.CX (a + d) (b + d)
  | Gate.CCX a b c  => Gate.CCX (a + d) (b + d) (c + d)
  | Gate.seq g₁ g₂  => Gate.seq (shiftGate d g₁) (shiftGate d g₂)

/-- `supp` commutes with shifting: `supp (shiftGate d g) = (supp g).map (· + d)`. -/
theorem supp_shiftGate (d : Nat) (g : Gate) :
    supp (shiftGate d g) = (supp g).map (· + d) := by
  induction g with
  | I => rfl
  | X q => rfl
  | CX a b => rfl
  | CCX a b c => rfl
  | seq g₁ g₂ ih₁ ih₂ =>
      show supp (shiftGate d g₁) ++ supp (shiftGate d g₂)
        = (supp g₁ ++ supp g₂).map (· + d)
      rw [ih₁, ih₂, List.map_append]

/-- `x + d ∈ map (·+d) qs ↔ x ∈ qs`. -/
theorem mem_map_add_iff (d x : Nat) (qs : List Nat) :
    x + d ∈ qs.map (· + d) ↔ x ∈ qs := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨y, hy, hyx⟩
    have : y = x := by omega
    subst this; exact hy
  · intro h; exact List.mem_map.mpr ⟨x, h, rfl⟩

/-- A `foldl`-max over the shifted list of `s` equals the `foldl`-max over the
    original list of `s ∘ (·+d)`. -/
theorem foldl_max_map_add (d : Nat) (s : Nat → Nat) (qs : List Nat) :
    ∀ init, (qs.map (· + d)).foldl (fun m q => max m (s q)) init
      = qs.foldl (fun m q => max m (s (q + d))) init := by
  induction qs with
  | nil => intro init; rfl
  | cons a t ih =>
      intro init
      simp only [List.map_cons, List.foldl_cons]
      exact ih (max init (s (a + d)))

/-- **`tick` shift law.**  `tick (map (·+d) qs) s (x+d) = tick qs (s∘(·+d)) x`. -/
theorem tick_shift (d : Nat) (qs : List Nat) (s : Nat → Nat) (x : Nat) :
    tick (qs.map (· + d)) s (x + d) = tick qs (fun y => s (y + d)) x := by
  unfold tick
  rw [foldl_max_map_add d s qs 0]
  by_cases hx : x ∈ qs
  · rw [if_pos ((mem_map_add_iff d x qs).mpr hx), if_pos hx]
  · rw [if_neg (fun h => hx ((mem_map_add_iff d x qs).mp h)), if_neg hx]

/-- **`sched` shift law.**  Scheduling the shifted gate at a shifted position
    equals scheduling the original gate (with a shifted initial map). -/
theorem sched_shift (d : Nat) (g : Gate) :
    ∀ (s : Nat → Nat) (x : Nat),
      sched (shiftGate d g) s (x + d) = sched g (fun y => s (y + d)) x := by
  induction g with
  | I => intro s x; rfl
  | X q => intro s x; exact tick_shift d [q] s x
  | CX a b => intro s x; exact tick_shift d [a, b] s x
  | CCX a b c => intro s x; exact tick_shift d [a, b, c] s x
  | seq g₁ g₂ ih₁ ih₂ =>
      intro s x
      show sched (shiftGate d g₂) (sched (shiftGate d g₁) s) (x + d)
        = sched g₂ (sched g₁ (fun y => s (y + d))) x
      rw [ih₂ (sched (shiftGate d g₁) s) x]
      -- now need: sched g₂ (fun y => sched (shiftGate d g₁) s (y+d)) x
      --         = sched g₂ (sched g₁ (fun y => s (y+d))) x
      congr 1
      funext y
      exact ih₁ s y

/-- `maxOver` over a shifted list of `f` = `maxOver` over the original of
    `f ∘ (·+d)`. -/
theorem maxOver_map_add (d : Nat) (f : Nat → Nat) (l : List Nat) :
    maxOver (l.map (· + d)) f = maxOver l (fun y => f (y + d)) := by
  unfold maxOver
  exact foldl_max_map_add d f l 0

/-- **`parallelDepth` is shift-invariant.**  A uniform relabelling `q ↦ q + d`
    does not change the ASAP parallel depth. -/
theorem parallelDepth_shiftGate (d : Nat) (g : Gate) :
    parallelDepth (shiftGate d g) = parallelDepth g := by
  unfold parallelDepth
  rw [supp_shiftGate, maxOver_map_add]
  -- maxOver (supp g) (fun y => sched (shiftGate d g) 0 (y+d))
  --   = maxOver (supp g) (sched g 0)
  apply maxOver_congr
  intro q _
  have := sched_shift d g (fun _ => 0) q
  simpa using this

/-! ## §9. The Cuccaro circuit at base `q` is a shift of base `0`. -/

/-- Shifting composes: `shiftGate d₁ (shiftGate d₂ g) = shiftGate (d₂ + d₁) g`. -/
theorem shiftGate_shiftGate (d₁ d₂ : Nat) (g : Gate) :
    shiftGate d₁ (shiftGate d₂ g) = shiftGate (d₂ + d₁) g := by
  induction g with
  | I => rfl
  | X q => show Gate.X (q + d₂ + d₁) = Gate.X (q + (d₂ + d₁)); rw [Nat.add_assoc]
  | CX a b =>
      show Gate.CX (a + d₂ + d₁) (b + d₂ + d₁) = Gate.CX (a + (d₂ + d₁)) (b + (d₂ + d₁))
      rw [Nat.add_assoc, Nat.add_assoc]
  | CCX a b c =>
      show Gate.CCX (a + d₂ + d₁) (b + d₂ + d₁) (c + d₂ + d₁)
        = Gate.CCX (a + (d₂ + d₁)) (b + (d₂ + d₁)) (c + (d₂ + d₁))
      rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
  | seq g₁ g₂ ih₁ ih₂ =>
      show Gate.seq (shiftGate d₁ (shiftGate d₂ g₁)) (shiftGate d₁ (shiftGate d₂ g₂))
        = Gate.seq (shiftGate (d₂ + d₁) g₁) (shiftGate (d₂ + d₁) g₂)
      rw [ih₁, ih₂]

open FormalRV.BQAlgo in
/-- The MAJ chain at base `q` is the base-`0` chain relabelled by `· + q`. -/
theorem cuccaro_maj_chain_shift (n : Nat) :
    ∀ q, cuccaro_maj_chain n q = shiftGate q (cuccaro_maj_chain n 0) := by
  induction n with
  | zero => intro q; rfl
  | succ k ih =>
      intro q
      show Gate.seq (cuccaro_MAJ q (q + 1) (q + 2)) (cuccaro_maj_chain k (q + 2))
        = Gate.seq (shiftGate q (cuccaro_MAJ 0 1 2)) (shiftGate q (cuccaro_maj_chain k 2))
      congr 1
      · -- MAJ q (q+1) (q+2) = shiftGate q (MAJ 0 1 2)
        show Gate.seq (Gate.CX (q + 2) (q + 1)) (Gate.seq (Gate.CX (q + 2) q) (Gate.CCX q (q + 1) (q + 2)))
          = Gate.seq (Gate.CX (2 + q) (1 + q)) (Gate.seq (Gate.CX (2 + q) (0 + q)) (Gate.CCX (0 + q) (1 + q) (2 + q)))
        congr 1 <;> [skip; congr 1] <;> congr 1 <;> omega
      · -- chain k (q+2) = shiftGate q (chain k 2)
        rw [ih (q + 2), ih 2, shiftGate_shiftGate, Nat.add_comm 2 q]

open FormalRV.BQAlgo in
/-- The reverse UMA chain at base `q` is the base-`0` chain relabelled by `· + q`. -/
theorem cuccaro_uma_chain_reverse_shift (n : Nat) :
    ∀ q, cuccaro_uma_chain_reverse n q = shiftGate q (cuccaro_uma_chain_reverse n 0) := by
  induction n with
  | zero => intro q; rfl
  | succ k ih =>
      intro q
      show Gate.seq (cuccaro_uma_chain_reverse k (q + 2)) (cuccaro_UMA q (q + 1) (q + 2))
        = Gate.seq (shiftGate q (cuccaro_uma_chain_reverse k 2))
                   (shiftGate q (cuccaro_UMA 0 1 2))
      congr 1
      · rw [ih (q + 2), ih 2, shiftGate_shiftGate, Nat.add_comm 2 q]
      · show Gate.seq (Gate.CCX q (q + 1) (q + 2)) (Gate.seq (Gate.CX (q + 2) q) (Gate.CX q (q + 1)))
          = Gate.seq (Gate.CCX (0 + q) (1 + q) (2 + q)) (Gate.seq (Gate.CX (2 + q) (0 + q)) (Gate.CX (0 + q) (1 + q)))
        congr 1 <;> [skip; congr 1] <;> congr 1 <;> omega

open FormalRV.BQAlgo in
/-- **The Cuccaro `n`-bit adder at base `q` is the base-`0` adder shifted by `q`.** -/
theorem cuccaro_circuit_shift (n q : Nat) :
    cuccaroAdder.circuit n q = shiftGate q (cuccaroAdder.circuit n 0) := by
  show cuccaro_n_bit_adder_full n q = shiftGate q (cuccaro_n_bit_adder_full n 0)
  show Gate.seq (cuccaro_maj_chain n q) (cuccaro_uma_chain_reverse n q)
    = Gate.seq (shiftGate q (cuccaro_maj_chain n 0)) (shiftGate q (cuccaro_uma_chain_reverse n 0))
  rw [cuccaro_maj_chain_shift n q, cuccaro_uma_chain_reverse_shift n q]

/-- **Parallel depth of a Cuccaro add is base-independent.** -/
theorem parallelDepth_cuccaro_base (n q : Nat) :
    parallelDepth (cuccaroAdder.circuit n q) = parallelDepth (cuccaroAdder.circuit n 0) := by
  rw [cuccaro_circuit_shift n q, parallelDepth_shiftGate]

/-- Every segment's parallel depth equals the base-`0` segment's: all segments
    are width-`(gSep+1)` Cuccaro adds, only their base differs, and parallel
    depth is base-independent. -/
theorem parallelDepth_segAdd_const (gSep m : Nat) :
    parallelDepth (segAdd gSep m)
      = parallelDepth (cuccaroAdder.circuit (gSep + 1) (segBase gSep 0)) := by
  unfold segAdd
  rw [parallelDepth_cuccaro_base (gSep + 1) (segBase gSep m),
      parallelDepth_cuccaro_base (gSep + 1) (segBase gSep 0)]

/-! ## §10. THE HEADLINE: runway parallel depth is constant in `k`. -/

/-- **THE STRUCTURAL FACT (max, not sum).**  Adding one more disjoint segment
    does not ADD to the parallel depth — it is the `max` with the new segment's
    depth.  This alone proves no segment serializes against the others. -/
theorem parallelDepth_runwayAddK_eq_max (gSep k : Nat) :
    parallelDepth (runwayAddK gSep (k + 1))
      = max (parallelDepth (runwayAddK gSep k)) (parallelDepth (segAdd gSep k)) := by
  rw [show runwayAddK gSep (k + 1)
        = Gate.seq (runwayAddK gSep k) (segAdd gSep k) from rfl]
  exact parallelDepth_seq_disjoint _ _ (runwayAddK_segAdd_disjoint gSep k)

/-- **HEADLINE — the realized depth advantage.**  For `k ≥ 1`, the ASAP parallel
    depth of the `k`-segment oblivious-carry-runway adder equals ONE segment's
    parallel depth, INDEPENDENT of `k`.  The `k` disjoint segments run
    concurrently, so adding more segments never increases the depth.  (Achieved
    via SHIFT-INVARIANCE: `parallelDepth_segAdd_const`, every segment has the same
    depth as the base-`0` segment.) -/
theorem parallelDepth_runwayAddK_eq (gSep : Nat) :
    ∀ k, 1 ≤ k →
      parallelDepth (runwayAddK gSep k)
        = parallelDepth (cuccaroAdder.circuit (gSep + 1) (segBase gSep 0)) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ m ih =>
      intro _
      rcases Nat.eq_zero_or_pos m with hm | hm
      · -- base case k = 1: runwayAddK gSep 1 = seq I (segAdd gSep 0).
        subst hm
        rw [parallelDepth_runwayAddK_eq_max]
        -- parallelDepth (runwayAddK gSep 0) = parallelDepth I = 0.
        have h0 : parallelDepth (runwayAddK gSep 0) = 0 := by
          show parallelDepth Gate.I = 0
          rfl
        rw [h0, parallelDepth_segAdd_const, Nat.zero_max]
      · -- inductive step m ≥ 1.
        rw [parallelDepth_runwayAddK_eq_max, ih hm, parallelDepth_segAdd_const]
        exact Nat.max_self _

end FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth
