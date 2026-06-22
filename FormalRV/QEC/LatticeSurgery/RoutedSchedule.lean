/-
  FormalRV.QEC.LatticeSurgery.RoutedSchedule
  ------------------------------------------
  **★ THE CONGESTION-AWARE SCHEDULER — pack merges into layers by HIGHWAY span,
  not just by qubit, and PROVE every layer is congestion-free. ★**

  The bug found in `modexpPPM`: the scheduler packed two merges into one layer
  because they were qubit-disjoint (`{4,7}` and `{3,8}`) — but their routing
  highways (spans 4–7 and 3–8) OVERLAP, so they cannot run in parallel.  Here a
  greedy first-fit packer places each merge in the earliest layer whose highways
  it does NOT cross, and `packSpans_CF` proves EVERY produced layer has pairwise
  span-disjoint merges (so the routed merges in it genuinely run in parallel).
-/
import FormalRV.QEC.LatticeSurgery.RoutedMerge

namespace FormalRV.QEC.LaSre

/-- Span disjointness is symmetric. -/
theorem spansDisjoint_comm (a b : List Nat) : spansDisjoint a b = spansDisjoint b a := by
  simp only [spansDisjoint]; rw [Bool.or_comm]

/-- A gadget (its qubit columns `g`) fits in a layer iff its highway span is
disjoint from every gadget already there. -/
def fits (layer : List (List Nat)) (g : List Nat) : Bool :=
  layer.all (fun h => spansDisjoint g h)

/-- Greedy first-fit: place `g` in the earliest layer it fits, else a new layer. -/
def addFF : List (List (List Nat)) → List Nat → List (List (List Nat))
  | [],        g => [[g]]
  | L :: rest, g => if fits L g = true then (L ++ [g]) :: rest else L :: addFF rest g

/-- **THE CONGESTION-AWARE SCHEDULE** — pack a list of merges (each = its qubit
columns) into time-layers with pairwise span-disjoint highways. -/
def packSpans (gs : List (List Nat)) : List (List (List Nat)) := gs.foldl addFF []

/-- A layer is CONGESTION-FREE iff its merges have pairwise-disjoint highway spans
(so they can be routed in parallel). -/
def CF (layer : List (List Nat)) : Prop :=
  layer.Pairwise (fun a b => spansDisjoint a b = true)

/-- `addFF` preserves the all-layers-congestion-free invariant. -/
theorem addFF_preserves (g : List Nat) : ∀ (ls : List (List (List Nat))),
    (∀ l ∈ ls, CF l) → ∀ l ∈ addFF ls g, CF l := by
  intro ls
  induction ls with
  | nil =>
    intro _ l hl
    simp only [addFF, List.mem_singleton] at hl
    subst hl
    simp [CF]
  | cons L rest ih =>
    intro h
    by_cases hf : fits L g = true
    · simp only [addFF, if_pos hf]
      intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · -- l = L ++ [g] is congestion-free
        rw [CF, List.pairwise_append]
        refine ⟨h L (by simp), by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        rw [spansDisjoint_comm]
        exact (List.all_eq_true.1 hf) a ha
      · exact h l (List.mem_cons_of_mem _ hl)
    · simp only [addFF, if_neg hf]
      intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact h l (by simp)
      · exact ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')) l hl

/-- **★ THE SCHEDULER IS CONGESTION-FREE BY CONSTRUCTION ★** — for ANY list of
merges, every layer the packer produces has pairwise span-disjoint highways, so
the routed merges in each layer genuinely run in parallel without collision. -/
theorem packSpans_CF (gs : List (List Nat)) : ∀ l ∈ packSpans gs, CF l := by
  have aux : ∀ (gs : List (List Nat)) (acc : List (List (List Nat))),
      (∀ l ∈ acc, CF l) → ∀ l ∈ gs.foldl addFF acc, CF l := by
    intro gs
    induction gs with
    | nil => intro acc h; simpa using h
    | cons g rest ih => intro acc h; exact ih (addFF acc g) (addFF_preserves g acc h)
  exact aux gs [] (by simp)

/-! ## Demonstrations — the `modexpPPM` L1 collision, scheduled correctly. -/

/-- **★ L1's COLLIDING MERGES ARE SERIALIZED ★** — `{4,7}` and `{3,8}` (overlapping
highways) are placed in SEPARATE layers, fixing the collision the old scheduler
caused. -/
theorem L1_serialized : packSpans [[4,7], [3,8]] = [[[4,7]], [[3,8]]] := by decide

/-- ...while two disjoint-highway merges `{0,3}`,`{5,8}` stay in ONE parallel
layer (the packer doesn't over-serialize). -/
theorem disjoint_parallel : packSpans [[0,3], [5,8]] = [[[0,3], [5,8]]] := by decide

/-- A 3-merge example: `{0,3}` ∥ `{5,8}` in layer 1, `{2,6}` (crosses both) in
layer 2 — the greedy packer interleaves correctly. -/
theorem three_merge_pack :
    packSpans [[0,3], [5,8], [2,6]] = [[[0,3], [5,8]], [[2,6]]] := by decide

end FormalRV.QEC.LaSre
