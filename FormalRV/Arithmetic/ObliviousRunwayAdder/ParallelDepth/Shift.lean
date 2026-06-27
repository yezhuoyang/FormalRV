/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth.Shift
  ──────────────────────────────────────────────────────
  Submodule of `ParallelDepth` (split out for per-file compile memory).
  Contains §8–§9: shift-invariance of `parallelDepth` (`shiftGate` …
  `parallelDepth_shiftGate`) and the base-independence of the Cuccaro circuit's
  parallel depth (`shiftGate_shiftGate` … `cuccaro_circuit_shift`,
  `parallelDepth_cuccaro_base`, `parallelDepth_segAdd_const`).

  Re-exported VERBATIM from the original `ParallelDepth.lean`; the declarations,
  statements, names, namespace and `open`s are unchanged.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth.CuccaroSupport

namespace FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional

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

end FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth
