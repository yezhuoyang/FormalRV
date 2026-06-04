/-
  FormalRV.Shor.Approx.Deviation — Gidney's combinatorial deviation metric and its
  subadditivity under composition (arXiv:1905.08488).

  Gidney 2019 measures the error of an *approximate encoded permutation* not by a
  norm but combinatorially (Def 2.4):

      Dev(P) = max_{g}  |Deviated_g(P)| / |C|,
      Deviated_g(P) = { c ∈ C | v(f(g,c)) ∉ Encodings_{u(g)}(P) },
      Encodings_g(P) = { f(g,c) | c ∈ C }.

  We fix the encoder `(G, E, C, f)` (with `f(g,·)` injective — the encoder is
  reversible) and model an operation as a pair `(u, v)` of permutations.  `Dev(P) ≤ ε`
  is captured by `DevBound`.  The headline is **Theorem 2.10**
  (`subadditive-compose-deviation`):

      Dev(P₀ ∘ P₁) ≤ Dev(P₀) + Dev(P₁)

  which is what lets per-addition errors accumulate additively over a circuit.
  PROVED here (a finite union/injection bound), kernel-clean.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace FormalRV.Shor.Approx.Deviation

variable {G E C : Type} [Fintype G] [Fintype C] [DecidableEq E] [DecidableEq C]

/-- An approximate encoded permutation over a fixed encoder `f`: a desired logical
    permutation `u` and the cheap encoded permutation `v` actually performed
    (Gidney Def 2.1, leakage `L` omitted; `f` injective per input). -/
structure Op (G E C : Type) where
  u : G → G
  v : E → E
  v_inj : Function.Injective v

/-- The possible encodings of `g`: `{ f(g,c) | c ∈ C }` (Gidney Def 2.2). -/
def encodings (f : G → C → E) (g : G) : Finset E := Finset.univ.image (f g)

/-- The deviated coset of `g`: coset values `c` for which `v` sends `f(g,c)` outside
    the valid encodings of the desired output `u(g)` (Gidney Def 2.3). -/
def deviated (f : G → C → E) (P : Op G E C) (g : G) : Finset C :=
  Finset.univ.filter (fun c => P.v (f g c) ∉ encodings f (P.u g))

/-- `Dev(P) ≤ ε`: every input's deviated coset is at most an `ε`-fraction of `C`
    (Gidney Def 2.4, `Dev = max_g |Deviated_g|/|C|`). -/
def DevBound (f : G → C → E) (P : Op G E C) (ε : ℝ) : Prop :=
  ∀ g, ((deviated f P g).card : ℝ) ≤ ε * (Fintype.card C : ℝ)

/-- Sequential composition `P₀ ∘ P₁` over a shared encoder (Gidney Def 2.7):
    compose both the logical and the encoded permutations. -/
def Op.comp (P₀ P₁ : Op G E C) : Op G E C :=
  ⟨P₀.u ∘ P₁.u, P₀.v ∘ P₁.v, P₀.v_inj.comp P₁.v_inj⟩

/-- **Theorem 2.10 (subadditive-compose-deviation), proved.**
    `Dev(P₀ ∘ P₁) ≤ Dev(P₀) + Dev(P₁)`.  Hence applying `k` operations gives
    deviation `≤ k ·` (per-operation deviation): per-addition errors add up. -/
theorem DevBound_comp (f : G → C → E) (hf : ∀ g, Function.Injective (f g))
    (P₀ P₁ : Op G E C) (ε₀ ε₁ : ℝ)
    (h₀ : DevBound f P₀ ε₀) (h₁ : DevBound f P₁ ε₁) :
    DevBound f (P₀.comp P₁) (ε₀ + ε₁) := by
  intro g
  -- ρ c = v₁(f g c) — concrete, injective (no choice needed)
  set ρ : C → E := fun c => P₁.v (f g c) with hρ
  have hρ_inj : Function.Injective ρ := fun c c' h => hf g (P₁.v_inj h)
  -- B = the f-image of the P₀-deviated coset at the intermediate input P₁.u g
  set B : Finset E := (deviated f P₀ (P₁.u g)).image (f (P₁.u g)) with hB
  have hBcard : B.card = (deviated f P₀ (P₁.u g)).card :=
    Finset.card_image_of_injOn (fun a _ b _ h => hf (P₁.u g) h)
  -- the key inclusion
  have hsub : deviated f (P₀.comp P₁) g
      ⊆ deviated f P₁ g ∪ Finset.univ.filter (fun c => ρ c ∈ B) := by
    intro c hc
    rw [deviated, Finset.mem_filter] at hc
    obtain ⟨-, hc2⟩ := hc
    -- hc2 : (P₀.comp P₁).v (f g c) ∉ encodings f ((P₀.comp P₁).u g)
    --     = P₀.v (ρ c) ∉ encodings f (P₀.u (P₁.u g))
    by_cases hc1 : c ∈ deviated f P₁ g
    · exact Finset.mem_union_left _ hc1
    · refine Finset.mem_union_right _ ?_
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      -- c ∉ deviated P₁ g  ⟹  ρ c ∈ encodings f (P₁.u g)
      rw [deviated, Finset.mem_filter, not_and, not_not] at hc1
      have hρmem : ρ c ∈ encodings f (P₁.u g) := hc1 (Finset.mem_univ _)
      rw [encodings, Finset.mem_image] at hρmem
      obtain ⟨c', -, hc'⟩ := hρmem
      -- hc' : f (P₁.u g) c' = ρ c.  Show ρ c ∈ B, i.e. c' ∈ deviated P₀ (P₁.u g).
      rw [hB, Finset.mem_image]
      refine ⟨c', ?_, hc'⟩
      rw [deviated, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      -- need: P₀.v (f (P₁.u g) c') ∉ encodings f (P₀.u (P₁.u g))
      rw [hc']
      exact hc2
  -- card bound
  have hfilter_card : (Finset.univ.filter (fun c => ρ c ∈ B)).card ≤ B.card :=
    Finset.card_le_card_of_injOn ρ (fun c hc => (Finset.mem_filter.mp hc).2)
      (fun a _ b _ h => hρ_inj h)
  have hcard : (deviated f (P₀.comp P₁) g).card
      ≤ (deviated f P₁ g).card + (deviated f P₀ (P₁.u g)).card := by
    calc (deviated f (P₀.comp P₁) g).card
        ≤ (deviated f P₁ g ∪ Finset.univ.filter (fun c => ρ c ∈ B)).card :=
          Finset.card_le_card hsub
      _ ≤ (deviated f P₁ g).card + (Finset.univ.filter (fun c => ρ c ∈ B)).card :=
          Finset.card_union_le _ _
      _ ≤ (deviated f P₁ g).card + (deviated f P₀ (P₁.u g)).card := by
          rw [← hBcard]; exact Nat.add_le_add_left hfilter_card _
  -- to ℝ and combine the two bounds
  have hgoal : ((deviated f (P₀.comp P₁) g).card : ℝ)
      ≤ (ε₀ + ε₁) * (Fintype.card C : ℝ) := by
    have h0' := h₀ (P₁.u g)
    have h1' := h₁ g
    calc ((deviated f (P₀.comp P₁) g).card : ℝ)
        ≤ ((deviated f P₁ g).card : ℝ) + ((deviated f P₀ (P₁.u g)).card : ℝ) := by
          exact_mod_cast hcard
      _ ≤ ε₁ * (Fintype.card C : ℝ) + ε₀ * (Fintype.card C : ℝ) := by linarith
      _ = (ε₀ + ε₁) * (Fintype.card C : ℝ) := by ring
  exact hgoal

/-- The identity operation (`u = v = id`) has zero deviation: every encoding is
    already a valid encoding of itself. -/
def Op.id : Op G E C := ⟨fun g => g, fun e => e, fun _ _ h => h⟩

theorem DevBound_id (f : G → C → E) : DevBound f Op.id 0 := by
  intro g
  have hempty : deviated f Op.id g = ∅ := by
    rw [deviated]
    refine Finset.filter_false_of_mem (fun c _ => ?_)
    rw [not_not, encodings]
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
  rw [hempty, Finset.card_empty]
  simp

/-- Sequential composition of a list of operations (rightmost applied first). -/
def compList : List (Op G E C) → Op G E C
  | [] => Op.id
  | P :: Ps => P.comp (compList Ps)

/-- **Errors accumulate (Gidney Thm 2.10, iterated).**  A circuit that performs
    `k` approximate operations, each with deviation `≤ ε`, has total deviation
    `≤ k · ε`.  This is the quantitative "per-addition errors add up" the 8-hours
    paper uses for its total-deviation budget. -/
theorem DevBound_compList (f : G → C → E) (hf : ∀ g, Function.Injective (f g)) (ε : ℝ) :
    ∀ (Ps : List (Op G E C)), (∀ P ∈ Ps, DevBound f P ε) →
      DevBound f (compList Ps) ((Ps.length : ℝ) * ε)
  | [], _ => by
      show DevBound f (compList []) (((([] : List (Op G E C)).length : ℝ)) * ε)
      simp only [List.length_nil, Nat.cast_zero, zero_mul]
      exact DevBound_id f
  | P :: Ps, h => by
      have hP := h P (by simp)
      have hPs := DevBound_compList f hf ε Ps (fun Q hQ => h Q (by simp [hQ]))
      have hcomp := DevBound_comp f hf P (compList Ps) ε ((Ps.length : ℝ) * ε) hP hPs
      have heq : ((P :: Ps).length : ℝ) * ε = ε + (Ps.length : ℝ) * ε := by
        rw [List.length_cons]; push_cast; ring
      show DevBound f (compList (P :: Ps)) (((P :: Ps).length : ℝ) * ε)
      rw [heq]; exact hcomp

end FormalRV.Shor.Approx.Deviation
