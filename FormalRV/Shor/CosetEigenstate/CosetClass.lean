/-
  FormalRV.Shor.CosetEigenstate.CosetClass — the coset C_j = residue class mod N.
  ════════════════════════════════════════════════════════════════════════════

  The orbit basis of the faithful coset eigenstate is the uniform superposition
  over a COSET: the set of register values `< 2^bits` congruent to `aʲ mod N`,

      cosetClass bits N c  =  { v < 2^bits : v ≡ c  (mod N) }.

  This is the index set `S` fed to `uniformSuperposition`.  Here we build the
  object and its two foundational facts — membership and nonemptiness (a residue
  always has the representative `c % N < 2^bits` when `N ≤ 2^bits`).

  THE DEVIATION, MADE CONCRETE (the honest frontier, named not hidden).  These
  classes do NOT all have the same size: `|cosetClass bits N c| ∈ {⌊2^bits/N⌋,
  ⌈2^bits/N⌉}`, the value depending on `c % N`.  So the orbit shift
  `cosetClass(aʲ) → cosetClass(aʲ⁺¹)` is a bijection EXACTLY when the two classes
  have equal size, and is off by one representative otherwise — and that O(1)
  per-step mismatch, accumulated over the orbit, IS the source of the wrap
  deviation `W`.  This file pins the object; the size-mismatch analysis and the
  gadget-driven shift are the next (genuinely mathematical) steps.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators

namespace FormalRV.Shor.CosetEigenstate.CosetClass

/-- The coset of register values `< 2^bits` congruent to `c` modulo `N`. -/
def cosetClass (bits N c : Nat) : Finset (Fin (2 ^ bits)) :=
  Finset.univ.filter (fun v => v.val % N = c % N)

/-- Membership: `v ∈ cosetClass bits N c ↔ v ≡ c (mod N)`. -/
@[simp] theorem mem_cosetClass (bits N c : Nat) (v : Fin (2 ^ bits)) :
    v ∈ cosetClass bits N c ↔ v.val % N = c % N := by
  simp [cosetClass]

/-- The canonical representative `c % N` lives in the class (`< 2^bits` when
    `N ≤ 2^bits`). -/
theorem cosetRep_mem (bits N c : Nat) (hN : 0 < N) (hNle : N ≤ 2 ^ bits) :
    (⟨c % N, lt_of_lt_of_le (Nat.mod_lt c hN) hNle⟩ : Fin (2 ^ bits)) ∈ cosetClass bits N c := by
  rw [mem_cosetClass]
  exact Nat.mod_eq_of_lt (Nat.mod_lt c hN)

/-- The class is NONEMPTY (so `uniformSuperposition` over it is a genuine state)
    whenever `N ≤ 2^bits`. -/
theorem cosetClass_nonempty (bits N c : Nat) (hN : 0 < N) (hNle : N ≤ 2 ^ bits) :
    (cosetClass bits N c).Nonempty :=
  ⟨_, cosetRep_mem bits N c hN hNle⟩

/-- Hence the class has positive cardinality — `uniformSuperposition` is normalized
    (`uniformSuperposition_total`). -/
theorem cosetClass_card_pos (bits N c : Nat) (hN : 0 < N) (hNle : N ≤ 2 ^ bits) :
    0 < (cosetClass bits N c).card :=
  Finset.card_pos.mpr (cosetClass_nonempty bits N c hN hNle)

end FormalRV.Shor.CosetEigenstate.CosetClass
