/-
  FormalRV.Shor.CosetEigenstate.CosetClass — the coset WINDOW (Zalka/Gidney).
  ════════════════════════════════════════════════════════════════════════════

  CORRECTED after reading Gidney, "Approximate encoded permutations and piecewise
  quantum adders" (arXiv:1905.08488).  The coset representation of `r mod N` is the
  uniform superposition over a FIXED window of `2^m` representatives:

      |Coset_m(r)⟩  =  (1/√2^m) · ∑_{j=0}^{2^m−1} |r + j·N⟩      (paper Def. 3.1)

  — NOT the variable-size residue class `{v < 2^bits : v ≡ r}`.  Every window has
  EXACTLY `2^m` elements, so there is NO size mismatch.  The deviation comes from a
  different place: when you add `k` (non-modularly) to the window, exactly ONE
  representative — the top one, `j = 2^m−1` — can wrap past the register, so the
  per-addition deviation is `1/2^m` (paper Thm 3.2), and deviations are subadditive
  (Thms 2.11–2.12).  (My earlier "size mismatch = deviation" claim here was WRONG;
  the index set fed to `uniformSuperposition` is this fixed window.)

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators

namespace FormalRV.Shor.CosetEigenstate.CosetClass

/-- The coset window: the `2^m` representatives `{r, r+N, …, r+(2^m−1)·N}` of the
    residue `r` that live in the register `Fin dim`.  Characterized by a DECIDABLE,
    division-free predicate (`r ≤ v`, `N ∣ (v−r)`, and `v−r < 2^m·N`). -/
def cosetWindow (dim N m r : Nat) : Finset (Fin dim) :=
  Finset.univ.filter
    (fun v => r ≤ (v : Nat) ∧ ((v : Nat) - r) % N = 0 ∧ (v : Nat) - r < 2 ^ m * N)

/-- Membership in terms of the `2^m` representatives (`N > 0`). -/
theorem mem_cosetWindow (dim N m r : Nat) (hN : 0 < N) (v : Fin dim) :
    v ∈ cosetWindow dim N m r ↔ ∃ j, j < 2 ^ m ∧ (v : Nat) = r + j * N := by
  rw [cosetWindow, Finset.mem_filter]
  constructor
  · rintro ⟨_, hge, hmod, hlt⟩
    have hmul : ((v : Nat) - r) / N * N = (v : Nat) - r :=
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
    refine ⟨((v : Nat) - r) / N, ?_, ?_⟩
    · have : ((v : Nat) - r) / N * N < 2 ^ m * N := by rw [hmul]; exact hlt
      exact Nat.lt_of_mul_lt_mul_right this
    · omega
  · rintro ⟨j, hj, hvj⟩
    have hsub : (v : Nat) - r = j * N := by omega
    refine ⟨Finset.mem_univ v, by omega, ?_, ?_⟩
    · rw [hsub]; exact Nat.mul_mod_left j N
    · rw [hsub]; exact (Nat.mul_lt_mul_right hN).mpr hj

/-- The base representative `r` (i.e. `j = 0`) is in the window (`r < dim`, `N > 0`). -/
theorem cosetRep_mem_window (dim N m r : Nat) (hN : 0 < N) (hr : r < dim) :
    (⟨r, hr⟩ : Fin dim) ∈ cosetWindow dim N m r := by
  rw [mem_cosetWindow dim N m r hN]
  exact ⟨0, Nat.two_pow_pos m, by simp⟩

/-- The window is NONEMPTY when its base representative fits. -/
theorem cosetWindow_nonempty (dim N m r : Nat) (hN : 0 < N) (hr : r < dim) :
    (cosetWindow dim N m r).Nonempty :=
  ⟨_, cosetRep_mem_window dim N m r hN hr⟩

/-- **Constant size — the heart of the correction.**  When all `2^m` representatives
    fit in the register (`r + (2^m−1)·N < dim`) and `N > 0`, the window has EXACTLY
    `2^m` elements — independent of `r`.  So the orbit shift between two windows is a
    genuine `2^m → 2^m` bijection; the deviation is NOT a size mismatch but the
    top-representative wrap (Gidney Thm 3.2). -/
theorem cosetWindow_card (dim N m r : Nat) (hN : 0 < N)
    (hfit : r + (2 ^ m - 1) * N < dim) :
    (cosetWindow dim N m r).card = 2 ^ m := by
  have hbound : ∀ j, j < 2 ^ m → r + j * N < dim := by
    intro j hj
    have : j * N ≤ (2 ^ m - 1) * N := Nat.mul_le_mul_right N (by omega)
    omega
  rw [← Finset.card_range (2 ^ m)]
  refine (Finset.card_bij
    (fun j hj => (⟨r + j * N, hbound j (Finset.mem_range.mp hj)⟩ : Fin dim)) ?_ ?_ ?_).symm
  · intro j hj
    rw [mem_cosetWindow dim N m r hN]
    exact ⟨j, Finset.mem_range.mp hj, rfl⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    have hval : r + j₁ * N = r + j₂ * N := congrArg Fin.val heq
    exact Nat.eq_of_mul_eq_mul_right hN (by omega)
  · intro v hv
    rw [mem_cosetWindow dim N m r hN] at hv
    obtain ⟨j, hj, hvj⟩ := hv
    exact ⟨j, Finset.mem_range.mpr hj, Fin.ext hvj.symm⟩

end FormalRV.Shor.CosetEigenstate.CosetClass
