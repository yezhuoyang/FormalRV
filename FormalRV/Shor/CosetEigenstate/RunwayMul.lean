/-
  FormalRV.Shor.CosetEigenstate.RunwayMul — the RUNWAY-PRESERVING coset multiplier (the
  CORRECT oracle model) and its EXACT orbit-shift.
  ════════════════════════════════════════════════════════════════════════════

  The adversarial audit (`CosetScalingAudit`) PROVED the literal `v ↦ c·v` coset multiplier
  is the wrong model — it coarsens the runway spacing `N → c·N`, giving only `≈ M/c` overlap
  with the canonical coset.  This file specifies the CORRECT model — a MODULAR-RESIDUE
  multiplier that keeps the runway index `j` fixed — and proves its orbit-shift is EXACT
  (no deviation), purely in `ℕ`/`Finset`/`QState` (NO circuit yet):

    `runwayMul c N v = (c·(v%N) mod N) + (v/N)·N`,   i.e.  `k + j·N ↦ (c·k mod N) + j·N`.

    * `runwayMul_on_coset` — THE key exact identity: on `k + j·N` (`k < N`) the residue maps
      `k ↦ (c·k) mod N` and the runway index `j` is UNCHANGED (spacing `N` preserved).
    * `runwayMul_residue_injective` / `_bijective` — under `Nat.Coprime c N` the residue map
      `k ↦ (c·k) mod N` is a permutation of `Fin N` (so `runwayMul` permutes the `N` cosets —
      this is what makes it usable as the QPE orbit operator `c = a`).
    * `runwayMul_window_image` — the EXACT orbit-shift at the value level: the window reps
      `{k+j·N | j<M}` map exactly to `{(c·k mod N)+j·N | j<M}` (`j` preserved term-by-term).
    * `runwayMulFin` + `runwayMulFin_cosetWindow_image` — lifted to `Fin dim`: under the two
      window-fit hypotheses, the source coset window maps EXACTLY onto the target coset
      window of `(c·k) mod N`.
    * `runwayMul_cosetState_shift` — THE EXACT COSET-STATE ORBIT-SHIFT: for a permutation `σ`
      realizing `runwayMulFin` on the windows, `permState σ⁻¹ (cosetState N m k) =
      cosetState N m ((c·k) mod N)` — EXACTLY (no deviation).  This is the `hshift` the
      eigenstate principle (`CosetEigenstateShift`) consumes, and it is EXACT for `runwayMul`
      (vs `Ω(1)` error for the literal `v ↦ c·v`).

  CONSEQUENCE for the Route-2 frontier: with this runway-preserving oracle the orbit-shift is
  EXACT, so the eigenstate-from-cyclic-shift reduction gives an EXACT coset eigenstate; the
  only residual `ε` is the already-handled WRAP/boundary mass.  The remaining circuit task is
  to build/identify a gate IMPLEMENTING `runwayMul` (NOT the repo's `cosetMulGate`, which is
  the audited bad `v ↦ c·v`).

  Self-contained `ℕ`/`Finset`/`QState` (no `uc_eval`).  Kernel-clean: no `sorry`, no
  `native_decide`, no axioms beyond the prelude.  De-risked via 3 parallel verified attempts.
-/
import FormalRV.Shor.CosetEigenstate.ApproxOp

namespace FormalRV.Shor.CosetEigenstate.RunwayMul

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.Shor.CosetEigenstate.ApproxOp (cosetState)
open FormalRV.Shor.CosetEigenstate.CosetClass (cosetWindow mem_cosetWindow)

/-! ## Lemma 1 (def): the runway-preserving coset multiplier. -/

/-- The RUNWAY-PRESERVING coset multiplier.  Given `v = k + j·N` with `k = v % N` (`k < N`)
    and `j = v / N` (the runway index), it multiplies ONLY the residue `k ↦ (c·k) mod N` and
    keeps the runway index `j` FIXED:  `v ↦ (c·k mod N) + j·N`.  The literal `v ↦ c·v`
    coarsens the spacing `N → cN`; `runwayMul` preserves the spacing `N`. -/
def runwayMul (c N v : Nat) : Nat := (c * (v % N)) % N + (v / N) * N

/-! ## Lemma 2 (THE KEY exact value identity — preserves `j`). -/

/-- On a coset representative `k + j·N` (with `k < N`), `runwayMul` multiplies the residue
    mod `N` and KEEPS the runway index `j`:  `runwayMul c N (k + j·N) = (c·k) % N + j·N`. -/
theorem runwayMul_on_coset (c N k j : Nat) (hk : k < N) :
    runwayMul c N (k + j * N) = (c * k) % N + j * N := by
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; omega)
  unfold runwayMul
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk,
      Nat.add_mul_div_right k j hN, Nat.div_eq_of_lt hk, Nat.zero_add]

/-! ## Lemma 3 (residue map is a permutation, given `Coprime`). -/

/-- The residue map `k ↦ (c·k) % N` is INJECTIVE on `Fin N` when `c` and `N` are coprime.
    (Together with `Fin N` finite, this makes it a bijection — the residue permutation
    underlying the runway multiplier.) -/
theorem runwayMul_residue_injective (c N : Nat) (hN : 0 < N) (hcop : Nat.Coprime c N) :
    Function.Injective
      (fun k : Fin N => (⟨(c * k.val) % N, Nat.mod_lt _ hN⟩ : Fin N)) := by
  intro a b hab
  have h1 : (c * a.val) % N = (c * b.val) % N := by simpa [Fin.ext_iff] using hab
  have h2 : c * a.val ≡ c * b.val [MOD N] := h1
  -- `cancel_left_of_coprime` wants `N.gcd c = 1`; `Nat.Coprime c N` is `c.gcd N = 1`.
  have hgcd : N.gcd c = 1 := by rw [Nat.gcd_comm]; exact hcop
  have h3 : a.val ≡ b.val [MOD N] := Nat.ModEq.cancel_left_of_coprime hgcd h2
  exact Fin.ext (by
    rw [Nat.ModEq] at h3
    rwa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at h3)

/-- The residue map is BIJECTIVE on `Fin N` (injective on a finite type). -/
theorem runwayMul_residue_bijective (c N : Nat) (hN : 0 < N) (hcop : Nat.Coprime c N) :
    Function.Bijective
      (fun k : Fin N => (⟨(c * k.val) % N, Nat.mod_lt _ hN⟩ : Fin N)) :=
  (Finite.injective_iff_bijective).mp (runwayMul_residue_injective c N hN hcop)

/-! ## Lemma 4 (the EXACT orbit-shift at the window/value level). -/

/-- **The exact orbit-shift (value/window level).**  The `runwayMul` images of the
    coset-window representatives `{k + j·N | j < M}` are EXACTLY the shifted-coset
    representatives `{(c·k mod N) + j·N | j < M}` — the runway index `j` is preserved term by
    term.  The clean contrast with the bad literal `v ↦ c·v` map (which gives spacing `cN`). -/
theorem runwayMul_window_image (c N k M : Nat) (hk : k < N) :
    (Finset.range M).image (fun j => runwayMul c N (k + j * N))
      = (Finset.range M).image (fun j => (c * k) % N + j * N) := by
  apply Finset.image_congr
  intro j _
  exact runwayMul_on_coset c N k j hk

/-! ## Lemma 5 (the exact coset-WINDOW image, lifted to the coset STATE). -/

/-- The total `Fin dim` index map induced by `runwayMul` (made total via `% dim`, which is
    the identity on every representative that fits the register). -/
def runwayMulFin (dim c N : Nat) (hdim : 0 < dim) (v : Fin dim) : Fin dim :=
  ⟨runwayMul c N (v : Nat) % dim, Nat.mod_lt _ hdim⟩

/-- **The EXACT coset-window orbit-shift (`Fin dim` level).**  Under the target-window fit
    `(c·k)%N + (2^m−1)·N < dim` AND the source-window fit `k + (2^m−1)·N < dim`, the image of
    the source window `cosetWindow dim N m k` under `runwayMulFin` is EXACTLY the shifted
    window `cosetWindow dim N m ((c·k)%N)` — runway index `j` preserved, residue multiplied,
    spacing `N` unchanged.  An EXACT equality (no sparse-overlap error). -/
theorem runwayMulFin_cosetWindow_image (dim N m c k : Nat) (hdim : 0 < dim) (hN : 0 < N)
    (hk : k < N) (hfit : (c * k) % N + (2 ^ m - 1) * N < dim)
    (hsrc : k + (2 ^ m - 1) * N < dim) :
    (cosetWindow dim N m k).image (runwayMulFin dim c N hdim)
      = cosetWindow dim N m ((c * k) % N) := by
  have hpow : 0 < 2 ^ m := Nat.two_pow_pos m
  have hcN : (c * k) % N < N := Nat.mod_lt _ hN
  ext w
  rw [Finset.mem_image]
  rw [mem_cosetWindow dim N m ((c * k) % N) hN]
  constructor
  · rintro ⟨v, hv, hvw⟩
    rw [mem_cosetWindow dim N m k hN] at hv
    obtain ⟨j, hj, hvj⟩ := hv
    refine ⟨j, hj, ?_⟩
    have hrun : runwayMul c N (v : Nat) = (c * k) % N + j * N := by
      rw [hvj]; exact runwayMul_on_coset c N k j hk
    have hbound : runwayMul c N (v : Nat) < dim := by
      rw [hrun]
      have : j * N ≤ (2 ^ m - 1) * N := Nat.mul_le_mul_right N (by omega)
      omega
    have : (w : Nat) = runwayMul c N (v : Nat) % dim := by
      rw [← hvw]; rfl
    rw [this, Nat.mod_eq_of_lt hbound, hrun]
  · rintro ⟨j, hj, hwj⟩
    have hsrcfit : k + j * N < dim := by
      have hjle : j * N ≤ (2 ^ m - 1) * N := Nat.mul_le_mul_right N (by omega)
      omega
    refine ⟨⟨k + j * N, hsrcfit⟩, ?_, ?_⟩
    · rw [mem_cosetWindow dim N m k hN]
      exact ⟨j, hj, rfl⟩
    · have hrun : runwayMul c N ((⟨k + j * N, hsrcfit⟩ : Fin dim) : Nat)
          = (c * k) % N + j * N := by
        show runwayMul c N (k + j * N) = (c * k) % N + j * N
        exact runwayMul_on_coset c N k j hk
      have hbound : runwayMul c N ((⟨k + j * N, hsrcfit⟩ : Fin dim) : Nat) < dim := by
        rw [hrun]
        have : j * N ≤ (2 ^ m - 1) * N := Nat.mul_le_mul_right N (by omega)
        omega
      apply Fin.ext
      show runwayMul c N ((⟨k + j * N, hsrcfit⟩ : Fin dim) : Nat) % dim = (w : Nat)
      rw [Nat.mod_eq_of_lt hbound, hrun, hwj]

/-- **THE EXACT COSET-STATE ORBIT-SHIFT (Lemma 5).**  For a permutation `σ : Equiv.Perm
    (Fin dim)` that realizes `runwayMulFin` on the source window and carries the target
    window back into the source (`hσ`, `hσinv`), reindexing `cosetState dim N m k` along `σ⁻¹`
    (`permState`) produces EXACTLY `cosetState dim N m ((c·k)%N)`: the runway multiplier carries
    the coset of `k` to the coset of `(c·k) mod N`, EXACTLY (same spacing `N`, no deviation).
    This is the `hshift` hypothesis the eigenstate-from-cyclic-shift reduction consumes. -/
theorem runwayMul_cosetState_shift (dim N m c k : Nat) (hdim : 0 < dim) (hN : 0 < N)
    (hk : k < N) (hfit : (c * k) % N + (2 ^ m - 1) * N < dim)
    (hsrc : k + (2 ^ m - 1) * N < dim)
    (σ : Equiv.Perm (Fin dim))
    (hσ : ∀ v : Fin dim, v ∈ cosetWindow dim N m k →
            σ v = runwayMulFin dim c N hdim v)
    (hσinv : ∀ w : Fin dim, w ∈ cosetWindow dim N m ((c * k) % N) →
            (σ⁻¹ w) ∈ cosetWindow dim N m k) :
    ApproxOp.permState σ⁻¹ (cosetState dim N m k) = cosetState dim N m ((c * k) % N) := by
  have himg := runwayMulFin_cosetWindow_image dim N m c k hdim hN hk hfit hsrc
  funext w z
  have hz : z = 0 := Subsingleton.elim z 0
  subst hz
  have hmem : w ∈ cosetWindow dim N m ((c * k) % N) ↔
      (σ⁻¹ w) ∈ cosetWindow dim N m k := by
    constructor
    · intro hw; exact hσinv w hw
    · intro hw
      have h1 : σ ((σ⁻¹ w)) = runwayMulFin dim c N hdim (σ⁻¹ w) := hσ _ hw
      have h2 : w = runwayMulFin dim c N hdim (σ⁻¹ w) := by
        rw [← h1]; simp
      rw [← himg, Finset.mem_image]
      exact ⟨σ⁻¹ w, hw, h2.symm⟩
  simp only [ApproxOp.permState, cosetState]
  by_cases hw : w ∈ cosetWindow dim N m ((c * k) % N)
  · rw [if_pos hw, if_pos (hmem.mp hw)]
  · rw [if_neg hw, if_neg (fun hc => hw (hmem.mpr hc))]

end FormalRV.Shor.CosetEigenstate.RunwayMul
