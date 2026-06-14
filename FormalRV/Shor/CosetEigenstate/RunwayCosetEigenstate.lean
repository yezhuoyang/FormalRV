/-
  FormalRV.Shor.CosetEigenstate.RunwayCosetEigenstate — the EIGENSTATE ASSEMBLY: the coset
  orbit state is an EXACT eigenstate of the runway-preserving multiplier.  Closes the
  ABSTRACT coset-Shor route.
  ════════════════════════════════════════════════════════════════════════════

  Feeds the EXACT runway orbit-shift (`RunwayMul.runwayMul_cosetState_shift`:
  `U |coset(k)⟩ = |coset(a·k mod N)⟩`) into the eigenstate-from-cyclic-shift principle
  (`CosetEigenstateShift.eigenstate_rootOfUnity`).  Result: the root-of-unity-weighted coset
  orbit `∑_{t : ZMod r} χ(t) • |coset(a^{t} mod N)⟩` is an EXACT eigenstate of the abstract
  runway oracle `U`, eigenvalue `ζ⁻¹` — NO circuit, NO `uc_eval`, NO Cuccaro; `U` is an
  abstract `Matrix` and `hrun` is exactly the runway orbit-shift.

    * `pow_mod_period` — `a^r % N = 1 ⟹ a^n % N = a^(n%r) % N` (the `ZMod r` orbit closes:
      `a^(r-1) ↦ a^r ≡ 1`).  Pure `Nat.ModEq`.
    * `runwayMul_coset_eigenstate` — THE eigenstate: `U · (∑_t χ(t)•|coset(a^t mod N)⟩) =
      ζ⁻¹ • (∑_t χ(t)•|coset(a^t mod N)⟩)`.

  AUDIT (the three convention points, all honest hypotheses):
    (1) WRAP / closure: `a^r % N = 1` (i.e. `a^r ≡ 1 mod N`) — exactly what closes the
        `ZMod r` orbit; for QPE this is `r = ord_N(a)`.
    (2) EIGENVALUE convention: the eigenvalue is `ζ⁻¹` (inherited from `eigenstate_rootOfUnity`).
        For a downstream QPE expecting eigenvalue `ω^s`, take `ζ = ω^{-s}` so `ζ⁻¹ = ω^s`.
    (3) `1 < r` (order `r ≥ 2` for any nontrivial `a`) — needed for `ZMod.val_one`; `0 < N`
        for `Nat.mod_lt`.

  CONSEQUENCE.  With the runway-preserving oracle the eigenstate is EXACT (no orbit-shift
  deviation), so the abstract coset-Shor route is essentially closed: the only residual `ε`
  is the already-handled wrap/boundary mass, and the SOLE remaining hard obligation is a
  `Gate` IMPLEMENTING `runwayMul` (the runway-preserving modular multiplier — NOT the repo's
  `cosetMulGate`, which is the audited bad `v ↦ c·v`).

  Note: `cosetVec` is a thin type-exposing wrapper, DEFINITIONALLY `cosetState` — `QState dim`
  is a non-reducible `def` for `Matrix (Fin dim)(Fin 1) ℂ`, so the `HMul`/`HSMul` instances do
  not fire through it; `cosetVec` exposes the matrix type so `U * _` and `ζ • _` typecheck.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.  De-risked via
  3 parallel verified attempts.
-/
import FormalRV.Shor.CosetEigenstate.CosetEigenstateShift
import FormalRV.Shor.CosetEigenstate.ApproxOp

namespace FormalRV.Shor.CosetEigenstate.RunwayCosetEigenstate

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.Shor.CosetEigenstate.ApproxOp (cosetState)
open FormalRV.Shor.CosetEigenstate.CosetEigenstateShift (eigenstate_rootOfUnity)

/-- A coset state, viewed as the underlying column-vector matrix.  `QState dim` is a plain
    (non-reducible) `def` for `Matrix (Fin dim)(Fin 1) ℂ`, so the matrix-mul / scalar-smul
    instances do not fire through it; this thin wrapper (definitionally `cosetState`) exposes
    the matrix type so `U * _` and `ζ • _` typecheck.  No content is added. -/
noncomputable def cosetVec (dim N m k : Nat) : Matrix (Fin dim) (Fin 1) ℂ :=
  cosetState dim N m k

/-- **Pow-periodicity from `a^r ≡ 1 (mod N)`.**  If `a^r % N = 1`, then `a^n % N` depends only
    on `n % r` — this is what makes the `ZMod r` orbit `t ↦ a^{t.val} mod N` well-defined and
    closed.  Proof: `a^n = (a^r)^(n/r) · a^(n%r) ≡ 1^(n/r) · a^(n%r) = a^(n%r) [MOD N]`. -/
theorem pow_mod_period (a N r n : Nat) (har : a ^ r % N = 1) :
    a ^ n % N = a ^ (n % r) % N := by
  -- `har : a^r % N = 1` already forces `N ≠ 1` (else `a^r % 1 = 0 ≠ 1`), so `1 % N = 1`.
  have hN1 : 1 % N = 1 := by
    rcases eq_or_ne N 1 with rfl | hne
    · rw [Nat.mod_one] at har; exact absurd har (by norm_num)
    · exact Nat.one_mod_eq_one.mpr hne
  have h1 : a ^ r ≡ 1 [MOD N] := by
    unfold Nat.ModEq; rw [har, hN1]
  calc a ^ n = a ^ (r * (n / r) + n % r) := by rw [Nat.div_add_mod]
    _ = (a ^ r) ^ (n / r) * a ^ (n % r) := by rw [pow_add, pow_mul]
    _ ≡ 1 ^ (n / r) * a ^ (n % r) [MOD N] := (h1.pow (n / r)).mul_right _
    _ = a ^ (n % r) := by rw [one_pow, one_mul]

/-- **THE COSET-ORBIT EIGENSTATE (closes the abstract route).**  For an abstract matrix `U`
    whose only assumed property is the per-residue runway orbit-shift
    `U |coset(k)⟩ = |coset(a·k mod N)⟩` (`k < N`, the `runwayMul_cosetState_shift` content),
    the root-of-unity-weighted coset orbit `∑_t χ(t) • |coset(a^{t} mod N)⟩` is an EXACT
    eigenstate of `U` with eigenvalue `ζ⁻¹`.  No circuit, no `uc_eval`, no Cuccaro. -/
theorem runwayMul_coset_eigenstate {dim N m a r : Nat} [NeZero r]
    (U : Matrix (Fin dim) (Fin dim) ℂ) {ζ : ℂ} (hζ : ζ ^ r = 1)
    (hN : 0 < N) (hr : 1 < r) (har : a ^ r % N = 1)
    (hrun : ∀ k, k < N → U * cosetVec dim N m k = cosetVec dim N m ((a * k) % N)) :
    U * (∑ t : ZMod r, (AddChar.zmodChar r hζ) t • cosetVec dim N m (a ^ t.val % N))
      = ζ⁻¹ • (∑ t : ZMod r, (AddChar.zmodChar r hζ) t • cosetVec dim N m (a ^ t.val % N)) := by
  apply eigenstate_rootOfUnity U (fun t => cosetVec dim N m (a ^ t.val % N)) hζ
  intro t
  -- goal: U * cosetVec dim N m (a^t.val % N) = cosetVec dim N m (a^((t+1).val) % N)
  rw [hrun (a ^ t.val % N) (Nat.mod_lt _ hN)]
  -- goal: cosetVec dim N m ((a * (a^t.val % N)) % N) = cosetVec dim N m (a^((t+1).val) % N)
  congr 1
  -- arithmetic: (a * (a^t.val % N)) % N = a^((t+1).val) % N
  have hLHS : (a * (a ^ t.val % N)) % N = a ^ (t.val + 1) % N := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← pow_succ']
  have hval : (t + 1).val = (t.val + 1) % r := by
    haveI : Fact (1 < r) := ⟨hr⟩
    rw [ZMod.val_add, ZMod.val_one]
  rw [hLHS, hval, pow_mod_period a N r (t.val + 1) har]

end FormalRV.Shor.CosetEigenstate.RunwayCosetEigenstate
