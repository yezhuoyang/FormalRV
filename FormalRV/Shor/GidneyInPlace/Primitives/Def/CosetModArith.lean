/-
  FormalRV.Shor.GidneyInPlace.CosetModArith — modular arithmetic for the inverse
  (uncompute) leg of the in-place coset multiplier.
  ════════════════════════════════════════════════════════════════════════════

  The in-place trick `mulFwd ; swap ; reverse mulInv` un-computes the scratch with a
  multiply by `a⁻¹`.  For that we need, from `Nat.Coprime a N`:

    * the modular inverse `aInv` with `(a * aInv) % N = 1`              (existence),
    * the in-place cancellation identity `aInv * (a * x) ≡ x (mod N)`   (correctness),

  so that the uncompute returns the scratch to the residue `0` (encoded as
  `cosetState N m 0`, NOT exact basis zero — the coset of `0`).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq

namespace FormalRV.Shor.GidneyInPlace.CosetModArith

/-- **Existence of the modular inverse from coprimality.**  If `a` is coprime to `N`
    and `1 < N`, there is a canonical `aInv < N` with `(a * aInv) % N = 1`.  (Direct
    from Mathlib's `Nat.exists_mul_emod_eq_one_of_coprime`.) -/
theorem cosetModInv_exists (a N : Nat) (hcop : Nat.Coprime a N) (hN : 1 < N) :
    ∃ aInv, aInv < N ∧ (a * aInv) % N = 1 :=
  Nat.exists_mul_mod_eq_one_of_coprime hcop hN

/-- **The in-place cancellation identity.**  Given `(a * aInv) % N = 1` (the modular
    inverse relation) and a canonical residue `x < N`, multiplying by `a` then by
    `aInv` returns `x` exactly (mod `N`): `aInv · (a · x) ≡ x (mod N)`.  This is what
    makes the uncompute leg restore the scratch residue to `x` (here `x = 0` after
    the forward multiply has been swapped out). -/
theorem modInv_mul_cancel (N a aInv x : Nat) (hN : 1 < N) (hx : x < N)
    (hinv : (a * aInv) % N = 1) :
    (aInv * (a * x)) % N = x := by
  have hmod : a * aInv ≡ 1 [MOD N] := by
    show (a * aInv) % N = 1 % N
    rw [hinv, Nat.mod_eq_of_lt hN]
  have hcong : aInv * (a * x) ≡ x [MOD N] := by
    have e1 : aInv * (a * x) = (a * aInv) * x := by
      rw [← mul_assoc, mul_comm aInv a]
    rw [e1]
    have e2 : (a * aInv) * x ≡ 1 * x [MOD N] := Nat.ModEq.mul_right x hmod
    rwa [one_mul] at e2
  have h2 : (aInv * (a * x)) % N = x % N := hcong
  rw [h2, Nat.mod_eq_of_lt hx]

/-- **The uncompute residue is `0`.**  Specialization at `x = 0`: after the forward
    multiply (`a·0 = 0`), the inverse multiply leaves residue `aInv · 0 = 0`.  This
    is the residue the scratch carries — encoded as `cosetState N m 0`, not exact
    zero — at the end of the in-place multiplier. -/
theorem modInv_uncompute_zero (N a aInv : Nat) (hN : 1 < N)
    (hinv : (a * aInv) % N = 1) :
    (aInv * (a * 0)) % N = 0 :=
  modInv_mul_cancel N a aInv 0 hN (by omega) hinv

end FormalRV.Shor.GidneyInPlace.CosetModArith
