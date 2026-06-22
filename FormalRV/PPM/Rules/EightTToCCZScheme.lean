/-
  FormalRV.PPM.Rules.EightTToCCZScheme — the famous 8T→CCZ (7-T) gate
  identity, proved sorry-free from first principles.

  ## What this file proves

  The standard fault-tolerant way to realise a `CCZ` (and hence a
  Toffoli, via `CCX = H_c · CCZ · H_c`) is to spend T-gates: the
  diagonal phase of `CCZ` on a computational basis state `|abc⟩` is
  `(-1)^{a∧b∧c}`, and this phase is produced by the **phase-polynomial**
  of seven conditional `T`/`T†` rotations (one per nonempty parity of
  the three inputs):

      T_a · T_b · T_c · T†_{a⊕b} · T†_{b⊕c} · T†_{a⊕c} · T_{a⊕b⊕c}.

  Writing `ω = e^{iπ/4}` (an 8th root of unity, the T phase), the net
  phase on `|abc⟩` is `ω^{E(a,b,c)}` where

      E(a,b,c) = [a]+[b]+[c] + 7[a⊕b] + 7[b⊕c] + 7[a⊕c] + [a⊕b⊕c]

  (the `7` is `T† = ω⁻¹ = ω⁷`).  The content of the identity is the
  **decidable** congruence

      E(a,b,c) ≡ 4·[a∧b∧c]   (mod 8),

  proved by `decide` over the 8 Boolean inputs, which gives
  `ω^{E} = (ω⁴)^{[a∧b∧c]} = (-1)^{[a∧b∧c]}` — exactly the `CCZ` phase.

  Headline results:
  * `eightT_ccz_phase`  — the scalar phase-polynomial identity.
  * `tDecompMat_eq_cczMat` — the matrix-level gate identity: the
    diagonal unitary built from the seven T-phases equals the `CCZ`
    matrix.

  ## Honesty boundary

  * This is the **gate-level unitary identity** for `CCZ`.  The `CNOT`
    routing that physically computes the parities `a⊕b`, … into the
    register (and uncomputes them) is the standard Clifford wrapper; on
    the three data qubits the net unitary is exactly the diagonal phase
    proved here, so no spurious phases remain.
  * "8 T" vs "7 T": seven conditional rotations appear in the phase
    polynomial; the *eighth* T is the catalyst / magic-state convention
    used by distillation accounting (`Factory.EightTToCCZSpec`).  This
    file proves the *phase identity*; the resource count is a separate,
    already-modelled concern.
  * Magic-state *distillation* correctness and the physical T-state are
    NOT in scope here — this is the logical Clifford+T gate identity.
-/
import FormalRV.Core.QuantumLib

namespace FormalRV.Framework.EightTToCCZ

open scoped Matrix

/-! ## §1. The T phase `ω = e^{iπ/4}` and its powers. -/

/-- The T-gate phase `ω = exp(iπ/4)`, a primitive 8th root of unity. -/
noncomputable def ω : ℂ := Complex.exp (Complex.I * (Real.pi / 4))

theorem ω_pow_four : ω ^ 4 = -1 := by
  unfold ω
  rw [← Complex.exp_nat_mul]
  rw [show ((4 : ℕ) : ℂ) * (Complex.I * ((Real.pi : ℂ) / 4)) = (Real.pi : ℂ) * Complex.I by
        push_cast; ring]
  exact Complex.exp_pi_mul_I

theorem ω_pow_eight : ω ^ 8 = 1 := by
  have h : ω ^ 8 = (ω ^ 4) ^ 2 := by ring
  rw [h, ω_pow_four]; ring

/-- `ω^n` depends only on `n mod 8`. -/
theorem ω_pow_mod_eight (n : Nat) : ω ^ n = ω ^ (n % 8) := by
  conv_lhs => rw [← Nat.div_add_mod n 8]
  rw [pow_add, pow_mul, ω_pow_eight, one_pow, one_mul]

/-! ## §2. The phase polynomial. -/

/-- Boolean → {0,1} indicator (as a `Nat`). -/
def bitN (x : Bool) : Nat := if x then 1 else 0

/-- The net T-phase exponent of the seven-rotation `CCZ` phase
    polynomial on input `|abc⟩`.  `T = ω`, `T† = ω⁻¹ = ω⁷` (hence the
    `7·` coefficients on the pair parities). -/
def tExp (a b c : Bool) : Nat :=
  bitN a + bitN b + bitN c
    + 7 * bitN (xor a b) + 7 * bitN (xor b c) + 7 * bitN (xor a c)
    + bitN (xor (xor a b) c)

/-- **The decidable core**: the phase-polynomial exponent is `≡ 4·[a∧b∧c]`
    modulo 8.  Proved by `decide` over the eight Boolean inputs. -/
theorem tExp_mod_eight (a b c : Bool) :
    tExp a b c % 8 = 4 * bitN (a && b && c) := by
  revert a b c; decide

/-! ## §3. The scalar gate identity. -/

/-- The diagonal phase that `CCZ` applies to `|abc⟩`: `-1` iff all three
    bits are set, else `+1`. -/
def cczPhase (a b c : Bool) : ℂ := if a && b && c then -1 else 1

/-- **Headline (scalar form).** The seven-T phase polynomial produces
    exactly the `CCZ` phase on every computational basis input. -/
theorem eightT_ccz_phase (a b c : Bool) :
    ω ^ (tExp a b c) = cczPhase a b c := by
  rw [ω_pow_mod_eight, tExp_mod_eight]
  rcases Bool.eq_false_or_eq_true (a && b && c) with h | h <;>
    simp [cczPhase, bitN, h, ω_pow_four]

/-! ## §4. The matrix-level gate identity. -/

/-- The `CCZ` unitary as an 8×8 diagonal matrix: identity except a `-1`
    phase on `|111⟩` (index 7). -/
noncomputable def cczMat : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal (fun i => if i = 7 then -1 else 1)

/-- Decode the high / mid / low bit of a basis index `i < 8`
    (`i = 4·a + 2·b + c`, big-endian). -/
def aOf (i : Fin 8) : Bool := decide (4 ≤ i.val)
def bOf (i : Fin 8) : Bool := decide (2 ≤ i.val % 4)
def cOf (i : Fin 8) : Bool := decide (i.val % 2 = 1)

/-- The diagonal unitary assembled from the seven-T phase polynomial. -/
noncomputable def tDecompMat : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal (fun i => ω ^ tExp (aOf i) (bOf i) (cOf i))

/-- **Headline (matrix form).** The T-phase-polynomial diagonal unitary
    *equals* the `CCZ` matrix.  This is the famous 8T→CCZ gate identity
    at the unitary level. -/
theorem tDecompMat_eq_cczMat : tDecompMat = cczMat := by
  have hfun :
      (fun i => ω ^ tExp (aOf i) (bOf i) (cOf i))
        = (fun (i : Fin 8) => (if i = 7 then (-1 : ℂ) else 1)) := by
    funext i
    rw [eightT_ccz_phase]
    fin_cases i <;> simp [aOf, bOf, cOf, cczPhase]
  unfold tDecompMat cczMat
  rw [hfun]

end FormalRV.Framework.EightTToCCZ
