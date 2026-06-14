/-
  FormalRV.Shor.CosetEigenstate.CosetTableSum — the windowed table-sum (endian audit)
  and the discharge of the `hfwd` obligation for an out-of-place coset multiplier.
  ════════════════════════════════════════════════════════════════════════════

  The out-of-place windowed coset multiplier adds, for each window `j` of the input
  `x`, the table constant `a·(2^w)^j·windowⱼ(x) mod N` into the coset accumulator.
  This file proves:

    * TABLE-SUM (endian audit): folding those window constants through the coset
      framework's IDEAL modular accumulator `idealAcc` (from `0`) computes exactly
      `(a·x) mod N`.  The window digit `windowⱼ(x) = (x/(2^w)^j) % 2^w` is the SAME
      base-`2^w` convention used by `decodeReg` and by the `cosetState` indices
      `k+j·N` (all Nat values), so the encodings are mutually consistent.  This reuses
      the proven windowed value-correctness `WindowedArith.windowedLookupFold_eq_modmul`
      — `idealAcc` and `windowedLookupFold` are literally the same modular fold.

    * DISCHARGE of `hfwd`: from a concrete out-of-place multiplier's per-input-branch
      contract (each control branch `b`, holding input `xval b`, runs the coset fold
      with the window table constants; control=0 branches agree; sub-normalized
      control), the forward leg's Born-L1 deviation from the IDEAL coset result
      `cosetState N m ((a·xval b) mod N)` is `≤ numWin·(2/2^m)` — discharging the
      `hfwd` hypothesis of `InPlaceCoset.inPlaceMul_coset_deviation_sqir`.

  HONEST FENCE.  The per-branch contract (`hfac_act` — that the LITERAL `uc_eval(mulFwd)`
  runs the coset fold on the scratch register, framing unrelated qubits and restoring
  ancilla) must be discharged by a concrete NON-MODULAR (runway) coset multiplier
  circuit.  The repo's existing `windowedMulCircuitOf` is the EXACT-MODULAR multiplier
  (zero deviation, a stronger-but-different object); a non-modular coset circuit with
  this Boolean contract is the remaining circuit-construction work.  What is proven
  here is the value identity + the deviation reduction; the contract is stated
  explicitly as the discharge hypothesis.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.CosetMul
import FormalRV.Arithmetic.Windowed.WindowedArith

namespace FormalRV.Shor.CosetEigenstate.CosetTableSum

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetEigenstate.ApproxOp (cosetState)
open FormalRV.Shor.CosetEigenstate.CosetMul (idealAcc actualAcc cosetMul_superposition_deviation)
open FormalRV.Shor.CosetEigenstate.ControlledLift (branchOf)
open FormalRV.Shor.WindowedArith (window tableValue windowedLookupFold windowedLookupFold_eq_modmul)

/-- The coset window constant for window `j` of input `x`: the table value
    `a·(2^w)^j·windowⱼ(x) mod N` — exactly what window `j`'s controlled lookup-add
    deposits into the coset accumulator. -/
def cosetWindowConst (a N w x : Nat) : Nat → Nat :=
  fun j => tableValue a N w j (window w x j)

/-- Each window constant is a canonical residue `< N`. -/
theorem cosetWindowConst_lt (a N w x : Nat) (hN : 0 < N) (j : Nat) :
    cosetWindowConst a N w x j < N := by
  simp only [cosetWindowConst, tableValue]
  exact Nat.mod_lt _ hN

/-- The coset ideal accumulator over the window constants IS the windowed modular fold
    (same per-step `(acc + cⱼ) mod N`). -/
theorem idealAcc_eq_windowedLookupFold (a N w x acc : Nat) :
    ∀ n, idealAcc N acc (cosetWindowConst a N w x) n
        = windowedLookupFold a N w (window w x) n acc := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
      show (idealAcc N acc (cosetWindowConst a N w x) m + cosetWindowConst a N w x m) % N
        = (windowedLookupFold a N w (window w x) m acc + tableValue a N w m (window w x m)) % N
      rw [ih]; simp only [cosetWindowConst]

/-- **THE TABLE-SUM (endian-consistent value identity).**  Folding the window table
    constants of `x` through the coset framework's modular accumulator from `0`
    computes exactly `(a·x) mod N` — the value an out-of-place modular multiplier
    targets.  (Reuses the proven `windowedLookupFold_eq_modmul`.) -/
theorem idealAcc_cosetWindowConst (a N w numWin x : Nat) (hN : 0 < N)
    (hx : x < (2 ^ w) ^ numWin) :
    idealAcc N 0 (cosetWindowConst a N w x) numWin = (a * x) % N := by
  rw [idealAcc_eq_windowedLookupFold a N w x 0 numWin,
      windowedLookupFold_eq_modmul a N w numWin x hN hx]

/-- **DISCHARGE OF `hfwd` FOR THE OUT-OF-PLACE COSET MULTIPLIER.**  Given the concrete
    multiplier's per-input-branch contract — each active control branch `b` (holding
    input `xval b < (2^w)^numWin`) runs the coset fold with the window table constants
    `cosetWindowConst a N w (xval b)` on the scratch; control=0 branches agree;
    sub-normalized control — the forward leg's Born-L1 deviation from the IDEAL coset
    result `cosetState N m ((a·xval b) mod N)` is `≤ numWin·(2/2^m)`.  This is exactly
    the `hfwd` obligation of `inPlaceMul_coset_deviation_sqir` (with `numAdds = numWin`).

    The ideal target is the genuine coset out-of-place modmul result (`(a·x) mod N`),
    by the table-sum.  The contract `hfac_act` (the literal gate runs the coset fold,
    framing unrelated qubits / restoring ancilla) is the concrete-circuit obligation. -/
theorem cosetOutOfPlace_hfwd {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (s_act s_idl : QState full_dim) (active : Finset (Fin m_dim)) (β : Fin m_dim → ℂ)
    (a N m w numWin : Nat) (xval : Fin m_dim → Nat)
    (hN : 0 < N) (hxval : ∀ b, b ∈ active → xval b < (2 ^ w) ^ numWin)
    (hfit : N + 2 ^ m * N ≤ full_dim / m_dim)
    (hzero : ∀ b, b ∉ active → branchOf h s_act b = branchOf h s_idl b)
    (hfac_act : ∀ b, b ∈ active → branchOf h s_act b
        = fun i z => β b * actualAcc (full_dim / m_dim) N m 0 (cosetWindowConst a N w (xval b)) numWin i z)
    (hfac_idl : ∀ b, b ∈ active → branchOf h s_idl b
        = fun i z => β b * cosetState (full_dim / m_dim) N m ((a * xval b) % N) i z)
    (hweight : ∑ b ∈ active, Complex.normSq (β b) ≤ 1) :
    normSqDist s_act s_idl ≤ (numWin : ℝ) * (2 / 2 ^ m) := by
  refine cosetMul_superposition_deviation h s_act s_idl active β N m 0 numWin
    (fun b => cosetWindowConst a N w (xval b)) hN hN
    (fun b t => cosetWindowConst_lt a N w (xval b) hN t) hfit hzero hfac_act ?_ hweight
  intro b hb
  rw [hfac_idl b hb]
  funext i z
  rw [idealAcc_cosetWindowConst a N w numWin (xval b) hN (hxval b hb)]

end FormalRV.Shor.CosetEigenstate.CosetTableSum
