/-
  FormalRV.Arithmetic.Windowed.WindowedExpInPlaceCount — the Toffoli COUNT of the value-correct
  in-place windowed modular exponentiation `windowedExpInPlace`, walked over the SAME `Gate` term
  that `windowedExpInPlace_correct` proves computes `g^e·y mod 2^bits`.

  ## Why this exists (Concern-2: resource on the SAME verified circuit)

  `windowedExpInPlace_correct` (`WindowedInPlace.lean`) is GE2021's value-correct modexp — but its
  resource cost was only counted on a DIFFERENT object (`modExpAt`, the scattered-address EGate of the
  audit).  So the verified circuit and the counted circuit were two different terms.  This file closes
  that seam the way `CFS.residueFold` does (semantic + resource on one `Gate`): it walks
  `Gate.tcount` over the SAME `windowedExpInPlace` term, by the fold-theorem standard —

    * `tcount_windowedMulInPlace` — one in-place multiply = two `windowedMulCircuitOf` (forward +
      inverse-uncompute) + a T-free `accYSwap`, so its T-count is `2·numWin·(28·w·2^w + tcount A.circuit)`,
      INDEPENDENT of the multiplier constant `a`/`ainv`;
    * `tcount_windowedMulInPlaceSeq` — the `nE`-fold of in-place multiplies counts `nE ×` that constant
      (via `tcount_foldl_seq_const`, the honest fold-count over the actual `foldl seq` term);
    * `tcount_windowedExpInPlace` — hence the whole modexp's T-count;
    * **`windowedExpInPlace_verified`** — VALUE (`g^e·y mod 2^bits`, from `windowedExpInPlace_correct`)
      AND the exact T-count, on the IDENTICAL `windowedExpInPlace A w bits numWin wE nE g e ainvs` term.
-/
import FormalRV.Arithmetic.Windowed.WindowedInPlace
import FormalRV.Arithmetic.Windowed.WindowedModNInPlace

namespace FormalRV.Shor.WindowedCircuit

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-- **One in-place windowed multiply's T-count.**  `windowedMulInPlace = (mulCircuit a) ; accYSwap ;
    (mulCircuit (2^bits − ainv))`: two `windowedMulCircuitOf` walks plus a T-free swap.  The count is
    `2·numWin·(28·w·2^w + tcount A.circuit)` — INDEPENDENT of the constant `a`/`ainv` (the table only
    changes the X-layer, never the CCX leaves), which is exactly why the `nE`-fold below is `nE ×` a
    constant. -/
theorem tcount_windowedMulInPlace (A : Adder) (w bits a ainv numWin : Nat) :
    tcount (windowedMulInPlace A w bits a ainv numWin)
      = 2 * (numWin * (28 * w * 2 ^ w + tcount (A.circuit bits (1 + 2 * w)))) := by
  unfold windowedMulInPlace
  simp only [tcount, tcount_accYSwap, tcount_windowedMulCircuitOf]
  ring

/-- **The in-place product chain's T-count.**  `windowedMulInPlaceSeq … n` is the `foldl` of `n`
    in-place multiplies; each has the constant per-multiply count, so the whole walk is `n ×` it
    (`tcount_foldl_seq_const` over the literal `foldl seq` term — the fold-theorem counting standard). -/
theorem tcount_windowedMulInPlaceSeq (A : Adder) (w bits numWin : Nat)
    (as ainvs : Nat → Nat) (n : Nat) :
    tcount (windowedMulInPlaceSeq A w bits numWin as ainvs n)
      = n * (2 * (numWin * (28 * w * 2 ^ w + tcount (A.circuit bits (1 + 2 * w))))) := by
  unfold windowedMulInPlaceSeq
  rw [tcount_foldl_seq_const (fun k => windowedMulInPlace A w bits (as k) (ainvs k) numWin)
        (2 * (numWin * (28 * w * 2 ^ w + tcount (A.circuit bits (1 + 2 * w)))))
        (fun k => tcount_windowedMulInPlace A w bits (as k) (ainvs k) numWin)
        (List.range n) Gate.I]
  simp [tcount, List.length_range]

/-- **The whole in-place windowed MODEXP's T-count**, walked over the SAME `windowedExpInPlace` term
    that `windowedExpInPlace_correct` verifies: `nE ×` the per-window in-place-multiply count. -/
theorem tcount_windowedExpInPlace (A : Adder) (w bits numWin wE nE g e : Nat) (ainvs : Nat → Nat) :
    tcount (windowedExpInPlace A w bits numWin wE nE g e ainvs)
      = nE * (2 * (numWin * (28 * w * 2 ^ w + tcount (A.circuit bits (1 + 2 * w))))) := by
  unfold windowedExpInPlace
  exact tcount_windowedMulInPlaceSeq A w bits numWin _ ainvs nE

/-- **★ GE2021 modexp — VALUE + RESOURCE on ONE circuit term ★.**  The single `Gate`
    `windowedExpInPlace A w bits numWin wE nE g e ainvs` simultaneously:
      (i)  COMPUTES `y ↦ g^e·y mod 2^bits` (Gidney's in-place windowed modexp value,
           `windowedExpInPlace_correct`); and
      (ii) has the EXACT walked T-count `nE·2·numWin·(28·w·2^w + tcount A.circuit)`
           (`tcount_windowedExpInPlace`).
    Semantic correctness and the resource count ride the IDENTICAL syntactic object — the GE2021
    analogue of `CFS.residueGate_verified` / `residueFold` for the windowed-modexp route. -/
theorem windowedExpInPlace_verified (A : Adder)
    (w bits numWin wE nE g e y : Nat) (ainvs : Nat → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hy : y < 2 ^ bits)
    (he : e < (2 ^ wE) ^ nE)
    (hpairs : ∀ k, k < nE → ainvs k < 2 ^ bits ∧
      g ^ ((2 ^ wE) ^ k * WindowedArith.window wE e k) * ainvs k % 2 ^ bits = 1)
    (hinj : ∀ i j, i < bits → j < bits →
      A.augendIdx (1 + 2 * w) i = A.augendIdx (1 + 2 * w) j → i = j)
    (f : Nat → Bool) (hf : MulReady A w bits numWin y f) :
    MulReady A w bits numWin (g ^ e * y % 2 ^ bits)
        (Gate.applyNat (windowedExpInPlace A w bits numWin wE nE g e ainvs) f)
    ∧ tcount (windowedExpInPlace A w bits numWin wE nE g e ainvs)
        = nE * (2 * (numWin * (28 * w * 2 ^ w + tcount (A.circuit bits (1 + 2 * w))))) :=
  ⟨windowedExpInPlace_correct A w bits numWin wE nE g e y ainvs hw hbits hy he hpairs hinj f hf,
   tcount_windowedExpInPlace A w bits numWin wE nE g e ainvs⟩

end FormalRV.Shor.WindowedCircuit
