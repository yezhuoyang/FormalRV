/-
  FormalRV.Shor.CFS.ResidueCRT — wiring the VERIFIED CIRCUIT residue vector into the CRT reconstruction:
  the concrete |P|-register residue circuit, read out and CRT-reconstructed, equals `g^e mod N`.

  This composes the two verified halves with NO new abstraction:
    * `residueFold_correct`            — each register `j` of the concrete `Gate` `residueFold`, run on the
                                         concrete `globalInput`, decodes to `modexpProd g N m e % (P j)`;
    * `residue_modexp_via_crt_explicit`— that residue vector, reconstructed via the CONSTRUCTED CRT basis
                                         `crtBasis` (no assumed units), reduced mod `N`, is `g^e mod N`.

  Result (`residueFold_crt_correct`): the integers read out of the actual circuit's `|P|` accumulators,
  CRT-combined, give the true modular exponential `g^e mod N` — the arithmetic spine of CFS, end to end
  on a concrete syntactic object.  The only hypotheses are genuine algorithmic preconditions (valid
  residue primes, pairwise coprime, `∏P ≥ N^m`, invertible per-prime multipliers).  Kernel-clean.
-/
import FormalRV.Shor.CFS.ResidueFold
import FormalRV.Shor.CFS.CRTBasis

namespace FormalRV.CFS

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open scoped BigOperators

/-- **THE CFS ARITHMETIC SPINE, END TO END ON THE CIRCUIT.**  Reading the `|P|` residue registers out
    of the concrete circuit `residueFold` (run on `globalInput`) and CRT-reconstructing them with the
    constructed basis yields exactly `g^e mod N`.  Composes `residueFold_correct` (circuit → residue
    vector) with `residue_modexp_via_crt_explicit` (residue vector → `g^e mod N`). -/
theorem residueFold_crt_correct (P : Nat → Nat) (ainvss : Nat → Nat → Nat)
    (numP w bits numWin g N e m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hPok : ∀ j, j < numP → 1 < P j ∧ 2 * P j ≤ 2 ^ bits ∧
      ∀ k, k < m → ainvss j k < P j ∧ residueConst g N (P j) e k * ainvss j k % (P j) = 1)
    (hN : 2 ≤ N) (hm : 1 ≤ m) (he : e < 2 ^ m)
    (hco : ∀ i j : Fin numP, i ≠ j → Nat.Coprime (P i.val) (P j.val))
    (hL : N ^ m ≤ ∏ i : Fin numP, P i.val) :
    (∑ j : Fin numP,
        (decodeReg (fun i => j.val * residueWidth w bits numWin + (1 + 2 * w + (2 * bits + 1) + i)) bits
          (Gate.applyNat (residueFold P ainvss numP w bits numWin g N e m) (globalInput w bits numWin)))
          * crtBasis (fun i : Fin numP => P i.val) j) % (∏ i : Fin numP, P i.val) % N
      = g ^ e % N := by
  have hsum : (∑ j : Fin numP,
        (decodeReg (fun i => j.val * residueWidth w bits numWin + (1 + 2 * w + (2 * bits + 1) + i)) bits
          (Gate.applyNat (residueFold P ainvss numP w bits numWin g N e m) (globalInput w bits numWin)))
          * crtBasis (fun i : Fin numP => P i.val) j)
      = ∑ j : Fin numP, (modexpProd g N m e % P j.val) * crtBasis (fun i : Fin numP => P i.val) j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [residueFold_correct P ainvss w bits numWin g N e m hw hbits numP hPok j.val j.isLt]
  rw [hsum]
  exact residue_modexp_via_crt_explicit g e N hN hm he (fun i : Fin numP => P i.val)
    (fun i => (hPok i.val i.isLt).1) hco hL

end FormalRV.CFS
