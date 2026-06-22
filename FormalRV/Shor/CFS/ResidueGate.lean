/-
  FormalRV.Shor.CFS.ResidueGate — the SYNTACTIC per-register residue circuit for Gidney 2025 / CFS,
  with BOTH semantic correctness (on the actual `Gate`) AND a resource count.

  `ResidueCircuit` proved the CLASSICAL action `residueAccumulate g N pj e m = modexpProd g N m e % pj`
  and documented the remaining gap: "the full `Gate`-IR ASSEMBLY ... is mechanical but not written
  out here".  This file CLOSES that gap for one residue register, by REUSING the already-verified
  in-place windowed modular multiplier chain `windowedModNMulInPlaceSeq` (Arithmetic/Windowed)
  instantiated at the small prime modulus `pj`:

    * each step `r ↦ (M_k^{e_k} · r) mod pj` is one `windowedModNMulInPlace` round (the verified gadget);
    * the `m`-step chain `windowedModNMulInPlaceSeq … (residueConst …) ainvs m` is the residue circuit;
    * `Gate.applyNat` on the clean encoded input leaves `modexpProd g N m e mod pj` in the result
      register — the EXACT residue the CFS arithmetic (layers 1–3) demands;
    * its Toffoli count is the closed form `m·numWin·(16·w·2^w + 16·bits)`, counted on the `Gate`.

  Reuse, not reconstruction: this is the standard windowed in-place multiplier, run at modulus `pj`
  with the CFS per-step constants `M_k^{e_k}`.  Kernel-clean; no `native_decide`.  The per-step
  multiplier invertibility mod `pj` (a genuine CFS precondition — the multipliers are units mod the
  residue prime) is carried as the inverse-table hypothesis the in-place uncompute needs.
-/
import FormalRV.Shor.CFS.ResidueArith
import FormalRV.Shor.CFS.DiscreteLogReduction
import FormalRV.Shor.WindowedModExpValue

namespace FormalRV.CFS

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit

/-- The per-step CFS residue multiplier constant on register `j` (reduced mod `pj`):
    `M_k^{e_k} mod pj` — `M_k = g^(2^k) mod N` when the exponent bit `e_k = 1`, else `1`. -/
def residueConst (g N pj e k : Nat) : Nat := Mconst g N k ^ bit e k % pj

/-- The product of the per-step residue constants collapses to the CFS residue
    `modexpProd g N m e mod pj` (mod is multiplicative; `modexpProd` is that product). -/
theorem residueConst_prod_collapse (g N pj e m : Nat) :
    (∏ k ∈ Finset.range m, residueConst g N pj e k) % pj = modexpProd g N m e % pj := by
  simp only [residueConst]
  rw [← Finset.prod_nat_mod, modexpProd_eq_prod g N e m]

/-- **THE SYNTACTIC CFS RESIDUE CIRCUIT, verified — one register, both faces.**
    The single syntactic `Gate` `windowedModNMulInPlaceSeq w bits pj numWin (residueConst …) ainvs m`
    — the `m`-step in-place mod-`pj` controlled-multiply chain, REUSING the verified windowed in-place
    modular multiplier — SIMULTANEOUSLY:

      (1) computes the CFS residue `modexpProd g N m e mod pj` in its result register under
          `Gate.applyNat` on the clean encoded input (SEMANTIC CORRECTNESS on the actual syntactic
          circuit), given any per-step inverse table `ainvs` witnessing invertibility mod `pj`; and
      (2) has the closed-form Toffoli count `m·numWin·(16·w·2^w + 16·bits)` (RESOURCE), counted on
          the same `Gate`.

    Kernel-clean.  This fills the `Gate`-IR ASSEMBLY gap documented in `ResidueCircuit`, by direct
    reuse of `Arithmetic/Windowed`'s verified multiplier. -/
theorem residueGate_verified (w bits numWin pj g N e m : Nat) (ainvs : Nat → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hpj1 : 1 < pj) (hpj2 : 2 * pj ≤ 2 ^ bits)
    (hinv : ∀ k, k < m → ainvs k < pj ∧ residueConst g N pj e k * ainvs k % pj = 1) :
    decodeReg (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits
        (Gate.applyNat (windowedModNMulInPlaceSeq w bits pj numWin (residueConst g N pj e) ainvs m)
          (mulInputOf cuccaroAdder w bits numWin 1))
        = modexpProd g N m e % pj
    ∧ toffoliCount (windowedModNMulInPlaceSeq w bits pj numWin (residueConst g N pj e) ainvs m)
        = m * numWin * (16 * w * 2 ^ w + 16 * bits) := by
  have hpj_pos : 0 < pj := by omega
  have hpj_le : pj ≤ 2 ^ bits := by omega
  -- (1) reuse the verified in-place mod-pj chain: it computes (∏ residueConst)·1 mod pj.
  have hcorr := windowedModNMulInPlaceSeq_correct w bits pj numWin (residueConst g N pj e) ainvs 1
    hw hbits hpj_pos hpj2 hpj1 _ (modNMulReady_mulInputOf w bits numWin 1) m hinv
  rw [Nat.mul_one, residueConst_prod_collapse] at hcorr
  have hval_lt : modexpProd g N m e % pj < pj := Nat.mod_lt _ hpj_pos
  refine ⟨?_, ?_⟩
  · -- SEMANTIC: read the residue off the clean result register.
    exact FormalRV.Shor.WindowedModExpValue.modNMulReady_decode w bits numWin
      (modexpProd g N m e % pj) pj _ hbits hpj_le hval_lt hcorr
  · -- RESOURCE: the m-step chain's Toffoli count (tcount / 7).
    rw [toffoliCount, tcount_windowedModNMulInPlaceSeq,
        show m * (2 * (numWin * (56 * w * 2 ^ w + 56 * bits)))
            = m * numWin * (16 * w * 2 ^ w + 16 * bits) * 7 by ring,
        Nat.mul_div_cancel _ (by norm_num)]

end FormalRV.CFS
