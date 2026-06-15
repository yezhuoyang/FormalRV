/-
  FormalRV.Shor.CosetEigenstate.CosetFoldWindowed — the windowed multiplier embedding:
  `cosetState z ↦ E_data ((a·z) % N)` off bad, with bad mass `≤ numWin/2^m` per side.
  ════════════════════════════════════════════════════════════════════════════

  Specializes the abstract fold agreement `CosetFold.cosetState_multiWrap_agree_off`
  with the windowed value identity `CosetTableSum.idealAcc_cosetWindowConst`
  (`= windowedLookupFold_eq_modmul`).  The unreduced windowed result
  `cosetState (runningSum (cosetWindowConst a N w x) numWin)` agrees off the symmetric
  difference with `E_data` of the canonical product `cosetState ((a·x) % N)`, and each
  side carries Born mass `≤ numWin/2^m` (the number of wraps `q = runningSum/N ≤ numWin`).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.CosetFold
import FormalRV.Shor.CosetEigenstate.CosetTableSum

namespace FormalRV.Shor.CosetEigenstate.CosetFoldWindowed

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.CosetEigenstate.ApproxOp (cosetState)
open FormalRV.Shor.CosetEigenstate.CosetMul (idealAcc runningSum)
open FormalRV.Shor.CosetEigenstate.CosetTableSum (cosetWindowConst cosetWindowConst_lt idealAcc_cosetWindowConst)
open FormalRV.Shor.CosetEigenstate.CosetFold (cosetState_multiWrap_agree_off)

/-- The ideal (mod-N reduced) accumulator is congruent to the unreduced running sum. -/
theorem idealAcc_modEq_runningSum (N : Nat) (cs : Nat → Nat) :
    ∀ t, idealAcc N 0 cs t % N = runningSum cs t % N := by
  intro t
  induction t with
  | zero => rfl
  | succ p ih =>
      show (idealAcc N 0 cs p + cs p) % N % N = (runningSum cs p + cs p) % N
      rw [Nat.mod_mod, Nat.add_mod (idealAcc N 0 cs p), ih, ← Nat.add_mod]

/-- The running sum of `t` addends each `< N` is `< t·N`. -/
theorem runningSum_lt (cs : Nat → Nat) (N : Nat) (hcs : ∀ i, cs i < N) :
    ∀ t, 0 < t → runningSum cs t < t * N := by
  intro t
  induction t with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ p ih =>
      intro _
      show runningSum cs p + cs p < (p + 1) * N
      have hpn : (p + 1) * N = p * N + N := by ring
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp; simp only [runningSum, Nat.zero_add, Nat.zero_mul] at *; have := hcs 0; omega
      · have h1 := ih hp
        have h2 := hcs p
        omega

/-- **THE WINDOWED MULTIPLIER COSET-EMBEDDING (off bad, `≤ numWin/2^m`).**  For
    `x < (2^w)^numWin`, the unreduced windowed result `cosetState (runningSum …)` (the
    coset accumulator after the `numWin` ordinary lookup-adds) agrees with `E_data` of
    the canonical product `cosetState ((a·x) % N)` off the symmetric-difference bad set,
    with each side's Born mass `≤ numWin/2^m` (the wrap count `q = runningSum/N ≤ numWin`). -/
theorem cosetState_windowedMul_embed_off (dim N m a w numWin x : Nat)
    (hN : 0 < N) (hx : x < (2 ^ w) ^ numWin) :
    ∃ B : Finset (Fin dim),
      (∀ i, i ∉ B →
        cosetState dim N m (runningSum (cosetWindowConst a N w x) numWin) i 0
          = cosetState dim N m ((a * x) % N) i 0)
      ∧ bornWeightOn (cosetState dim N m (runningSum (cosetWindowConst a N w x) numWin)) B
          ≤ (numWin : ℝ) / 2 ^ m
      ∧ bornWeightOn (cosetState dim N m ((a * x) % N)) B ≤ (numWin : ℝ) / 2 ^ m := by
  set cs := cosetWindowConst a N w x with hcs_def
  set rs := runningSum cs numWin with hrs
  -- rs ≡ (a·x) % N  (mod N), and the canonical residue is < N
  have hmodeq : rs % N = (a * x) % N := by
    rw [hrs, ← idealAcc_modEq_runningSum N cs numWin,
        idealAcc_cosetWindowConst a N w numWin x hN hx,
        Nat.mod_eq_of_lt (Nat.mod_lt _ hN)]
  -- rs = (a·x)%N + q·N, with q = rs/N the wrap count
  set q := rs / N with hq
  have hrs_eq : rs = (a * x) % N + q * N := by
    conv_lhs => rw [← Nat.div_add_mod rs N, hmodeq]
    rw [hq]; ring
  -- q ≤ numWin
  have hq_le : q ≤ numWin := by
    rcases Nat.eq_zero_or_pos numWin with h0 | h0
    · rw [hq, hrs, h0]; simp [runningSum]
    · have hlt : rs < numWin * N :=
        hrs ▸ runningSum_lt cs N (fun i => cosetWindowConst_lt a N w x hN i) numWin h0
      rw [hq]
      exact Nat.le_of_lt (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hlt))
  obtain ⟨B, hagree, hb1, hb2⟩ := cosetState_multiWrap_agree_off dim N m ((a * x) % N) q hN
  refine ⟨B, ?_, ?_, ?_⟩
  · rw [hrs_eq]; exact hagree
  · rw [hrs_eq]; exact le_trans hb1 (by gcongr)
  · exact le_trans hb2 (by gcongr)

end FormalRV.Shor.CosetEigenstate.CosetFoldWindowed
