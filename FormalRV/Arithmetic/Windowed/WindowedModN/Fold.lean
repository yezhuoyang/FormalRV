/- WindowedModN — §10-11 prefix fold + HEADLINE correctness.
   Part of `WindowedModN` (the `WindowedModN.lean` shim re-exports all parts). -/
import FormalRV.Arithmetic.Windowed.WindowedModN.StepInvariant

namespace FormalRV.Shor.WindowedCircuit
open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §10. The fold: the invariant holds after every prefix of window steps. -/

/-- Running the first `n ≤ numWin` mod-N window steps establishes the
    invariant with running value `windowedLookupFold a N w (window w y) n 0`
    — the circuit-aligned per-window mod-N fold of `WindowedArith`. -/
theorem modNStepInv_fold (w bits a N numWin y : Nat) (hw : 0 < w)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) :
    ∀ n, n ≤ numWin →
      ModNStepInv w bits numWin y
        (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) n 0)
        (Gate.applyNat
          (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
          (mulInputOf cuccaroAdder w bits numWin y)) := by
  intro n
  induction n with
  | zero =>
    intro _
    show ModNStepInv w bits numWin y
      (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) 0 0)
      (Gate.applyNat Gate.I (mulInputOf cuccaroAdder w bits numWin y))
    rw [Gate.applyNat_I]
    exact modNStepInv_init w bits numWin y
  | succ n ih =>
    intro hn
    have hsplit : windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) (n + 1)
        = Gate.seq
            (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
            (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n) := by
      unfold windowedModNMul
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq]
    have hfold_lt : WindowedArith.windowedLookupFold a N w
        (WindowedArith.window w y) n 0 < N := by
      cases n with
      | zero => exact hN_pos
      | succ m => exact Nat.mod_lt _ hN_pos
    exact modNStepInv_step w bits a N numWin y hw hN_pos hN2 n (by omega) _
      hfold_lt _ (ih (by omega))

/-! ## §11. HEADLINE — the per-window mod-N windowed multiplier is correct. -/

/-- **HEADLINE — per-window mod-N windowed-multiplier VALUE theorem.**
    The full per-window mod-N circuit (each window doing
    `acc ← (acc + T_j[v]) mod N` with `T_j[v] = a·(2^w)^j·v mod N`),
    run on the SAME clean encoded input as the product-adder multiplier
    (`mulInputOf cuccaroAdder`: ctrl set, `y` in the y-register, everything
    else — including the new comparison-flag qubit — clean), leaves

        (a · y) mod N

    in the accumulator, provided `0 < w`, `0 < N`, `2·N ≤ 2^bits`, and
    `y < 2^(w·numWin)`.  This closes the "product-adder only" gap: the
    multiplier reduces mod N after EVERY window, exactly as in Gidney
    (arXiv:1905.07682). -/
theorem windowedModNMulCircuit_correct (w bits a N numWin y : Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < 2 ^ (w * numWin)) :
    decodeAccOf cuccaroAdder
        (Gate.applyNat (windowedModNMulCircuit w bits a N numWin)
          (mulInputOf cuccaroAdder w bits numWin y)) (1 + 2 * w) bits
      = (a * y) % N := by
  have hy' : y < (2 ^ w) ^ numWin := by
    rw [← pow_mul]
    exact hy
  have hfold := (modNStepInv_fold w bits a N numWin y hw hN_pos hN2 numWin
    (le_refl numWin)).2.2.2.2
  have hfold_lt : WindowedArith.windowedLookupFold a N w
      (WindowedArith.window w y) numWin 0 < N := by
    rw [WindowedArith.windowedLookupFold_eq a N w (WindowedArith.window w y) 0
          hN_pos numWin]
    exact Nat.mod_lt _ hN_pos
  have hval : WindowedArith.windowedLookupFold a N w
      (WindowedArith.window w y) numWin 0 = (a * y) % N :=
    WindowedArith.windowedLookupFold_eq_modmul a N w numWin y hN_pos hy'
  show decodeReg (cuccaroAdder.augendIdx (1 + 2 * w)) bits
      (Gate.applyNat (windowedModNMulCircuit w bits a N numWin)
        (mulInputOf cuccaroAdder w bits numWin y)) = (a * y) % N
  unfold windowedModNMulCircuit
  rw [decodeReg_eq_mod_of_testBit (cuccaroAdder.augendIdx (1 + 2 * w)) bits
        (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) numWin 0)
        _ (fun i hi => hfold i hi)]
  rw [Nat.mod_eq_of_lt (by omega :
        WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) numWin 0
          < 2 ^ bits)]
  exact hval


end FormalRV.Shor.WindowedCircuit
