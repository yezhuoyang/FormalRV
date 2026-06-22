/-
  FormalRV.Shor.GidneyRunwayMulInPlace — the IN-PLACE windowed mod-N multiplier at the Gidney
  all-temporary-AND layout: `y ↦ (a·y) mod N` via the two-pass + swap coset construction.

  ## The construction (Gidney/Zalka two-pass)

    pass1: multiply-add with `a`   — accumulator (0) ← S₁ = Σⱼ tableValueⱼ^a(windowⱼ y) ≡ a·y mod N
    swap : exchange accumulator ↔ y-register — y-register ← S₁, accumulator ← old y
    pass2: multiply-add with `N−a⁻¹` — accumulator (old y) ← y + Σⱼ tableValueⱼ^{N−a⁻¹}(windowⱼ S₁)
                                       ≡ y − a⁻¹·(a·y) ≡ 0 mod N

  Net: the y-register holds `S₁` (a coset representative of `(a·y) mod N`), and the accumulator
  returns to a coset representative of `0` — exactly the Gidney/Babbush coset in-place multiplier,
  on an ALL-temporary-AND verified circuit (the swap is CX-only, T-free; both passes are the
  `gidneyRunwayMul` whose every gadget is a genuine temporary AND).

  ## Honest scope

  This is the COSET-level in-place map: `(y-register) mod N = (a·y) mod N` and `(accumulator)
  mod N = 0` are proven EXACTLY (computational basis).  The registers hold coset reps (not the
  reduced residues), exactly as in the runway/coset design.  The no-wrap budgets are carried as
  explicit hypotheses (`numWin·N ≤ 2^bits` for pass 1, `y + numWin·N ≤ 2^bits` for pass 2 — the
  runway padding).  Width: `numWin·w = n+2` (the windows tile the n+2-bit register, so the swap is
  a clean bijection accumulator ↔ y-register).

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyRunwayMul
import FormalRV.Shor.WindowedModNShor

namespace FormalRV.Shor.GidneyRunwayMulInPlace

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Arithmetic.MeasuredAdder
open FormalRV.Shor.GidneyTCount
open FormalRV.Shor.GidneyMeasuredLookupAdd
open FormalRV.Shor.GidneyRunwayMul
open FormalRV.BQAlgo.WindowedModNShor

/-! ## §1. The fold from an ARBITRARY invariant state (generalizes `gInv_fold`). -/

/-- **The fold from any `GInv` start.**  Folding `m ≤ numWin` windows (multiplier `a`, reading the
    register value `yval`) from any `GInv yval s0` state lands `GInv yval (s0 + Σⱼ tableValueⱼ)` —
    the running sum accumulates onto `s0` with no per-step reduction (runway). -/
theorem gInv_fold_gen (w n a N numWin yval s0 : Nat) (g0 : Nat → Bool)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 2))
    (hrun : s0 + numWin * N ≤ 2 ^ (n + 2)) (hg0 : GInv w n numWin yval s0 g0) :
    ∀ m, m ≤ numWin →
      GInv w n numWin yval
          (s0 + ∑ j ∈ Finset.range m, WindowedArith.tableValue a N w j (WindowedArith.window w yval j))
          (EGate.applyNat (gidneyRunwayMulN w n a N numWin m) g0) := by
  intro m
  induction m with
  | zero =>
      intro _
      rw [Finset.sum_range_zero, Nat.add_zero]
      have he : EGate.applyNat (gidneyRunwayMulN w n a N numWin 0) g0 = g0 := by
        simp [gidneyRunwayMulN, EGate.applyNat, Gate.applyNat_I]
      rw [he]; exact hg0
  | succ m ih =>
      intro hm
      have hsplit : gidneyRunwayMulN w n a N numWin (m + 1)
          = EGate.seq (gidneyRunwayMulN w n a N numWin m) (gidneyRunwayStep w n a N numWin m) := by
        unfold gidneyRunwayMulN
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hsplit]
      show GInv w n numWin yval
          (s0 + ∑ j ∈ Finset.range (m + 1),
            WindowedArith.tableValue a N w j (WindowedArith.window w yval j))
          (EGate.applyNat (gidneyRunwayStep w n a N numWin m)
            (EGate.applyNat (gidneyRunwayMulN w n a N numWin m) g0))
      rw [Finset.sum_range_succ, ← Nat.add_assoc]
      have hs : s0 + ∑ j ∈ Finset.range m,
          WindowedArith.tableValue a N w j (WindowedArith.window w yval j) < 2 ^ (n + 2) := by
        have hle : (∑ j ∈ Finset.range m,
            WindowedArith.tableValue a N w j (WindowedArith.window w yval j)) ≤ m * N := by
          calc (∑ j ∈ Finset.range m, WindowedArith.tableValue a N w j (WindowedArith.window w yval j))
              ≤ ∑ _j ∈ Finset.range m, N :=
                Finset.sum_le_sum (fun j _ => le_of_lt (by
                  unfold WindowedArith.tableValue; exact Nat.mod_lt _ hN))
            _ = m * N := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        have h1 : (m + 1) * N ≤ numWin * N := Nat.mul_le_mul_right N hm
        have h2 : (m + 1) * N = m * N + N := by ring
        omega
      exact gInv_step w n a N numWin yval
        (s0 + ∑ j ∈ Finset.range m, WindowedArith.tableValue a N w j (WindowedArith.window w yval j)) m
        hw hN hN2 (by omega) hs _ (ih (by omega))

/-! ## §2. The accumulator ↔ y-register swap transports the invariant. -/

/-- The Gidney-layout accumulator↔y-register swap: exchange `target_idx i ↔ gYBase n + i` for the
    `n+2` register bits (CX-only, T-free).  Reuses the verified generic `swapCascade`. -/
def gAccYSwap (n : Nat) : Gate :=
  swapCascade target_idx (fun i => gYBase n + i) (n + 2)

/-- **★ THE SWAP TRANSPORTS THE INVARIANT ★** — `GInv yval s → GInv s yval`: it exchanges the
    accumulator value `s` (the target register) with the y-register value `yval`, leaving the read/
    carry scratch clean and the ancilla/control untouched.  Needs `numWin·w = n+2` (the y-register
    is exactly the `n+2` bits being swapped). -/
theorem gAccYSwap_GInv (w n numWin yval s : Nat) (hbits : numWin * w = n + 2)
    (g : Nat → Bool) (hg : GInv w n numWin yval s g) :
    GInv w n numWin s yval (Gate.applyNat (gAccYSwap n) g) := by
  obtain ⟨hblock, hy, hanc, hctrl⟩ := hg
  have hgY : gYBase n = 3 * (n + 2) + 2 := by unfold gYBase adder_n_qubits; ring
  obtain ⟨swap_u, swap_v, swap_fr⟩ :=
    swapCascade_apply target_idx (fun i => gYBase n + i) (n + 2) g
      (fun i k _ _ hik => by simp only [target_idx]; omega)
      (fun i k _ _ hik => by simp only []; omega)
      (fun i k _ _ => by simp only [target_idx, hgY]; omega)
  unfold gAccYSwap
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 from by omega) with h | h | h
    · have hi : q / 3 < n + 2 := by omega
      have hqr : q = read_idx (q / 3) := by simp only [read_idx]; omega
      rw [hqr,
          swap_fr _ (fun i _ => ⟨by simp only [read_idx, target_idx]; omega,
            by simp only [read_idx, hgY]; omega⟩),
          hblock (read_idx (q / 3)) (by rw [← hqr]; exact hq),
          adder_input_F_at_read, adder_input_F_at_read]
    · have hi : q / 3 < n + 2 := by omega
      have hqt : q = target_idx (q / 3) := by simp only [target_idx]; omega
      rw [hqt, swap_u (q / 3) hi]
      show g (gYBase n + q / 3) = adder_input_F (n + 2) 0 yval (target_idx (q / 3))
      rw [hy (q / 3) (by omega), adder_input_F_at_target]; simp [hi]
    · have hi : q / 3 < n + 2 := by omega
      have hqc : q = carry_idx (q / 3) := by simp only [carry_idx]; omega
      rw [hqc,
          swap_fr _ (fun i _ => ⟨by simp only [carry_idx, target_idx]; omega,
            by simp only [carry_idx, hgY]; omega⟩),
          hblock (carry_idx (q / 3)) (by rw [← hqc]; exact hq),
          adder_input_F_at_carry, adder_input_F_at_carry]
  · intro k hk
    rw [swap_v k (by omega)]
    show g (target_idx k) = s.testBit k
    rw [hblock (target_idx k) (by simp only [target_idx]; omega), adder_input_F_at_target]
    simp [show k < n + 2 from by omega]
  · intro i hi
    rw [swap_fr _ (fun i' _ => ⟨by simp only [gCAnc, gCBase, target_idx, hgY]; omega,
      by simp only [gCAnc, gCBase, hgY]; omega⟩)]
    exact hanc i hi
  · rw [swap_fr _ (fun i' _ => ⟨by simp only [gCtrl, gCBase, target_idx, hgY]; omega,
      by simp only [gCtrl, gCBase, hgY]; omega⟩)]
    exact hctrl

/-! ## §3. The pass-2 clearing identity (number theory). -/

/-- **The pass-2 accumulator clears mod N.**  With `S₁ ≡ a·y (mod N)` and `a·a⁻¹ ≡ 1 (mod N)`,
    adding the `(N − a⁻¹)`-table sum (which `≡ (N−a⁻¹)·S₁ ≡ −y mod N`) to the held value `y`
    yields `≡ 0 (mod N)`. -/
theorem inplace_clearing_modN (N a ainv y S1 : Nat) (hN : 1 < N) (hainv_le : ainv ≤ N)
    (hav : a * ainv % N = 1) (hS1 : S1 % N = (a * y) % N) :
    (y + (N - ainv) * S1) % N = 0 := by
  have e_av : a * ainv ≡ 1 [MOD N] := by
    show a * ainv % N = 1 % N; rw [hav, Nat.mod_eq_of_lt hN]
  have hS1' : S1 ≡ a * y [MOD N] := hS1
  have h_ainvS1 : ainv * S1 ≡ y [MOD N] := by
    calc ainv * S1 ≡ ainv * (a * y) [MOD N] := Nat.ModEq.mul_left ainv hS1'
      _ = (a * ainv) * y := by ring
      _ ≡ 1 * y [MOD N] := Nat.ModEq.mul_right y e_av
      _ = y := Nat.one_mul y
  have hsum : (N - ainv) * S1 + ainv * S1 = N * S1 := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hainv_le]
  have key : y + (N - ainv) * S1 ≡ 0 [MOD N] := by
    have hL : (y + (N - ainv) * S1) + ainv * S1 ≡ 0 + ainv * S1 [MOD N] := by
      rw [show (y + (N - ainv) * S1) + ainv * S1 = y + N * S1 by omega, Nat.zero_add]
      calc y + N * S1 ≡ y + 0 [MOD N] :=
            Nat.ModEq.add_left y ((Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right N S1))
        _ = y := Nat.add_zero y
        _ ≡ ainv * S1 [MOD N] := h_ainvS1.symm
    exact Nat.ModEq.add_right_cancel' (ainv * S1) hL
  have hk : (y + (N - ainv) * S1) % N = 0 % N := key
  rwa [Nat.zero_mod] at hk

/-! ## §4. The in-place gate and its coset-level correctness. -/

/-- **The in-place windowed runway multiplier**: `multiply-add(a) ; swap ; multiply-add(N − a⁻¹)`.
    Maps `y ↦ (a·y) mod N` in place (coset level), all temporary AND (the swap is CX-only). -/
def gidneyRunwayMulInPlace (w n a N ainv numWin : Nat) : EGate :=
  EGate.seq (EGate.seq (gidneyRunwayMulN w n a N numWin numWin) (EGate.base (gAccYSwap n)))
    (gidneyRunwayMulN w n (N - ainv) N numWin numWin)

/-- **★ THE IN-PLACE COSET MULTIPLIER IS CORRECT ★** — on the clean input, after the full two-pass
    gate: (i) the y-register holds a coset representative of `(a·y) mod N` (its residue mod `N` is
    `(a·y) mod N`); and (ii) the accumulator returns to a coset representative of `0` (residue
    `0`).  The map `y ↦ (a·y) mod N` is realized in place, on the all-temporary-AND circuit.  The
    runway no-overflow budgets are explicit (`numWin·N ≤ 2^bits` for pass 1, `y + numWin·N ≤ 2^bits`
    for pass 2); `numWin·w = n+2` makes the swap a clean accumulator↔y-register bijection. -/
theorem gidneyRunwayMulInPlace_correct (w n a N ainv numWin y : Nat)
    (hw : 0 < w) (hN : 1 < N) (hbits : numWin * w = n + 2)
    (hainv_lt : ainv < N) (hav : a * ainv % N = 1) (hy : y < N)
    (hrun1 : numWin * N ≤ 2 ^ (n + 2)) (hrun2 : y + numWin * N ≤ 2 ^ (n + 2)) :
    (decodeReg (fun k => gYBase n + k) (n + 2)
        (EGate.applyNat (gidneyRunwayMulInPlace w n a N ainv numWin) (gMulInput w n numWin y))) % N
      = (a * y) % N
    ∧ (gidney_target_val (n + 2)
        (EGate.applyNat (gidneyRunwayMulInPlace w n a N ainv numWin) (gMulInput w n numWin y))) % N
      = 0 := by
  have hN0 : 0 < N := by omega
  have hnumWin : 1 ≤ numWin := by
    rcases Nat.eq_zero_or_pos numWin with h | h
    · exfalso; rw [h, Nat.zero_mul] at hbits; omega
    · exact h
  have hN2 : N ≤ 2 ^ (n + 2) := by
    have : N ≤ numWin * N := by
      calc N = 1 * N := (Nat.one_mul N).symm
        _ ≤ numWin * N := Nat.mul_le_mul_right N hnumWin
    omega
  have hpow : (2 ^ w) ^ numWin = 2 ^ (n + 2) := by
    rw [← Nat.pow_mul, Nat.mul_comm w numWin, hbits]
  -- thread the three stages
  set input := gMulInput w n numWin y with hinput
  set S1 := ∑ j ∈ Finset.range numWin, WindowedArith.tableValue a N w j (WindowedArith.window w y j)
    with hS1
  set g1 := EGate.applyNat (gidneyRunwayMulN w n a N numWin numWin) input with hg1
  have hp1 : GInv w n numWin y S1 g1 :=
    gInv_fold w n a N numWin y hw hN0 hN2 hrun1 numWin (le_refl _)
  set g2 := Gate.applyNat (gAccYSwap n) g1 with hg2
  have hp2 : GInv w n numWin S1 y g2 := gAccYSwap_GInv w n numWin y S1 hbits g1 hp1
  set S2 := ∑ j ∈ Finset.range numWin,
    WindowedArith.tableValue (N - ainv) N w j (WindowedArith.window w S1 j) with hS2
  set gF := EGate.applyNat (gidneyRunwayMulN w n (N - ainv) N numWin numWin) g2 with hgF
  have hp3 : GInv w n numWin S1 (y + S2) gF :=
    gInv_fold_gen w n (N - ainv) N numWin S1 y g2 hw hN0 hN2 hrun2 hp2 numWin (le_refl _)
  have hgate : EGate.applyNat (gidneyRunwayMulInPlace w n a N ainv numWin) input = gF := rfl
  rw [hgate]
  -- bounds
  have hS1_lt_bits : S1 < 2 ^ (n + 2) := runwaySum_lt w n a N numWin y hN0 hrun1
  have hS1_lt_pow : S1 < (2 ^ w) ^ numWin := by rw [hpow]; exact hS1_lt_bits
  have hy_lt_pow : y < (2 ^ w) ^ numWin := by rw [hpow]; exact lt_of_lt_of_le hy hN2
  have hS1mod : S1 % N = (a * y) % N :=
    WindowedArith.windowed_modProductAdd w numWin a N y hy_lt_pow
  refine ⟨?_, ?_⟩
  · -- y-register residue
    have hYdec : decodeReg (fun k => gYBase n + k) (n + 2) gF = S1 := by
      rw [FormalRV.Shor.WindowedCircuit.decodeReg_eq_mod_of_testBit (fun k => gYBase n + k) (n + 2)
            S1 gF (fun i hi => hp3.2.1 i (by omega)), Nat.mod_eq_of_lt hS1_lt_bits]
    rw [hYdec, hS1mod]
  · -- accumulator residue
    have hS2_lt : S2 < numWin * N := by
      calc S2 < ∑ _j ∈ Finset.range numWin, N :=
            Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega))
              (fun j _ => by unfold WindowedArith.tableValue; exact Nat.mod_lt _ hN0)
        _ = numWin * N := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hyS2_lt_bits : y + S2 < 2 ^ (n + 2) := by omega
    have hAccdec : gidney_target_val (n + 2) gF = y + S2 := by
      rw [gidney_target_val_eq_sum_when_bits_match (n + 2) (y + S2) gF (fun i hi => by
            rw [hp3.1 (target_idx i) (by simp only [target_idx]; omega), adder_input_F_at_target];
            simp [hi])]
      exact Nat.mod_eq_of_lt hyS2_lt_bits
    rw [hAccdec]
    have hS2mod : S2 % N = ((N - ainv) * S1) % N :=
      WindowedArith.windowed_modProductAdd w numWin (N - ainv) N S1 hS1_lt_pow
    have hrw : (y + S2) % N = (y + (N - ainv) * S1) % N := Nat.ModEq.add_left y hS2mod
    rw [hrw]
    exact inplace_clearing_modN N a ainv y S1 hN (le_of_lt hainv_lt) hav hS1mod

/-! ## §5. Counts — two passes + the T-free swap, all temporary AND. -/

theorem tcount_gidneyRunwayMulInPlace (w n a N ainv numWin : Nat) :
    EGate.tcount (gidneyRunwayMulInPlace w n a N ainv numWin)
      = 2 * numWin * (7 * ((2 ^ w - 1) + (n + 2))) := by
  have e3 : EGate.tcount (EGate.base (gAccYSwap n)) = 0 := by
    show Gate.tcount (gAccYSwap n) = 0
    unfold gAccYSwap; exact tcount_swapCascade _ _ _
  have e1 : EGate.tcount (gidneyRunwayMulN w n a N numWin numWin)
      = numWin * (7 * ((2 ^ w - 1) + (n + 2))) := tcount_gidneyRunwayMul w n a N numWin
  have e2 : EGate.tcount (gidneyRunwayMulN w n (N - ainv) N numWin numWin)
      = numWin * (7 * ((2 ^ w - 1) + (n + 2))) := tcount_gidneyRunwayMul w n (N - ainv) N numWin
  have hstruct : EGate.tcount (gidneyRunwayMulInPlace w n a N ainv numWin)
      = (EGate.tcount (gidneyRunwayMulN w n a N numWin numWin)
          + EGate.tcount (EGate.base (gAccYSwap n)))
        + EGate.tcount (gidneyRunwayMulN w n (N - ainv) N numWin numWin) := rfl
  rw [hstruct, e3, e1, e2]
  ring

/-- **Whole in-place Toffoli count: `2·numWin·((2^w − 1) + bits)`** (two multiply-add passes; the
    swap is CX-only, Toffoli-free). -/
theorem toffoli_gidneyRunwayMulInPlace (w n a N ainv numWin : Nat) :
    EGate.toffoli (gidneyRunwayMulInPlace w n a N ainv numWin)
      = 2 * numWin * ((2 ^ w - 1) + (n + 2)) := by
  unfold EGate.toffoli
  rw [tcount_gidneyRunwayMulInPlace,
      show 2 * numWin * (7 * ((2 ^ w - 1) + (n + 2)))
          = (2 * numWin * ((2 ^ w - 1) + (n + 2))) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **★ WHOLE IN-PLACE GADGET-BY-GADGET-HONEST T-COUNT ★** — every gadget in both passes is a
    genuine temporary AND (Babbush merged-AND loads + measured Gidney adders + `mz`-clears; the
    swap is T-free), so the uniform Gidney 4-T model is exact:
    `gidneyTCount = 2·numWin·(4·((2^w − 1) + bits))`. -/
theorem gidneyTCount_gidneyRunwayMulInPlace (w n a N ainv numWin : Nat) :
    gidneyTCount (gidneyRunwayMulInPlace w n a N ainv numWin)
      = 2 * numWin * (4 * ((2 ^ w - 1) + (n + 2))) := by
  unfold gidneyTCount FormalRV.PaperClaims.gidney_2018_logical_AND_compute_tcount
  rw [toffoli_gidneyRunwayMulInPlace]; ring

end FormalRV.Shor.GidneyRunwayMulInPlace
