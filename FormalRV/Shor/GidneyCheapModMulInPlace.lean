/-
  FormalRV.Shor.GidneyCheapModMulInPlace — the IN-PLACE cheap windowed modular multiplier
  `x ↦ (a·x) mod N` built from `GidneyCheapModMul.gcMul` via the Bennett two-pass trick, then
  wrapped into the canonical `encodeDataZeroAnc` Shor layout and wired to the full Shor success
  bound — semantics on ONE composed syntactic circuit, no cheating.

  ## Construction (no second keystone — subtract = add-of-negation mod N)

  `gcMul` is OUT-OF-PLACE: it reads `y` from the y-register and accumulates `(a·y) mod N` into the
  (initially-0) accumulator/target register, leaving `y` intact.  In-place `x ↦ (a·x) mod N` is the
  standard Bennett `mul ; swap ; mul⁻¹`:

    pass 1  `gcMul a`        : y-reg = x,        acc = (a·x) mod N
    swap    `gcSwap`         : y-reg = (a·x)%N,  acc = x
    pass 2  `gcMul (N−ainv)` : y-reg = (a·x)%N,  acc = (x + (N−ainv)·(a·x)) mod N = 0   ← `mod_inv_cancel_identity`

  So pass 2 is the SAME `gcMul`, just with multiplier `N − ainv` (subtract realized as add of the
  negated inverse mod `N`).  The result `(a·x) mod N` lands in the y-register with the accumulator,
  flag, lookup ancilla all clean — in-place on the y-register.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyCheapModMul
import FormalRV.Shor.WindowedModNShor
import FormalRV.Arithmetic.ModularAdder.Gidney.ControlledPipeline
import FormalRV.Arithmetic.ModularAdder.GidneyModAddRegWellTyped
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Shor.VerifiedShor.WindowedSwapLoaderWithDataClear

namespace FormalRV.Shor.GidneyCheapModMulInPlace

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Arithmetic.MeasuredAdder
open FormalRV.Arithmetic.ModularAdder.GidneyModAddReg
open FormalRV.Arithmetic.ModularAdder.GidneyModAddRegWellTyped
open FormalRV.Shor.GidneyRunwayMul
open FormalRV.Shor.GidneyCheapModMul
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.Shor.MeasuredBabbushRead
open FormalRV.Shor.EGateToUnitaryBridge

/-! ## §1. The fold from an arbitrary starting accumulator (the second Bennett pass starts at `x`). -/

/-- **`gcInv_fold` generalized to any starting accumulator `acc₀ < N`.**  Folding the windowed
    lookup-adds from `GCInv … acc₀` lands at `GCInv … (windowedLookupFold … m acc₀)`. -/
theorem gcInv_fold_acc (w n a N numWin y acc0 : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 1)) (hbw : numWin * w = n + 1) (hacc0 : acc0 < N)
    (g : Nat → Bool) (hg : GCInv w (n + 1) numWin y acc0 g) :
    ∀ m, m ≤ numWin →
      GCInv w (n + 1) numWin y
          (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) m acc0)
          (EGate.applyNat (gcMulN w (n + 1) a N numWin m) g) := by
  have hfoldlt : ∀ m, WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) m acc0 < N := by
    intro m; cases m with
    | zero => exact hacc0
    | succ k => exact Nat.mod_lt _ hN
  intro m
  induction m with
  | zero =>
      intro _
      have he : EGate.applyNat (gcMulN w (n + 1) a N numWin 0) g = g := by
        simp [gcMulN, EGate.applyNat, Gate.applyNat_I]
      rw [show WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) 0 acc0 = acc0 from rfl, he]
      exact hg
  | succ m ih =>
      intro hm
      have hkn : m < numWin := by omega
      have hsplit : gcMulN w (n + 1) a N numWin (m + 1)
          = EGate.seq (gcMulN w (n + 1) a N numWin m) (gcStep w (n + 1) a N numWin m) := by
        unfold gcMulN; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hsplit]
      show GCInv w (n + 1) numWin y
          (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) (m + 1) acc0)
          (EGate.applyNat (gcStep w (n + 1) a N numWin m)
            (EGate.applyNat (gcMulN w (n + 1) a N numWin m) g))
      rw [show WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) (m + 1) acc0
            = (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) m acc0
                + WindowedArith.tableValue a N w m (WindowedArith.window w y m)) % N from rfl]
      exact gcInv_step w n a N numWin y
        (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) m acc0) m
        hw hN hN2 hbw hkn (hfoldlt m) _ (ih (by omega))

/-- **Whole `gcMul` from `GCInv … acc₀`** — the accumulator nets `(acc₀ + a·y) mod N`, y-register
    `y` and all ancillas preserved/clean. -/
theorem gcMul_GCInv_from_acc (w n a N numWin y acc0 : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 1)) (hbw : numWin * w = n + 1)
    (hacc0 : acc0 < N) (hy : y < (2 ^ w) ^ numWin)
    (g : Nat → Bool) (hg : GCInv w (n + 1) numWin y acc0 g) :
    GCInv w (n + 1) numWin y ((acc0 + a * y) % N)
      (EGate.applyNat (gcMul w (n + 1) a N numWin) g) := by
  have h := gcInv_fold_acc w n a N numWin y acc0 hw hN hN2 hbw hacc0 g hg numWin (le_refl _)
  rwa [WindowedArith.windowedLookupFold_modProductAdd a N w numWin y acc0 hacc0 hy] at h

/-! ## §2. The accumulator↔y-register swap and its GCInv transport. -/

/-- The acc↔y swap at the gcMul layout: swap the accumulator/target register (`target_idx ·`) with
    the y-register (`gcYBase + ·`), bit-by-bit over the `bits` value bits.  T-free (`swapCascade`). -/
def gcSwap (bits : Nat) : Gate :=
  swapCascade target_idx (fun k => gcYBase bits + k) bits

/-- Off the swapped target bits (`target_idx i`, `i < bits`), the block input function is insensitive
    to the accumulator value (it differs only at those target bits; the top qubit reads `0` since
    `A, Y < 2^bits`). -/
theorem adder_input_F_eq_off_target (bits A Y q : Nat)
    (hq : q < adder_n_qubits (bits + 1)) (hnot : ∀ i, i < bits → q ≠ target_idx i)
    (hA : A < 2 ^ bits) (hY : Y < 2 ^ bits) :
    adder_input_F (bits + 1) 0 A q = adder_input_F (bits + 1) 0 Y q := by
  rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 by omega) with h | h | h
  · rw [show q = read_idx (q / 3) by simp only [read_idx]; omega, adder_input_F_at_read,
        adder_input_F_at_read]
  · have hqt : q = target_idx (q / 3) := by simp only [target_idx]; omega
    have hjge : bits ≤ q / 3 := by
      by_contra hlt; push_neg at hlt; exact hnot (q / 3) hlt hqt
    rw [hqt, adder_input_F_at_target, adder_input_F_at_target,
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) hjge)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hY (Nat.pow_le_pow_right (by norm_num) hjge))]
  · rw [show q = carry_idx (q / 3) by simp only [carry_idx]; omega, adder_input_F_at_carry,
        adder_input_F_at_carry]

/-- **The swap transports `GCInv … Y A` to `GCInv … A Y`** — the y-register value `Y` and the
    accumulator value `A` are exchanged (both `< 2^bits`); read/carry/flag/ancilla/control untouched. -/
theorem gcSwap_transport (w n numWin Y A : Nat)
    (hbw : numWin * w = n + 1) (hY : Y < 2 ^ (n + 1)) (hA : A < 2 ^ (n + 1))
    (g : Nat → Bool) (hg : GCInv w (n + 1) numWin Y A g) :
    GCInv w (n + 1) numWin A Y (EGate.applyNat (EGate.base (gcSwap (n + 1))) g) := by
  obtain ⟨hblock, hflag, hy, hanc, hctrl⟩ := hg
  set bits := n + 1 with hbits
  have hu_inj : ∀ i k, i < bits → k < bits → i ≠ k → target_idx i ≠ target_idx k := by
    intro i k _ _ hik; simp only [target_idx]; omega
  have hv_inj : ∀ i k, i < bits → k < bits → i ≠ k → gcYBase bits + i ≠ gcYBase bits + k := by
    intro i k _ _ hik; omega
  have huv : ∀ i k, i < bits → k < bits → target_idx i ≠ gcYBase bits + k := by
    intro i k hi _; simp only [target_idx, gcYBase, adder_n_qubits]; omega
  obtain ⟨hsw_uv, hsw_vu, hsw_frame⟩ :=
    swapCascade_apply target_idx (fun k => gcYBase bits + k) bits g hu_inj hv_inj huv
  show GCInv w bits numWin A Y
    (Gate.applyNat (swapCascade target_idx (fun k => gcYBase bits + k) bits) g)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- block = adder_input_F (bits+1) 0 Y
    intro q hq
    by_cases hqtgt : ∃ i, i < bits ∧ q = target_idx i
    · obtain ⟨i, hi, rfl⟩ := hqtgt
      rw [hsw_uv i hi, hy i (by omega), adder_input_F_at_target,
          decide_eq_true (show i < bits + 1 by omega), Bool.true_and]
    · push_neg at hqtgt
      rw [hsw_frame q (fun i hi => ⟨hqtgt i hi, by simp only [gcYBase]; omega⟩), hblock q hq]
      exact adder_input_F_eq_off_target bits A Y q hq hqtgt hA hY
  · -- flag preserved
    show Gate.applyNat (swapCascade target_idx (fun k => gcYBase bits + k) bits) g (gcFlag bits) = false
    rw [hsw_frame (gcFlag bits) (by intro i hi; refine ⟨by simp only [gcFlag, target_idx, adder_n_qubits]; omega,
          by simp only [gcFlag, gcYBase, adder_n_qubits]; omega⟩)]
    exact hflag
  · -- new y-register = A
    intro k hk
    have hkb : k < bits := by omega
    rw [hsw_vu k hkb, hblock (target_idx k) (by simp only [target_idx, adder_n_qubits]; omega),
        adder_input_F_at_target, decide_eq_true (show k < bits + 1 by omega), Bool.true_and]
  · -- ancilla cleared (framed)
    intro i hi
    rw [hsw_frame (gcCAnc w bits numWin i) (by intro j hj; refine ⟨by simp only [gcCAnc, target_idx, gcYBase, adder_n_qubits]; omega,
          by simp only [gcCAnc, gcYBase]; omega⟩)]
    exact hanc i hi
  · -- control preserved (framed)
    rw [hsw_frame (gcCtrl w bits numWin) (by intro j hj; refine ⟨by simp only [gcCtrl, target_idx, gcYBase, adder_n_qubits]; omega,
          by simp only [gcCtrl, gcYBase]; omega⟩)]
    exact hctrl

/-! ## §3. The in-place multiplier `x ↦ (a·x) mod N` (Bennett `mul ; swap ; mul(N−ainv)`). -/

/-- **The in-place cheap windowed modular multiplier.**  `mul(a) ; swap ; mul(N−ainv)`: the product
    lands in the y-register, the accumulator clears (the second pass multiplies by the negated
    inverse, `mod_inv_cancel_identity`). -/
def gcMulInPlace (w bits a ainv N numWin : Nat) : EGate :=
  EGate.seq (EGate.seq (gcMul w bits a N numWin) (EGate.base (gcSwap bits)))
    (gcMul w bits (N - ainv) N numWin)

/-- **★ IN-PLACE VALUE ★** — from the clean `GCInv … 0` input (y-register `= x`), the y-register ends
    `(a·x) mod N` and the accumulator/flag/ancilla are all clean (`GCInv … ((a·x)%N) 0`). -/
theorem gcMulInPlace_value (w n a ainv N numWin x : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 1)) (hbw : numWin * w = n + 1)
    (hx : x < N) (hainv : ainv < N) (h_inv : a * ainv % N = 1)
    (g : Nat → Bool) (hg : GCInv w (n + 1) numWin x 0 g) :
    GCInv w (n + 1) numWin ((a * x) % N) 0
      (EGate.applyNat (gcMulInPlace w (n + 1) a ainv N numWin) g) := by
  have hpow : (2 ^ w) ^ numWin = 2 ^ (n + 1) := by rw [← pow_mul, Nat.mul_comm w numWin, hbw]
  have hxlt2 : x < 2 ^ (n + 1) := lt_of_lt_of_le hx hN2
  have hx_pow : x < (2 ^ w) ^ numWin := by rw [hpow]; exact hxlt2
  -- pass 1: accumulate (a·x) mod N
  have h1 := gcMul_GCInv_from_acc w n a N numWin x 0 hw hN hN2 hbw hN hx_pow g hg
  rw [Nat.zero_add] at h1
  set P := (a * x) % N with hP
  have hPlt : P < N := by rw [hP]; exact Nat.mod_lt _ hN
  have hPlt2 : P < 2 ^ (n + 1) := lt_of_lt_of_le hPlt hN2
  have hP_pow : P < (2 ^ w) ^ numWin := by rw [hpow]; exact hPlt2
  -- swap: y-reg ↔ accumulator
  have h2 := gcSwap_transport w n numWin x P hbw hxlt2 hPlt2 _ h1
  -- pass 2: multiply by N − ainv to clear the accumulator
  have h3 := gcMul_GCInv_from_acc w n (N - ainv) N numWin P x hw hN hN2 hbw hx hP_pow _ h2
  have hclean : (x + (N - ainv) * P) % N = 0 := by
    rw [hP]; exact mod_inv_cancel_identity a ainv N x hN hx hainv h_inv
  rw [hclean] at h3
  show GCInv w (n + 1) numWin P 0
    (EGate.applyNat (gcMul w (n + 1) (N - ainv) N numWin)
      (EGate.applyNat (EGate.base (gcSwap (n + 1)))
        (EGate.applyNat (gcMul w (n + 1) a N numWin) g)))
  exact h3

/-! ## §4. The encode adapters and the canonical `encodeDataZeroAnc` round-trip gate. -/

/-- The ancilla width hosting the full gcMul layout above the `bits` data wires:
    `bits + gcAnc = gcCtrl + 1` (every gcMul index is then `< bits + gcAnc`). -/
def gcAnc (w bits : Nat) : Nat := 3 * bits + w + 7

/-- Encode-in adapter: swap the `bits` data wires `[0,bits)` (big-endian) into the y-register, then
    set the lookup control.  Maps `encodeDataZeroAnc bits (gcAnc) x` to the clean `GCInv … 0` input. -/
def gcEncodeIn (w bits numWin : Nat) : Gate :=
  Gate.seq (swapCascade (fun k => bits - 1 - k) (fun k => gcYBase bits + k) bits)
    (Gate.X (gcCtrl w bits numWin))

/-- Encode-out adapter: clear the control, swap the y-register product back to the data wires. -/
def gcEncodeOut (w bits numWin : Nat) : Gate :=
  Gate.seq (Gate.X (gcCtrl w bits numWin))
    (swapCascade (fun k => bits - 1 - k) (fun k => gcYBase bits + k) bits)

/-- **The canonical encode gate**: `encodeDataZeroAnc bits (gcAnc) x ↦ encodeDataZeroAnc bits (gcAnc)
    ((a·x) mod N)` — the in-place cheap multiplier wrapped into the Shor layout. -/
def gcMulEncodeGate (w bits a ainv N numWin : Nat) : EGate :=
  EGate.seq (EGate.base (gcEncodeIn w bits numWin))
    (EGate.seq (gcMulInPlace w bits a ainv N numWin)
      (EGate.base (gcEncodeOut w bits numWin)))

/-! ## §5. Well-typedness of the whole encode gate (the witness `eg_wellTyped`). -/

theorem gcStep_wellTypedAt (w n a N numWin j dim : Nat)
    (hbw : numWin * w = n + 1) (hj : j < numWin)
    (hdim : 4 * (n + 1) + w + 7 ≤ dim) :
    EGate.WellTypedAt dim (gcStep w (n + 1) a N numWin j) := by
  refine ⟨?_, ?_⟩
  · apply unaryQROMPos_wellTypedAt (gcAIdxAt w (n + 1) j) (gcCAnc w (n + 1) numWin) read_idx (n + 1 + 1)
      (biasedTableValue a N (n + 1) w j) dim
      (by intro i i' h; simp only [gcCAnc] at h; omega) w (gcCtrl w (n + 1) numWin) 0
    · simp only [gcCtrl, gcYBase, adder_n_qubits]; omega
    · intro i hi
      simp only [gcAIdxAt, gcYBase, adder_n_qubits]
      have : j * w + i < numWin * w := by
        have : j * w + w ≤ numWin * w := by
          calc j * w + w = (j + 1) * w := by ring
          _ ≤ numWin * w := Nat.mul_le_mul_right w hj
        omega
      omega
    · intro i hi
      simp only [gcCAnc, gcYBase, adder_n_qubits]; omega
    · intro k hk
      simp only [read_idx]; omega
    · intro i i' hi _; simp only [gcAIdxAt, gcCAnc]
      have : j * w + i < numWin * w := by
        have : j * w + w ≤ numWin * w := by
          calc j * w + w = (j + 1) * w := by ring
          _ ≤ numWin * w := Nat.mul_le_mul_right w hj
        omega
      omega
    · intro i jj _ hjj; simp only [gcAIdxAt, gcYBase, read_idx, adder_n_qubits]; omega
    · intro i jj _ hjj; simp only [gcCAnc, gcYBase, read_idx, adder_n_qubits]; omega
    · intro i hi; simp only [gcCtrl, gcAIdxAt]
      have : j * w + i < numWin * w := by
        have : j * w + w ≤ numWin * w := by
          calc j * w + w = (j + 1) * w := by ring
          _ ≤ numWin * w := Nat.mul_le_mul_right w hj
        omega
      omega
    · intro i hi; simp only [gcCtrl, gcCAnc]; omega
    · intro jj hjj; simp only [gcCtrl, gcYBase, read_idx, adder_n_qubits]; omega
  · exact gidneyModAddRegMeasured_wellTypedAt n N dim (by simp only [adder_n_qubits]; omega)

theorem gcMulN_wellTypedAt (w n a N numWin m dim : Nat)
    (hbw : numWin * w = n + 1) (hm : m ≤ numWin)
    (hdim : 4 * (n + 1) + w + 7 ≤ dim) :
    EGate.WellTypedAt dim (gcMulN w (n + 1) a N numWin m) := by
  induction m with
  | zero =>
      show Gate.WellTyped dim Gate.I
      show 0 < dim
      omega
  | succ k ih =>
      have hsplit : gcMulN w (n + 1) a N numWin (k + 1)
          = EGate.seq (gcMulN w (n + 1) a N numWin k) (gcStep w (n + 1) a N numWin k) := by
        unfold gcMulN; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hsplit]
      exact ⟨ih (by omega), gcStep_wellTypedAt w n a N numWin k dim hbw (by omega) hdim⟩

theorem gcMul_wellTypedAt (w n a N numWin dim : Nat)
    (hbw : numWin * w = n + 1)
    (hdim : 4 * (n + 1) + w + 7 ≤ dim) :
    EGate.WellTypedAt dim (gcMul w (n + 1) a N numWin) := by
  show EGate.WellTypedAt dim (gcMulN w (n + 1) a N numWin numWin)
  exact gcMulN_wellTypedAt w n a N numWin numWin dim hbw (le_refl _) hdim

theorem gcSwap_wellTyped (w n numWin dim : Nat)
    (hbw : numWin * w = n + 1)
    (hdim : 4 * (n + 1) + w + 7 ≤ dim) :
    Gate.WellTyped dim (gcSwap (n + 1)) := by
  show Gate.WellTyped dim (swapCascade target_idx (fun k => gcYBase (n + 1) + k) (n + 1))
  apply swapCascade_wellTyped target_idx (fun k => gcYBase (n + 1) + k) (n + 1) dim (by omega)
  intro i hi
  refine ⟨?_, ?_, ?_⟩
  · simp only [target_idx]; omega
  · simp only [gcYBase, adder_n_qubits]; omega
  · simp only [target_idx, gcYBase, adder_n_qubits]; omega

theorem gcMulInPlace_wellTypedAt (w n a ainv N numWin dim : Nat)
    (hbw : numWin * w = n + 1)
    (hdim : 4 * (n + 1) + w + 7 ≤ dim) :
    EGate.WellTypedAt dim (gcMulInPlace w (n + 1) a ainv N numWin) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact gcMul_wellTypedAt w n a N numWin dim hbw hdim
  · show Gate.WellTyped dim (gcSwap (n + 1))
    exact gcSwap_wellTyped w n numWin dim hbw hdim
  · exact gcMul_wellTypedAt w n (N - ainv) N numWin dim hbw hdim

theorem gcEncodeIn_wellTyped (w n numWin dim : Nat)
    (hbw : numWin * w = n + 1)
    (hdim : 4 * (n + 1) + w + 7 ≤ dim) :
    Gate.WellTyped dim (gcEncodeIn w (n + 1) numWin) := by
  refine ⟨?_, ?_⟩
  · apply swapCascade_wellTyped (fun k => (n + 1) - 1 - k) (fun k => gcYBase (n + 1) + k) (n + 1) dim
      (by omega)
    intro i hi
    refine ⟨?_, ?_, ?_⟩
    · omega
    · simp only [gcYBase, adder_n_qubits]; omega
    · simp only [gcYBase, adder_n_qubits]; omega
  · show Gate.WellTyped dim (Gate.X (gcCtrl w (n + 1) numWin))
    show gcCtrl w (n + 1) numWin < dim
    simp only [gcCtrl, gcYBase, adder_n_qubits]; omega

theorem gcEncodeOut_wellTyped (w n numWin dim : Nat)
    (hbw : numWin * w = n + 1)
    (hdim : 4 * (n + 1) + w + 7 ≤ dim) :
    Gate.WellTyped dim (gcEncodeOut w (n + 1) numWin) := by
  refine ⟨?_, ?_⟩
  · show Gate.WellTyped dim (Gate.X (gcCtrl w (n + 1) numWin))
    show gcCtrl w (n + 1) numWin < dim
    simp only [gcCtrl, gcYBase, adder_n_qubits]; omega
  · apply swapCascade_wellTyped (fun k => (n + 1) - 1 - k) (fun k => gcYBase (n + 1) + k) (n + 1) dim
      (by omega)
    intro i hi
    refine ⟨?_, ?_, ?_⟩
    · omega
    · simp only [gcYBase, adder_n_qubits]; omega
    · simp only [gcYBase, adder_n_qubits]; omega

theorem gcMulEncodeGate_wellTypedAt (w n a ainv N numWin dim : Nat)
    (hbw : numWin * w = n + 1)
    (hdim : 4 * (n + 1) + w + 7 ≤ dim) :
    EGate.WellTypedAt dim (gcMulEncodeGate w (n + 1) a ainv N numWin) := by
  refine ⟨?_, ?_, ?_⟩
  · show Gate.WellTyped dim (gcEncodeIn w (n + 1) numWin)
    exact gcEncodeIn_wellTyped w n numWin dim hbw hdim
  · exact gcMulInPlace_wellTypedAt w n a ainv N numWin dim hbw hdim
  · show Gate.WellTyped dim (gcEncodeOut w (n + 1) numWin)
    exact gcEncodeOut_wellTyped w n numWin dim hbw hdim

theorem gcMulEncodeGate_wellTypedAt_canonical (w n a ainv N numWin : Nat)
    (hbw : numWin * w = n + 1) :
    EGate.WellTypedAt ((n + 1) + gcAnc w (n + 1)) (gcMulEncodeGate w (n + 1) a ainv N numWin) := by
  apply gcMulEncodeGate_wellTypedAt w n a ainv N numWin _ hbw
  simp only [gcAnc]; omega

/-! ## §6. The Toffoli count (measured temporary-AND), on the encode gate. -/

theorem toffoli_gcMulInPlace (w n a ainv N numWin : Nat) :
    EGate.toffoli (gcMulInPlace w (n + 1) a ainv N numWin)
      = 2 * (numWin * ((2 ^ w - 1) + 2 * (n + 2))) := by
  have htc : EGate.tcount (gcMulInPlace w (n + 1) a ainv N numWin)
      = 2 * (numWin * (7 * ((2 ^ w - 1) + 2 * (n + 2)))) := by
    show EGate.tcount (gcMul w (n + 1) a N numWin)
        + EGate.tcount (EGate.base (gcSwap (n + 1)))
        + EGate.tcount (gcMul w (n + 1) (N - ainv) N numWin)
      = 2 * (numWin * (7 * ((2 ^ w - 1) + 2 * (n + 2))))
    have hswap : EGate.tcount (EGate.base (gcSwap (n + 1))) = 0 := by
      show Gate.tcount (gcSwap (n + 1)) = 0
      show Gate.tcount (swapCascade target_idx (fun k => gcYBase (n + 1) + k) (n + 1)) = 0
      exact tcount_swapCascade _ _ _
    show EGate.tcount (gcMulN w (n + 1) a N numWin numWin)
        + EGate.tcount (EGate.base (gcSwap (n + 1)))
        + EGate.tcount (gcMulN w (n + 1) (N - ainv) N numWin numWin)
      = 2 * (numWin * (7 * ((2 ^ w - 1) + 2 * (n + 2))))
    rw [tcount_gcMulN, tcount_gcMulN, hswap]
    ring
  unfold EGate.toffoli
  rw [htc, show 2 * (numWin * (7 * ((2 ^ w - 1) + 2 * (n + 2))))
        = (2 * (numWin * ((2 ^ w - 1) + 2 * (n + 2)))) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **★ THE ENCODE-GATE TOFFOLI COUNT ★** — `2·numWin·((2^w−1) + 3·(bits+1))`, the cheap measured
    count of the in-place multiplier (two passes, T-free swap/encode adapters). -/
theorem toffoli_gcMulEncodeGate (w n a ainv N numWin : Nat) :
    EGate.toffoli (gcMulEncodeGate w (n + 1) a ainv N numWin)
      = 2 * (numWin * ((2 ^ w - 1) + 2 * (n + 2))) := by
  have htc : EGate.tcount (gcMulEncodeGate w (n + 1) a ainv N numWin)
      = 2 * (numWin * (7 * ((2 ^ w - 1) + 2 * (n + 2)))) := by
    show EGate.tcount (EGate.base (gcEncodeIn w (n + 1) numWin))
        + (EGate.tcount (gcMulInPlace w (n + 1) a ainv N numWin)
          + EGate.tcount (EGate.base (gcEncodeOut w (n + 1) numWin)))
      = 2 * (numWin * (7 * ((2 ^ w - 1) + 2 * (n + 2))))
    have hin : EGate.tcount (EGate.base (gcEncodeIn w (n + 1) numWin)) = 0 := by
      show Gate.tcount (gcEncodeIn w (n + 1) numWin) = 0
      show Gate.tcount (Gate.seq (swapCascade (fun k => (n + 1) - 1 - k)
          (fun k => gcYBase (n + 1) + k) (n + 1)) (Gate.X (gcCtrl w (n + 1) numWin))) = 0
      show Gate.tcount (swapCascade (fun k => (n + 1) - 1 - k) (fun k => gcYBase (n + 1) + k) (n + 1))
          + Gate.tcount (Gate.X (gcCtrl w (n + 1) numWin)) = 0
      rw [tcount_swapCascade]; rfl
    have hout : EGate.tcount (EGate.base (gcEncodeOut w (n + 1) numWin)) = 0 := by
      show Gate.tcount (gcEncodeOut w (n + 1) numWin) = 0
      show Gate.tcount (Gate.seq (Gate.X (gcCtrl w (n + 1) numWin))
          (swapCascade (fun k => (n + 1) - 1 - k) (fun k => gcYBase (n + 1) + k) (n + 1))) = 0
      show Gate.tcount (Gate.X (gcCtrl w (n + 1) numWin))
          + Gate.tcount (swapCascade (fun k => (n + 1) - 1 - k) (fun k => gcYBase (n + 1) + k) (n + 1)) = 0
      rw [tcount_swapCascade]; rfl
    have hmip : EGate.tcount (gcMulInPlace w (n + 1) a ainv N numWin)
        = 2 * (numWin * (7 * ((2 ^ w - 1) + 2 * (n + 2)))) := by
      show EGate.tcount (gcMul w (n + 1) a N numWin)
          + EGate.tcount (EGate.base (gcSwap (n + 1)))
          + EGate.tcount (gcMul w (n + 1) (N - ainv) N numWin)
        = 2 * (numWin * (7 * ((2 ^ w - 1) + 2 * (n + 2))))
      have hswap : EGate.tcount (EGate.base (gcSwap (n + 1))) = 0 := by
        show Gate.tcount (gcSwap (n + 1)) = 0
        exact tcount_swapCascade _ _ _
      show EGate.tcount (gcMulN w (n + 1) a N numWin numWin)
          + EGate.tcount (EGate.base (gcSwap (n + 1)))
          + EGate.tcount (gcMulN w (n + 1) (N - ainv) N numWin numWin)
        = 2 * (numWin * (7 * ((2 ^ w - 1) + 2 * (n + 2))))
      rw [tcount_gcMulN, tcount_gcMulN, hswap]; ring
    rw [hin, hout, hmip]; ring
  unfold EGate.toffoli
  rw [htc, show 2 * (numWin * (7 * ((2 ^ w - 1) + 2 * (n + 2))))
        = (2 * (numWin * ((2 ^ w - 1) + 2 * (n + 2)))) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-! ## §7. The encode-in adapter maps `encodeDataZeroAnc` to the clean GCInv input. -/

theorem gcEncodeIn_GCInv (w n a numWin x : Nat)
    (hbw : numWin * w = n + 1) (hx2 : x < 2 ^ (n + 1)) :
    GCInv w (n + 1) numWin x 0
      (EGate.applyNat (EGate.base (gcEncodeIn w (n + 1) numWin))
        (encodeDataZeroAnc (n + 1) (gcAnc w (n + 1)) x)) := by
  set bits := n + 1 with hbits
  set anc := gcAnc w bits with hanc_def
  set g0 := encodeDataZeroAnc bits anc x with hg0
  have hanc_pos : 0 < anc := by rw [hanc_def, gcAnc]; omega
  have hu_inj : ∀ i k, i < bits → k < bits → i ≠ k → (bits - 1 - i) ≠ (bits - 1 - k) := by
    intro i k hi hk hik; omega
  have hv_inj : ∀ i k, i < bits → k < bits → i ≠ k → gcYBase bits + i ≠ gcYBase bits + k := by
    intro i k _ _ hik; omega
  have huv : ∀ i k, i < bits → k < bits → (bits - 1 - i) ≠ gcYBase bits + k := by
    intro i k hi _; simp only [gcYBase, adder_n_qubits]; omega
  obtain ⟨hsw_uv, hsw_vu, hsw_frame⟩ :=
    swapCascade_apply (fun k => bits - 1 - k) (fun k => gcYBase bits + k) bits g0 hu_inj hv_inj huv
  set swapG := swapCascade (fun k => bits - 1 - k) (fun k => gcYBase bits + k) bits with hswapG
  set gs := Gate.applyNat swapG g0 with hgs
  have hYbase_eq : gcYBase bits = 3 * bits + 6 := by simp only [gcYBase, adder_n_qubits]; ring
  have hctrl_eq : gcCtrl w bits numWin = 4 * bits + w + 6 := by
    simp only [gcCtrl, gcYBase, adder_n_qubits, hbw]; omega
  have hcanc_eq : ∀ i, gcCAnc w bits numWin i = 3 * bits + 6 + bits + i := by
    intro i; simp only [gcCAnc, gcYBase, adder_n_qubits, hbw]; omega
  have hflag_eq : gcFlag bits = 3 * bits + 5 := by simp only [gcFlag, adder_n_qubits]; ring
  have hanceq : anc = 3 * bits + w + 7 := by rw [hanc_def, gcAnc]
  have hanc_eval : ∀ p, bits ≤ p → p < bits + anc → g0 p = false := by
    intro p hge hlt
    have hrw : g0 p = g0 (bits + (p - bits)) := by congr 1; omega
    rw [hrw]
    exact encodeDataZeroAnc_anc (n := bits) (anc := anc) (x := x) hx2 (by omega)
  show GCInv w bits numWin x 0 (Gate.applyNat (Gate.X (gcCtrl w bits numWin)) gs)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hq3 : q < 3 * bits + 5 := by simp only [adder_n_qubits] at hq; omega
    have hq_ne_ctrl : q ≠ gcCtrl w bits numWin := by rw [hctrl_eq]; omega
    rw [Gate.applyNat_X, update_neq _ _ _ _ hq_ne_ctrl, adder_input_F_zero]
    by_cases hqb : q < bits
    · have huq : (bits - 1 - (bits - 1 - q)) = q := by omega
      have hh := hsw_uv (bits - 1 - q) (by omega)
      rw [huq] at hh
      rw [hh]
      apply hanc_eval
      · rw [hYbase_eq]; omega
      · rw [hYbase_eq, hanceq]; omega
    · have hframe := hsw_frame q (by
        intro i hi
        exact ⟨by omega, by rw [hYbase_eq]; omega⟩)
      rw [hframe]
      apply hanc_eval q (by omega)
      rw [hanceq]; omega
  · show Gate.applyNat (Gate.X (gcCtrl w bits numWin)) gs (gcFlag bits) = false
    have hne : gcFlag bits ≠ gcCtrl w bits numWin := by rw [hflag_eq, hctrl_eq]; omega
    rw [Gate.applyNat_X, update_neq _ _ _ _ hne]
    have hframe := hsw_frame (gcFlag bits) (by
      intro i hi
      exact ⟨by rw [hflag_eq]; omega, by rw [hflag_eq, hYbase_eq]; omega⟩)
    rw [hframe]
    apply hanc_eval (gcFlag bits)
    · rw [hflag_eq]; omega
    · rw [hflag_eq, hanceq]; omega
  · intro k hk
    have hkb : k < bits := by omega
    have hne : gcYBase bits + k ≠ gcCtrl w bits numWin := by rw [hYbase_eq, hctrl_eq]; omega
    rw [Gate.applyNat_X, update_neq _ _ _ _ hne]
    have hh := hsw_vu k hkb
    rw [hh, hg0, encodeDataZeroAnc_data hx2 (by omega),
        VerifiedShor.Windowed.nat_to_funbool_eq_testBit]
    congr 1
    omega
  · intro i hi
    have hne : gcCAnc w bits numWin i ≠ gcCtrl w bits numWin := by rw [hcanc_eq, hctrl_eq]; omega
    rw [Gate.applyNat_X, update_neq _ _ _ _ hne]
    have hframe := hsw_frame (gcCAnc w bits numWin i) (by
      intro j hj
      exact ⟨by rw [hcanc_eq]; omega, by rw [hcanc_eq, hYbase_eq]; omega⟩)
    rw [hframe]
    apply hanc_eval
    · rw [hcanc_eq]; omega
    · rw [hcanc_eq, hanceq]; omega
  · show Gate.applyNat (Gate.X (gcCtrl w bits numWin)) gs (gcCtrl w bits numWin) = true
    rw [Gate.applyNat_X, update_eq]
    have hframe := hsw_frame (gcCtrl w bits numWin) (by
      intro j hj
      exact ⟨by rw [hctrl_eq]; omega, by rw [hctrl_eq, hYbase_eq]; omega⟩)
    rw [hframe, hanc_eval (gcCtrl w bits numWin) (by rw [hctrl_eq]; omega)
      (by rw [hctrl_eq, hanceq]; omega)]
    rfl

/-! ## §8. Frame: the whole gate fixes every index `≥ bits + gcAnc`. -/

theorem gcStep_frame (w n a N numWin j : Nat) (hbw : numWin * w = n + 1) (f : Nat → Bool) (p : Nat)
    (hp : (n + 1) + gcAnc w (n + 1) ≤ p) :
    EGate.applyNat (gcStep w (n + 1) a N numWin j) f p = f p := by
  set bits := n + 1 with hbits
  have hdimbig : bits + gcAnc w bits = 4 * bits + w + 7 := by simp only [gcAnc]; omega
  show EGate.applyNat (gidneyModAddRegMeasured bits N)
      (EGate.applyNat (unaryQROMPos (gcAIdxAt w bits j) (gcCAnc w bits numWin) read_idx (bits + 1)
        (biasedTableValue a N bits w j) w (gcCtrl w bits numWin) 0) f) p = f p
  have hadd_bnd : EGate.boundedBy (adder_n_qubits (n + 2) + 1) (gidneyModAddRegMeasured (n + 1) N) :=
    gidneyModAddRegMeasured_boundedBy n N
  have hYbase_eq : adder_n_qubits (n + 2) + 1 = 3 * bits + 6 := by simp only [adder_n_qubits]; omega
  have hp_ge_add : adder_n_qubits (n + 2) + 1 ≤ p := by rw [hYbase_eq]; simp only [gcAnc] at hp; omega
  rw [EGate_applyNat_ge_of_boundedBy (adder_n_qubits (n + 2) + 1) (gidneyModAddRegMeasured (n + 1) N)
    hadd_bnd _ p hp_ge_add]
  apply unaryQROMPos_frame
  · intro j' hj'; simp only [read_idx]; simp only [gcAnc] at hp; omega
  · intro i hi; simp only [gcCAnc, gcYBase, adder_n_qubits, hbw]; simp only [gcAnc] at hp; omega

theorem gcMulN_frame (w n a N numWin : Nat) (hbw : numWin * w = n + 1) (p : Nat)
    (hp : (n + 1) + gcAnc w (n + 1) ≤ p) :
    ∀ m (f : Nat → Bool), EGate.applyNat (gcMulN w (n + 1) a N numWin m) f p = f p := by
  intro m
  induction m with
  | zero =>
      intro f
      show EGate.applyNat (gcMulN w (n + 1) a N numWin 0) f p = f p
      have : EGate.applyNat (gcMulN w (n + 1) a N numWin 0) f = f := by
        simp [gcMulN, EGate.applyNat, Gate.applyNat_I]
      rw [this]
  | succ m ih =>
      intro f
      have hsplit : gcMulN w (n + 1) a N numWin (m + 1)
          = EGate.seq (gcMulN w (n + 1) a N numWin m) (gcStep w (n + 1) a N numWin m) := by
        unfold gcMulN; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hsplit]
      show EGate.applyNat (gcStep w (n + 1) a N numWin m)
        (EGate.applyNat (gcMulN w (n + 1) a N numWin m) f) p = f p
      rw [gcStep_frame w n a N numWin m hbw _ p hp, ih f]

theorem gcMul_frame (w n a N numWin : Nat) (hbw : numWin * w = n + 1) (f : Nat → Bool) (p : Nat)
    (hp : (n + 1) + gcAnc w (n + 1) ≤ p) :
    EGate.applyNat (gcMul w (n + 1) a N numWin) f p = f p := by
  show EGate.applyNat (gcMulN w (n + 1) a N numWin numWin) f p = f p
  exact gcMulN_frame w n a N numWin hbw p hp numWin f

theorem gcSwap_frame (w n numWin : Nat) (hbw : numWin * w = n + 1) (f : Nat → Bool) (p : Nat)
    (hp : (n + 1) + gcAnc w (n + 1) ≤ p) :
    EGate.applyNat (EGate.base (gcSwap (n + 1))) f p = f p := by
  set bits := n + 1 with hbits
  have hu_inj : ∀ i k, i < bits → k < bits → i ≠ k → target_idx i ≠ target_idx k := by
    intro i k _ _ hik; simp only [target_idx]; omega
  have hv_inj : ∀ i k, i < bits → k < bits → i ≠ k → gcYBase bits + i ≠ gcYBase bits + k := by
    intro i k _ _ hik; omega
  have huv : ∀ i k, i < bits → k < bits → target_idx i ≠ gcYBase bits + k := by
    intro i k hi _; simp only [target_idx, gcYBase, adder_n_qubits]; omega
  obtain ⟨_, _, hsw_frame⟩ :=
    swapCascade_apply target_idx (fun k => gcYBase bits + k) bits f hu_inj hv_inj huv
  show Gate.applyNat (swapCascade target_idx (fun k => gcYBase bits + k) bits) f p = f p
  apply hsw_frame
  intro i hi
  refine ⟨?_, ?_⟩
  · simp only [target_idx]; simp only [gcAnc] at hp; omega
  · simp only [gcYBase, adder_n_qubits]; simp only [gcAnc] at hp; omega

theorem gcEncodeIn_frame (w n numWin : Nat) (hbw : numWin * w = n + 1) (f : Nat → Bool) (p : Nat)
    (hp : (n + 1) + gcAnc w (n + 1) ≤ p) :
    EGate.applyNat (EGate.base (gcEncodeIn w (n + 1) numWin)) f p = f p := by
  set bits := n + 1 with hbits
  have hu_inj : ∀ i k, i < bits → k < bits → i ≠ k → (bits - 1 - i) ≠ (bits - 1 - k) := by
    intro i k hi hk hik; omega
  have hv_inj : ∀ i k, i < bits → k < bits → i ≠ k → gcYBase bits + i ≠ gcYBase bits + k := by
    intro i k _ _ hik; omega
  have huv : ∀ i k, i < bits → k < bits → (bits - 1 - i) ≠ gcYBase bits + k := by
    intro i k hi _; simp only [gcYBase, adder_n_qubits]; omega
  obtain ⟨_, _, hsw_frame⟩ :=
    swapCascade_apply (fun k => bits - 1 - k) (fun k => gcYBase bits + k) bits f hu_inj hv_inj huv
  show Gate.applyNat (Gate.X (gcCtrl w bits numWin))
      (Gate.applyNat (swapCascade (fun k => bits - 1 - k) (fun k => gcYBase bits + k) bits) f) p = f p
  have hctrl_eq : gcCtrl w bits numWin = 4 * bits + w + 6 := by
    simp only [gcCtrl, gcYBase, adder_n_qubits, hbw]; omega
  have hp_ne_ctrl : p ≠ gcCtrl w bits numWin := by rw [hctrl_eq]; simp only [gcAnc] at hp; omega
  rw [Gate.applyNat_X, update_neq _ _ _ _ hp_ne_ctrl]
  apply hsw_frame
  intro i hi
  refine ⟨?_, ?_⟩
  · simp only [gcAnc] at hp; omega
  · simp only [gcYBase, adder_n_qubits]; simp only [gcAnc] at hp; omega

theorem gcEncodeOut_frame (w n numWin : Nat) (hbw : numWin * w = n + 1) (f : Nat → Bool) (p : Nat)
    (hp : (n + 1) + gcAnc w (n + 1) ≤ p) :
    EGate.applyNat (EGate.base (gcEncodeOut w (n + 1) numWin)) f p = f p := by
  set bits := n + 1 with hbits
  have hu_inj : ∀ i k, i < bits → k < bits → i ≠ k → (bits - 1 - i) ≠ (bits - 1 - k) := by
    intro i k hi hk hik; omega
  have hv_inj : ∀ i k, i < bits → k < bits → i ≠ k → gcYBase bits + i ≠ gcYBase bits + k := by
    intro i k _ _ hik; omega
  have huv : ∀ i k, i < bits → k < bits → (bits - 1 - i) ≠ gcYBase bits + k := by
    intro i k hi _; simp only [gcYBase, adder_n_qubits]; omega
  have hctrl_eq : gcCtrl w bits numWin = 4 * bits + w + 6 := by
    simp only [gcCtrl, gcYBase, adder_n_qubits, hbw]; omega
  have hp_ne_ctrl : p ≠ gcCtrl w bits numWin := by rw [hctrl_eq]; simp only [gcAnc] at hp; omega
  show Gate.applyNat (swapCascade (fun k => bits - 1 - k) (fun k => gcYBase bits + k) bits)
      (Gate.applyNat (Gate.X (gcCtrl w bits numWin)) f) p = f p
  obtain ⟨_, _, hsw_frame⟩ :=
    swapCascade_apply (fun k => bits - 1 - k) (fun k => gcYBase bits + k) bits
      (Gate.applyNat (Gate.X (gcCtrl w bits numWin)) f) hu_inj hv_inj huv
  rw [hsw_frame p (by
    intro i hi
    refine ⟨by simp only [gcAnc] at hp; omega, by simp only [gcYBase, adder_n_qubits]; simp only [gcAnc] at hp; omega⟩)]
  rw [Gate.applyNat_X, update_neq _ _ _ _ hp_ne_ctrl]

theorem gcMulInPlace_frame (w n a ainv N numWin : Nat) (hbw : numWin * w = n + 1)
    (f : Nat → Bool) (p : Nat) (hp : (n + 1) + gcAnc w (n + 1) ≤ p) :
    EGate.applyNat (gcMulInPlace w (n + 1) a ainv N numWin) f p = f p := by
  show EGate.applyNat (gcMul w (n + 1) (N - ainv) N numWin)
      (EGate.applyNat (EGate.base (gcSwap (n + 1)))
        (EGate.applyNat (gcMul w (n + 1) a N numWin) f)) p = f p
  rw [gcMul_frame w n (N - ainv) N numWin hbw _ p hp,
      gcSwap_frame w n numWin hbw _ p hp,
      gcMul_frame w n a N numWin hbw f p hp]

theorem gcMulEncodeGate_frame (w n a ainv N numWin : Nat) (hbw : numWin * w = n + 1)
    (f : Nat → Bool) (p : Nat) (hp : (n + 1) + gcAnc w (n + 1) ≤ p) :
    EGate.applyNat (gcMulEncodeGate w (n + 1) a ainv N numWin) f p = f p := by
  show EGate.applyNat (EGate.base (gcEncodeOut w (n + 1) numWin))
      (EGate.applyNat (gcMulInPlace w (n + 1) a ainv N numWin)
        (EGate.applyNat (EGate.base (gcEncodeIn w (n + 1) numWin)) f)) p = f p
  rw [gcEncodeOut_frame w n numWin hbw _ p hp,
      gcMulInPlace_frame w n a ainv N numWin hbw _ p hp,
      gcEncodeIn_frame w n numWin hbw f p hp]

/-! ## §9. ★ THE ENCODE ROUND-TRIP VALUE ★ — `x ↦ (a·x) mod N` on the canonical encoding. -/

theorem gcMulEncodeGate_apply (w n a ainv N numWin x : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 1)) (hbw : numWin * w = n + 1)
    (hx : x < N) (hainv : ainv < N) (h_inv : a * ainv % N = 1) :
    EGate.applyNat (gcMulEncodeGate w (n + 1) a ainv N numWin)
        (encodeDataZeroAnc (n + 1) (gcAnc w (n + 1)) x)
      = encodeDataZeroAnc (n + 1) (gcAnc w (n + 1)) ((a * x) % N) := by
  set bits := n + 1 with hbits
  set anc := gcAnc w bits with hanc_def
  set g0 := encodeDataZeroAnc bits anc x with hg0
  have hanc_pos : 0 < anc := by rw [hanc_def, gcAnc]; omega
  have hanceq : anc = 3 * bits + w + 7 := by rw [hanc_def, gcAnc]
  have hxlt2 : x < 2 ^ bits := lt_of_lt_of_le hx hN2
  have h1 := gcEncodeIn_GCInv w n a numWin x hbw hxlt2
  have h2 := gcMulInPlace_value w n a ainv N numWin x hw hN hN2 hbw hx hainv h_inv
    (EGate.applyNat (EGate.base (gcEncodeIn w bits numWin)) g0) h1
  obtain ⟨hblock, hflag, hy, hancc, hctrl⟩ := h2
  set g2 := EGate.applyNat (gcMulInPlace w bits a ainv N numWin)
    (EGate.applyNat (EGate.base (gcEncodeIn w bits numWin)) g0) with hg2def
  have hYbase_eq : gcYBase bits = 3 * bits + 6 := by simp only [gcYBase, adder_n_qubits]; ring
  have hctrl_eq : gcCtrl w bits numWin = 4 * bits + w + 6 := by
    simp only [gcCtrl, gcYBase, adder_n_qubits, hbw]; omega
  have hcanc_eq : ∀ i, gcCAnc w bits numWin i = 4 * bits + 6 + i := by
    intro i; simp only [gcCAnc, gcYBase, adder_n_qubits, hbw]; omega
  have hflag_eq : gcFlag bits = 3 * bits + 5 := by simp only [gcFlag, adder_n_qubits]; ring
  have hPlt2 : (a * x) % N < 2 ^ bits := lt_of_lt_of_le (Nat.mod_lt _ hN) hN2
  show EGate.applyNat (EGate.base (gcEncodeOut w bits numWin)) g2
      = encodeDataZeroAnc bits anc ((a * x) % N)
  have hu_inj : ∀ i k, i < bits → k < bits → i ≠ k → (bits - 1 - i) ≠ (bits - 1 - k) := by
    intro i k hi hk hik; omega
  have hv_inj : ∀ i k, i < bits → k < bits → i ≠ k → gcYBase bits + i ≠ gcYBase bits + k := by
    intro i k _ _ hik; omega
  have huv : ∀ i k, i < bits → k < bits → (bits - 1 - i) ≠ gcYBase bits + k := by
    intro i k hi _; simp only [gcYBase, adder_n_qubits]; omega
  set g2' := Gate.applyNat (Gate.X (gcCtrl w bits numWin)) g2 with hg2'def
  obtain ⟨hsw_uv, hsw_vu, hsw_frame⟩ :=
    swapCascade_apply (fun k => bits - 1 - k) (fun k => gcYBase bits + k) bits g2' hu_inj hv_inj huv
  set swapG := swapCascade (fun k => bits - 1 - k) (fun k => gcYBase bits + k) bits with hswapG
  have hg2'_off : ∀ q, q ≠ gcCtrl w bits numWin → g2' q = g2 q := by
    intro q hq; rw [hg2'def, Gate.applyNat_X, update_neq _ _ _ _ hq]
  have hfinal : EGate.applyNat (EGate.base (gcEncodeOut w bits numWin)) g2
      = Gate.applyNat swapG g2' := by
    show Gate.applyNat (Gate.seq (Gate.X (gcCtrl w bits numWin)) swapG) g2 = Gate.applyNat swapG g2'
    rw [Gate.applyNat_seq]
  rw [hfinal]
  apply eq_encodeDataZeroAnc_of_data_anc_oob hanc_pos hPlt2
  · intro i hi
    have hkb : bits - 1 - i < bits := by omega
    have hh := hsw_uv (bits - 1 - i) hkb
    have huq : (bits - 1 - (bits - 1 - i)) = i := by omega
    rw [huq] at hh
    rw [hh]
    have hne : gcYBase bits + (bits - 1 - i) ≠ gcCtrl w bits numWin := by
      rw [hYbase_eq, hctrl_eq]; omega
    rw [hg2'_off _ hne]
    have := hy (bits - 1 - i) (by omega)
    rw [this, VerifiedShor.Windowed.nat_to_funbool_eq_testBit]
  · intro j hj
    set p := bits + j with hpdef
    have hpge : bits ≤ p := by omega
    have hplt : p < bits + anc := by rw [hanceq]; omega
    by_cases hvr : ∃ k, k < bits ∧ p = gcYBase bits + k
    · obtain ⟨k, hk, hpk⟩ := hvr
      rw [hpk, hsw_vu k hk]
      have hne : (bits - 1 - k) ≠ gcCtrl w bits numWin := by rw [hctrl_eq]; omega
      rw [hg2'_off _ hne]
      rw [hblock (bits - 1 - k) (by simp only [adder_n_qubits]; omega), adder_input_F_zero]
    · push_neg at hvr
      have hframe := hsw_frame p (by
        intro i hi
        refine ⟨by omega, ?_⟩
        intro hcontra
        exact (hvr i hi) hcontra)
      rw [hframe]
      by_cases hpc : p = gcCtrl w bits numWin
      · rw [hpc, hg2'def, Gate.applyNat_X, update_eq, hctrl, Bool.not_true]
      · rw [hg2'_off p hpc]
        by_cases hpblk : p < 3 * bits + 5
        · rw [hblock p (by simp only [adder_n_qubits]; omega), adder_input_F_zero]
        · by_cases hpf : p = gcFlag bits
          · rw [hpf, hflag]
          · have hnotv : ∀ k, k < bits → p ≠ gcYBase bits + k := hvr
            have hpge2 : 4 * bits + 6 ≤ p := by
              by_contra hlt
              push_neg at hlt
              have hk : p - (3 * bits + 6) < bits := by omega
              exact hnotv (p - (3 * bits + 6)) hk (by rw [hYbase_eq]; omega)
            have hi : p - (4 * bits + 6) < w := by
              rw [hctrl_eq] at hpc
              rw [hanceq] at hplt
              omega
            have hpeq : p = gcCAnc w bits numWin (p - (4 * bits + 6)) := by
              rw [hcanc_eq]; omega
            rw [hpeq, hancc (p - (4 * bits + 6)) hi]
  · intro i hi
    have hge : bits + gcAnc w bits ≤ i := by rw [← hanc_def]; exact hi
    have hframe := hsw_frame i (by
      intro k hk
      refine ⟨by simp only [gcAnc] at hge; omega, by simp only [gcYBase, adder_n_qubits]; simp only [gcAnc] at hge; omega⟩)
    rw [hframe]
    have hne : i ≠ gcCtrl w bits numWin := by rw [hctrl_eq]; simp only [gcAnc] at hge; omega
    rw [hg2'_off i hne, hg2def,
        gcMulInPlace_frame w n a ainv N numWin hbw _ i hge,
        gcEncodeIn_frame w n numWin hbw g0 i hge, hg0]
    exact encodeDataZeroAnc_oob hanc_pos hi

end FormalRV.Shor.GidneyCheapModMulInPlace
