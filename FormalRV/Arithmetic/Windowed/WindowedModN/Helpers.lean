/- WindowedModN — §1-2 arithmetic helpers + target-complement gate.
   Part of `WindowedModN` (the `WindowedModN.lean` shim re-exports all parts). -/
import FormalRV.Arithmetic.Windowed.WindowedCircuitCorrect
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroDirtyFlagStageCorrectness

namespace FormalRV.Shor.WindowedCircuit
open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §1. Arithmetic helpers. -/

/-- **Complemented-carry = strict comparison (mod-windows form).**  The
    ripple carry of `(¬u) + t` through the low `k` bits equals
    `[u mod 2^k < t mod 2^k]`. -/
theorem carry_compl_eq_decide_lt (u t : Nat) :
    ∀ k, Adder.carry false k (fun i => !u.testBit i) (fun i => t.testBit i)
      = decide (u % 2 ^ k < t % 2 ^ k)
  | 0 => by simp [Adder.carry, Nat.mod_one]
  | k + 1 => by
    rw [Adder.carry_succ, carry_compl_eq_decide_lt u t k]
    have hu : u % 2 ^ (k + 1) = u % 2 ^ k + 2 ^ k * (u / 2 ^ k % 2) := by
      rw [pow_succ, Nat.mod_mul]
    have ht : t % 2 ^ (k + 1) = t % 2 ^ k + 2 ^ k * (t / 2 ^ k % 2) := by
      rw [pow_succ, Nat.mod_mul]
    have hum : u % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    have htm : t % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    rw [show u.testBit k = decide (u / 2 ^ k % 2 = 1) from
          Nat.testBit_eq_decide_div_mod_eq,
        show t.testBit k = decide (t / 2 ^ k % 2 = 1) from
          Nat.testBit_eq_decide_div_mod_eq,
        hu, ht]
    have hud : u / 2 ^ k % 2 = 0 ∨ u / 2 ^ k % 2 = 1 := by omega
    have htd : t / 2 ^ k % 2 = 0 ∨ t / 2 ^ k % 2 = 1 := by omega
    rcases hud with h1 | h1 <;> rcases htd with h2 | h2 <;> rw [h1, h2] <;>
      cases hc : decide (u % 2 ^ k < t % 2 ^ k) <;>
      (try have hcp := of_decide_eq_true hc) <;>
      (try have hcn := of_decide_eq_false hc) <;>
      simp only [show decide ((0 : Nat) = 1) = false from rfl,
                 Bool.not_false, Bool.true_and,
                 Bool.and_true, Bool.and_false, Bool.xor_false, Bool.false_xor,
                 Bool.xor_true, Bool.xor_self] <;>
      first
        | rfl
        | (symm; exact decide_eq_true (by omega))
        | (symm; exact decide_eq_false (by omega))

/-- **Complemented-carry = strict comparison.**  For `u, t < 2^n`, the carry
    out of `(¬u) + t` over `n` bits is `[u < t]`. -/
theorem carry_compl_lt (n u t : Nat) (hu : u < 2 ^ n) (ht : t < 2 ^ n) :
    Adder.carry false n (fun i => !u.testBit i) (fun i => t.testBit i)
      = decide (u < t) := by
  rw [carry_compl_eq_decide_lt u t n, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt ht]

/-- **The flag-uncompute comparison.**  For `s, t < N`, the reduced sum is
    below the addend exactly when the reduction fired:
    `(s+t) mod N < t  ⟺  N ≤ s+t`. -/
theorem modReduce_lt_decide (N s t : Nat) (hs : s < N) (ht : t < N) :
    decide ((s + t) % N < t) = decide (N ≤ s + t) := by
  by_cases h : N ≤ s + t
  · have hmod : (s + t) % N = s + t - N := by
      conv_lhs => rw [show s + t = N + (s + t - N) from by omega]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    have h1 : decide (s + t - N < t) = true := by
      rw [decide_eq_true_iff]; omega
    have h2 : decide (N ≤ s + t) = true := by
      rw [decide_eq_true_iff]; omega
    rw [h1, h2]
  · push Not at h
    rw [Nat.mod_eq_of_lt h]
    have h1 : decide (s + t < t) = false := by
      rw [decide_eq_false_iff_not]; omega
    have h2 : decide (N ≤ s + t) = false := by
      rw [decide_eq_false_iff_not]; omega
    rw [h1, h2]

/-- **General-state sum bits of the full Cuccaro adder.**  If the carry-in is
    clear and the target/read registers hold the bits of `x`/`y` (below
    `bits`), the adder leaves `(x+y).testBit i` at target position `i`.
    (The general-state analogue of the decoded `sumCorrect`, at bit level.) -/
theorem cuccaro_adder_sum_bits_general
    (bits q_start x y : Nat) (f : Nat → Bool)
    (h_cin : f q_start = false)
    (h_tgt : ∀ i, i < bits → f (q_start + 2 * i + 1) = x.testBit i)
    (h_read : ∀ i, i < bits → f (q_start + 2 * i + 2) = y.testBit i)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) f (q_start + 2 * i + 1)
      = (x + y).testBit i := by
  rw [(cuccaro_n_bit_adder_full_correct bits q_start f).2.1 i hi]
  rw [cuccaro_carry_eq_Adder_carry, h_cin]
  rw [Adder.carry_ext_below false i
        (fun j => f (q_start + 2 * j + 1)) (fun j => f (q_start + 2 * j + 2))
        (fun j => x.testBit j) (fun j => y.testBit j)
        (fun j hj => h_tgt j (by omega)) (fun j hj => h_read j (by omega))]
  rw [h_tgt i hi, h_read i hi]
  have h := Adder.sumfb_eq_testBit_add_gen false x y i
  unfold Adder.sumfb at h
  simpa [Bool.toNat] using h

/-! ## §2. The target-complement gate (X on every accumulator bit). -/

/-- X on each target/augend position `q_start + 2i + 1`, `i < bits`.  Used to
    conjugate the MAJ chain so its top carry computes `¬acc + t ≥ 2^bits`,
    i.e. the strict comparison `acc < t`. -/
def targetComplement : Nat → Nat → Gate
  | 0, _ => Gate.I
  | n + 1, q_start =>
      Gate.seq (targetComplement n q_start) (Gate.X (q_start + 2 * n + 1))

/-- Frame: `targetComplement` only touches the target positions. -/
theorem targetComplement_at_other
    (bits q_start q : Nat)
    (hq : ∀ i, i < bits → q ≠ q_start + 2 * i + 1)
    (f : Nat → Bool) :
    Gate.applyNat (targetComplement bits q_start) f q = f q := by
  induction bits generalizing f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat
        (Gate.seq (targetComplement k q_start) (Gate.X (q_start + 2 * k + 1))) f q = _
    simp only [Gate.applyNat_seq, Gate.applyNat_X]
    rw [update_neq _ _ _ _ (hq k (by omega))]
    exact ih (fun i hi => hq i (by omega)) f

/-- Action at a target position: bit `j < bits` is complemented. -/
theorem targetComplement_at_target
    (bits q_start j : Nat) (hj : j < bits) (f : Nat → Bool) :
    Gate.applyNat (targetComplement bits q_start) f (q_start + 2 * j + 1)
      = !(f (q_start + 2 * j + 1)) := by
  induction bits generalizing f with
  | zero => omega
  | succ k ih =>
    show Gate.applyNat
        (Gate.seq (targetComplement k q_start) (Gate.X (q_start + 2 * k + 1))) f
        (q_start + 2 * j + 1) = _
    simp only [Gate.applyNat_seq, Gate.applyNat_X]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · rw [update_neq _ _ _ _ (by omega)]
      exact ih hjk f
    · have hjk_eq : j = k := by omega
      subst hjk_eq
      rw [update_eq]
      congr 1
      exact targetComplement_at_other j q_start (q_start + 2 * j + 1)
        (fun i hi => by omega) f


end FormalRV.Shor.WindowedCircuit
