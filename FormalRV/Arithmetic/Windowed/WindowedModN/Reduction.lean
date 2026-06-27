/- WindowedModN — §6 register mod-N reduction primitive.
   Part of `WindowedModN` (the `WindowedModN.lean` shim re-exports all parts). -/
import FormalRV.Arithmetic.Windowed.WindowedModN.CondSub

namespace FormalRV.Shor.WindowedCircuit
open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §6. The register mod-N reduction primitive. -/

/-- Reduction arithmetic: for `x < 2N ≤ 2^bits`,
    `(x + [N ≤ x]·(2^bits − N)) mod 2^bits = x mod N`. -/
theorem modNReduce_arith (bits N x : Nat)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hx : x < 2 * N) :
    (x + if decide (N ≤ x) then 2 ^ bits - N else 0) % 2 ^ bits = x % N := by
  by_cases h : N ≤ x
  · rw [if_pos (by simp [h] : decide (N ≤ x) = true)]
    have h_eq : x + (2 ^ bits - N) = (x - N) + 2 ^ bits := by omega
    rw [h_eq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : x - N < 2 ^ bits)]
    have h_xN : x % N = x - N := by
      conv_lhs => rw [show x = N + (x - N) from by omega]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : x - N < N)]
    rw [h_xN]
  · push Not at h
    rw [if_neg (by simp [Nat.not_le.mpr h] : ¬ decide (N ≤ x) = true)]
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega : x < 2 ^ bits), Nat.mod_eq_of_lt h]

/-- **The register mod-N reduction with comparison flag**:
    constant-compare against `N`, then flag-conditional subtract of `N`.
    Takes an accumulator in `[0, 2N)` to `[0, N)`; the flag picks up
    `[N ≤ acc]` (uncomputed later by `regCompareXor` against the addend). -/
def modNReduceFlag (bits q_start N flagPos : Nat) : Gate :=
  Gate.seq (sqir_style_compareConst_candidate bits q_start N flagPos)
           (sqir_conditionalSubConstGate bits q_start N flagPos)

/-- **HEADLINE general-state bundle for the mod-N reduction.**  On any state
    with clear carry-in / read register / flag and accumulator `x < 2N`:
    accumulator becomes `x mod N`, read and carry stay clear, the flag holds
    `[N ≤ x]`, and everything outside workspace ∪ {flag} is untouched. -/
theorem modNReduceFlag_state_general
    (bits q_start N flagPos x : Nat) (f : Nat → Bool)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hx : x < 2 * N)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (h_cin : f q_start = false)
    (h_flag : f flagPos = false)
    (h_tgt : ∀ i, i < bits → f (q_start + 2 * i + 1) = x.testBit i)
    (h_read : ∀ i, i < bits → f (q_start + 2 * i + 2) = false) :
    (∀ i, i < bits →
        Gate.applyNat (modNReduceFlag bits q_start N flagPos) f (q_start + 2 * i + 1)
          = (x % N).testBit i)
    ∧ (∀ i, i < bits →
        Gate.applyNat (modNReduceFlag bits q_start N flagPos) f (q_start + 2 * i + 2)
          = false)
    ∧ Gate.applyNat (modNReduceFlag bits q_start N flagPos) f q_start = false
    ∧ Gate.applyNat (modNReduceFlag bits q_start N flagPos) f flagPos
        = decide (N ≤ x)
    ∧ (∀ p, p ≠ flagPos → p < q_start ∨ q_start + 2 * bits + 1 ≤ p →
        Gate.applyNat (modNReduceFlag bits q_start N flagPos) f p = f p) := by
  have hx' : x < 2 ^ bits := by omega
  have hN : N ≤ 2 ^ bits := by omega
  have h_flag_ne_tgt : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 1 := by
    intro i hi
    rcases hflag_out with h | h <;> omega
  have h_flag_ne_read : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2 := by
    intro i hi
    rcases hflag_out with h | h <;> omega
  have h_flag_ne_cin : flagPos ≠ q_start := by
    rcases hflag_out with h | h <;> omega
  unfold modNReduceFlag
  simp only [Gate.applyNat_seq]
  rw [compareConstXor_state_general bits q_start N flagPos x f
        hN_pos hN hx' hflag_out h_cin h_tgt h_read, h_flag, Bool.false_xor]
  -- The post-compare state: `f` with the flag set to `[N ≤ x]`.
  have hg1_tgt : ∀ i, i < bits →
      update f flagPos (decide (N ≤ x)) (q_start + 2 * i + 1) = x.testBit i := by
    intro i hi
    rw [update_neq _ _ _ _ (fun h => h_flag_ne_tgt i hi h.symm)]
    exact h_tgt i hi
  have hg1_read : ∀ i, i < bits →
      update f flagPos (decide (N ≤ x)) (q_start + 2 * i + 2) = false := by
    intro i hi
    rw [update_neq _ _ _ _ (fun h => h_flag_ne_read i hi h.symm)]
    exact h_read i hi
  have hg1_cin : update f flagPos (decide (N ≤ x)) q_start = false := by
    rw [update_neq _ _ _ _ (fun h => h_flag_ne_cin h.symm)]
    exact h_cin
  have hsub := condSub_state_general bits q_start N flagPos x
    (update f flagPos (decide (N ≤ x))) hx' hflag_out hg1_cin hg1_tgt hg1_read
  refine ⟨?_, hsub.2.1, hsub.2.2.1, ?_, ?_⟩
  · intro i hi
    rw [hsub.1 i hi, update_eq]
    rw [modNReduce_arith bits N x hN_pos hN2 hx]
  · rw [hsub.2.2.2 flagPos hflag_out, update_eq]
  · intro p hp_ne hp_out
    rw [hsub.2.2.2 p hp_out]
    exact update_neq _ _ _ _ hp_ne


end FormalRV.Shor.WindowedCircuit
