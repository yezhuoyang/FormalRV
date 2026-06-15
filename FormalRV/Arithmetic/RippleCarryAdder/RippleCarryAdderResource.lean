/-
  FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderResource
  ─────────────────────────────────────────────────────────────
  THE resource theorems for the Gidney ripple-carry adder, surfaced as thin
  wrappers over the proofs in the supporting files, plus a
  resource-after-correctness bundle that states the resource about the SAME
  circuit the correctness theorem verifies.

  Headlines:
    • `gidney_adder_tcount` — T-count of the gate-explicit (no-measurement)
      n-bit adder = `14·n` (n forward + n reverse Toffolis, 7 T each;
      CX/final-CX are T-free).
    • `gidney_adder_tcount_vs_measurement` — that `14·n` is exactly **twice**
      the `7·n` measurement-uncomputation figure (qianxu Eq. E3). The
      factor-of-2 is the formally-surfaced no-measurement vs. measurement gap.
    • `gidney_adder_RSA2048_tcount` — at the RSA-2048 adder size `q_A = 33`,
      the T-count is `462`, matching the `gidney_adder_RSA2048_T_count_verified`
      paper-claim anchor.
    • `gidney_adder_patched_wellTyped` — the (carry-clean) patched adder is
      WellTyped on `adder_n_qubits bits = 3·bits + 2` qubits.
    • `gidney_adder_verified` — resource AFTER correctness: the one circuit is
      simultaneously sum-correct, read-preserving, and `14·n` T-gates.

  Where to look next:
    • Semantic correctness : `RippleCarryAdderCorrectness.lean`
    • Worked example + QASM : `RippleCarryAdderExample.lean`
    • Supporting proofs : `RippleCarryAdderForwardAndCost.lean` (T-counts +
      forward correctness/reversibility), `RippleCarryAdderClassicalBridge.lean`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderForwardAndCost
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderCorrectness

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims

/-! ## T-count -/

/-- **Gidney adder — T-count (THE headline).** The full gate-explicit
no-measurement n-bit adder uses exactly `14·n` T-gates (`n` forward + `n`
reverse Toffolis at 7 T each; the final-CX cascade is T-free). -/
theorem gidney_adder_tcount (n : Nat) :
    tcount (gidney_adder (n + 2)) = 14 * (n + 2) := by
  unfold gidney_adder
  exact tcount_gidney_adder_full_faithful_no_measurement n

/-- **Gidney adder — the measurement-uncomputation gap.** The gate-explicit
`14·n` T-count is exactly **twice** the `7·n` figure achievable with Gidney's
measurement-based uncomputation (qianxu Eq. E3). Surfacing this factor-of-2 is
the honest statement of the optimization that is costed but not gate-level
formalized. -/
theorem gidney_adder_tcount_vs_measurement (n : Nat) :
    tcount (gidney_adder (n + 2))
      = 2 * gidney_adder_full_with_measurement_uncompute_tcount (n + 2) := by
  unfold gidney_adder
  exact gidney_adder_full_faithful_no_measurement_vs_measurement_factor n

/-! ## RSA-2048 instantiation -/

/-- **RSA-2048 adder T-count = 462.** At the maximum adder size in the
RSA-2048 Shor circuit (`q_A = 33`, qianxu p. 22), the gate-explicit adder has
T-count `14·33 = 462`, matching the verified paper-claim anchor
`gidney_adder_RSA2048_T_count_verified`. -/
theorem gidney_adder_RSA2048_tcount :
    tcount (gidney_adder qianxu_q_A_RSA2048) = gidney_adder_RSA2048_T_count_verified := by
  unfold gidney_adder qianxu_q_A_RSA2048 gidney_adder_RSA2048_T_count_verified
  exact tcount_gidney_adder_full_faithful_no_measurement 31

/-! ## Qubits -/

/-- **Gidney adder — qubit budget.** The carry-clean patched adder is WellTyped
on `adder_n_qubits bits = 3·bits + 2` qubits (`read`, `target`, `carry`
interleaved, `read`/`target` carrying one extra overflow position). -/
theorem gidney_adder_patched_wellTyped (bits : Nat) (hbits : 2 ≤ bits) :
    Gate.WellTyped (adder_n_qubits bits)
      (gidney_adder_full_faithful_no_measurement_patched bits) :=
  gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits

/-! ## Resource after correctness -/

/-- **Gidney adder — verified-with-resource (resource AFTER correctness).**

The single object `gidney_adder (n+2)` is simultaneously:
  1. sum-correct — `target_i = (a+b).testBit i` for all `i < n+2`;
  2. read-preserving — `read_i = a.testBit i` for all `i < n+2`;
  3. `14·(n+2)` T-gates.

The resource bound is stated about *exactly* the circuit the correctness
theorem verifies, so "resource" is established only after "correctness". (For
clean carries + WellTyped, use the patched bundle `gidney_adder_correct_full`.) -/
theorem gidney_adder_verified (n a b : Nat)
    (ha : a < 2 ^ (n + 2)) (hb : b < 2 ^ (n + 2)) :
    (∀ i, i < n + 2 →
        Gate.applyNat (gidney_adder (n + 2)) (adder_input_F (n + 2) a b) (target_idx i)
          = adder_sum_bit_classical a b i)
    ∧ (∀ i, i < n + 2 →
        Gate.applyNat (gidney_adder (n + 2)) (adder_input_F (n + 2) a b) (read_idx i)
          = a.testBit i)
    ∧ tcount (gidney_adder (n + 2)) = 14 * (n + 2) :=
  ⟨gidney_adder_correct (n + 2) a b (by omega) ha hb,
   gidney_adder_read_preserved (n + 2) a b (by omega) ha hb,
   gidney_adder_tcount n⟩

end FormalRV.BQAlgo
