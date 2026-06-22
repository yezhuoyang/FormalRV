/-
  FormalRV.Audit.Gidney2025.GidneyCheapModMulConnection — importing the cost-optimal canonical
  windowed multiplier `gcMul` into the Gidney-2025 audit (the audit's listed "import the capstones"
  action), now MEANINGFUL because `gcMul`'s count is PROVEN EQUAL to Gidney-2025's per-gadget cost
  model (`lookupCost + addCost`), gadget-for-gadget — no over-count.

  This connects the standalone `gcMul_shor_resource_capstone` to THIS paper: the cost-optimal,
  canonical-arithmetic (in-register-reduced, `< N` — no coset rep, no `adaptOut`), measured windowed
  multiplier drives Shor success AND its per-window / whole cost is exactly Gidney-2025's verified
  loop-body figures.

  HONEST SCOPE: this is the PER-MULTIPLICATION cost in Gidney-2025's terms (`numWin·(lookupCost+
  addCost)`), NOT the full `6.5×10⁹` modexp schedule total (which is a sum over the exponent loop —
  the schedule tally `gidney2025_toffoli_mixed_actualP` already reproduces that to ~6%).  Here we pin
  the cost-optimal multiplier's per-window cost to the paper's verified gadget model, on a
  success-driving canonical circuit.  Order-finding is standard QPE (not Ekerå–Håstad), and the
  success bound rides the reversible family bridged per-encoded-basis-state to the measured gate
  (the witness `egate_matches_rev`, genuinely discharged) — the same legitimate structure as
  `measWindowed_shor_resource_capstone`.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyCheapModMulShor

namespace FormalRV.Audit.Gidney2025

open FormalRV.SQIRPort
open VerifiedShor
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.GidneyCheapModMul
open FormalRV.Shor.GidneyCheapModMulInPlace
open FormalRV.Shor.GidneyCheapModMulShor
open FormalRV.Audit.Gidney2025.ToffoliReproduction
open FormalRV.BQAlgo.MultiplierInstances
open FormalRV.BQAlgo (gidney_target_val)

/-- The measured per-iterate gate's Toffoli count, in Gidney-2025's per-gadget terms:
    `2·numWin·(lookupCost + addCost)` (the in-place 2-pass Bennett multiplier). -/
theorem toffoli_gcMulEncodeGate_eq_gidney2025 (w n a ainv N numWin : Nat) :
    EGate.toffoli (gcMulEncodeGate w (n + 1) a ainv N numWin)
      = 2 * (numWin * (lookupCost w + addCost (n + 1))) := by
  rw [toffoli_gcMulEncodeGate]
  unfold lookupCost addCost; ring

/-- **★ GIDNEY-2025 COST-OPTIMAL CANONICAL SHOR ★** — the cost-optimal, canonical-arithmetic,
    measured windowed multiplier `gcMul`/`gcMulEncodeGate` (Babbush lookup + Gidney-2025's 2-add
    register modular-add), imported into the Gidney-2025 audit:

    1. the family it realizes attains the Shor success bound `≥ κ/(log₂N)⁴`;
    2. its per-window Toffoli cost is EXACTLY Gidney-2025's loop body `lookupCost w + addCost (bits)`;
    3. its whole-multiplier count is `numWin·(lookupCost + addCost)`;
    4. its measured per-iterate (in-place) count is `2·numWin·(lookupCost + addCost)`;
    5. its output is the CANONICAL residue `(a·x) mod N` (`< N`) in-register — no coset rep,
       no `adaptOut` obligation (the audit's "non-canonical arithmetic" obstruction is ABSENT). -/
theorem gidney2025_cost_optimal_canonical_shor
    (w n numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = n + 1)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ (n + 1)) (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m (n + 1)) :
    probability_of_success a r N m (n + 1) (3 * (n + 1) + w + 7)
        (gcRevFamily w (n + 1) numWin N a ainv0 hw hbits (by omega) hN1 hN2 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4
    ∧ (∀ j, EGate.toffoli (gcStep w (n + 1) a N numWin j) = lookupCost w + addCost (n + 1))
    ∧ EGate.toffoli (gcMul w (n + 1) a N numWin) = numWin * (lookupCost w + addCost (n + 1))
    ∧ (∀ i, EGate.toffoli (gcMulEncodeGate w (n + 1) ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i))) N numWin)
        = 2 * (numWin * (lookupCost w + addCost (n + 1))))
    ∧ (∀ x, x < N → gidney_target_val (n + 1)
        (EGate.applyNat (gcMul w (n + 1) a N numWin) (gcInit w (n + 1) numWin x)) = (a * x) % N) := by
  have hxpow : ∀ x, x < N → x < (2 ^ w) ^ numWin := by
    intro x hx
    have hpw : (2 ^ w) ^ numWin = 2 ^ (n + 1) := by rw [← pow_mul, Nat.mul_comm w numWin, hbits]
    rw [hpw]; exact lt_of_lt_of_le hx (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (gcMul_shor_resource_capstone w n numWin N a ainv0 r m hw hbits hN1 hN2 h_inv0 h_setting).1
  · exact fun j => gcStep_eq_gidney2025_loopBody w n a N numWin j
  · exact gcMul_count_eq_gidney2025 w n a N numWin
  · exact fun i => toffoli_gcMulEncodeGate_eq_gidney2025 w n ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i))) N numWin
  · exact fun x hx => gcMul_value_init w n a N numWin x hw (by omega) (by omega) hbits (hxpow x hx)

end FormalRV.Audit.Gidney2025
