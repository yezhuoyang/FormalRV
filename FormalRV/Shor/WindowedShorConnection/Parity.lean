/- WindowedShorConnection — Â§6 even-bits parity restriction is WLOG.
   Part of the `WindowedShorConnection` re-export shim (same namespace). -/
import FormalRV.Shor.WindowedShorConnection.SwapCascade

namespace FormalRV.BQAlgo.WindowedShorConnection

open FormalRV.SQIRPort
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open VerifiedShor
open VerifiedShor.Windowed

/-! ## §6. Gap 2 — the even-`bits` (parity) restriction is WLOG.

    `windowedForwardGate_apply` needs `2 ∣ bits` (windowSize-2 exact
    coverage `2·numWin = bits`).  We close this as a genuine
    non-restriction: the Shor data-register width is a free parameter,
    and for any `N` one can always pick an EVEN width that still
    satisfies both the sizing predicate and the (relaxed) Shor
    setting.  Hence requiring even `bits` costs nothing.

    These are real, kernel-clean lemmas (monotonicity of the two
    predicates in the register width, plus an even-width existence
    witness at `log₂(2N)+1` rounded up to even). -/

/-- The relaxed Shor setting only constrains the data width through
    `N < 2^n`, which is monotone in `n`; so it transfers to any wider
    register. -/
theorem BasicSettingRelaxed_bits_mono
    {a r N m n n' : Nat} (h : BasicSettingRelaxed a r N m n) (hle : n ≤ n') :
    BasicSettingRelaxed a r N m n' :=
  ⟨h.1, h.2.1, h.2.2.1,
    Nat.lt_of_lt_of_le h.2.2.2 (Nat.pow_le_pow_right (by omega) hle)⟩

/-- Verified-circuit sizing is monotone in the register width. -/
theorem VerifiedCircuitSizing_bits_mono
    {N n n' : Nat} (h : VerifiedCircuitSizing N n) (hle : n ≤ n') :
    VerifiedCircuitSizing N n' :=
  ⟨le_trans h.1 hle,
   le_trans h.2.1 (Nat.pow_le_pow_right (by omega) hle),
   le_trans h.2.2 (Nat.pow_le_pow_right (by omega) hle)⟩

/-- **Even-width sizing always exists.** For any `N > 0` there is an
    even data width satisfying `VerifiedCircuitSizing`.  Witness:
    `log₂(2N)+1` rounded up to even.  This discharges the `2 ∣ bits`
    hypothesis as a free choice. -/
theorem exists_even_bits_sizing (N : Nat) (hN : 0 < N) :
    ∃ bits, 2 ∣ bits ∧ VerifiedCircuitSizing N bits := by
  have h0 : VerifiedCircuitSizing N (Nat.log2 (2 * N) + 1) :=
    VerifiedCircuitSizing_canonical_pow2_succ N hN
  exact ⟨(Nat.log2 (2 * N) + 1) + (Nat.log2 (2 * N) + 1) % 2,
    by omega, VerifiedCircuitSizing_bits_mono h0 (by omega)⟩

/-- **Even-width setting always exists.** Given a relaxed Shor setting
    at some width, there is an even width `≥` it that satisfies both
    the setting and the sizing — the canonical instantiation point for
    the windowed family once its in-place completion (gap 1) lands. -/
theorem exists_even_bits_setting_sizing
    {a r N m n : Nat} (hN : 0 < N) (h_setting : BasicSettingRelaxed a r N m n) :
    ∃ bits, n ≤ bits ∧ 2 ∣ bits
      ∧ BasicSettingRelaxed a r N m bits ∧ VerifiedCircuitSizing N bits := by
  have h0 : VerifiedCircuitSizing N (Nat.log2 (2 * N) + 1) :=
    VerifiedCircuitSizing_canonical_pow2_succ N hN
  -- Round (max n (log₂(2N)+1)) up to even.
  set base := max n (Nat.log2 (2 * N) + 1) with hbase
  refine ⟨base + base % 2, by omega, by omega,
    BasicSettingRelaxed_bits_mono h_setting (by omega),
    VerifiedCircuitSizing_bits_mono h0 (by omega)⟩


end FormalRV.BQAlgo.WindowedShorConnection
