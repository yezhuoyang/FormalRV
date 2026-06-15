/-
  Audit · cain-xu-2026 · DERIVED-k  (OFF the default build path)
  ----------------------------------------------------------------------------
  The expensive GF(2)-rank "derived k" results for the real memory codes:
  `native_decide` Gaussian elimination over large parity matrices (lp_20 is
  4350 columns → ~hundreds of seconds to compile). These theorems are NOT
  depended on by any `#verify_clean`'d result (the gated headline
  `qianxu_verified_upper_bound` uses only Nat-arithmetic bounds), so they live
  in this standalone file kept OFF the default build path. Build on demand:

    lake build FormalRV.Audit.CainXu2026.CodeKDerived
-/
import FormalRV.Audit.CainXu2026.L4_Code
import FormalRV.QEC.Instances
import FormalRV.QEC.CodeDimension
import FormalRV.QEC.GF2Rank

namespace FormalRV.Audit.CainXu2026

open FormalRV.QEC.Instances
open FormalRV.QEC   -- general `derivedK`
open FormalRV.Framework.LDPC   -- `rank` (GF(2) Gaussian-elimination rank)

/-! ## bb18 [[248,10,18]] — k derived from the constructed matrices -/

/-- bb18's n is kernel-clean (the easy half). -/
theorem bb18_n : bb18.n = 248 := by decide

/-- **bb18's k = 10, DERIVED from its constructed matrices** (n=248, rank H_X =
    rank H_Z = 119), matching `[[248,10,18]]`.  Certificate: `native_decide`
    (kernel `decide` times out at 248 qubits). -/
theorem bb18_k_derived : derivedK bb18 = 10 := by
  unfold derivedK; native_decide

/-- The derived k matches the paper's reported logical count for bb18. -/
theorem bb18_k_matches_paper : derivedK bb18 = 10 := bb18_k_derived

/-! ## lp_16 / lp_20 — k derived from the parity matrices -/

/-- **lp_16^{3,7}: k = 744, derived from the parity matrices** (n=2610, rank H_X =
    rank H_Z = 933), matching [[2610, 744, 16]].  Certified by `native_decide`. -/
theorem lp16_k_derived : lp16.n - rank lp16.hx - rank lp16.hz = 744 := by native_decide

/-- **lp_20^{3,7}: k = 1224, DERIVED from the parity matrices** (n=4350), matching
    [[4350,1224,20]].  Certified by `native_decide` (4350 columns). -/
theorem lp20_k_derived : lp20.n - rank lp20.hx - rank lp20.hz = 1224 := by native_decide

/-! ## The headline report (bundles the derived-k with the L4_Code brackets) -/

/-- **FULL LP-CODE REPORT.**  lp_16's logical count is DERIVED (=744); the full
    lp_20 instance qubit resource is bracketed [4350, 14961] with a 4961
    optimization gap; the time is bracketed with a ~1000× parallelisation gap. -/
theorem full_lp_report :
    lp16.n - rank lp16.hx - rank lp16.hz = 744
    ∧ lp20_qubit_bounds.bracketed = true ∧ lp20_qubit_bounds.optimizationGap = 4_961
    ∧ lp20_time_bounds.bracketed = true := by
  refine ⟨lp16_k_derived, lp20_qubit_bracketed, lp20_qubit_gap, lp20_time_bracketed⟩

end FormalRV.Audit.CainXu2026

-- ➗ k DERIVED from the constructed matrices via GF(2) rank (native_decide):
#check @FormalRV.Audit.CainXu2026.bb18_k_derived        -- bb18 k = 10
#check @FormalRV.Audit.CainXu2026.lp20_k_derived        -- lp_20 k = 1224
