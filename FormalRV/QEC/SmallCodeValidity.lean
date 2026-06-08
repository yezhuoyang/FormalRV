/-
  FormalRV.QEC.SmallCodeValidity — M2 (WS2'): kernel-clean validity for a small real code.

  Audit gaps H7/H8: for the large LP codes, css_condition (H_X·H_Z^T = 0) is unproven and the
  derived k uses `native_decide` (not kernel-clean) — so the advertised k is "rank arithmetic on
  an object not proven to be a valid CSS code." Per the locked "small real code first" plan, this
  file pins a fully kernel-clean foundation on the Steane [[7,1,3]] code:

    • it IS a CSS code (css_condition by `decide`, NOT native_decide), and
    • its rank-derived dimension k = 1 (by `decide`), and
    • that k is MEANINGFUL: it equals the size of an explicit, independently-valid logical basis.

  No `sorry`, no new `axiom`, no `native_decide`; all three theorems are #verify_clean-gated.
  (Next M2 step: the [[18,2,d]] bivariate-bicycle code; then the homological derivedK = logical-dim
  bridge that makes the rank formula meaningful for codes too large to `decide`.)
-/
import FormalRV.QEC.Logical
import FormalRV.QEC.LogicalFinder
import FormalRV.QEC.CodeDimension
import FormalRV.Verifier.ProofGate

namespace FormalRV.QEC

open FormalRV.QEC.LogicalFinder

/-- **Steane is a genuine CSS code** — `H_X · H_Z^T = 0`, by kernel `decide` (not `native_decide`). -/
theorem steaneCSS_is_CSS : steaneCSS.css_condition = true := by decide

/-- **Steane derived dimension** `k = n − rank H_X − rank H_Z = 1`, by kernel `decide`. -/
theorem steaneCSS_k_derived : derivedK steaneCSS = 1 := by decide

/-- **★ M2 — `derivedK` is a MEANINGFUL logical count for Steane (kernel-clean).**
The rank-derived dimension `k = 1` is corroborated three independent ways: the code genuinely
satisfies the CSS condition, the rank formula gives `1`, and there exists an explicit, separately
-verified valid logical basis of exactly that size (`steaneLogical : LogicalBasis steaneCSS 1`).
So here `derivedK` is the true logical-qubit count, not rank arithmetic on a non-code — the kernel
-clean small-code anchor the end-to-end capstone (M4) is built on. -/
theorem steane_valid_code_k1 :
    steaneCSS.css_condition = true
    ∧ derivedK steaneCSS = 1
    ∧ steaneLogical.valid = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## The [[18,2,d]] bivariate-bicycle code (the CainXu2026 BB family) — now KERNEL-clean.

The audit (H8) flagged that the BB/LP codes' `derivedK` used `native_decide` (the `ofReduceBool`
axiom, outside the kernel). For this [[18,2,d]] code that is unnecessary: kernel `decide` discharges
both the CSS condition and the rank-derived `k = 2` (it is slower than native, but real, axiom-clean,
and accepted by the project's own gate). -/

/-- **bbSmall is a genuine CSS code** (`H_X·H_Z^T = 0`), by kernel `decide` — NOT `native_decide`. -/
theorem bbSmall_is_CSS : bbSmall.css_condition = true := by decide

/-- **bbSmall derived dimension** `k = 2` by kernel `decide` (replaces the audited native_decide). -/
theorem bbSmall_k_derived : derivedK bbSmall = 2 := by decide

/-- **★ M2 — `derivedK = 2` is a MEANINGFUL logical count for the [[18,2,d]] BB code (kernel-clean).**
As for Steane: genuinely CSS, rank-derived `k = 2`, and an explicit valid logical basis of exactly
size 2 (`bbSmallLogicalBasis`) exists — all by kernel `decide`, all `#verify_clean`-accepted. This is
the BB-code family CainXu2026 uses, now with a kernel-clean (not native) dimension. -/
theorem bbSmall_valid_code_k2 :
    bbSmall.css_condition = true
    ∧ derivedK bbSmall = 2
    ∧ bbSmallLogicalBasis.valid = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Anti-cheat gate: the build FAILS if these stop being kernel-clean (no native_decide allowed). -/

#verify_clean steaneCSS_is_CSS
#verify_clean steaneCSS_k_derived
#verify_clean steane_valid_code_k1
#verify_clean bbSmall_is_CSS
#verify_clean bbSmall_k_derived
#verify_clean bbSmall_valid_code_k2

end FormalRV.QEC
